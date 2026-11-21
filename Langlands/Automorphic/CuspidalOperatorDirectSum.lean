import Langlands.Automorphic.CuspidalOperatorSemisimplicity
import Langlands.Automorphic.CuspidalOperatorRealization
import Mathlib.LinearAlgebra.DFinsupp

/-! Actual cuspidal factors and their algebraic direct-sum projections. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

namespace Langlands.Automorphic

open Global _root_.Representation
open scoped MonoidAlgebra

attribute [local instance] subquotientRationalGroup subquotientContinuousGroup
  subquotientSmoothGroup subquotientFormGroup subquotientStableGroup subquotientRealizationGroup

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
  {r : ℕ} (S : OperatorRealization F (r + 1))

/-- The natural inclusion of a contained operator realization. -/
def OperatorRealization.inclusionOfLE {T : OperatorRealization F (r + 1)} (h : T ≤ S) :
    T.representation.IntertwiningMap S.representation where
  toLinearMap := Submodule.inclusion h
  isIntertwining' _ := LinearMap.ext fun _ => rfl

set_option maxHeartbeats 650000 in
/-- Coordinates in an algebraic direct sum of actual irreducible cuspidal subrealizations. -/
structure CuspidalOperatorDirectSum where
  Index : Type u
  factor : Index → CuspidalOperatorRealization F r
  factor_le : ∀ i, (factor i).realization ≤ S
  project : ∀ i, S.representation.IntertwiningMap (factor i).realization.representation
  project_inclusion_same : ∀ i (v : (factor i).realization.Space),
    project i (S.inclusionOfLE (factor_le i) v) = v
  project_inclusion_ne : ∀ i j, j ≠ i → ∀ v : (factor i).realization.Space,
    project j (S.inclusionOfLE (factor_le i) v) = 0
  finite_sum : ∀ x : S.Space, ∃ s : Finset Index,
    (∀ i ∉ s, project i x = 0) ∧
      (∑ i ∈ s, S.inclusionOfLE (factor_le i) (project i x)) = x

theorem CuspidalOperatorDirectSum.finite_support (D : CuspidalOperatorDirectSum S) (x : S.Space) :
    {i | D.project i x ≠ 0}.Finite := by
  obtain ⟨s, hs, _⟩ := D.finite_sum x
  exact s.finite_toSet.subset fun i hi => by
    by_contra h
    exact hi (hs i h)

theorem CuspidalOperatorDirectSum.project_eq_zero_detects (D : CuspidalOperatorDirectSum S)
    (x : S.Space) (h : ∀ i, D.project i x = 0) : x = 0 := by
  obtain ⟨s, _, hs⟩ := D.finite_sum x
  rw [← hs]
  simp [h]

private abbrev OperatorRing := ℂ[automorphicOperatorAlgebra F (r + 1)]

private def imageRealization
    (P : Submodule (OperatorRing (F := F) (r := r)) S.representation.asModule) :
    OperatorRealization F (r + 1) :=
  Subrepresentation.ofSubmodule' (P.map (IntertwiningMap.equivLinearMapAsModule _ _ S.inclusion))

omit [CompactSpace (AdeleQuotient F)] in
private theorem imageRealization_le
    (P : Submodule (OperatorRing (F := F) (r := r)) S.representation.asModule) :
    imageRealization S P ≤ S := by
  intro x hx
  change x ∈ P.map (IntertwiningMap.equivLinearMapAsModule _ _ S.inclusion) at hx
  obtain ⟨y, _, he⟩ := hx
  change y.val = x at he
  exact he ▸ y.property

set_option maxHeartbeats 850000 in
private def imageRealizationEquiv
    (P : Submodule (OperatorRing (F := F) (r := r)) S.representation.asModule) :
    (imageRealization S P).representation.asModule ≃ₗ[OperatorRing (F := F) (r := r)] P := by
  let R := OperatorRing (F := F) (r := r)
  let T := imageRealization S P
  let a : T.representation.IntertwiningMap S.representation :=
    S.inclusionOfLE (imageRealization_le S P)
  let b : T.representation.asModule →ₗ[R] S.representation.asModule :=
    IntertwiningMap.equivLinearMapAsModule _ _ a
  let j : S.representation.asModule →ₗ[R] (stableAutomorphicAction F (r + 1)).asModule :=
    IntertwiningMap.equivLinearMapAsModule _ _ S.inclusion
  let c : T.representation.asModule →ₗ[R] P := b.codRestrict P fun x => by
    have hx : x.val ∈ P.map j := x.property
    obtain ⟨y, hy, he⟩ := hx
    have h : y = b x := Subtype.ext he
    exact h ▸ hy
  refine LinearEquiv.ofBijective c ⟨?_, ?_⟩
  · intro x y h
    apply Subtype.ext
    exact congrArg (fun w : P => w.val.val) h
  · intro x
    have hx : j x.val ∈ P.map j := Submodule.mem_map_of_mem x.property
    refine ⟨⟨j x.val, hx⟩, ?_⟩
    apply Subtype.ext
    rfl

private def cuspidalImageRealization (hS : S.IsCuspidal)
    (P : Submodule (OperatorRing (F := F) (r := r)) S.representation.asModule)
    (hP : IsSimpleModule (OperatorRing (F := F) (r := r)) P) : CuspidalOperatorRealization F r where
  realization := imageRealization S P
  irreducible := (irreducible_iff_isSimpleModule_asModule _).mpr
    ((imageRealizationEquiv S P).isSimpleModule_iff.mpr hP)
  cuspidal := ((imageRealization S P).isCuspidal_iff).mpr fun f =>
    S.isCuspidal_iff.mp hS ⟨f.val, imageRealization_le S P f.property⟩

private theorem exists_coordinates_for_semisimpleModule
    {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] [IsSemisimpleModule R M] :
    ∃ (s : Set (Submodule R M)) (c : ∀ i : s, M →ₗ[R] i.val),
      (∀ i : s, IsSimpleModule R i.val) ∧
      (∀ (i : s) (v : i.val), c i v.val = v) ∧
      (∀ (i j : s), j ≠ i → ∀ v : i.val, c j v.val = 0) ∧
      ∀ x, ∃ t : Finset s, (∀ i ∉ t, c i x = 0) ∧ (∑ i ∈ t, (c i x).val) = x := by
  classical
  obtain ⟨s, hsind, hs, hsimp⟩ := IsSemisimpleModule.exists_sSupIndep_sSup_simples_eq_top R M
  let P := fun i : s => i.val
  let sumMap : (Π₀ i : s, P i) →ₗ[R] M := DFinsupp.lsum ℕ (fun i => (P i).subtype)
  have hinj : Function.Injective sumMap := ((sSupIndep_iff s).mp hsind).dfinsupp_lsum_injective
  have hsurj : Function.Surjective sumMap := LinearMap.range_eq_top.mp (by
    rw [← Submodule.iSup_eq_range_dfinsupp_lsum P, ← sSup_eq_iSup', hs])
  let e := (LinearEquiv.ofBijective sumMap ⟨hinj, hsurj⟩).symm
  let c (i : s) : M →ₗ[R] i.val := (DFinsupp.lapply i).comp e.toLinearMap
  have hsingle (i : s) (v : i.val) : e v.val = DFinsupp.single i v := by
    have he : e.symm (DFinsupp.single i v) = v.val :=
      DFinsupp.lsum_single ℕ (fun i => (P i).subtype) i v
    rw [← he, e.apply_symm_apply]
  refine ⟨s, c, fun i => hsimp i.val i.property, ?_, ?_, ?_⟩
  · intro i v
    change e v.val i = v
    rw [hsingle, DFinsupp.single_eq_same]
  · intro i j hne v
    change e v.val j = 0
    rw [hsingle, DFinsupp.single_eq_of_ne hne]
  · intro x
    refine ⟨(e x).support, fun i hi => DFinsupp.notMem_support_iff.mp hi, ?_⟩
    have hsum : sumMap (e x) = x := e.symm_apply_apply x
    change (∑ i ∈ (e x).support, (e x i).val) = x
    simpa only [sumMap, DFinsupp.lsum_apply_apply, DFinsupp.sumAddHom_apply, DFinsupp.sum,
      LinearMap.toAddMonoidHom_coe, Submodule.subtype_apply] using hsum

set_option maxHeartbeats 2500000 in
/-- A semisimple cuspidal operator realization admits actual cuspidal
subrealizations with finite algebraic support and full equivariant projections. -/
theorem exists_cuspidalOperatorDirectSum (hS : S.IsCuspidal)
    (hsemi : S.representation.IsSemisimpleRepresentation) : Nonempty (CuspidalOperatorDirectSum S) := by
  classical
  let R := OperatorRing (F := F) (r := r)
  let M := S.representation.asModule
  have : IsSemisimpleModule R M :=
    (isSemisimpleRepresentation_iff_isSemisimpleModule_asModule _).mp hsemi
  obtain ⟨s, c, hsimp, hsame, hne, hsum⟩ :=
    exists_coordinates_for_semisimpleModule (R := R) (M := M)
  let T := fun i : s => cuspidalImageRealization S hS i.val (hsimp i)
  let p : ∀ i : s, S.representation.IntertwiningMap (T i).realization.representation :=
    fun i => (IntertwiningMap.equivLinearMapAsModule _ _).symm
      ((imageRealizationEquiv S i.val).symm.toLinearMap ∘ₗ c i)
  have hp (i : s) (x : S.Space) : imageRealizationEquiv S i.val (p i x) = c i x :=
    (imageRealizationEquiv S i.val).apply_symm_apply (c i x)
  refine ⟨⟨s, T, fun i => imageRealization_le S i.val, p, ?_, ?_, ?_⟩⟩
  · intro i v
    apply (imageRealizationEquiv S i.val).injective
    exact (hp i _).trans (hsame i (imageRealizationEquiv S i.val v))
  · intro i j hij v
    apply (imageRealizationEquiv S j.val).injective
    exact (hp j _).trans ((hne i j hij (imageRealizationEquiv S i.val v)).trans
      (imageRealizationEquiv S j.val).map_zero.symm)
  · intro x
    obtain ⟨t, ht, he⟩ := hsum x
    refine ⟨t, fun i hi => ?_, ?_⟩
    · exact (congrArg (imageRealizationEquiv S i.val).symm (ht i hi)).trans
        (imageRealizationEquiv S i.val).symm.map_zero
    · exact (Finset.sum_congr rfl (fun i _ => congrArg Subtype.val (hp i x))).trans he

/-- A chosen algebraic direct sum at a fixed unitary central character. -/
def cuspidalOperatorDirectSumOfUnitaryCentralCharacter (hS : S.IsCuspidal)
    (χ : HeckeCharacter F) (hχ : χ.IsUnitary) (hSχ : S.HasCentralCharacter χ) :
    CuspidalOperatorDirectSum S :=
  Classical.choice (exists_cuspidalOperatorDirectSum S hS
    (CuspidalAdmissible.isSemisimpleRepresentation_of_cuspidal_of_unitaryCentralCharacter S
      (Nat.succ_ne_zero r) hS χ hχ hSχ))

end Langlands.Automorphic
