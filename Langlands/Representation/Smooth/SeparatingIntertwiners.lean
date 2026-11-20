import Langlands.Representation.FiniteVectors
import Langlands.Representation.Smooth.Factorization.TwoFactorExistenceProof
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.RingTheory.Artinian.Module

/-! An irreducible subrepresentation in a nonzero image of a smooth
representation with separating intertwiners to an admissible Artinian one. -/

noncomputable section

namespace Langlands

open Representation FiniteVectors TwoFactorExistence
open scoped MonoidAlgebra

universe uG uV uW uX

variable {G : Type uG} [Group G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {X : Type uX} [AddCommGroup X] [Module ℂ X]

/-- The intertwining maps to `σ` jointly separate the vectors of `ρ`. -/
def HasSeparatingIntertwiners (ρ : Representation ℂ G V) (σ : Representation ℂ G W) : Prop :=
  ∀ x, (∀ f : ρ.IntertwiningMap σ, f x = 0) → x = 0

variable {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
  {τ : Representation ℂ G X}

private theorem exists_restriction_of_finite_separation
    (q : ρ.IntertwiningMap τ) (s : Finset (ρ.IntertwiningMap σ)) (P : Subrepresentation ρ)
    (hne : ∃ x ∈ P, q x ≠ 0)
    (hker : ∀ x ∈ P, (∀ f ∈ s, f x = 0) → q x = 0) :
    ∃ (U : Subrepresentation ρ) (f : ρ.IntertwiningMap σ),
      (∃ x ∈ U, q x ≠ 0) ∧ ∀ x ∈ U, f x = 0 → q x = 0 := by
  classical
  induction s using Finset.induction_on generalizing P with
  | empty =>
      obtain ⟨x, hx, hqx⟩ := hne
      exact (hqx (hker x hx (by simp))).elim
  | @insert f s hfs ih =>
      by_cases h : ∃ x ∈ P ⊓ f.ker, q x ≠ 0
      · refine ih (P ⊓ f.ker) h fun x hx hs => hker x hx.1 ?_
        intro g hg
        rcases Finset.mem_insert.mp hg with rfl | hg
        · exact hx.2
        · exact hs g hg
      · exact ⟨P, f, hne, fun x hx hfx => by
          by_contra hqx
          exact h ⟨x, ⟨hx, hfx⟩, hqx⟩⟩

/-- Factor `q` through the actual image of `f` when `q` kills its kernel. -/
private theorem exists_descendToRange (f : ρ.IntertwiningMap σ) (q : ρ.IntertwiningMap τ)
    (hker : f.toLinearMap.ker ≤ q.toLinearMap.ker) :
    ∃ d : f.range.toRepresentation.IntertwiningMap τ,
      ∀ x, d (f.toLinearMap.rangeRestrict x) = q x := by
  let d : f.range.toSubmodule →ₗ[ℂ] X :=
    (f.toLinearMap.ker.liftQ q.toLinearMap hker) ∘ₗ
      f.toLinearMap.quotKerEquivRange.symm.toLinearMap
  have hd (x : V) : d (f.toLinearMap.rangeRestrict x) = q x := by
    change f.toLinearMap.ker.liftQ q.toLinearMap hker
      (f.toLinearMap.quotKerEquivRange.symm (f.toLinearMap.rangeRestrict x)) = q x
    have h : f.toLinearMap.quotKerEquivRange.symm (f.toLinearMap.rangeRestrict x) =
        f.toLinearMap.ker.mkQ x :=
      LinearMap.quotKerEquivRange_symm_apply_image f.toLinearMap x _
    rw [h]
    rfl
  refine ⟨d.intertwiningMap_of_isIntertwiningMap _ _ (fun g v => ?_), hd⟩
  obtain ⟨x, rfl⟩ := f.toLinearMap.surjective_rangeRestrict v
  have hfx : f.range.toRepresentation g (f.toLinearMap.rangeRestrict x) =
      f.toLinearMap.rangeRestrict (ρ g x) := by
    apply Subtype.ext
    change σ g (f x) = f (ρ g x)
    exact (IntertwiningMap.isIntertwining ρ σ f g x).symm
  calc
    _ = d (f.toLinearMap.rangeRestrict (ρ g x)) := congrArg d hfx
    _ = q (ρ g x) := hd _
    _ = τ g (q x) := IntertwiningMap.isIntertwining ρ τ q g x
    _ = _ := congrArg (τ g) (hd x).symm

private theorem exists_irreducible_subrepresentation_of_image
    (hArt : IsArtinian ℂ[G] σ.asModule)
    (N : Subrepresentation σ) (d : N.toRepresentation.IntertwiningMap τ)
    (hd : ∃ x, d x ≠ 0) :
    ∃ (S : Subrepresentation τ), S.toRepresentation.IsIrreducible ∧
      ∃ (T : Subrepresentation σ) (p : T.toRepresentation.IntertwiningMap S.toRepresentation),
        Function.Surjective p := by
  let := hArt
  let j := IntertwiningMap.equivLinearMapAsModule _ _ (subtypeHom N)
  let : IsArtinian ℂ[G] N.toRepresentation.asModule :=
    isArtinian_of_injective j N.toSubmodule.injective_subtype
  let d' := IntertwiningMap.equivLinearMapAsModule _ _ d
  let I := d'.range
  let : IsArtinian ℂ[G] I :=
    isArtinian_of_surjective _ d'.rangeRestrict d'.surjective_rangeRestrict
  obtain ⟨x, hx⟩ := hd
  let : Nontrivial I := ⟨⟨d'.rangeRestrict x, 0, fun h => hx (congrArg Subtype.val h)⟩⟩
  obtain ⟨M, hM⟩ := IsAtomic.exists_atom (Submodule ℂ[G] I)
  let Sg := M.map I.subtype
  let S : Subrepresentation τ := Subrepresentation.ofSubmodule' Sg
  let iS : S.toRepresentation.asModule →ₗ[ℂ[G]] Sg :=
    (IntertwiningMap.equivLinearMapAsModule _ _ (subtypeHom S)).codRestrict Sg (fun v => v.2)
  have hiS : Function.Bijective iS :=
    ⟨fun _ _ h => Subtype.ext (congrArg Subtype.val h), fun v => ⟨⟨v.1, v.2⟩, rfl⟩⟩
  have hSg : IsSimpleModule ℂ[G] Sg := by
    let e := M.equivMapOfInjective I.subtype I.injective_subtype
    exact (e.toLinearMap.isSimpleModule_iff_of_bijective e.bijective).mp
      (isSimpleModule_iff_isAtom.mpr hM)
  have hS : S.toRepresentation.IsIrreducible :=
    (irreducible_iff_isSimpleModule_asModule _).mpr
      ((iS.isSimpleModule_iff_of_bijective hiS).mpr hSg)
  let T : Subrepresentation σ :=
    { toSubmodule := (S.toSubmodule.comap d.toLinearMap).map N.toSubmodule.subtype
      apply_mem_toSubmodule g := by
        rintro _ ⟨v, hv, rfl⟩
        refine ⟨N.toRepresentation g v, ?_, rfl⟩
        change d (N.toRepresentation g v) ∈ S
        rw [d.isIntertwining]
        exact S.apply_mem_toSubmodule g hv }
  have hTN : T.toSubmodule ≤ N.toSubmodule := Submodule.map_subtype_le _ _
  have hT (v : T.toSubmodule) : d (Submodule.inclusion hTN v) ∈ S := by
    obtain ⟨w, hw, he⟩ := v.2
    have hev : Submodule.inclusion hTN v = w := Subtype.ext he.symm
    rw [hev]
    exact hw
  let p : T.toRepresentation.IntertwiningMap S.toRepresentation :=
    { toLinearMap := (d.toLinearMap ∘ₗ Submodule.inclusion hTN).codRestrict _ hT
      isIntertwining' g := by
        apply LinearMap.ext
        intro v
        apply Subtype.ext
        exact IntertwiningMap.isIntertwining N.toRepresentation τ d g
          (Submodule.inclusion hTN v) }
  refine ⟨S, hS, T, p, fun v => ?_⟩
  have hv : v.val ∈ I := Submodule.map_subtype_le I M v.2
  obtain ⟨w, hw⟩ := hv
  have hw' : d w = v.val := hw
  have hwS : d w ∈ S := by
    rw [hw']
    exact v.2
  exact ⟨⟨w.1, w, hwS, rfl⟩, Subtype.ext hw'⟩

variable [TopologicalSpace G]

/-- Evaluation on the generator embeds the intertwiner space from a smooth
cyclic orbit into one finite-dimensional fixed space of the target. -/
theorem finiteDimensional_intertwiningMap_orbit (hσ : IsAdmissible σ) {x : V}
    (hx : IsSmoothVector ρ x) :
    FiniteDimensional ℂ ((orbitSubrepresentation ρ x).toRepresentation.IntertwiningMap σ) := by
  let C := orbitSubrepresentation ρ x
  let e : C.toSubmodule := ⟨x, self_mem_orbitSpan ρ x⟩
  obtain ⟨L, hL⟩ := hx
  have he (k : L) : C.toRepresentation k.val e = e := Subtype.ext (hL k)
  let ev : (C.toRepresentation.IntertwiningMap σ) →ₗ[ℂ] fixedVectors σ L.toSubgroup :=
    { toFun := fun f => ⟨f e, fun k => by
        change σ (k : G) (f e) = f e
        rw [← f.isIntertwining, he k]⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let := hσ.2 L
  refine FiniteDimensional.of_injective ev (LinearMap.ker_eq_bot.mp
    (LinearMap.ker_eq_bot'.mpr fun f hf => ?_))
  have hf₀ : f e = 0 := congrArg Subtype.val hf
  have hspan : C.toSubmodule ≤ f.ker.toSubmodule.map C.toSubmodule.subtype := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨g, rfl⟩
    refine ⟨C.toRepresentation g e, ?_, rfl⟩
    change f (C.toRepresentation g e) = 0
    rw [f.isIntertwining, hf₀, map_zero]
  apply IntertwiningMap.ext
  ext v
  obtain ⟨w, hw, heq⟩ := hspan v.2
  have hw' : f w = 0 := hw
  have hwv : w = v := Subtype.ext heq
  exact hwv ▸ hw'

/-- A nonzero image of a smooth `ρ` with separating intertwiners to an
admissible Artinian `σ` contains an irreducible subrepresentation which
is a quotient of an actual subrepresentation of `σ`. -/
theorem HasSeparatingIntertwiners.exists_irreducible_subrepresentation
    (hsep : HasSeparatingIntertwiners ρ σ) (hρ : IsSmooth ρ) (hσ : IsAdmissible σ)
    (hArt : IsArtinian ℂ[G] σ.asModule)
    (q : ρ.IntertwiningMap τ) (hq : ∃ x, q x ≠ 0) :
    ∃ (S : Subrepresentation τ), S.toRepresentation.IsIrreducible ∧
      ∃ (T : Subrepresentation σ) (p : T.toRepresentation.IntertwiningMap S.toRepresentation),
        Function.Surjective p := by
  classical
  obtain ⟨x, hx⟩ := hq
  let C := orbitSubrepresentation ρ x
  let qC := q.comp (subtypeHom C)
  let : FiniteDimensional ℂ (C.toRepresentation.IntertwiningMap σ) :=
    finiteDimensional_intertwiningMap_orbit hσ (hρ x)
  let b := Module.finBasis ℂ (C.toRepresentation.IntertwiningMap σ)
  let s := Finset.univ.image b
  have hsepC (v : C.toSubmodule) (hv : ∀ f ∈ s, f v = 0) : v = 0 := by
    have hb (i : Fin (Module.finrank ℂ (C.toRepresentation.IntertwiningMap σ))) :
        b i v = 0 := hv _ (Finset.mem_image_of_mem b (Finset.mem_univ i))
    have heval (f : C.toRepresentation.IntertwiningMap σ) : f v = 0 := by
      let eval : C.toRepresentation.IntertwiningMap σ →ₗ[ℂ] W :=
        { toFun := fun g => g v, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
      calc
        f v = eval f := rfl
        _ = eval (∑ i, b.repr f i • b i) := congrArg eval (b.sum_repr f).symm
        _ = 0 := by
          rw [map_sum]
          refine Finset.sum_eq_zero fun i _ => ?_
          rw [map_smul]
          change b.repr f i • b i v = 0
          rw [hb, smul_zero]
    exact Subtype.ext (hsep v.val fun f => heval (f.comp (subtypeHom C)))
  obtain ⟨U, f, hU, hker⟩ := exists_restriction_of_finite_separation qC s ⊤
    ⟨⟨x, self_mem_orbitSpan ρ x⟩, TwoFactorExistence.mem_top _, hx⟩
    (fun v _ hv => by rw [hsepC v hv, map_zero])
  let fU := f.comp (subtypeHom U)
  let qU := qC.comp (subtypeHom U)
  have hk : fU.toLinearMap.ker ≤ qU.toLinearMap.ker := fun v hv => hker v.val v.2 hv
  obtain ⟨v, hv, hqv⟩ := hU
  obtain ⟨d, hd⟩ := exists_descendToRange fU qU hk
  exact exists_irreducible_subrepresentation_of_image hArt fU.range
    d ⟨fU.toLinearMap.rangeRestrict ⟨v, hv⟩, fun h => hqv ((hd _).symm.trans h)⟩

end Langlands
