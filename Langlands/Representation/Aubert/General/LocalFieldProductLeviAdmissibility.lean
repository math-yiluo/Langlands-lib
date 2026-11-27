import Langlands.AllField.Representation.CuspidalSupport.QuasicuspidalLeviAdmissibilityProof
import Langlands.AllField.Representation.Parabolic.RefinedInductionAdmissibility
import Langlands.AllField.Representation.Parabolic.RefinementCharacter
import Langlands.Representation.CuspidalSupport.RefinedQuasicuspidalEmbeddingProof
import Langlands.Representation.CuspidalSupport.GroupTransport
import Langlands.Representation.Smooth.Admissibility.EmbeddingProof

/-! Admissibility of smooth irreducibles for actual local-field GL product Levis. -/

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false

open scoped NNReal

namespace Langlands.AllField.CuspidalSupport

open Langlands.GeneralLinear Langlands.Geometric
open Langlands.CuspidalSupport (IsLeviQuasicuspidal)
open Langlands.CuspidalSupport.MinimalRefinedJacquet
open Langlands.CuspidalSupport.QuasicuspidalEmbedding
open Langlands.CuspidalSupport.RefinedQuasicuspidalEmbedding (flattenedLeviEquiv_eq_leviRefinementEquiv)

universe uF uV uW

section Modulus

variable {F : Type uF} [Field F] (T : LocalFieldData F) {n : ℕ}
variable (B : BlockShape n) (S : BlockRefinement B) (S' : BlockRefinement (B.flatten S))

/-- The full refined modulus is trivial on such a middle Levi element. -/
private theorem refinedLeviModulus_eq_one (m : refinedLevi F B S)
    (hm : ∀ i, (refinedLeviEquiv F B S).symm m i ∈
      refinedUnipotent F (S i) (B.refinementWithin S S' i)) :
    T.refinedLeviModulus B S m = 1 := by
  rw [T.refinedLeviModulus_apply B S]
  exact Finset.prod_eq_one fun i _ =>
    T.leviModulus_refinedUnipotent (S i) (B.refinementWithin S S' i) ⟨_, hm i⟩

end Modulus

section Representation

variable {F : Type uF} [Field F] (T : LocalFieldData F) {n : ℕ}
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (B : BlockShape n) (S : BlockRefinement B) (S' : BlockRefinement (B.flatten S))
  (ρ : Representation ℂ (B.Levi F) V)

/-- The normalized refined Jacquet action pulled back to the flattened Levi, as
in the target statement. -/
private abbrev flattenedAction :
    Representation ℂ ((B.flatten S).Levi F) (RefinedJacquetModule B S ρ) :=
  (T.normalizedRefinedJacquet B S ρ).comp (flattenLeviEquiv B S).toMonoidHom

/-- A radical element of the composed refinement acts trivially on the iterated
coinvariants: its middle radical part dies in the refined Jacquet module, and its
middle Levi part has trivial normalization and comes from the radical of `S'`. -/
private theorem mk_refinedJacquetMk_composeRefinement {g : B.Levi F}
    (hg : g ∈ refinedUnipotent F B (B.composeRefinement S S')) (v : V) :
    Jacquet.mk (flattenedAction T B S ρ) (refinedUnipotent F (B.flatten S) S')
        (refinedJacquetMk B S ρ (ρ g v)) =
      Jacquet.mk (flattenedAction T B S ρ) (refinedUnipotent F (B.flatten S) S')
        (refinedJacquetMk B S ρ v) := by
  let q : refinedParabolic F B S :=
    ⟨g, composeRefinement_refinedUnipotent_le B S S' hg⟩
  let m := refinedLeviProjection F B S q
  have hm : ∀ i, (refinedLeviEquiv F B S).symm m i ∈
      refinedUnipotent F (S i) (B.refinementWithin S S' i) :=
    refinedLeviEquiv_symm_mem B S S' hg
  have hq : g = ((refinedUnipotentPart F B S q).val : B.Levi F) * m.val :=
    congrArg Subtype.val (inv_mul_cancel_right q (refinedLeviSection F B S m)).symm
  have hu : ((refinedUnipotentPart F B S q).val : B.Levi F) ∈
      refinedUnipotent F B S :=
    (mem_refinedUnipotentRadical F B S _).mp
      (refinedUnipotentPart F B S q).property
  have h1 : refinedJacquetMk B S ρ (ρ g v) = refinedJacquetMk B S ρ (ρ m.val v) := by
    rw [hq, map_mul, Module.End.mul_apply]
    exact Jacquet.mk_apply_subgroup ρ (refinedUnipotent F B S) ⟨_, hu⟩ _
  have hδ : T.refinedLeviInverseHalfModulus B S m = 1 :=
    (Jacquet.inverseHalfCharacter_eq_one _ m).mpr (refinedLeviModulus_eq_one T B S S' m hm)
  have h2 : flattenedAction T B S ρ ((flattenLeviEquiv B S).symm m)
      (refinedJacquetMk B S ρ v) = refinedJacquetMk B S ρ (ρ m.val v) := by
    change T.normalizedRefinedJacquet B S ρ
      ((flattenLeviEquiv B S) ((flattenLeviEquiv B S).symm m)) _ = _
    rw [MulEquiv.apply_symm_apply, T.normalizedRefinedJacquet_mk, hδ, Units.val_one, one_smul]
  rw [h1, ← h2]
  exact Jacquet.mk_apply_subgroup (flattenedAction T B S ρ)
    (refinedUnipotent F (B.flatten S) S')
    ⟨_, flattenLeviEquiv_symm_mem B S S' m hm⟩ _

/-- The refined Jacquet module of the composed refinement maps onto the
coinvariants of the pulled-back normalized action for `S'`. -/
private def composeJacquetMap :
    RefinedJacquetModule B (B.composeRefinement S S') ρ →ₗ[ℂ]
      Jacquet.Coinvariants (flattenedAction T B S ρ)
        (refinedUnipotent F (B.flatten S) S') :=
  Jacquet.lift ρ (refinedUnipotent F B (B.composeRefinement S S'))
    (Jacquet.mk (flattenedAction T B S ρ) (refinedUnipotent F (B.flatten S) S') ∘ₗ
      refinedJacquetMk B S ρ)
    (fun u => LinearMap.ext fun v =>
      mk_refinedJacquetMk_composeRefinement T B S S' ρ u.property v)

private theorem composeJacquetMap_surjective : Function.Surjective (composeJacquetMap T B S S' ρ) := by
  intro y
  obtain ⟨x, rfl⟩ := Jacquet.mk_surjective _ _ y
  obtain ⟨v, rfl⟩ := Jacquet.mk_surjective _ _ x
  exact ⟨refinedJacquetMk B (B.composeRefinement S S') ρ v, rfl⟩

/-- Nonzero iterated coinvariants give a nonzero composed refined Jacquet module. -/
private theorem nontrivial_composeRefinement
    (h : Nontrivial (Jacquet.Coinvariants (flattenedAction T B S ρ)
      (refinedUnipotent F (B.flatten S) S'))) :
    Nontrivial (RefinedJacquetModule B (B.composeRefinement S S') ρ) :=
  (composeJacquetMap_surjective T B S S' ρ).nontrivial

end Representation

private theorem maximalRefinement {n : ℕ} (B : BlockShape n) (good : BlockRefinement B → Prop)
    (h : good (wholeRefinement B)) :
    ∃ S : BlockRefinement B, good S ∧
      ∀ R : BlockRefinement B, (B.flatten S).length < (B.flatten R).length → ¬ good R := by
  classical
  let P : ℕ → Prop := fun k => ∃ R : BlockRefinement B, (B.flatten R).length = k ∧ good R
  have h₀ : P (B.flatten (wholeRefinement B)).length := ⟨wholeRefinement B, rfl, h⟩
  obtain ⟨S, hS, hgood⟩ := Nat.findGreatest_spec (P := P)
    (B.flatten (wholeRefinement B)).length_le h₀
  refine ⟨S, hgood, fun R hlt hR => ?_⟩
  rw [hS] at hlt
  exact Nat.findGreatest_is_greatest hlt (B.flatten R).length_le ⟨R, rfl, hR⟩

private theorem quasicuspidal_of_maximalRefinement {F : Type uF} [Field F] (T : LocalFieldData F)
    {n : ℕ} (B : BlockShape n) {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (B.Levi F) V) (S : BlockRefinement B)
    (hmax : ∀ R : BlockRefinement B, (B.flatten S).length < (B.flatten R).length →
      ¬ Nontrivial (RefinedJacquetModule B R ρ)) :
    IsLeviQuasicuspidal (B.flatten S) (flattenedAction T B S ρ) := by
  intro R hR
  have hlt := (B.flatten S).length_lt_flatten R F hR
  have hlen := congrArg BlockShape.length (B.flatten_composeRefinement S R)
  exact not_nontrivial_iff_subsingleton.mp fun hnonzero =>
    hmax (B.composeRefinement S R) (hlt.trans_eq hlen)
      (nontrivial_composeRefinement T B S R ρ hnonzero)

private theorem nontrivial_wholeRefinement_of_field {F : Type uF} [Field F]
    {n : ℕ} (B : BlockShape n) {V : Type uV} [AddCommGroup V] [Module ℂ V] [Nontrivial V]
    (ρ : Representation ℂ (B.Levi F) V) :
    Nontrivial (RefinedJacquetModule B (wholeRefinement B) ρ) := by
  have hinj : Function.Injective (refinedJacquetMk B (wholeRefinement B) ρ) := by
    rw [← LinearMap.ker_eq_bot, Jacquet.ker_mk, Jacquet.relations_eq_span,
      Submodule.span_eq_bot]
    rintro _ ⟨⟨u, w⟩, rfl⟩
    have hu : (u : B.Levi F) = 1 := eq_one_of_mem_refinedUnipotent_wholeRefinement B u.property
    simp [hu]
  exact hinj.nontrivial

private theorem minimalRefinement {F : Type uF} [Field F] (T : LocalFieldData F)
    {n : ℕ} (B : BlockShape n) {V : Type uV} [AddCommGroup V] [Module ℂ V] [Nontrivial V]
    (ρ : Representation ℂ (B.Levi F) V) :
    ∃ S : BlockRefinement B, Nontrivial (RefinedJacquetModule B S ρ) ∧
      IsLeviQuasicuspidal (B.flatten S) (flattenedAction T B S ρ) := by
  obtain ⟨S, hS, hmax⟩ := maximalRefinement B
    (fun R => Nontrivial (RefinedJacquetModule B R ρ)) (nontrivial_wholeRefinement_of_field B ρ)
  exact ⟨S, hS, quasicuspidal_of_maximalRefinement T B ρ S hmax⟩

section Refined

variable {F : Type uF} [Field F] (T : LocalFieldData F) {n : ℕ}
  (B : BlockShape n) (S : BlockRefinement B) {V : Type uV} {W : Type uW}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- A refined parabolic element acts on refined Jacquet classes through its
refined Levi part. -/
private theorem refinedJacquetMk_parabolic (ρ : Representation ℂ (B.Levi F) V)
    (q : refinedParabolic F B S) (v : V) :
    refinedJacquetMk B S ρ (ρ q.val v) =
      refinedJacquetMk B S ρ (ρ (refinedLeviProjection F B S q).val v) := by
  have hu := (mem_refinedUnipotentRadical F B S _).mp
    (refinedUnipotentPart F B S q).property
  have h := Jacquet.mk_apply_subgroup ρ (refinedUnipotent F B S)
    ⟨_, hu⟩ (ρ (refinedLeviProjection F B S q).val v)
  rw [← h]
  congr 1
  change ρ q.val v = ρ (q * (refinedLeviSection F B S
      (refinedLeviProjection F B S q))⁻¹).val
    (ρ (refinedLeviSection F B S (refinedLeviProjection F B S q)).val v)
  rw [← Module.End.mul_apply, ← map_mul, ← Subgroup.coe_mul, inv_mul_cancel_right]

/-- Undo the inverse half-modulus of the normalized refined Jacquet action. -/
private theorem refinedJacquetMk_levi (ρ : Representation ℂ (B.Levi F) V)
    (m : refinedLevi F B S) (v : V) :
    refinedJacquetMk B S ρ (ρ m.val v) =
      (T.refinedLeviHalfModulus B S m : ℂ) •
        T.normalizedRefinedJacquet B S ρ m (refinedJacquetMk B S ρ v) := by
  rw [T.normalizedRefinedJacquet_mk, T.refinedLeviInverseHalfModulus_eq_inv,
    MonoidHom.inv_apply, smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul]

variable {ρ : Representation ℂ (B.Levi F) V}
  {σ : Representation ℂ (refinedLevi F B S) W}

/-- A refined Levi intertwiner from the normalized refined Jacquet module,
composed with the quotient map, is covariant for the refined parabolic with the
positive half modulus. -/
private theorem refinedJacquet_covariant (A : (T.normalizedRefinedJacquet B S ρ).IntertwiningMap σ)
    (q : refinedParabolic F B S) (v : V) :
    A (refinedJacquetMk B S ρ (ρ q.val v)) =
      (T.refinedParabolicHalfModulus B S q : ℂ) •
        σ (refinedLeviProjection F B S q) (A (refinedJacquetMk B S ρ v)) := by
  rw [refinedJacquetMk_parabolic, refinedJacquetMk_levi T, map_smul,
    Representation.IntertwiningMap.isIntertwining]
  rfl

/-- The covariant orbit functions of a refined Jacquet intertwiner, before
restricting to smooth vectors. -/
private def refinedOrbitMap (A : (T.normalizedRefinedJacquet B S ρ).IntertwiningMap σ) :
    ρ.IntertwiningMap (Induction.equivariantAction (refinedParabolic F B S)
      (twist (T.refinedParabolicHalfModulus B S)
        (σ.comp (refinedLeviProjection F B S)))) where
  toLinearMap :=
    { toFun := fun v => ⟨fun g => A (refinedJacquetMk B S ρ (ρ g v)), by
        intro q g
        change A (refinedJacquetMk B S ρ (ρ (q.val * g) v)) =
          (T.refinedParabolicHalfModulus B S q : ℂ) •
            σ (refinedLeviProjection F B S q) (A (refinedJacquetMk B S ρ (ρ g v)))
        rw [map_mul, Module.End.mul_apply]
        exact refinedJacquet_covariant T B S A q (ρ g v)⟩
      map_add' := by intros; ext g; simp
      map_smul' := by intros; ext g; simp }
  isIntertwining' g := by
    ext v x
    change A (refinedJacquetMk B S ρ (ρ x (ρ g v))) = A (refinedJacquetMk B S ρ (ρ (x * g) v))
    rw [map_mul, Module.End.mul_apply]

/-- The refined Frobenius intertwiner into normalized refined induction. -/
private def refinedFrobenius (hρ : letI := T.topology
      letI := T.leviTopologicalGroup B
      IsSmooth ρ)
    (A : (T.normalizedRefinedJacquet B S ρ).IntertwiningMap σ) :
    letI := T.topology
    letI := T.leviTopologicalGroup B
    ρ.IntertwiningMap (T.normalizedRefinedInduced B S σ) :=
  letI := T.topology
  letI := T.leviTopologicalGroup B
  smoothLift hρ (refinedOrbitMap T B S A)

private theorem refinedFrobenius_eval (hρ : letI := T.topology
      letI := T.leviTopologicalGroup B
      IsSmooth ρ)
    (A : (T.normalizedRefinedJacquet B S ρ).IntertwiningMap σ) (v : V) (g : B.Levi F) :
    letI := T.topology
    letI := T.leviTopologicalGroup B
    Induction.eval (refinedParabolic F B S)
        (twist (T.refinedParabolicHalfModulus B S)
          (σ.comp (refinedLeviProjection F B S)))
        (refinedFrobenius T B S hρ A v) g =
      A (refinedJacquetMk B S ρ (ρ g v)) := rfl

end Refined

section Generation

variable {F : Type uF} [Field F] (T : LocalFieldData F) {n : ℕ}
  (B : BlockShape n) (S : BlockRefinement B) {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The normalized refined Jacquet action pulled back to the flattened Levi
along the target's coordinate equivalence. -/
private abbrev flattenedJacquet (ρ : Representation ℂ (B.Levi F) V) :
    Representation ℂ ((B.flatten S).Levi F) (RefinedJacquetModule B S ρ) :=
  (T.normalizedRefinedJacquet B S ρ).comp (flattenedLeviEquiv F B S).toMonoidHom

private theorem flattenedJacquet_symm (ρ : Representation ℂ (B.Levi F) V)
    (m : refinedLevi F B S) (x : RefinedJacquetModule B S ρ) :
    flattenedJacquet T B S ρ ((flattenedLeviEquiv F B S).symm m) x =
      T.normalizedRefinedJacquet B S ρ m x := by
  change T.normalizedRefinedJacquet B S ρ
    (flattenedLeviEquiv F B S ((flattenedLeviEquiv F B S).symm m)) x = _
  rw [MulEquiv.apply_symm_apply]

/-- An invariant subspace for the flattened action containing the class of `v`
contains the class of every refined parabolic translate of `v`. -/
private theorem refinedJacquetMk_parabolic_mem {ρ : Representation ℂ (B.Levi F) V}
    (U : Subrepresentation (flattenedJacquet T B S ρ)) (q : refinedParabolic F B S)
    {v : V} (hv : refinedJacquetMk B S ρ v ∈ U) :
    refinedJacquetMk B S ρ (ρ q.val v) ∈ U := by
  rw [refinedJacquetMk_parabolic,
    refinedJacquetMk_levi T, ← flattenedJacquet_symm]
  exact U.toSubmodule.smul_mem _ (U.apply_mem_toSubmodule _ hv)

/-- The refined Jacquet module of a representation generated by one smooth
vector is generated, for the flattened action, by finitely many vectors. -/
private theorem exists_finset_generating {ρ : Representation ℂ (B.Levi F) V}
    (hρ : letI := T.topology
      letI := T.leviTopologicalGroup B
      IsSmooth ρ) (v₀ : V)
    (hgen : ∀ v : V, v ∈ Submodule.span ℂ (Set.range fun g => ρ g v₀)) :
    ∃ s : Finset (RefinedJacquetModule B S ρ),
      ∀ U : Subrepresentation (flattenedJacquet T B S ρ), (∀ x ∈ s, x ∈ U) → U = ⊤ := by
  let := T.topology
  let := T.leviTopologicalGroup B
  have : CompactSpace (Induction.LeftQuotient (refinedParabolic F B S)) :=
    Langlands.AllField.Parabolic.refinedParabolicQuotientCompact F T B S
  obtain ⟨K, hK⟩ := hρ v₀
  obtain ⟨t, ht⟩ := Induction.exists_finset_doubleCoset_cover (refinedParabolic F B S) K
  classical
  refine ⟨t.image fun i => refinedJacquetMk B S ρ (ρ i v₀), ?_⟩
  intro U hU
  have hmem : ∀ g : B.Levi F, refinedJacquetMk B S ρ (ρ g v₀) ∈ U := by
    intro g
    obtain ⟨i, hi, q, hq, k, hk, rfl⟩ := ht g
    have hk' : ρ k v₀ = v₀ := hK ⟨k, hk⟩
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hk']
    exact refinedJacquetMk_parabolic_mem T B S U ⟨q, hq⟩ (hU _ (Finset.mem_image_of_mem _ hi))
  have hle : Submodule.span ℂ (Set.range fun g => ρ g v₀) ≤
      U.toSubmodule.comap (refinedJacquetMk B S ρ) := by
    rw [Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    exact hmem g
  apply SetLike.ext
  intro x
  refine ⟨fun _ => Submodule.mem_top, fun _ => ?_⟩
  obtain ⟨v, rfl⟩ := Jacquet.mk_surjective ρ _ x
  exact hle (hgen v)

end Generation

private theorem admissible_transport {F : Type uF} [Field F] (T : LocalFieldData F)
    {n : ℕ} (B : BlockShape n) (S : BlockRefinement B) :
    letI := T.topology
    ∀ (σ : SmoothRep.{0, uF, uV} ℂ ((B.flatten S).Levi F)),
      σ.IsIrreducible → IsLeviQuasicuspidal (B.flatten S) σ.representation →
        IsAdmissible (σ.representation.comp (flattenedLeviEquiv F B S).symm.toMonoidHom) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro σ hσ hq
  exact isAdmissible_comp_continuousMulEquiv σ.representation (flattenedLeviEquivContinuous F B S).symm
    (LeviAdmissibility.irreducibleQuasicuspidalLeviAdmissibility F T (B.flatten S) σ hσ hq)

/-- The normalized inducing character of an actual refined parabolic has open kernel. -/
theorem isOpen_ker_refinedParabolicHalfModulus {F : Type uF} [Field F] (T : LocalFieldData F)
    {n : ℕ} (B : BlockShape n) (S : BlockRefinement B) :
    letI := T.topology
    IsOpen ((T.refinedParabolicHalfModulus B S).ker : Set (refinedParabolic F B S)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have hhalf : (T.refinedLeviHalfModulus B S).ker = (T.refinedLeviModulus B S).ker := by
    ext m
    change T.refinedLeviHalfModulus B S m = 1 ↔ T.refinedLeviModulus B S m = 1
    have hh : Jacquet.inverseHalfCharacter (T.refinedLeviModulus B S) m =
        (T.refinedLeviHalfModulus B S m)⁻¹ := rfl
    simpa only [hh, inv_eq_one] using Jacquet.inverseHalfCharacter_eq_one (T.refinedLeviModulus B S) m
  change IsOpen ((refinedLeviProjection F B S) ⁻¹' ((T.refinedLeviHalfModulus B S).ker : Set _))
  rw [hhalf]
  exact (T.isOpen_ker_refinedLeviModulus B S).preimage
    (refinedLeviProjectionContinuous F B S).continuous

private theorem admissible_refinedInduced {F : Type uF} [Field F] (T : LocalFieldData F)
    {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (refinedLevi F B S) V) :
    letI := T.topology
    letI := T.leviTopologicalGroup B
    IsAdmissible σ → IsAdmissible (T.normalizedRefinedInduced B S σ) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.leviTopologicalGroup B
  intro hσ
  let p := refinedLeviProjection F B S
  let i := refinedLeviSection F B S
  have hp : Continuous p := (refinedLeviProjectionContinuous F B S).continuous
  have hi : Continuous i := (refinedLeviSectionContinuous F B S).continuous
  have hpi : Function.RightInverse i p := refinedLeviProjection_section F B S
  have hinf := (isAdmissible_comp_iff_of_open_surjective σ p hp
    (isOpenMap_of_continuous_rightInverse p i hi hpi) hpi.surjective).mpr hσ
  have hker := isOpen_ker_refinedParabolicHalfModulus T B S
  let := Langlands.AllField.Parabolic.refinedParabolicQuotientCompact F T B S
  exact Induction.smoothInduced_isAdmissible_of_compactSpace _ _
    ((isAdmissible_twist_iff _ _ hker).mpr hinf)

/-- An irreducible smooth complex representation of an actual standard
product Levi over a nonarchimedean local field is admissible. -/
theorem irreducibleLeviAdmissibility {F : Type uF} [Field F] (T : LocalFieldData F)
    (n : ℕ) (B : BlockShape n) :
    letI := T.topology
    ∀ (ω : SmoothRep.{0, uF, uV} ℂ (B.Levi F)), ω.IsIrreducible → ω.IsAdmissible := by
  let := T.topology
  intro ω hω
  let : Nontrivial ω := nontrivial_of_isIrreducible ω.representation hω
  let ρ := ω.representation
  obtain ⟨S, hJne, hJq⟩ := minimalRefinement T B ρ
  let τ := flattenedJacquet T B S ρ
  have hτ : IsSmooth τ := by
    let := T.valuativeRel
    let := T.localField
    exact isSmooth_comp _ (flattenedLeviEquivContinuous F B S).continuous
      (isSmooth_normalizedRefinedJacquetOf B S _ (T.isOpen_ker_refinedLeviModulus B S) ω.isSmooth)
  let J := SmoothRep.of τ hτ
  obtain ⟨v₀, hv₀⟩ := exists_ne (0 : ω)
  obtain ⟨s, hs⟩ := exists_finset_generating T B S ω.isSmooth v₀ (mem_span_orbit ρ hω hv₀)
  have : Nontrivial J := hJne
  obtain ⟨U, hU⟩ := exists_isCoatom_subrepresentation J.representation s hs
  let σ := SmoothRep.quotient J U
  let q : J.representation.IntertwiningMap σ.representation := SmoothRep.hom (SmoothRep.mkQ J U)
  have hq : Function.Surjective q := SmoothRep.mkQ_surjective J U
  have hqker : ∀ x, q x = 0 ↔ x ∈ U := fun x => Submodule.Quotient.mk_eq_zero _
  have hσ : σ.IsIrreducible := isIrreducible_of_isCoatom q hq U hU hqker
  have hτq : IsLeviQuasicuspidal (B.flatten S) τ := by
    change IsLeviQuasicuspidal (B.flatten S)
      ((T.normalizedRefinedJacquet B S ρ).comp (flattenedLeviEquiv F B S).toMonoidHom)
    rw [flattenedLeviEquiv_eq_leviRefinementEquiv]
    exact hJq
  have hσq : IsLeviQuasicuspidal (B.flatten S) σ.representation := fun R hR =>
    coinvariants_subsingleton_of_surjective q hq _ (hτq R hR)
  let A : (T.normalizedRefinedJacquet B S ρ).IntertwiningMap
      (σ.representation.comp (flattenedLeviEquiv F B S).symm.toMonoidHom) :=
    { toLinearMap := q.toLinearMap
      isIntertwining' := fun m => LinearMap.ext fun x => by
        change q (T.normalizedRefinedJacquet B S ρ m x) =
          σ.representation ((flattenedLeviEquiv F B S).symm m) (q x)
        rw [← flattenedJacquet_symm T B S ρ m x]
        exact Representation.IntertwiningMap.isIntertwining _ _ q _ x }
  let := T.leviTopologicalGroup B
  let j := refinedFrobenius T B S ω.isSmooth A
  refine isAdmissible_of_injective j ?_
    (admissible_refinedInduced T B S _ (admissible_transport T B S σ hσ hσq))
  have : Representation.IsIrreducible ω.representation := hω
  rcases Representation.IsIrreducible.injective_or_eq_zero j with h | h
  · exact h
  · exfalso
    obtain ⟨x, hx⟩ : ∃ x, x ∉ U := by
      by_contra hall
      push Not at hall
      apply hU.1
      apply SetLike.ext
      intro x
      exact ⟨fun _ => Submodule.mem_top, fun _ => hall x⟩
    obtain ⟨v, rfl⟩ := Jacquet.mk_surjective ρ _ x
    have h1 := refinedFrobenius_eval T B S ω.isSmooth A v 1
    rw [map_one, Module.End.one_apply] at h1
    change Induction.eval _ _ (j v) 1 = _ at h1
    rw [h] at h1
    have h0 : q (refinedJacquetMk B S ρ v) = 0 := h1.symm.trans rfl
    exact hx ((hqker _).mp h0)

end Langlands.AllField.CuspidalSupport
