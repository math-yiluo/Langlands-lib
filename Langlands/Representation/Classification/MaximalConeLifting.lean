import Langlands.Representation.Classification.MaximalConeExponents
import Langlands.Representation.Parabolic.OppositeJacquetMap
import Langlands.Representation.Parabolic.OppositeRefinementTransitivityProof
import Langlands.Representation.Parabolic.FlattenedOppositeUnipotentComparisonProof
import Langlands.Representation.Parabolic.FlattenedRefinementModulusCalculation
import Langlands.Representation.Parabolic.RefinedLeviRealTwistProof

/-!
# Lifting opposite exponents of a twisted Jacquet quotient

Let `S` be a quotient of the normalized opposite Jacquet module of `A` along `C`,
twisted by a real determinant character of the product Levi. A dual
eigenfunctional on an opposite Jacquet module of the twist along a refinement of
`C` gives a dual exponent of `A` along the flattened shape. The twist and the
outer half modulus are absorbed into the exponent.
-/

noncomputable section

namespace Langlands

open GeneralLinear Geometric
open scoped BigOperators NNReal

universe uF uV

namespace GeneralLinear.BlockShape

variable {n : ℕ} (C : BlockShape n) (D : BlockRefinement C)

/-- The outer block containing a flattened block. -/
def flattenOuter (k : Fin (C.flatten D).length) : Fin C.length :=
  ((C.flattenBlockEquiv D).symm k).1

@[simp] theorem flattenOuter_flattenBlockEquiv (q : (i : Fin C.length) × Fin (D i).length) :
    C.flattenOuter D (C.flattenBlockEquiv D q) = q.1 := by
  simp [flattenOuter]

theorem flattenBlockEquiv_le_iff {j : Fin C.length} (i i' : Fin (D j).length) :
    C.flattenBlockEquiv D ⟨j, i⟩ ≤ C.flattenBlockEquiv D ⟨j, i'⟩ ↔ i ≤ i' := by
  constructor
  · intro h
    by_contra hne
    push Not at hne
    have hlt := (C.flattenBlockEquiv_lt_iff D ⟨j, i'⟩ ⟨j, i⟩).mpr (Or.inr ⟨rfl, hne⟩)
    exact absurd h (not_le.mpr hlt)
  · intro h
    rcases h.lt_or_eq with h | rfl
    · exact ((C.flattenBlockEquiv_lt_iff D ⟨j, i⟩ ⟨j, i'⟩).mpr (Or.inr ⟨rfl, h⟩)).le
    · exact le_rfl

theorem flattenOuter_mono : Monotone (C.flattenOuter D) := by
  intro k k' hkk'
  obtain ⟨q, rfl⟩ := (C.flattenBlockEquiv D).surjective k
  obtain ⟨q', rfl⟩ := (C.flattenBlockEquiv D).surjective k'
  rw [flattenOuter_flattenBlockEquiv, flattenOuter_flattenBlockEquiv]
  rcases hkk'.lt_or_eq with h | h
  · rcases (C.flattenBlockEquiv_lt_iff D q q').mp h with h1 | ⟨h1, _⟩
    · exact h1.le
    · exact h1.le
  · rw [(C.flattenBlockEquiv D).injective h]

/-- Sums over the flattened blocks inside one outer block. -/
theorem sum_filter_flattenOuter {M : Type*} [AddCommMonoid M]
    (g : Fin (C.flatten D).length → M) (j : Fin C.length) :
    ∑ k ∈ Finset.univ.filter (fun k => C.flattenOuter D k = j), g k =
      ∑ i : Fin (D j).length, g (C.flattenBlockEquiv D ⟨j, i⟩) := by
  classical
  rw [Finset.sum_filter, ← (C.flattenBlockEquiv D).sum_comp, Fintype.sum_sigma,
    Finset.sum_eq_single j]
  · simp
  · intro j' _ hj'
    simp [hj']
  · simp

theorem size_eq_sum_flattenOuter (j : Fin C.length) :
    C.size j = ∑ k ∈ Finset.univ.filter (fun k => C.flattenOuter D k = j),
      (C.flatten D).size k := by
  rw [sum_filter_flattenOuter]
  simp only [flatten_size_flattenBlockEquiv]
  exact (D j).sum_eq.symm

/-- Partial sums inside an outer block, in inner coordinates. -/
theorem sum_filter_flattenOuter_le {M : Type*} [AddCommMonoid M]
    (g : Fin (C.flatten D).length → M) (j : Fin C.length) (i : Fin (D j).length) :
    ∑ k ∈ Finset.univ.filter (fun k => C.flattenOuter D k =
        C.flattenOuter D (C.flattenBlockEquiv D ⟨j, i⟩) ∧ k ≤ C.flattenBlockEquiv D ⟨j, i⟩),
        g k =
      ∑ i' ∈ Finset.univ.filter (fun i' : Fin (D j).length => i' ≤ i),
        g (C.flattenBlockEquiv D ⟨j, i'⟩) := by
  classical
  rw [flattenOuter_flattenBlockEquiv]
  have h : ∑ k ∈ Finset.univ.filter (fun k => C.flattenOuter D k = j ∧
      k ≤ C.flattenBlockEquiv D ⟨j, i⟩), g k =
      ∑ k ∈ Finset.univ.filter (fun k => C.flattenOuter D k = j),
        (if k ≤ C.flattenBlockEquiv D ⟨j, i⟩ then g k else 0) := by
    rw [Finset.sum_filter, Finset.sum_filter]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases h1 : C.flattenOuter D k = j <;> by_cases h2 : k ≤ C.flattenBlockEquiv D ⟨j, i⟩ <;>
      simp [h1, h2]
  rw [h, sum_filter_flattenOuter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i' _ => ?_
  simp only [flattenBlockEquiv_le_iff]

/-- A flattened block scalar that is constant on each outer block is the outer
block scalar. -/
theorem flattenedLeviEquiv_blockScalarLevi_comp (R : Type*) [CommRing R]
    (a : Fin C.length → Rˣ) :
    (flattenedLeviEquiv R C D ((C.flatten D).blockScalarLevi R (a ∘ C.flattenOuter D))).val =
      C.blockScalarLevi R a := by
  apply C.leviEmbedding_injective R
  rw [flattenedLeviEquiv_embedding]
  exact leviEmbedding_blockScalarLevi_coarsen R (C.flattenOuter_mono D)
    (C.size_eq_sum_flattenOuter D) a

end GeneralLinear.BlockShape

namespace PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData) {n : ℕ}

theorem oppositeJacquetMk_surjective (C : BlockShape n)
    (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier)) :
    Function.Surjective (T.oppositeJacquetMk C A) :=
  Jacquet.mk_surjective _ _

theorem oppositeJacquetMk_apply_of_mem (C : BlockShape n)
    (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier)) {g : GeneralLinear n F.Carrier}
    (hg : g ∈ C.oppositeUnipotentSubgroup F.Carrier) (v : A) :
    T.oppositeJacquetMk C A (A.ρ g v) = T.oppositeJacquetMk C A v :=
  Jacquet.mk_apply_subgroup A.ρ _ ⟨g, hg⟩ v

/-- The normalized action of a Levi element on classes of the opposite Jacquet
module carries the positive half modulus. -/
theorem oppositeJacquet_mk (C : BlockShape n) (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier))
    (m : C.Levi F.Carrier) (v : A) :
    (CuspidalJacquetMultiplicity.oppositeJacquet T C A).ρ m (T.oppositeJacquetMk C A v) =
      (T.leviHalfModulus C m : ℂ) •
        T.oppositeJacquetMk C A (A.ρ (C.leviEmbedding F.Carrier m) v) := by
  change (Jacquet.inverseHalfCharacter
      ((T.leviModulus C).comp (C.leviEquiv F.Carrier).symm.toMonoidHom)⁻¹
      (C.leviEquiv F.Carrier m) : ℂ) •
      Jacquet.mk A.ρ (C.oppositeUnipotentSubgroup F.Carrier)
        (A.ρ (C.leviEmbedding F.Carrier m) v) = _
  congr 1
  simp [Jacquet.inverseHalfCharacter, Jacquet.complexCharacter,
    Jacquet.positiveHalfCharacter, PadicField.TopologicalData.leviHalfModulus]

variable (C : BlockShape n) (D : BlockRefinement C)

/-- The refined opposite radical has determinant norm one in every block. -/
theorem mem_normOneLevi_of_mem_refinedOppositeUnipotent {u : C.Levi F.Carrier}
    (hu : u ∈ refinedOppositeUnipotent F.Carrier C D) : u ∈ T.normOneLevi C := by
  apply (T.mem_normOneLevi C u).mpr
  intro i
  change T.normalizedAbsUnits (determinant (u i)) = 1
  rw [Parabolic.OppositeTransitivity.lower_determinant_one (D i)
    ((mem_refinedOppositeUnipotent F.Carrier C D u).mp hu i), map_one]

theorem leviHalfModulus_of_mem_refinedOppositeUnipotent {u : C.Levi F.Carrier}
    (hu : u ∈ refinedOppositeUnipotent F.Carrier C D) : T.leviHalfModulus C u = 1 :=
  (T.leviHalfModulus_eq_one C u).mpr
    (T.normOneLevi_le_ker_leviModulus C (T.mem_normOneLevi_of_mem_refinedOppositeUnipotent C D hu))

theorem leviRealPowerCharacter_of_mem_refinedOppositeUnipotent (t : Fin C.length → ℝ)
    {u : C.Levi F.Carrier} (hu : u ∈ refinedOppositeUnipotent F.Carrier C D) :
    T.leviRealPowerCharacter C t u = 1 :=
  T.normOneLevi_le_ker_leviRealPowerCharacter C t
    (T.mem_normOneLevi_of_mem_refinedOppositeUnipotent C D hu)

/-- The half modulus of a flattened shape is the outer half modulus times the
refined half modulus. -/
theorem leviHalfModulus_flatten (m : (C.flatten D).Levi F.Carrier) :
    T.leviHalfModulus (C.flatten D) m =
      T.leviHalfModulus C (flattenedLeviEquiv F.Carrier C D m).val *
        T.refinedLeviHalfModulus C D (flattenedLeviEquiv F.Carrier C D m) := by
  have h1 : T.leviHalfModulus (C.flatten D) m =
      T.composedLeviHalfModulus C D (flattenedLeviEquiv F.Carrier C D m) := by
    change Jacquet.complexCharacter (Jacquet.positiveHalfCharacter
      (T.leviModulus (C.flatten D))) m = Jacquet.complexCharacter
        (Jacquet.positiveHalfCharacter (T.composedLeviModulus C D)) _
    rw [← T.composedLeviModulus_flattened C D]
    rfl
  rw [h1, T.composedLeviHalfModulus_eq, MonoidHom.mul_apply]
  congr 1

/-- The coarse real determinant character on a flattened block scalar is the
flattened real determinant character with the coarse exponents. -/
theorem leviRealPowerCharacter_flatten (t : Fin C.length → ℝ)
    (m : (C.flatten D).Levi F.Carrier) :
    T.leviRealPowerCharacter C t (flattenedLeviEquiv F.Carrier C D m).val =
      T.leviRealPowerCharacter (C.flatten D)
        (fun k => t ((C.flattenBlockEquiv D).symm k).1) m := by
  have h := (refinedLeviRealTwist.{uF, 0, 0} p F T n C D
    (Rep.trivial ℂ _ ℂ) 0 t).1
    (refinedLeviSection F.Carrier C D (flattenedLeviEquiv F.Carrier C D m))
  simpa using h

/-- Real parts of a product with a real determinant character on block scalars. -/
theorem isRealPartOf_mul_leviRealPowerCharacter (B : BlockShape n)
    {ψ : (Fin B.length → F.Carrierˣ) →* ℂˣ} {s : Fin B.length → ℝ}
    (hs : T.IsRealPartOf ψ s) (u : Fin B.length → ℝ) :
    T.IsRealPartOf (ψ * (T.leviRealPowerCharacter B u).comp (B.blockScalarLevi F.Carrier))
      (fun k => s k + (B.size k : ℝ) * u k) := by
  intro a
  rw [MonoidHom.mul_apply, Units.val_mul, norm_mul, hs a, MonoidHom.comp_apply,
    T.coe_leviRealPowerCharacter_blockScalar B, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Finset.prod_nonneg fun k _ => Real.rpow_nonneg (T.normalizedAbs_nonneg _) _),
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Real.rpow_add (T.normalizedAbs_pos (a k).ne_zero)]

/-- A dual eigenfunctional of the real twist of a quotient of the opposite Jacquet
module along a refinement `D` of `C` gives a dual exponent of the source along the
flattened shape. -/
theorem isDualJacquetExponent_flatten_of_quotient
    {A : Rep.{uV} ℂ (GeneralLinear n F.Carrier)} {S : Rep.{uV} ℂ (C.Levi F.Carrier)}
    (f : (CuspidalJacquetMultiplicity.oppositeJacquet T C A).ρ.IntertwiningMap S.ρ)
    (hf : Function.Surjective f) (t : Fin C.length → ℝ)
    {ψ : (Fin (C.flatten D).length → F.Carrierˣ) →* ℂˣ}
    (hψ : letI := T.topology; IsOpen (ψ.ker : Set (Fin (C.flatten D).length → F.Carrierˣ)))
    {φ : Module.Dual ℂ (RefinedOppositeJacquetModule C D (T.leviRealPowerTwist C (-t) S.ρ))}
    (hφ : φ ≠ 0)
    (heig : ∀ (a : Fin (C.flatten D).length → F.Carrierˣ) (v : S),
      φ (T.normalizedRefinedOppositeJacquet C D (T.leviRealPowerTwist C (-t) S.ρ)
          (flattenedLeviEquiv F.Carrier C D ((C.flatten D).blockScalarLevi F.Carrier a))
          (refinedOppositeJacquetMk C D (T.leviRealPowerTwist C (-t) S.ρ) v)) =
        (ψ a : ℂ) * φ (refinedOppositeJacquetMk C D (T.leviRealPowerTwist C (-t) S.ρ) v)) :
    T.IsDualJacquetExponent (C.flatten D) A
      (ψ * (T.leviRealPowerCharacter (C.flatten D)
        (fun k => t ((C.flattenBlockEquiv D).symm k).1)).comp
          ((C.flatten D).blockScalarLevi F.Carrier)) := by
  let := T.topology
  let := T.valuativeRel
  have := T.localField
  let ℓ : Module.Dual ℂ A :=
    φ ∘ₗ refinedOppositeJacquetMk C D (T.leviRealPowerTwist C (-t) S.ρ) ∘ₗ f.toLinearMap ∘ₗ
      T.oppositeJacquetMk C A
  have hℓ : ∀ w, ℓ w = φ (refinedOppositeJacquetMk C D (T.leviRealPowerTwist C (-t) S.ρ)
      (f (T.oppositeJacquetMk C A w))) := fun w => rfl
  refine (T.isDualJacquetExponent_iff (C.flatten D) A _).mpr ⟨?_, ℓ, ?_, ?_, ?_⟩
  · have hcont : Continuous ((C.flatten D).blockScalarLevi F.Carrier) := by
      change Continuous fun a : Fin (C.flatten D).length → F.Carrierˣ =>
        fun k => GeneralLinear.scalar (n := (C.flatten D).size k) (a k)
      exact continuous_pi fun k =>
        GeneralLinear.scalarContinuous.continuous.comp (continuous_apply k)
    let c := (T.leviRealPowerCharacter (C.flatten D)
      (fun k => t ((C.flattenBlockEquiv D).symm k).1)).comp
        ((C.flatten D).blockScalarLevi F.Carrier)
    have hc : IsOpen (c.ker : Set (Fin (C.flatten D).length → F.Carrierˣ)) :=
      (T.isOpen_ker_leviRealPowerCharacter (C.flatten D) _).preimage hcont
    refine Subgroup.isOpen_mono (H₁ := ψ.ker ⊓ c.ker) ?_ (hψ.inter hc)
    intro a ha
    obtain ⟨h1, h2⟩ := ha
    have h1' : ψ a = 1 := h1
    have h2' : c a = 1 := h2
    rw [MonoidHom.mem_ker, MonoidHom.mul_apply, h1', one_mul]
    exact h2'
  · intro h0
    apply hφ
    apply LinearMap.ext
    intro x
    obtain ⟨v, rfl⟩ := refinedOppositeJacquetMk_surjective C D _ x
    obtain ⟨y, rfl⟩ := hf v
    obtain ⟨w, rfl⟩ := T.oppositeJacquetMk_surjective C A y
    exact (hℓ w).symm.trans (LinearMap.congr_fun h0 w)
  · intro g hg w
    rw [← Parabolic.flattenedOppositeUnipotentComparison F.Carrier n C D] at hg
    obtain ⟨hp, hm⟩ := (Parabolic.mem_oppositeLeviPreimage_iff F.Carrier C
      (refinedOppositeUnipotent F.Carrier C D) g).mp hg
    let q : C.oppositeParabolic F.Carrier := ⟨g, hp⟩
    let u := C.oppositeUnipotentPart F.Carrier q
    let m := C.oppositeLeviProjection F.Carrier q
    have hdecomp : u.val.val * C.leviEmbedding F.Carrier m = g :=
      congrArg Subtype.val ((C.oppositeDecomposition F.Carrier).left_inv q)
    have h1 : T.oppositeJacquetMk C A (A.ρ g w) =
        (CuspidalJacquetMultiplicity.oppositeJacquet T C A).ρ m (T.oppositeJacquetMk C A w) := by
      rw [T.oppositeJacquet_mk C A m w,
        T.leviHalfModulus_of_mem_refinedOppositeUnipotent C D hm, Units.val_one, one_smul,
        ← hdecomp, map_mul, Module.End.mul_apply]
      exact T.oppositeJacquetMk_apply_of_mem C A ⟨u.val, u.property, rfl⟩ _
    have h3 : ∀ v : S, T.leviRealPowerTwist C (-t) S.ρ m v = S.ρ m v := by
      intro v
      rw [T.leviRealPowerTwist_apply,
        T.leviRealPowerCharacter_of_mem_refinedOppositeUnipotent C D (-t) hm,
        Units.val_one, one_smul]
    rw [hℓ, hℓ, h1, f.isIntertwining, ← h3]
    exact congrArg φ (Jacquet.mk_apply_subgroup (T.leviRealPowerTwist C (-t) S.ρ)
      (refinedOppositeUnipotent F.Carrier C D) ⟨m, hm⟩ _)
  · intro a w
    set x := flattenedLeviEquiv F.Carrier C D ((C.flatten D).blockScalarLevi F.Carrier a)
      with hx
    have hemb : (C.flatten D).leviEmbedding F.Carrier
        ((C.flatten D).blockScalarLevi F.Carrier a) = C.leviEmbedding F.Carrier x.val :=
      (flattenedLeviEquiv_embedding F.Carrier C D _).symm
    have hδC : (T.leviHalfModulus C x.val : ℂ) ≠ 0 := Units.ne_zero _
    have hδD : (T.refinedLeviHalfModulus C D x : ℂ) ≠ 0 := Units.ne_zero _
    have h1 : T.oppositeJacquetMk C A (A.ρ (C.leviEmbedding F.Carrier x.val) w) =
        (T.leviHalfModulus C x.val : ℂ)⁻¹ •
          (CuspidalJacquetMultiplicity.oppositeJacquet T C A).ρ x.val
            (T.oppositeJacquetMk C A w) := by
      rw [T.oppositeJacquet_mk C A x.val w, smul_smul, inv_mul_cancel₀ hδC, one_smul]
    have h2 : ∀ v : S, S.ρ x.val v =
        (T.leviRealPowerCharacter C t x.val : ℂ) • T.leviRealPowerTwist C (-t) S.ρ x.val v := by
      intro v
      rw [T.leviRealPowerTwist_apply, T.leviRealPowerCharacter_neg, MonoidHom.inv_apply,
        smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul]
    have h3 : ∀ v : S, refinedOppositeJacquetMk C D (T.leviRealPowerTwist C (-t) S.ρ)
          (T.leviRealPowerTwist C (-t) S.ρ x.val v) =
        (T.refinedLeviHalfModulus C D x : ℂ)⁻¹ •
          T.normalizedRefinedOppositeJacquet C D (T.leviRealPowerTwist C (-t) S.ρ) x
            (refinedOppositeJacquetMk C D (T.leviRealPowerTwist C (-t) S.ρ) v) := by
      intro v
      rw [T.normalizedRefinedOppositeJacquet_mk, smul_smul, inv_mul_cancel₀ hδD, one_smul]
    have hc := T.leviRealPowerCharacter_flatten C D t ((C.flatten D).blockScalarLevi F.Carrier a)
    have hδ := T.leviHalfModulus_flatten C D ((C.flatten D).blockScalarLevi F.Carrier a)
    rw [← hx] at hc hδ
    have hfs : ∀ (c : ℂ) y, f (c • y) = c • f y := fun c y => f.toLinearMap.map_smul c y
    have heig' := heig a (f (T.oppositeJacquetMk C A w))
    rw [← hx] at heig'
    rw [hℓ, hℓ, hemb, h1, hfs, f.isIntertwining, h2]
    simp only [map_smul, h3, smul_eq_mul]
    rw [heig', hδ]
    simp only [MonoidHom.mul_apply, MonoidHom.comp_apply]
    rw [← hc]
    simp only [Units.val_mul, mul_inv]
    ring

/-- The refined half modulus is trivial on outer block scalars. -/
theorem refinedLeviHalfModulus_blockScalarLevi_comp (a : Fin C.length → F.Carrierˣ) :
    T.refinedLeviHalfModulus C D (flattenedLeviEquiv F.Carrier C D
      ((C.flatten D).blockScalarLevi F.Carrier (a ∘ C.flattenOuter D))) = 1 := by
  have h := T.leviHalfModulus_flatten C D
    ((C.flatten D).blockScalarLevi F.Carrier (a ∘ C.flattenOuter D))
  rw [C.flattenedLeviEquiv_blockScalarLevi_comp D F.Carrier a] at h
  have h2 : T.leviHalfModulus (C.flatten D)
      ((C.flatten D).blockScalarLevi F.Carrier (a ∘ C.flattenOuter D)) =
      T.leviHalfModulus C (C.blockScalarLevi F.Carrier a) := by
    apply Units.ext
    rw [leviHalfModulus_apply, leviHalfModulus_apply,
      T.leviModulus_blockScalarLevi_coarsen (C.flattenOuter_mono D)
        (C.size_eq_sum_flattenOuter D) a]
  rw [h2] at h
  exact (mul_eq_left.mp h.symm)

/-- If the outer block scalars act on `σ` by a unitary character, the real part of
every dual eigencharacter of a refined opposite Jacquet module of `σ` has zero
sum over each outer block. -/
theorem sum_fibre_eq_zero_of_unitary {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (C.Levi F.Carrier) V) {ω : (Fin C.length → F.Carrierˣ) →* ℂˣ}
    (hω : Classification.HasScalarCharacter σ (C.blockScalarLevi F.Carrier) ω)
    (hunit : ∀ a, ‖(ω a : ℂ)‖ = 1)
    {ψ : (Fin (C.flatten D).length → F.Carrierˣ) →* ℂˣ} {s : Fin (C.flatten D).length → ℝ}
    {φ : Module.Dual ℂ (RefinedOppositeJacquetModule C D σ)} (hφ : φ ≠ 0)
    (heig : ∀ (a : Fin (C.flatten D).length → F.Carrierˣ) (v : V),
      φ (T.normalizedRefinedOppositeJacquet C D σ
          (flattenedLeviEquiv F.Carrier C D ((C.flatten D).blockScalarLevi F.Carrier a))
          (refinedOppositeJacquetMk C D σ v)) =
        (ψ a : ℂ) * φ (refinedOppositeJacquetMk C D σ v))
    (hs : T.IsRealPartOf ψ s) (j : Fin C.length) :
    ∑ k ∈ Finset.univ.filter (fun k => C.flattenOuter D k = j), s k = 0 := by
  obtain ⟨v, hv⟩ : ∃ v, φ (refinedOppositeJacquetMk C D σ v) ≠ 0 := by
    by_contra h
    push Not at h
    apply hφ
    apply LinearMap.ext
    intro x
    obtain ⟨v, rfl⟩ := refinedOppositeJacquetMk_surjective C D σ x
    exact h v
  have hkey : ∀ a : Fin C.length → F.Carrierˣ, ω a = ψ (a ∘ C.flattenOuter D) := by
    intro a
    have h := heig (a ∘ C.flattenOuter D) v
    rw [T.normalizedRefinedOppositeJacquet_mk, T.refinedLeviHalfModulus_blockScalarLevi_comp,
      C.flattenedLeviEquiv_blockScalarLevi_comp D F.Carrier a, hω a v, Units.val_one, one_smul,
      map_smul, map_smul, smul_eq_mul] at h
    exact Units.ext (mul_right_cancel₀ hv h)
  have h1 : T.IsRealPartOf ω (fun j => ∑ k ∈ Finset.univ.filter
      (fun k => C.flattenOuter D k = j), s k) :=
    T.isRealPartOf_coarsen hs hkey _ fun _ => rfl
  have h0 : T.IsRealPartOf ω 0 := by
    intro a
    simp [hunit a]
  exact congrFun (h1.eq h0) j

end PadicField.TopologicalData

end Langlands
