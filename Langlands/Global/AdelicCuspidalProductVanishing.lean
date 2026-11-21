import Langlands.Global.AdelicLeadingCuspidalPairing
import Langlands.Global.AdelicConstantTermSplitComponent
import Langlands.Global.AdelicNestedSplitComponents
import Langlands.Global.AdelicCuspidalAnnihilator
import Langlands.Global.AdelicRepresentationHeightPropernessProof

/-! # Products of split-component differences killed by the vanishing criterion

Bernstein–Lapid, proof of Lemma 8.1: from the cuspidal tests of the constant terms along all
`Q ⊆ P`, the vanishing criterion (8.1) kills the product of the corresponding differences
applied to the constant term along `P`. Here every factor uses one positive point of `A_P`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory NumberField Opposite
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace Langlands.Global

section Polynomial

variable {E E' : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup E'] [Module ℂ E']

/-- Powers of an endomorphism preserve a submodule that it preserves. -/
theorem pow_apply_mem_of_mapsTo (S : Submodule ℂ E) (L : Module.End ℂ E)
    (hL : ∀ v ∈ S, L v ∈ S) (n : ℕ) : ∀ v ∈ S, (L ^ n) v ∈ S := by
  induction n with
  | zero => intro v hv; simpa using hv
  | succ n ih =>
    intro v hv
    rw [pow_succ', Module.End.mul_apply]
    exact hL _ (ih v hv)

/-- Polynomials in an endomorphism preserve a submodule that it preserves. -/
theorem aeval_apply_mem_of_mapsTo (S : Submodule ℂ E) (L : Module.End ℂ E)
    (hL : ∀ v ∈ S, L v ∈ S) (D : Polynomial ℂ) : ∀ v ∈ S, Polynomial.aeval L D v ∈ S := by
  induction D using Polynomial.induction_on' with
  | add p q hp hq =>
    intro v hv
    rw [map_add, LinearMap.add_apply]
    exact S.add_mem (hp v hv) (hq v hv)
  | monomial n c =>
    intro v hv
    rw [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
    exact S.smul_mem c (pow_apply_mem_of_mapsTo S L hL n v hv)

/-- A map that is additive and homogeneous on a submodule and intertwines two endomorphisms there
intertwines all their polynomials there. -/
theorem map_aeval_of_intertwines (S : Submodule ℂ E) (L : Module.End ℂ E) (L' : Module.End ℂ E')
    (T : E → E') (hL : ∀ v ∈ S, L v ∈ S)
    (hadd : ∀ v ∈ S, ∀ w ∈ S, T (v + w) = T v + T w)
    (hsmul : ∀ (c : ℂ), ∀ v ∈ S, T (c • v) = c • T v)
    (hT : ∀ v ∈ S, T (L v) = L' (T v)) (D : Polynomial ℂ) :
    ∀ v ∈ S, T (Polynomial.aeval L D v) = Polynomial.aeval L' D (T v) := by
  have hpow : ∀ n : ℕ, ∀ v ∈ S, T ((L ^ n) v) = (L' ^ n) (T v) := by
    intro n
    induction n with
    | zero => intro v _; simp
    | succ n ih =>
      intro v hv
      rw [pow_succ', Module.End.mul_apply, hT _ (pow_apply_mem_of_mapsTo S L hL n v hv), ih v hv,
        pow_succ', Module.End.mul_apply]
  induction D using Polynomial.induction_on' with
  | add p q hp hq =>
    intro v hv
    rw [map_add, LinearMap.add_apply, hadd _ (aeval_apply_mem_of_mapsTo S L hL p v hv) _
      (aeval_apply_mem_of_mapsTo S L hL q v hv), hp v hv, hq v hv, map_add, LinearMap.add_apply]
  | monomial n c =>
    intro v hv
    rw [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply,
      hsmul c _ (pow_apply_mem_of_mapsTo S L hL n v hv), hpow n v hv, Polynomial.aeval_monomial,
      Module.End.mul_apply, Module.algebraMap_end_apply]

end Polynomial

section Coset

/-- On a compact left quotient, every coset has a representative at which a continuous real
function is bounded by one common constant. -/
theorem exists_le_of_compactSpace_leftCosetSpace {H : Type*} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] (Γ : Subgroup H) [CompactSpace (LeftCosetSpace Γ)] (φ : H → ℝ)
    (hφ : Continuous φ) : ∃ B : ℝ, ∀ x : H, ∃ gam ∈ Γ, φ (gam * x) ≤ B := by
  let O : H → Set (LeftCosetSpace Γ) := fun y => LeftCosetSpace.mk Γ '' {z | φ z < φ y + 1}
  have hO : ∀ y, IsOpen (O y) := fun y =>
    (LeftCosetSpace.isOpenQuotientMap_mk Γ).isOpenMap _ (isOpen_lt hφ continuous_const)
  have hcov : (Set.univ : Set (LeftCosetSpace Γ)) ⊆ ⋃ y, O y := by
    intro q _
    obtain ⟨y, rfl⟩ := LeftCosetSpace.mk_surjective Γ q
    exact Set.mem_iUnion.mpr ⟨y, y, by simp, rfl⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover O hO hcov
  refine ⟨∑ y ∈ t, |φ y| + 1, fun x => ?_⟩
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ (LeftCosetSpace.mk Γ x)))
  obtain ⟨z, hz, hzx⟩ := hxy
  have hmem := (LeftCosetSpace.mk_eq_mk_iff Γ x z).mp hzx.symm
  refine ⟨z * x⁻¹, hmem, ?_⟩
  rw [inv_mul_cancel_right]
  have h1 : φ y ≤ ∑ y ∈ t, |φ y| :=
    (le_abs_self _).trans (Finset.single_le_sum (fun i _ => abs_nonneg (φ i)) hy)
  change φ z < φ y + 1 at hz
  linarith

end Coset

/-- The raw left shift `φ ↦ φ(x ·)` on scalar functions on `G(𝔸)`. -/
def adelicLeftShift {F : Type u} [Field F] [NumberField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} (x : AdelicGroupPoints F G) :
    Module.End ℂ (AdelicGroupPoints F G → ℂ) where
  toFun φ g := φ (x * g)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem adelicLeftShift_apply {F : Type u} [Field F] [NumberField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} (x : AdelicGroupPoints F G)
    (φ : AdelicGroupPoints F G → ℂ) (g : AdelicGroupPoints F G) :
    adelicLeftShift x φ g = φ (x * g) := rfl

section Growth

open Langlands.GroupScheme

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} {N : ℕ}
  (rho : MatrixRepresentation G (Fin N))

/-- Polynomial growth in the submultiplicative height, with nonnegative constants. -/
def HasHeightGrowth (f : AdelicGroupPoints F G → ℂ) : Prop :=
  ∃ C r : ℝ, 0 ≤ C ∧ 0 ≤ r ∧
    ∀ g, ‖f g‖ ≤ C * RepresentationGrowth.adelicHeight F G rho g ^ r

variable {rho}

theorem hasModerateGrowthFunction_iff_hasHeightGrowth (hN : 0 < N)
    (f : AdelicGroupPoints F G → ℂ) :
    Automorphic.GroupSchemeFunctions.HasModerateGrowthFunction F G rho f ↔
      HasHeightGrowth rho f := by
  set s : ℝ := (N : ℝ) ^ (∑ v : InfinitePlace F, v.mult) with hs
  have hs0 : 0 < s := pow_pos (by exact_mod_cast hN) _
  have hH : ∀ g, RepresentationGrowth.adelicHeight F G rho g =
      s * RepresentationGrowth.adelicSourceNorm F G rho g :=
    fun g => RepresentationGrowth.adelicHeight_eq_scalar_mul_sourceNorm F G rho g
  have hS0 : ∀ g, 0 < RepresentationGrowth.adelicSourceNorm F G rho g :=
    fun g => RepresentationGrowth.adelicSourceNorm_pos F G rho hN g
  have h1 : ∀ g, 1 ≤ RepresentationGrowth.adelicHeight F G rho g :=
    fun g => RepresentationGrowth.one_le_adelicHeight F G rho hN g
  constructor
  · rintro ⟨C, hC, r, hf⟩
    refine ⟨C / s ^ r, max r 0, by positivity, le_max_right _ _, fun g => ?_⟩
    have hSg : RepresentationGrowth.adelicSourceNorm F G rho g =
        RepresentationGrowth.adelicHeight F G rho g / s := by
      rw [hH g]; field_simp
    calc ‖f g‖ ≤ C * RepresentationGrowth.adelicSourceNorm F G rho g ^ r := hf g
      _ = C / s ^ r * RepresentationGrowth.adelicHeight F G rho g ^ r := by
        rw [hSg, Real.div_rpow (by linarith [h1 g]) hs0.le]; ring
      _ ≤ C / s ^ r * RepresentationGrowth.adelicHeight F G rho g ^ max r 0 :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le (h1 g) (le_max_left _ _)) (by positivity)
  · rintro ⟨C, r, hC, hr, hf⟩
    refine ⟨(C + 1) * s ^ r, by positivity, r, fun g => ?_⟩
    have hSr : 0 ≤ RepresentationGrowth.adelicSourceNorm F G rho g ^ r :=
      Real.rpow_nonneg (hS0 g).le _
    have hsr : 0 ≤ s ^ r := Real.rpow_nonneg hs0.le _
    calc ‖f g‖ ≤ C * RepresentationGrowth.adelicHeight F G rho g ^ r := hf g
      _ = C * s ^ r * RepresentationGrowth.adelicSourceNorm F G rho g ^ r := by
        rw [hH g, Real.mul_rpow hs0.le (hS0 g).le]; ring
      _ ≤ (C + 1) * s ^ r * RepresentationGrowth.adelicSourceNorm F G rho g ^ r := by
        gcongr; linarith

theorem HasHeightGrowth.zero : HasHeightGrowth rho (0 : AdelicGroupPoints F G → ℂ) :=
  ⟨0, 0, le_rfl, le_rfl, fun g => by simp⟩

theorem HasHeightGrowth.add (hN : 0 < N) {f h : AdelicGroupPoints F G → ℂ}
    (hf : HasHeightGrowth rho f) (hh : HasHeightGrowth rho h) : HasHeightGrowth rho (f + h) := by
  obtain ⟨C, r, hC, hr, hf⟩ := hf
  obtain ⟨D, t, hD, ht, hh⟩ := hh
  refine ⟨C + D, max r t, by positivity, le_max_of_le_left hr, fun g => ?_⟩
  have hg := RepresentationGrowth.one_le_adelicHeight F G rho hN g
  have h1 := Real.rpow_le_rpow_of_exponent_le hg (le_max_left r t)
  have h2 := Real.rpow_le_rpow_of_exponent_le hg (le_max_right r t)
  calc ‖(f + h) g‖ ≤ ‖f g‖ + ‖h g‖ := norm_add_le _ _
    _ ≤ C * RepresentationGrowth.adelicHeight F G rho g ^ r +
        D * RepresentationGrowth.adelicHeight F G rho g ^ t := add_le_add (hf g) (hh g)
    _ ≤ C * RepresentationGrowth.adelicHeight F G rho g ^ max r t +
        D * RepresentationGrowth.adelicHeight F G rho g ^ max r t :=
      add_le_add (mul_le_mul_of_nonneg_left h1 hC) (mul_le_mul_of_nonneg_left h2 hD)
    _ = (C + D) * RepresentationGrowth.adelicHeight F G rho g ^ max r t := by ring

theorem HasHeightGrowth.smul (c : ℂ) {f : AdelicGroupPoints F G → ℂ}
    (hf : HasHeightGrowth rho f) : HasHeightGrowth rho (c • f) := by
  obtain ⟨C, r, hC, hr, hf⟩ := hf
  refine ⟨‖c‖ * C, r, by positivity, hr, fun g => ?_⟩
  rw [Pi.smul_apply, norm_smul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hf g) (norm_nonneg c)

theorem HasHeightGrowth.adelicLeftShift (hN : 0 < N) (x : AdelicGroupPoints F G)
    {f : AdelicGroupPoints F G → ℂ} (hf : HasHeightGrowth rho f) :
    HasHeightGrowth rho (adelicLeftShift x f) := by
  obtain ⟨C, r, hC, hr, hf⟩ := hf
  have hx := RepresentationGrowth.one_le_adelicHeight F G rho hN x
  refine ⟨C * RepresentationGrowth.adelicHeight F G rho x ^ r, r,
    mul_nonneg hC (Real.rpow_nonneg (by linarith) _), hr, fun g => ?_⟩
  have hg := RepresentationGrowth.one_le_adelicHeight F G rho hN g
  have hxg := RepresentationGrowth.one_le_adelicHeight F G rho hN (x * g)
  calc ‖Global.adelicLeftShift x f g‖ ≤ C * RepresentationGrowth.adelicHeight F G rho (x * g) ^ r :=
        hf (x * g)
    _ ≤ C * (RepresentationGrowth.adelicHeight F G rho x *
        RepresentationGrowth.adelicHeight F G rho g) ^ r :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by linarith)
        (RepresentationGrowth.adelicHeight_mul_le F G rho hN x g) hr) hC
    _ = C * RepresentationGrowth.adelicHeight F G rho x ^ r *
        RepresentationGrowth.adelicHeight F G rho g ^ r := by
      rw [Real.mul_rpow (by linarith) (by linarith)]; ring

end Growth

namespace StandardParabolicFamily

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (𝓕 : StandardParabolicFamily F G)

local notation "Idx" => StandardIndex F G 𝓕.i 𝓕.ν
local notation "rad(" J ")" => SubgroupFunctor.range (𝓕.iU J ≫ 𝓕.p J)

/-- A raw difference of `AdelicExponentPolynomials` is the raw left shift minus a scalar. -/
theorem unnormalizedExponentDifference_eq_adelicLeftShift (J : Idx)
    (lam : ComplexCharacterParameter F (𝓕.P J)) (a : AdelicGroupPoints F (𝓕.P J)) :
    𝓕.unnormalizedExponentDifference J lam a =
      adelicLeftShift (map F (𝓕.P J) G (𝓕.p J) a) -
        algebraMap ℂ _ (parameterPower F (𝓕.P J) lam a) := by
  apply LinearMap.ext
  intro φ
  funext g
  rw [unnormalizedExponentDifference_apply]
  rfl

section Annihilator

variable (Kinf : Subgroup (InfiniteAdelicGroupPoints F G)) {N : ℕ}
  (rho : MatrixRepresentation G (Fin N))

/-- The cuspidal annihilator along `J` is stable under raw shifts by positive points of `A_J`:
such a point is central in the Levi, so the shift becomes a right translate. -/
theorem InCuspidalAnnihilator.adelicLeftShift {J : Idx} (b : 𝓕.positiveSplitComponent J)
    {h : AdelicGroupPoints F G → ℂ} (hh : 𝓕.InCuspidalAnnihilator Kinf rho J h) :
    𝓕.InCuspidalAnnihilator Kinf rho J
      (Global.adelicLeftShift (map F (𝓕.P J) G (𝓕.p J) b) h) := by
  intro ψ hψ g
  have heq : 𝓕.leviPairingIntegrand J
      (Global.adelicLeftShift (map F (𝓕.P J) G (𝓕.p J) b) h) g ψ =
      𝓕.leviPairingIntegrand J h (map F (𝓕.P J) G (𝓕.p J) b * g) ψ := by
    funext q
    simp only [leviPairingIntegrand, adelicLeftShift_apply]
    rw [← mul_assoc, (𝓕.commute_positiveSplitComponent_levi J b _).eq, mul_assoc]
  obtain ⟨hI, h0⟩ := hh ψ hψ (map F (𝓕.P J) G (𝓕.p J) b * g)
  refine ⟨heq ▸ hI, ?_⟩
  unfold leviPairing
  rw [heq]
  exact h0

/-- For `Q ≤ P` and a positive point of `A_P`, every polynomial in the raw shift preserves
the cuspidal annihilator along `Q`. -/
theorem aeval_adelicLeftShift_mem_cuspidalAnnihilator {Q P : Idx} (hQP : Q ≤ P)
    (a : 𝓕.positiveSplitComponent P) (D : Polynomial ℂ) {h : AdelicGroupPoints F G → ℂ}
    (hh : h ∈ 𝓕.cuspidalAnnihilator Kinf rho Q) :
    Polynomial.aeval (Global.adelicLeftShift (map F (𝓕.P P) G (𝓕.p P) a)) D h ∈
      𝓕.cuspidalAnnihilator Kinf rho Q := by
  obtain ⟨b, hb, -⟩ := 𝓕.exists_positiveSplitComponent_lift_with_values hQP a
  rw [← hb]
  exact aeval_apply_mem_of_mapsTo _ _
    (fun v hv => InCuspidalAnnihilator.adelicLeftShift 𝓕 Kinf rho b hv) D h hh

end Annihilator

section ConstantTerm

/-- Inputs on which `C_Q` is additive and commutes with raw shifts by `A_P`, for `Q ≤ P`. -/
def radicalIntegrableSubmodule (Q P : Idx) : Submodule ℂ (AdelicGroupPoints F G → ℂ) where
  carrier := {f | 𝓕.IsRadicalInvariant P f ∧ 𝓕.HasIntegrableConstantTerm Q f}
  zero_mem' := ⟨fun _ _ => rfl, fun _ => integrable_zero _ _ _⟩
  add_mem' {f h} hf hh := ⟨fun n g => by
      change f _ + h _ = f g + h g
      rw [hf.1 n g, hh.1 n g], fun g => (hf.2 g).add (hh.2 g)⟩
  smul_mem' c f hf := ⟨fun n g => by
      change c • f _ = c • f g
      rw [hf.1 n g], fun g => (hf.2 g).const_mul c⟩

theorem constantTerm_add_of_hasIntegrableConstantTerm {Q : Idx}
    {f h : AdelicGroupPoints F G → ℂ} (hf : 𝓕.HasIntegrableConstantTerm Q f)
    (hh : 𝓕.HasIntegrableConstantTerm Q h) :
    𝓕.constantTerm Q (f + h) = 𝓕.constantTerm Q f + 𝓕.constantTerm Q h := by
  funext g
  unfold constantTerm AdelicGroupPoints.subgroupConstantTerm
  exact integral_add (hf g) (hh g)

theorem constantTerm_const_smul (Q : Idx) (c : ℂ) (f : AdelicGroupPoints F G → ℂ) :
    𝓕.constantTerm Q (c • f) = c • 𝓕.constantTerm Q f := by
  funext g
  unfold constantTerm AdelicGroupPoints.subgroupConstantTerm
  exact integral_const_mul c _

theorem adelicLeftShift_mem_radicalIntegrableSubmodule {Q P : Idx} (hQP : Q ≤ P)
    (a : 𝓕.positiveSplitComponent P) {f : AdelicGroupPoints F G → ℂ}
    (hf : f ∈ 𝓕.radicalIntegrableSubmodule Q P) :
    Global.adelicLeftShift (map F (𝓕.P P) G (𝓕.p P) a) f ∈ 𝓕.radicalIntegrableSubmodule Q P := by
  obtain ⟨hr, hi⟩ := hf
  refine ⟨IsRadicalInvariant.unnormalizedAction 𝓕 hr a, ?_⟩
  intro g
  refine (hi (map F (𝓕.P P) G (𝓕.p P) a * g)).congr (Filter.Eventually.of_forall fun q => ?_)
  exact (IsRadicalInvariant.unnormalizedAction_radical_mul 𝓕 hQP hr a (Quotient.out q) g).symm

/-- For `Q ≤ P`, the `Q` constant term intertwines every polynomial in the raw shift by a
positive point of `A_P`, on radical-invariant inputs with integrable `Q` constant terms. -/
theorem constantTerm_aeval_adelicLeftShift {Q P : Idx} (hQP : Q ≤ P)
    (a : 𝓕.positiveSplitComponent P) (D : Polynomial ℂ) {f : AdelicGroupPoints F G → ℂ}
    (hf : f ∈ 𝓕.radicalIntegrableSubmodule Q P) :
    𝓕.constantTerm Q (Polynomial.aeval (Global.adelicLeftShift (map F (𝓕.P P) G (𝓕.p P) a)) D f) =
      Polynomial.aeval (Global.adelicLeftShift (map F (𝓕.P P) G (𝓕.p P) a)) D
        (𝓕.constantTerm Q f) :=
  map_aeval_of_intertwines (𝓕.radicalIntegrableSubmodule Q P)
    (Global.adelicLeftShift (map F (𝓕.P P) G (𝓕.p P) a))
    (Global.adelicLeftShift (map F (𝓕.P P) G (𝓕.p P) a)) (𝓕.constantTerm Q)
    (fun _ hv => 𝓕.adelicLeftShift_mem_radicalIntegrableSubmodule hQP a hv)
    (fun _ hv _ hw => 𝓕.constantTerm_add_of_hasIntegrableConstantTerm hv.2 hw.2)
    (fun c v _ => 𝓕.constantTerm_const_smul Q c v)
    (fun _ hv => 𝓕.constantTerm_unnormalizedAction_of_radicalInvariant hQP a hv.1)
    D f hf

end ConstantTerm

section Parabolic

/-- The left stabilizer `{y | ∀ g, h (y g) = h g}` of a scalar function. -/
def scalarLeftStabilizer (h : AdelicGroupPoints F G → ℂ) : Subgroup (AdelicGroupPoints F G) where
  carrier := {y | ∀ g, h (y * g) = h g}
  mul_mem' {y z} hy hz g := by
    change h (y * z * g) = h g
    rw [mul_assoc, hy, hz]
  one_mem' g := by
    change h (1 * g) = h g
    rw [one_mul]
  inv_mem' {y} hy g := by
    rw [← hy (y⁻¹ * g), mul_inv_cancel_left]

/-- Left invariance by the two generating subgroups `U_P(𝔸)` and `M_P(F)` of the
parabolic quotient subgroup. -/
def IsParabolicGeneratorInvariant (P : Idx) (h : AdelicGroupPoints F G → ℂ) : Prop :=
  𝓕.IsRadicalInvariant P h ∧
    ∀ (m : RationalGroupPoints F (𝓕.M P)) (g : AdelicGroupPoints F G),
      h (map F (𝓕.M P) G (𝓕.l P ≫ 𝓕.p P) (AdelicGroupPoints.rational F (𝓕.M P) m) * g) = h g

theorem IsParabolicGeneratorInvariant.isLeftInvariantUnder {P : Idx}
    {h : AdelicGroupPoints F G → ℂ} (hh : 𝓕.IsParabolicGeneratorInvariant P h) :
    IsLeftInvariantUnder F G (parabolicQuotientSubgroup F (𝓕.p P) (𝓕.iU P) (𝓕.l P)) h := by
  have hle : parabolicQuotientSubgroup F (𝓕.p P) (𝓕.iU P) (𝓕.l P) ≤ scalarLeftStabilizer h := by
    apply sup_le
    · rintro _ ⟨u, rfl⟩ g
      exact hh.1 ⟨_, SubgroupFunctor.mem_range.mpr ⟨u, rfl⟩⟩ g
    · rintro _ ⟨m, rfl⟩ g
      exact hh.2 m g
  intro x hx g
  exact hle hx g

theorem IsParabolicGeneratorInvariant.adelicLeftShift {P : Idx}
    {h : AdelicGroupPoints F G → ℂ} (hh : 𝓕.IsParabolicGeneratorInvariant P h)
    (a : 𝓕.positiveSplitComponent P) :
    𝓕.IsParabolicGeneratorInvariant P
      (Global.adelicLeftShift (map F (𝓕.P P) G (𝓕.p P) a) h) := by
  refine ⟨IsRadicalInvariant.unnormalizedAction 𝓕 hh.1 a, fun m g => ?_⟩
  simp only [adelicLeftShift_apply]
  rw [← mul_assoc, (𝓕.commute_positiveSplitComponent_levi P a _).eq, mul_assoc, hh.2 m]

omit [NumberField F] in
/-- The Levi of `P` normalizes the radical of `P`, on every test scheme. -/
theorem radical_isNormalizedBy_levi (P : Idx) :
    rad(P).IsNormalizedBy (SubgroupFunctor.range (𝓕.l P ≫ 𝓕.p P)) := by
  rw [𝓕.range_radical_eq_standardUnipotent]
  intro X v u hv hu
  have hvP : v ∈ (SubgroupFunctor.range (𝓕.p P)).carrier X := by
    obtain ⟨m, hm⟩ := SubgroupFunctor.mem_range.mp hv
    exact SubgroupFunctor.mem_range.mpr ⟨m ≫ (𝓕.l P).hom.hom, by
      simpa only [Grp.comp_hom_hom, Category.assoc] using hm⟩
  rw [(𝓕.isCompatible P).parabolic_eq] at hvP
  exact StandardLeviIntersection.conj_mem_standardUnipotent 𝓕.i 𝓕.ν hvP hu

variable {N : ℕ} (rho : MatrixRepresentation G (Fin N))

/-- Continuous functions of polynomial height growth, invariant by `U_P(𝔸)` and `M_P(F)`. -/
def parabolicModerateSubmodule (hN : 0 < N) (P : Idx) :
    Submodule ℂ (AdelicGroupPoints F G → ℂ) where
  carrier := {f | 𝓕.IsParabolicGeneratorInvariant P f ∧ Continuous f ∧ HasHeightGrowth rho f}
  zero_mem' := ⟨⟨fun _ _ => rfl, fun _ _ => rfl⟩, continuous_const, HasHeightGrowth.zero⟩
  add_mem' {f h} hf hh := ⟨⟨fun n g => by
        change f _ + h _ = f g + h g
        rw [hf.1.1 n g, hh.1.1 n g],
      fun m g => by
        change f _ + h _ = f g + h g
        rw [hf.1.2 m g, hh.1.2 m g]⟩,
    hf.2.1.add hh.2.1, hf.2.2.add hN hh.2.2⟩
  smul_mem' c f hf := ⟨⟨fun n g => by
        change c • f _ = c • f g
        rw [hf.1.1 n g],
      fun m g => by
        change c • f _ = c • f g
        rw [hf.1.2 m g]⟩,
    hf.2.1.const_smul c, hf.2.2.smul c⟩

theorem adelicLeftShift_mem_parabolicModerateSubmodule (hN : 0 < N) {P : Idx}
    (a : 𝓕.positiveSplitComponent P) {f : AdelicGroupPoints F G → ℂ}
    (hf : f ∈ 𝓕.parabolicModerateSubmodule rho hN P) :
    Global.adelicLeftShift (map F (𝓕.P P) G (𝓕.p P) a) f ∈
      𝓕.parabolicModerateSubmodule rho hN P := by
  refine ⟨IsParabolicGeneratorInvariant.adelicLeftShift 𝓕 hf.1 a, ?_,
    HasHeightGrowth.adelicLeftShift hN _ hf.2.2⟩
  change Continuous (fun g => f (map F (𝓕.P P) G (𝓕.p P) a * g))
  exact hf.2.1.comp (continuous_const.mul continuous_id)

/-- The `P` constant term of a continuous rational-invariant function of polynomial height
growth lies in the parabolic moderate submodule. -/
theorem constantTerm_mem_parabolicModerateSubmodule (hN : 0 < N) (P : Idx)
    (f : ContinuousRationalFunctions F G) (hf : HasHeightGrowth rho (evaluate F G f)) :
    𝓕.constantTerm P (evaluate F G f) ∈ 𝓕.parabolicModerateSubmodule rho hN P := by
  let U := rad(P)
  let : IsClosed (AdelicSubgroupPoints.adelicPoints F G U : Set (AdelicGroupPoints F G)) :=
    AdelicSubgroupPoints.isClosed_adelicPoints_range F G (𝓕.iU P ≫ 𝓕.p P)
  let := 𝓕.compactSpace_radicalRationalQuotient P
  have hP : 𝓕.constantTerm P (evaluate F G f) =
      AdelicSubgroupPoints.normalizedConstantTerm F G U f :=
    funext fun x => (AdelicSubgroupPoints.normalizedConstantTerm_range_eq_subgroupConstantTerm
      F G (𝓕.iU P ≫ 𝓕.p P) f x).symm
  refine ⟨⟨𝓕.isRadicalInvariant_constantTerm P f, fun m g => ?_⟩, ?_, ?_⟩
  · rw [hP]
    let q : AdelicSubgroupPoints.rationalPoints F G (SubgroupFunctor.range (𝓕.l P ≫ 𝓕.p P)) :=
      ⟨(𝓕.M P).affinePointsTarget (𝓕.l P ≫ 𝓕.p P) (CommAlgCat.of F F) m,
        SubgroupFunctor.mem_range.mpr ⟨m, rfl⟩⟩
    have hq : AdelicGroupPoints.rational F G q.val =
        map F (𝓕.M P) G (𝓕.l P ≫ 𝓕.p P) (AdelicGroupPoints.rational F (𝓕.M P) m) :=
      DFunLike.congr_fun (AdelicGroupPoints.rational_naturality F (𝓕.M P) (𝓕.l P ≫ 𝓕.p P)) m
    rw [← hq]
    exact AdelicSubgroupPoints.normalizedConstantTerm_rationalNormalizer_mul F G U
      (𝓕.radical_isNormalizedBy_levi P) q f g
  · rw [hP]
    exact AdelicSubgroupPoints.continuous_normalizedConstantTerm F G U f
  · let m := AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F G U
    let : IsProbabilityMeasure m :=
      AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure_isProbabilityMeasure F G U
    obtain ⟨C, r, hC, hr, hf⟩ := hf
    obtain ⟨B, hB⟩ := exists_le_of_compactSpace_leftCosetSpace
      (AdelicSubgroupPoints.rationalSubgroup F G U)
      (fun n : AdelicSubgroupPoints.adelicPoints F G U =>
        RepresentationGrowth.adelicHeight F G rho (n : AdelicGroupPoints F G))
      ((RepresentationGrowth.continuous_adelicHeight F G rho hN).comp continuous_subtype_val)
    have hB1 : 1 ≤ B := by
      obtain ⟨gam, -, hgam⟩ := hB 1
      exact (RepresentationGrowth.one_le_adelicHeight F G rho hN _).trans hgam
    refine ⟨C * B ^ r, r, mul_nonneg hC (Real.rpow_nonneg (by linarith) _), hr, fun g => ?_⟩
    have hg := RepresentationGrowth.one_le_adelicHeight F G rho hN g
    have hpt : ∀ q : AdelicSubgroupPoints.RationalQuotient F G U,
        ‖evaluate F G f (((Quotient.out q : AdelicSubgroupPoints.adelicPoints F G U) :
          AdelicGroupPoints F G) * g)‖ ≤
          C * B ^ r * RepresentationGrowth.adelicHeight F G rho g ^ r := by
      intro q
      obtain ⟨gam, hgam, hgamB⟩ := hB (Quotient.out q)
      obtain ⟨q0, hq0⟩ := hgam
      have hval : ((gam : AdelicSubgroupPoints.adelicPoints F G U) : AdelicGroupPoints F G) =
          AdelicGroupPoints.rational F G q0.val := by
        rw [← hq0]; rfl
      have heq : evaluate F G f (((Quotient.out q : AdelicSubgroupPoints.adelicPoints F G U) :
            AdelicGroupPoints F G) * g) =
          evaluate F G f (((gam * Quotient.out q : AdelicSubgroupPoints.adelicPoints F G U) :
            AdelicGroupPoints F G) * g) := by
        rw [Subgroup.coe_mul, hval, mul_assoc]
        exact (f.val.property q0.val _).symm
      rw [heq]
      set y : AdelicGroupPoints F G :=
        ((gam * Quotient.out q : AdelicSubgroupPoints.adelicPoints F G U) : AdelicGroupPoints F G)
      have hyB : RepresentationGrowth.adelicHeight F G rho y ≤ B := hgamB
      have hy := RepresentationGrowth.one_le_adelicHeight F G rho hN y
      have hyg := RepresentationGrowth.one_le_adelicHeight F G rho hN (y * g)
      calc ‖evaluate F G f (y * g)‖
          ≤ C * RepresentationGrowth.adelicHeight F G rho (y * g) ^ r := hf _
        _ ≤ C * (RepresentationGrowth.adelicHeight F G rho y *
            RepresentationGrowth.adelicHeight F G rho g) ^ r :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by linarith)
            (RepresentationGrowth.adelicHeight_mul_le F G rho hN y g) hr) hC
        _ = C * (RepresentationGrowth.adelicHeight F G rho y ^ r *
            RepresentationGrowth.adelicHeight F G rho g ^ r) := by
          rw [Real.mul_rpow (by linarith) (by linarith)]
        _ ≤ C * (B ^ r * RepresentationGrowth.adelicHeight F G rho g ^ r) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
            (Real.rpow_le_rpow (by linarith) hyB hr) (Real.rpow_nonneg (by linarith) _)) hC
        _ = C * B ^ r * RepresentationGrowth.adelicHeight F G rho g ^ r := by ring
    unfold constantTerm AdelicGroupPoints.subgroupConstantTerm
    refine (norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall hpt)).trans ?_
    simp

end Parabolic

section Main

variable {N : ℕ} (rho : MatrixRepresentation G (Fin N))

/-- Bernstein–Lapid, proof of Lemma 8.1, conditional on the vanishing criterion (8.1): fix a
positive point `a` of `A_P`. If for each `Q ≤ P` a polynomial `D_Q` in the raw shift by `a`
sends the `Q` constant term of `f` into the cuspidal annihilator of `Q`, then the product of
all `D_Q` (over any finite set containing every `Q ≤ P`) kills the `P` constant term of `f`. -/
theorem aeval_prod_adelicLeftShift_constantTerm_eq_zero
    (hvan : ParabolicCuspidalVanishingStatement.{u})
    (K : Subgroup (AdelicGroupPoints F G)) (hK : IsMaximalCompactSubgroup F G K)
    (hIw : ∀ Q : Idx, IsIwasawaCompact (𝓕.p Q) K) (hN : 0 < N) (hrho : IsClosedSubgroup rho)
    (P : Idx) (f : ContinuousRationalFunctions F G)
    (hf : HasModerateGrowthFunction F G rho (evaluate F G f))
    (a : 𝓕.positiveSplitComponent P) (S : Finset Idx) (hS : ∀ Q : Idx, Q ≤ P → Q ∈ S)
    (D : Idx → Polynomial ℂ)
    (hD : ∀ Q : Idx, Q ≤ P →
      Polynomial.aeval (Global.adelicLeftShift (map F (𝓕.P P) G (𝓕.p P) a)) (D Q)
          (𝓕.constantTerm Q (evaluate F G f)) ∈
        𝓕.cuspidalAnnihilator (K.comap (ofInfinite F G).toMonoidHom) rho Q) :
    Polynomial.aeval (Global.adelicLeftShift (map F (𝓕.P P) G (𝓕.p P) a)) (∏ Q ∈ S, D Q)
      (𝓕.constantTerm P (evaluate F G f)) = 0 := by
  classical
  have hfH := (hasModerateGrowthFunction_iff_hasHeightGrowth hN _).mp hf
  have hmem : Polynomial.aeval (Global.adelicLeftShift (map F (𝓕.P P) G (𝓕.p P) a))
      (∏ Q ∈ S, D Q) (𝓕.constantTerm P (evaluate F G f)) ∈
        𝓕.parabolicModerateSubmodule rho hN P :=
    aeval_apply_mem_of_mapsTo _ _
      (fun _ hv => 𝓕.adelicLeftShift_mem_parabolicModerateSubmodule rho hN a hv) _ _
      (𝓕.constantTerm_mem_parabolicModerateSubmodule rho hN P f hfH)
  apply hvan F G 𝓕 K hK hIw rho hN hrho P
  · unfold IsModerateContinuousOnParabolic
    exact ⟨IsParabolicGeneratorInvariant.isLeftInvariantUnder 𝓕 hmem.1, hmem.2.1,
      (hasModerateGrowthFunction_iff_hasHeightGrowth hN _).mpr hmem.2.2⟩
  · intro Q hQP
    have hin : 𝓕.constantTerm P (evaluate F G f) ∈ 𝓕.radicalIntegrableSubmodule Q P :=
      ⟨𝓕.isRadicalInvariant_constantTerm P f, 𝓕.hasIntegrableConstantTerm_constantTerm_of_le hQP f⟩
    rw [𝓕.constantTerm_aeval_adelicLeftShift hQP a _ hin, 𝓕.constantTerm_constantTerm_of_le hQP f,
      ← Finset.prod_erase_mul S D (hS Q hQP), map_mul, Module.End.mul_apply]
    exact 𝓕.aeval_adelicLeftShift_mem_cuspidalAnnihilator _ rho hQP a _ (hD Q hQP)

end Main

end StandardParabolicFamily

end Langlands.Global
