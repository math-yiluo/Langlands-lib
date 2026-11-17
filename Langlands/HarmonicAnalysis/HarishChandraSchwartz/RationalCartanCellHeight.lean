import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalXiSquareIntegrableOfUpperBound
import Langlands.Representation.Aubert.General.RationalCartanJointDetection
import Langlands.GroupScheme.Rational.RelativeRootsCharacterSpan
import Langlands.GroupScheme.Rational.RelativeRootSystemProof
import Langlands.Representation.Plancherel.RationalCharacterTopology

/-! # The height on the norm-one points of a Cartan cell

For a maximal split torus `i : S → G` of a connected reductive group, a generic cocharacter `ν`,
a compact subgroup `K₀` and a finite set `F₀` of points of the centralizer of `S`, the height
`σ` of a point `g ∈ K₀ ϖ^y f K₀` (`f ∈ F₀`) of the norm-one subgroup `G¹` is at most
`C (1 + T)`, where `T` bounds the absolute values of the pairings of `y` with the simple roots.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct
open Langlands.GroupScheme Langlands.LinearAlgebra.RationalSpan
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.HarishChandraSchwartz

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact

section AbstractHeight

variable {X : Type*} [Group X] {σ : X → ℝ}

/-- A subadditive, inversion-invariant `σ` with `σ(1) = 0` along a homomorphism `φ` from a
lattice: `σ(φ(∑ aₖ bₖ)) ≤ ∑ |aₖ| σ(φ(bₖ))`. -/
theorem le_sum_abs_mul_of_subadditive {Y : Type*} [AddCommGroup Y]
    (φ : Multiplicative Y →* X) (h1 : σ 1 = 0) (hinv : ∀ x, σ x⁻¹ = σ x)
    (hmul : ∀ x y, σ (x * y) ≤ σ x + σ y) {Idx : Type*} (s : Finset Idx) (a : Idx → ℤ)
    (b : Idx → Y) :
    σ (φ (.ofAdd (∑ k ∈ s, a k • b k))) ≤ ∑ k ∈ s, |(a k : ℝ)| * σ (φ (.ofAdd (b k))) := by
  classical
  have hpow : ∀ (x : X) (m : ℕ), σ (x ^ m) ≤ m * σ x := by
    intro x m
    induction m with
    | zero => simp [h1]
    | succ m ih =>
      rw [pow_succ]
      refine (hmul _ _).trans ?_
      push_cast
      linarith
  have hzpow : ∀ (x : X) (m : ℤ), σ (x ^ m) ≤ |(m : ℝ)| * σ x := by
    intro x m
    obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg m
    · simpa using hpow x m
    · rw [zpow_neg, hinv]
      simpa using hpow x m
  induction s using Finset.induction_on with
  | empty => simp [h1]
  | insert k s hk ih =>
    rw [Finset.sum_insert hk, Finset.sum_insert hk, ofAdd_add, map_mul]
    refine (hmul _ _).trans (add_le_add ?_ ih)
    rw [ofAdd_zsmul, map_zpow]
    exact hzpow _ _

end AbstractHeight

section BoundedFunctionals

variable {M Y : Type*} [AddCommGroup M] [AddCommGroup Y]

/-- The extension `ℚ ⊗ M → ℚ` of the pairing `m ↦ P m y` with a fixed `y`. -/
def rationalPairingAt (P : M →ₗ[ℤ] Y →ₗ[ℤ] ℤ) (y : Y) : ℚ ⊗[ℤ] M →ₗ[ℤ] ℚ :=
  TensorProduct.lift ((LinearMap.mul ℤ ℚ).compl₂ ((Algebra.linearMap ℤ ℚ).comp (P.flip y)))

theorem rationalPairingAt_toRat (P : M →ₗ[ℤ] Y →ₗ[ℤ] ℤ) (y : Y) (m : M) :
    rationalPairingAt P y (toRat m) = (P m y : ℚ) := by
  rw [rationalPairingAt, toRat_apply]
  erw [TensorProduct.lift.tmul]
  simp

/-- **Linear bounds propagate along a rational spanning set.** If the elements of `R` span
`ℚ ⊗ M` over `ℚ` and every `m ∈ R` satisfies `|P m y| ≤ C_m t` for all `(y, t) ∈ W`, then so
does every `m ∈ M`. -/
theorem exists_abs_pairing_le_of_span_eq_top (P : M →ₗ[ℤ] Y →ₗ[ℤ] ℤ) {R : Set M}
    (hR : Submodule.span ℚ (toRat '' R) = ⊤) (W : Set (Y × ℝ))
    (hb : ∀ m ∈ R, ∃ C : ℝ, ∀ p ∈ W, |(P m p.1 : ℝ)| ≤ C * p.2) (m : M) :
    ∃ C : ℝ, ∀ p ∈ W, |(P m p.1 : ℝ)| ≤ C * p.2 := by
  have key : ∀ x ∈ Submodule.span ℚ (toRat '' R), ∃ C : ℝ, ∀ p ∈ W,
      |((rationalPairingAt P p.1 x : ℚ) : ℝ)| ≤ C * p.2 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨m, hm, rfl⟩ := hx
      obtain ⟨C, hC⟩ := hb m hm
      exact ⟨C, fun p hp => by rw [rationalPairingAt_toRat, Rat.cast_intCast]; exact hC p hp⟩
    | zero => exact ⟨0, fun p _ => by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨C₁, h₁⟩ := hx
      obtain ⟨C₂, h₂⟩ := hy
      refine ⟨C₁ + C₂, fun p hp => ?_⟩
      rw [map_add, Rat.cast_add, add_mul]
      exact (abs_add_le _ _).trans (add_le_add (h₁ p hp) (h₂ p hp))
    | smul a x _ hx =>
      obtain ⟨C, hC⟩ := hx
      refine ⟨|(a : ℝ)| * C, fun p hp => ?_⟩
      rw [map_rat_smul, smul_eq_mul, Rat.cast_mul, abs_mul, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hC p hp) (abs_nonneg _)
  obtain ⟨C, hC⟩ := key (toRat m) (hR ▸ Submodule.mem_top)
  refine ⟨C, fun p hp => ?_⟩
  have := hC p hp
  rwa [rationalPairingAt_toRat, Rat.cast_intCast] at this

end BoundedFunctionals

section Bounds

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}

omit [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
/-- For a split torus `S`, the height of the uniformizer powers `ϖ^y` is bounded by a
nonnegative combination `∑_k M_k |⟨α_k, y⟩|` of the absolute values of the pairings of `y`
with finitely many characters `α_k` of `S` (the coordinates of `y` in a basis of `X_*(S)`). -/
theorem exists_rationalHeight_uniformizerPowers_le_sum (hS : IsSplitTorus S.toGrp)
    (i : S.toGrp ⟶ G) {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]
    (ρ : MatrixRepresentation G n) :
    ∃ (I : Type u) (_ : Fintype I) (α : I → characterLattice S) (M : I → ℝ),
      (∀ k, 0 ≤ M k) ∧ ∀ y : cocharacterLattice S,
        rationalHeight (F := F) ρ (Aubert.General.uniformizerPowers i (.ofAdd y)) ≤
          ∑ k, M k * |(latticePairing S (α k) y : ℝ)| := by
  obtain ⟨I, hI, ⟨e⟩⟩ := hS.exists_cocharacterCoordinates
  let : Fintype I := Fintype.ofFinite I
  have := CocharacterUniformizer.latticePairing_isPerfPair F S hS
  have hα : ∀ k : I, ∃ α : characterLattice S, ∀ y, latticePairing S α y = e y k := fun k => by
    obtain ⟨α, hα⟩ := (LinearMap.IsPerfPair.bijective_left (latticePairing S)).2
      ((LinearMap.proj k).comp e.toLinearMap)
    exact ⟨α, fun y => LinearMap.congr_fun hα y⟩
  choose α hα using hα
  let b : Module.Basis I ℤ (cocharacterLattice S) := Module.Basis.ofEquivFun e
  refine ⟨I, inferInstance, α, fun k =>
    rationalHeight (F := F) ρ (Aubert.General.uniformizerPowers i (.ofAdd (b k))),
    fun k => rationalHeight_nonneg ρ _, fun y => ?_⟩
  have hy : ∑ k, e y k • b k = y := by
    conv_rhs => rw [← b.sum_repr y]
    simp [b]
  have h := le_sum_abs_mul_of_subadditive (σ := rationalHeight (F := F) ρ)
    (Aubert.General.uniformizerPowers i) (by simp) (rationalHeight_inv ρ)
    (rationalHeight_mul_le ρ) Finset.univ (fun k => e y k) b
  rw [hy] at h
  refine h.trans (le_of_eq (Finset.sum_congr rfl fun k _ => ?_))
  rw [hα k y, mul_comm]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
/-- Bounds `|⟨β, y⟩| ≤ C t` on the pairings with the simple roots `β` and with the restrictions
of the rational characters of `G`, valid on a set of pairs `(y, t)`, propagate to every
character of `S`: the simple roots span the relative root span over `ℚ`, and the relative
roots together with the restricted rational characters span the rational character space. -/
theorem exists_abs_latticePairing_le_of_simpleRoots (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    {P : cocharacterLattice S → ℝ → Prop}
    (hroot : ∀ β : Aubert.General.RationalPointFamily.SimpleRoot i ν, ∃ C : ℝ,
      ∀ y t, P y t → |(latticePairing S β.1 y : ℝ)| ≤ C * t)
    (hres : ∀ χ : rationalCharacters G, ∃ C : ℝ,
      ∀ y t, P y t → |(latticePairing S (torusCharacterRestrict i χ) y : ℝ)| ≤ C * t)
    (α : characterLattice S) :
    ∃ C : ℝ, ∀ y t, P y t → |(latticePairing S α y : ℝ)| ≤ C * t := by
  have := hi.isSplitSubtorus.mono
  let W : Submodule ℚ (ℚ ⊗[ℤ] characterLattice S) :=
    { carrier := {w | ∃ C : ℝ, ∀ y t, P y t →
        |((rationalCocharacterEvaluation y w : ℚ) : ℝ)| ≤ C * t}
      add_mem' := by
        rintro a c ⟨C₁, h₁⟩ ⟨C₂, h₂⟩
        refine ⟨C₁ + C₂, fun y t hP => ?_⟩
        rw [map_add, Rat.cast_add, add_mul]
        exact (abs_add_le _ _).trans (add_le_add (h₁ y t hP) (h₂ y t hP))
      zero_mem' := ⟨0, fun y t _ => by simp⟩
      smul_mem' := by
        rintro q a ⟨C, h⟩
        refine ⟨|(q : ℝ)| * C, fun y t hP => ?_⟩
        rw [map_smul, smul_eq_mul, Rat.cast_mul, abs_mul, mul_assoc]
        exact mul_le_mul_of_nonneg_left (h y t hP) (abs_nonneg _) }
  have hsimple : ratSpan (simpleRelativeRoots i ν) ≤ W := by
    apply Submodule.span_le.mpr
    rintro _ ⟨β, hβ, rfl⟩
    obtain ⟨C, hC⟩ := hroot ⟨β, hβ⟩
    refine ⟨C, fun y t hP => ?_⟩
    rw [rationalCocharacterEvaluation_toRat, Rat.cast_intCast]
    exact hC y t hP
  have htop : (⊤ : Submodule ℚ (ℚ ⊗[ℤ] characterLattice S)) ≤ W := by
    rw [← relativeRootsRestrictedCharactersSpan F G hG S i hi]
    apply Submodule.span_le.mpr
    rintro _ ⟨β, hβ, rfl⟩
    rcases hβ with hβ | ⟨χ, rfl⟩
    · apply hsimple
      rw [ratSpan_simpleRelativeRoots_eq_relativeRootSpan i ν hν
        (fun _ hα => (relativeRootSystem F G hG S i hi).neg_mem_relativeRoots i
          hi.isSplitSubtorus.1 hα)]
      exact toRat_mem_ratSpan hβ
    · obtain ⟨C, hC⟩ := hres χ
      refine ⟨C, fun y t hP => ?_⟩
      rw [rationalCocharacterEvaluation_toRat, Rat.cast_intCast]
      exact hC y t hP
  obtain ⟨C, hC⟩ := htop (Submodule.mem_top (x := toRat α))
  refine ⟨C, fun y t hP => ?_⟩
  have h := hC y t hP
  rwa [rationalCocharacterEvaluation_toRat, Rat.cast_intCast] at h

/-- **The height on the norm-one points of a Cartan cell.** For a maximal split torus `i` of a
connected reductive group `G`, a generic cocharacter `ν`, a compact subgroup `K₀`, a finite set
`F₀` of points of the centralizer of `S` and a matrix representation `ρ`, there is `C` such that
every point `g` of `G¹` in the Cartan cell `⋃_{f ∈ F₀} K₀ ϖ^y f K₀` satisfies
`σ(g) ≤ C (1 + T)` whenever `0 ≤ T` and `|⟨β, y⟩| ≤ T` for all simple roots `β`. -/
theorem exists_rationalHeight_le_of_mem_rationalCartanCell (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    {K0 : Subgroup (rationalPoints G)} (hK0c : IsCompact (K0 : Set (rationalPoints G)))
    (F0 : Finset (centralizerPoints i)) {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]
    (ρ : MatrixRepresentation G n) :
    ∃ C : ℝ, ∀ (y : cocharacterLattice S) (T : ℝ), 0 ≤ T →
      (∀ β : Aubert.General.RationalPointFamily.SimpleRoot i ν,
        |(Aubert.General.simpleRootPairing i ν β y : ℝ)| ≤ T) →
      ∀ g ∈ rationalCartanCell i K0 F0 y, g ∈ Plancherel.rationalCommonNormKernel G →
        rationalHeight (F := F) ρ g ≤ C * (1 + T) := by
  have hK0 := Plancherel.compactSubgroup_le_rationalCommonNormKernel G K0 hK0c
  obtain ⟨b, hb⟩ := hK0c.bddAbove_image (continuous_rationalHeight (F := F) ρ).continuousOn
  obtain ⟨b', hb'⟩ := (F0.image fun f : centralizerPoints i =>
    rationalHeight (F := F) ρ (f : rationalPoints G)).exists_le
  let P : cocharacterLattice S → ℝ → Prop := fun y t =>
    1 ≤ t ∧ (∀ β : Aubert.General.RationalPointFamily.SimpleRoot i ν,
      |(Aubert.General.simpleRootPairing i ν β y : ℝ)| ≤ t) ∧
      ∃ f ∈ F0, Aubert.General.uniformizerPowers i (.ofAdd y) * (f : rationalPoints G) ∈
        Plancherel.rationalCommonNormKernel G
  have hroot : ∀ β : Aubert.General.RationalPointFamily.SimpleRoot i ν, ∃ C : ℝ,
      ∀ y t, P y t → |(latticePairing S β.1 y : ℝ)| ≤ C * t :=
    fun β => ⟨1, fun y t hP => by simpa using hP.2.1 β⟩
  have hres : ∀ χ : rationalCharacters G, ∃ C : ℝ,
      ∀ y t, P y t → |(latticePairing S (torusCharacterRestrict i χ) y : ℝ)| ≤ C * t := by
    intro χ
    obtain ⟨V, hV⟩ := (F0.image fun f : centralizerPoints i =>
      |((Plancherel.rationalCharacterValuation G (f : rationalPoints G)).toAdd χ : ℝ)|).exists_le
    refine ⟨V, fun y t hP => ?_⟩
    obtain ⟨ht, -, f, hf, hker⟩ := hP
    have hz := (Plancherel.mem_rationalCommonNormKernel_iff_valuation G _).mp hker χ
    rw [map_mul, toAdd_mul, AddMonoidHom.add_apply] at hz
    have hpair : (Plancherel.rationalCharacterValuation G
        (Aubert.General.uniformizerPowers i (.ofAdd y))).toAdd χ =
        latticePairing S (torusCharacterRestrict i χ) y := by
      simp only [Aubert.General.uniformizerPowers, MonoidHom.comp_apply,
        Plancherel.RenardCartan.rationalCharacterValuation_map_uniformizerSection]
      rfl
    have hfV := hV _ (Finset.mem_image_of_mem _ hf)
    rw [← hpair, eq_neg_of_add_eq_zero_left hz, Int.cast_neg, abs_neg]
    have h0 : 0 ≤ |((Plancherel.rationalCharacterValuation G
        (f : rationalPoints G)).toAdd χ : ℝ)| := abs_nonneg _
    nlinarith
  obtain ⟨I, _, α, M, hM, hσ⟩ :=
    exists_rationalHeight_uniformizerPowers_le_sum hi.isSplitSubtorus.1 i ρ
  choose Cα hCα using fun k => exists_abs_latticePairing_le_of_simpleRoots hG hi hν hroot hres
    (α k)
  refine ⟨|2 * b + b'| + ∑ k, M k * |Cα k|, fun y T hT hβ g hg hgker => ?_⟩
  obtain ⟨k₁, hk₁, k₂, hk₂, f, hf, rfl⟩ := hg
  set w := Aubert.General.uniformizerPowers i (.ofAdd y)
  have hwf : w * (f : rationalPoints G) ∈ Plancherel.rationalCommonNormKernel G := by
    have heq : w * (f : rationalPoints G) =
        k₁⁻¹ * (k₁ * w * (f : rationalPoints G) * k₂) * k₂⁻¹ := by group
    rw [heq]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hK0 (K0.inv_mem hk₁)) hgker)
      (hK0 (K0.inv_mem hk₂))
  have hP : P y (1 + T) := ⟨by linarith, fun β => by linarith [hβ β], f, hf, hwf⟩
  have hsum : rationalHeight (F := F) ρ w ≤ ∑ k, M k * |Cα k| * (1 + T) := by
    refine (hσ y).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ((hCα k y (1 + T) hP).trans ?_) (hM k)
    exact mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
  have h₁ : rationalHeight (F := F) ρ k₁ ≤ b := hb ⟨k₁, hk₁, rfl⟩
  have h₂ : rationalHeight (F := F) ρ k₂ ≤ b := hb ⟨k₂, hk₂, rfl⟩
  have h₃ : rationalHeight (F := F) ρ (f : rationalPoints G) ≤ b' :=
    hb' _ (Finset.mem_image_of_mem _ hf)
  have e₁ := rationalHeight_mul_le (F := F) ρ (k₁ * w * (f : rationalPoints G)) k₂
  have e₂ := rationalHeight_mul_le (F := F) ρ (k₁ * w) (f : rationalPoints G)
  have e₃ := rationalHeight_mul_le (F := F) ρ k₁ w
  have habs : 2 * b + b' ≤ |2 * b + b'| * (1 + T) := by
    have := le_abs_self (2 * b + b')
    have := abs_nonneg (2 * b + b')
    nlinarith
  have hs : (|2 * b + b'| + ∑ k, M k * |Cα k|) * (1 + T) =
      |2 * b + b'| * (1 + T) + ∑ k, M k * |Cα k| * (1 + T) := by
    rw [add_mul, Finset.sum_mul]
  rw [hs]
  linarith

end Bounds

end Langlands.HarishChandraSchwartz
