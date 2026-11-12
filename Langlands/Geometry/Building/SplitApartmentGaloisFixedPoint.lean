import Langlands.Geometry.Building.SplitChevalleyApartment
import Langlands.Geometry.Building.IntegerOmegaGaloisStability
import Langlands.GroupScheme.Rational.RootRankOneFactorizationProof
import Langlands.GroupScheme.Absolute.MaximalTorusCentralizerProof
import Langlands.GroupScheme.Torus.MaximalSplitComparison

/-! # Uniqueness and Galois-fixed points of split apartment classes -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.Geometry.Building

section FixedPoint

/-- A finite group acting by affine equivalences on a nonempty real affine space has a
fixed point: the barycenter of any orbit. -/
theorem exists_fixed_of_finite_affineAction {M V P : Type*} [Group M] [Finite M]
    [AddCommGroup V] [Module ℝ V] [AddTorsor V P] [Nonempty P]
    (ρ : M →* (P ≃ᵃ[ℝ] P)) : ∃ x : P, ∀ m, ρ m x = x := by
  classical
  have := Fintype.ofFinite M
  obtain ⟨p⟩ := (inferInstance : Nonempty P)
  set N : ℝ := (Fintype.card M : ℝ)
  have hN : N ≠ 0 := by
    simp only [N, ne_eq, Nat.cast_eq_zero]
    exact Fintype.card_ne_zero
  let c : V := N⁻¹ • ∑ n : M, (ρ n p -ᵥ p)
  refine ⟨c +ᵥ p, fun m => ?_⟩
  have hlin : (ρ m).linear c = N⁻¹ • ∑ n : M, (ρ (m * n) p -ᵥ ρ m p) := by
    simp only [c, map_smul, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    have h := (ρ m).toAffineMap.linearMap_vsub (ρ n p) p
    rw [map_mul, AffineEquiv.coe_mul, Function.comp_apply]
    exact h
  have hsum : ∑ n : M, (ρ (m * n) p -ᵥ ρ m p) =
      (∑ n : M, (ρ n p -ᵥ p)) - N • (ρ m p -ᵥ p) := by
    have hre : ∑ n : M, (ρ (m * n) p -ᵥ p) = ∑ n : M, (ρ n p -ᵥ p) :=
      Fintype.sum_equiv (Equiv.mulLeft m) _ _ fun n => rfl
    have hsplit : ∀ n : M, ρ (m * n) p -ᵥ ρ m p = (ρ (m * n) p -ᵥ p) - (ρ m p -ᵥ p) :=
      fun n => (vsub_sub_vsub_cancel_right _ _ p).symm
    rw [Finset.sum_congr rfl fun n _ => hsplit n, Finset.sum_sub_distrib, hre,
      Finset.sum_const, Finset.card_univ]
    simp only [N, Nat.cast_smul_eq_nsmul]
  rw [AffineEquiv.map_vadd, hlin, hsum, smul_sub, smul_smul, inv_mul_cancel₀ hN, one_smul]
  have hq : ρ m p = (ρ m p -ᵥ p) +ᵥ p := (vsub_vadd _ _).symm
  calc (N⁻¹ • ∑ n : M, (ρ n p -ᵥ p) - (ρ m p -ᵥ p)) +ᵥ ρ m p
      = (N⁻¹ • ∑ n : M, (ρ n p -ᵥ p) - (ρ m p -ᵥ p)) +ᵥ ((ρ m p -ᵥ p) +ᵥ p) := by
        rw [← hq]
    _ = c +ᵥ p := by rw [vadd_vadd, sub_add_cancel]

end FixedPoint

section SplitUniqueness

variable {k : Type u} [Field k] {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} {i : T.toGrp ⟶ G} [Mono i.hom.hom.left]
  [IsAffineHom G.X.hom]

omit [Mono i.hom.hom.left] [IsAffineHom G.X.hom] in
/-- On a split torus, the negative valuation of the character values at a rational point
is evaluation at a real cocharacter vector. -/
theorem exists_eval_eq_neg_order (hT : IsSplitTorus T.toGrp) (ω : kˣ → ℝ)
    (hadd : ∀ x y : kˣ, ω (x * y) = ω x + ω y) (τ : rationalPoints T.toGrp) :
    ∃ w : V T, ∀ a, eval T a w = -ω (rationalCharacterEval
      ((rationalCharacters.equivCharacterLattice T).symm a) τ) := by
  have hone : ω 1 = 0 := by
    have h := hadd 1 1
    rw [mul_one] at h
    linarith
  exact Langlands.BruhatTits.Cartan.exists_eval_eq hT
    { toFun := fun a => -ω (rationalCharacterEval
        ((rationalCharacters.equivCharacterLattice T).symm a) τ)
      map_zero' := by rw [map_zero, rationalCharacterEval_zero, hone, neg_zero]
      map_add' := by
        intro a c
        rw [map_add, rationalCharacterEval_add, hadd, neg_add] }

/-- A rational torus point acts on a split-torus-compatible valuation by the translation
whose character values are the negative valuations of the character values. -/
theorem IsSplitTorusCompatible.centralizer_smul_eq_vadd {ω : kˣ → ℝ}
    {φ : RootFunctionFamily T G} (hφ : IsRootDatumValuation i φ)
    (hω : IsSplitTorusCompatible i ω φ) (z : centralizerPoints i)
    (τ : rationalPoints T.toGrp) (hτ : rationalPoints.map i τ = z) (w : V T)
    (hw : ∀ a, eval T a w = -ω (rationalCharacterEval
      ((rationalCharacters.equivCharacterLattice T).symm a) τ)) :
    Subgroup.inclusion (centralizerPoints_le_normalizerPoints i) z • φ = w +ᵥ φ := by
  refine RootFunctionFamily.centralizer_smul_eq_vadd φ hφ.eq_top_of_not_mem_roots
    (fun a ha g hg => hφ.eq_top_of_not_mem a ha g hg) z w ?_
  intro a ha g hg
  rw [← hτ, hω a ha τ g hg, hw]

/-- **Uniqueness of split apartment classes.** For a split maximal torus of a connected
reductive group and an additive order function, there is at most one normalizer-stable
apartment class. -/
theorem KPApartmentData.eq_of_isMaximalTorus_of_isSplitTorus (hG : IsConnectedReductive G)
    (hT : IsSplitTorus T.toGrp) (hi : IsMaximalTorus i) {ω : kˣ → ℝ}
    (hadd : ∀ x y : kˣ, ω (x * y) = ω x + ω y) (D E : KPApartmentData i ω) : D = E := by
  have hmax : IsMaximalSplitTorus i := hi.isMaximalSplitTorus hT
  have : Smooth G.X.hom := hG.smooth
  have hpair : RelativeRoot.HasOppositeFactorPairs i :=
    (RelativeRoot.hasRankOneFactorization_iff_hasOppositeFactorPairs i hT).mp
      (rootRankOneFactorization k G hG T i hmax)
  refine KPApartmentData.eq_of_hasCommonCentralizerDisplacements_of_hasOppositeFactorPairs
    (D := D) (E := E) ?_ hG hmax hpair
  intro n hn x y
  have hc := centralizerPoints_le_torusCentralizer i hn
  rw [maximalTorusCentralizer k G hG T i hi] at hc
  obtain ⟨τ, hτ⟩ := SubgroupFunctor.mem_range.1 hc
  obtain ⟨w, hw⟩ := exists_eval_eq_neg_order hT ω hadd τ
  have hnz : n = Subgroup.inclusion (centralizerPoints_le_normalizerPoints i) ⟨_, hn⟩ :=
    Subtype.ext rfl
  have hτ' : rationalPoints.map i τ = (⟨_, hn⟩ : centralizerPoints i) := hτ
  rw [E.vsub_eq_mk (w := w) (by
      rw [KPApartmentData.val_smul, hnz]
      exact IsSplitTorusCompatible.centralizer_smul_eq_vadd y.isValuation y.isSplitTorusCompatible ⟨_, hn⟩
        τ hτ' w hw),
    D.vsub_eq_mk (w := w) (by
      rw [KPApartmentData.val_smul, hnz]
      exact IsSplitTorusCompatible.centralizer_smul_eq_vadd x.isValuation x.isSplitTorusCompatible ⟨_, hn⟩
        τ hτ' w hw)]

end SplitUniqueness

section Galois

namespace KPApartmentData

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G)

local notation "b" => algebraBaseMap k K
local notation "T_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) T
local notation "G_K" => baseChanged k K G
local notation "i_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b) i

private instance extendedAffine : IsAffineHom (G_K).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

variable [Mono (CategoryTheory.Functor.map
    (GroupScheme.baseChange (algebraBaseMap k K)) i).hom.hom.left] {ω : Kˣ → ℝ}

/-- **Galois stability of split apartment classes.** If the base-changed torus is a split
maximal torus of the base-changed connected reductive group and the order function is
additive and invariant under coefficient automorphisms, every apartment class is stable
under the actual coefficient action. -/
theorem galoisStable_of_isSplitTorus (hG : IsConnectedReductive G_K)
    (hT : IsSplitTorus (T_K).toGrp) (hi : IsMaximalTorus (T := T_K) i_K)
    (hadd : ∀ x y : Kˣ, ω (x * y) = ω x + ω y)
    (hω : ∀ (σ : K ≃ₐ[k] K) (t : Kˣ), ω (Units.map σ.toMonoidHom t) = ω t)
    (D : KPApartmentData (S := T_K) i_K ω) : GaloisStable k K i D := by
  intro σ φ hφ
  have h := eq_of_isMaximalTorus_of_isSplitTorus hG hT hi hadd
    (galoisImage k K i D σ (hω σ)) D
  rw [← h]
  exact ⟨φ, hφ, rfl⟩

/-- **Galois-fixed points.** A Galois-stable apartment class over a finite extension has a
point fixed by every coefficient automorphism. -/
theorem exists_galoisFixed [FiniteDimensional k K] (D : KPApartmentData (S := T_K) i_K ω)
    (hD : GaloisStable k K i D) :
    ∃ x : D.Apartment, ∀ σ : K ≃ₐ[k] K,
      RootFunctionFamily.galoisAction k K T G σ x.val = x.val := by
  obtain ⟨x, hx⟩ := exists_fixed_of_finite_affineAction (galoisAffineAction k K i D hD)
  exact ⟨x, (mem_galoisFixedApartment_iff k K i D hD x).1 hx⟩

/-- A chosen point of a Galois-stable apartment class over a finite extension that is fixed by
every coefficient automorphism. -/
def galoisFixedPoint [FiniteDimensional k K] (D : KPApartmentData (S := T_K) i_K ω)
    (hD : GaloisStable k K i D) : D.Apartment :=
  Classical.choose (exists_galoisFixed k K i D hD)

/-- The chosen Galois-fixed point is fixed by every coefficient automorphism. -/
theorem galoisAction_galoisFixedPoint [FiniteDimensional k K]
    (D : KPApartmentData (S := T_K) i_K ω) (hD : GaloisStable k K i D) (σ : K ≃ₐ[k] K) :
    RootFunctionFamily.galoisAction k K T G σ (galoisFixedPoint k K i D hD).val =
      (galoisFixedPoint k K i D hD).val :=
  Classical.choose_spec (exists_galoisFixed k K i D hD) σ

end KPApartmentData

end Galois

end Langlands.Geometry.Building
