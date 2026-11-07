import Langlands.GroupScheme.Rational.RootActionWeights
import Langlands.GroupScheme.Rational.RepresentationNormalizerWeights
import Langlands.GroupScheme.Rational.SteinbergPolynomialAction
import Langlands.GroupScheme.Rational.SteinbergCanonicalRepresentatives
import Langlands.GroupScheme.Rational.SteinbergCoxeterTorus
import Langlands.GroupScheme.Rational.RootSubgroupConjugation

/-! # Nonvanishing in a simple-root string of length one -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix Polynomial

namespace Langlands.GroupScheme
namespace SplitPinning

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (p : SplitPinning G)

/-- A negative nonzero multiple of a simple root is outside the positive cone. -/
theorem neg_nsmul_simpleRoot_not_mem_positiveRootMonoid
    (a : p.base.support) {m : ℕ} (hm : 0 < m) :
    -(m • p.rootDatum.root a) ∉ p.positiveRootMonoid := by
  classical
  intro h
  change -(m • p.rootDatum.root a) ∈
    AddSubmonoid.closure (Set.range fun b : p.base.support => p.rootDatum.root b) at h
  rw [← Submodule.span_nat_eq_addSubmonoidClosure, Submodule.mem_toAddSubmonoid,
    Submodule.mem_span_range_iff_exists_fun] at h
  obtain ⟨c, hc⟩ := h
  have he : (∑ b : p.base.support, (c b : ℤ) • p.rootDatum.root b) =
      ∑ b : p.base.support, (if b = a then -(m : ℤ) else 0) • p.rootDatum.root b := by
    simpa only [natCast_zsmul, ite_smul, zero_smul,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true, neg_smul] using hc
  have ha := Fintype.linearIndependent_iffₛ.mp p.base.linearIndepOn_root
    (fun b => (c b : ℤ)) (fun b => if b = a then -(m : ℤ) else 0) he a
  change (c a : ℤ) = (if a = a then -(m : ℤ) else 0) at ha
  simp only [ite_true] at ha
  have hca : (0 : ℤ) ≤ c a := Int.natCast_nonneg _
  omega

variable {n : Type} [Fintype n] [DecidableEq n]
    (ρ : MatrixRepresentation G n)

/-- No weight strictly above a highest weight along a simple root occurs. -/
theorem IsHighestWeight.weightSpace_add_nsmul_simpleRoot_eq_bot
    {lam : characterLattice p.torus} (h : p.IsHighestWeight ρ lam)
    (a : p.base.support) {m : ℕ} (hm : 0 < m) :
    p.representationWeightSpace ρ (lam + m • p.rootDatum.root a) = ⊥ := by
  by_contra hbot
  have hcone := h.2.2.2 _ hbot
  have hneg : lam - (lam + m • p.rootDatum.root a) = -(m • p.rootDatum.root a) := by
    abel
  rw [hneg] at hcone
  exact p.neg_nsmul_simpleRoot_not_mem_positiveRootMonoid a hm hcone

end SplitPinning

namespace MatrixRepresentation.AdditiveDividedPowers

variable {k : Type u} [Field k] {n : Type} [Fintype n] [DecidableEq n]
    (ρ : MatrixRepresentation (VectorGroup.groupScheme (CommRingCat.of k) 1) n)

/-- A vector annihilated by the positive-degree coefficients is fixed on every affine test. -/
theorem affineMatrix_mulVec_eq_self_of_dividedPower_eq_zero
    {v : n → k} (hv : ∀ m : ℕ, 0 < m → dividedPower ρ m v = 0)
    (A : CommAlgCat.{u} k) (c : A) :
    (ρ.affineMatrix A
        (VectorGroup.affinePoint (R := CommRingCat.of k) (d := 1) A (fun _ => c)) :
      Matrix n n A) *ᵥ (fun i => algebraMap k A (v i)) =
        (fun i => algebraMap k A (v i)) := by
  classical
  rw [affineMatrix_mulVec_eq_sum]
  rw [Finset.sum_eq_single 0]
  · simp only [pow_zero, dividedPower_zero, Module.End.one_apply, one_smul]
  · intro m hm hm0
    rw [hv m (Nat.pos_of_ne_zero hm0)]
    simp only [Pi.zero_apply, map_zero]
    exact smul_zero _
  · intro h0
    exact (h0 (Finset.mem_range.mpr (Nat.succ_pos _))).elim

end MatrixRepresentation.AdditiveDividedPowers

namespace SplitPinning.NormalizedRootParametrization

open MatrixRepresentation.AdditiveDividedPowers

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {p : SplitPinning G} {a : p.base.support}
    (x : p.NormalizedRootParametrization a)
    {n : Type} [Fintype n] [DecidableEq n] (ρ : MatrixRepresentation G n)

/-- Every positive-degree simple-root coefficient kills a highest-weight vector. -/
theorem dividedPower_eq_zero_of_highestWeight
    {lam : characterLattice p.torus} (h : p.IsHighestWeight ρ lam)
    {v : n → k} (hv : v ∈ p.representationWeightSpace ρ lam)
    {m : ℕ} (hm : 0 < m) :
    dividedPower (ρ.restrict x.hom) m v = 0 :=
  x.dividedPower_eq_zero_of_weightSpace_eq_bot ρ m hv
    (SplitPinning.IsHighestWeight.weightSpace_add_nsmul_simpleRoot_eq_bot p ρ h a hm)

/-- The affine root coordinate of a rational root point is its usual scalar extension. -/
theorem affinePoint_eq_constantPoint_rationalPoint
    (A : CommAlgCat.{u} k) (c : k) :
    VectorGroup.affinePoint (R := CommRingCat.of k) (d := 1) A
        (fun _ => algebraMap k A c) ≫ x.hom.hom.hom =
      G.constantPoint (x.toRootParametrization.rationalPoint c)
        ((algSpec (CommRingCat.of k)).obj (op A)) := by
  let T := (algSpec (CommRingCat.of k)).obj (op A)
  have hc : T.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c) =
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv (algebraMap k A c) := by
    exact (ConcreteCategory.congr_hom
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap k A))) c).symm
  rw [VectorGroup.affinePoint_eq_scalarPoint]
  change x.toRootParametrization.point T _ = _
  rw [← hc, ← x.toRootParametrization.toUnit_comp_rationalPoint]
  rfl

/-- Vanishing of all positive coefficients makes the full rational root subgroup fix a vector. -/
theorem rationalMatrix_mulVec_eq_self_of_dividedPower_eq_zero
    {v : n → k}
    (hv : ∀ m : ℕ, 0 < m → dividedPower (ρ.restrict x.hom) m v = 0)
    {g : rationalPoints G}
    (hg : g ∈ (RelativeRoot.subgroup p.inclusion (p.rootDatum.root a)).carrier
      (Over.mk (𝟙 _))) :
    (ρ.rationalMatrix g : Matrix n n k) *ᵥ v = v := by
  obtain ⟨c, hc⟩ := x.toRootParametrization.mem_rootSubgroup_iff _ g |>.mp hg
  have hg' : g = x.toRootParametrization.rationalPoint
      ((Scheme.ΓSpecIso (CommRingCat.of k)).hom c) := by
    rw [RootParametrization.rationalPoint]
    simpa using hc.symm
  rw [hg']
  have hfix := affineMatrix_mulVec_eq_self_of_dividedPower_eq_zero
    (ρ.restrict x.hom) hv (CommAlgCat.of k k)
      ((Scheme.ΓSpecIso (CommRingCat.of k)).hom c)
  change (ρ.affineMatrix (CommAlgCat.of k k)
    (VectorGroup.affinePoint (R := CommRingCat.of k) (d := 1) (CommAlgCat.of k k)
      (fun _ => (Scheme.ΓSpecIso (CommRingCat.of k)).hom c) ≫ x.hom.hom.hom) :
      Matrix n n k) *ᵥ (fun i => algebraMap k k (v i)) = _ at hfix
  rw [show (fun _ : Fin 1 => (Scheme.ΓSpecIso (CommRingCat.of k)).hom c) =
      (fun _ : Fin 1 => algebraMap k k ((Scheme.ΓSpecIso (CommRingCat.of k)).hom c)) from rfl,
    x.affinePoint_eq_constantPoint_rationalPoint, ρ.affineMatrix_constantPoint] at hfix
  simpa using hfix

/-- On the reflected highest-weight line, every coefficient of degree at least two vanishes. -/
theorem dividedPower_reflected_eq_zero_of_one_lt
    {lam : characterLattice p.torus} (h : p.IsHighestWeight ρ lam)
    (hpair : p.rootDatum.toLinearMap lam (p.rootDatum.coroot a) = 1)
    (s : p.SimpleReflectionRepresentative a)
    {v : n → k} (hv : v ∈ p.representationWeightSpace ρ lam)
    {m : ℕ} (hm : 1 < m) :
    dividedPower (ρ.restrict x.hom) m
      ((ρ.rationalMatrix s.point : Matrix n n k) *ᵥ v) = 0 := by
  have hw := s.rationalMatrix_mem_representationWeightSpace ρ lam hv
  apply x.dividedPower_eq_zero_of_weightSpace_eq_bot ρ m hw
  have hr : p.rootDatum.reflection a lam = lam - p.rootDatum.root a := by
    rw [RootPairing.reflection_apply]
    change lam - p.rootDatum.toLinearMap lam (p.rootDatum.coroot a) •
      p.rootDatum.root a = _
    rw [hpair, one_smul]
  have hs : m • p.rootDatum.root a =
      (m - 1) • p.rootDatum.root a + p.rootDatum.root a := by
    conv_lhs => rw [show m = (m - 1) + 1 by omega, add_nsmul, one_nsmul]
  have he : p.rootDatum.reflection a lam + m • p.rootDatum.root a =
      lam + (m - 1) • p.rootDatum.root a := by
    rw [hr, hs]
    abel
  rw [he]
  exact SplitPinning.IsHighestWeight.weightSpace_add_nsmul_simpleRoot_eq_bot p ρ h a
    (by omega)

local instance : Mono p.inclusion.hom.hom.left := p.isMaximalTorus.2.1.mono

/-- If the positive root fixes a reflected vector, the negative root fixes the original. -/
theorem rationalMatrix_negRoot_mulVec_eq_self_of_root_fixed_reflection
    (s : p.SimpleReflectionRepresentative a) {v : n → k}
    (hw : ∀ g : rationalPoints G,
      g ∈ (RelativeRoot.subgroup p.inclusion (p.rootDatum.root a)).carrier (Over.mk (𝟙 _)) →
      (ρ.rationalMatrix g : Matrix n n k) *ᵥ
        ((ρ.rationalMatrix s.point : Matrix n n k) *ᵥ v) =
          (ρ.rationalMatrix s.point : Matrix n n k) *ᵥ v)
    {g : rationalPoints G}
    (hg : g ∈ (RelativeRoot.subgroup p.inclusion (-(p.rootDatum.root a))).carrier
      (Over.mk (𝟙 _))) :
    (ρ.rationalMatrix g : Matrix n n k) *ᵥ v = v := by
  have hc := RelativeRoot.normalizer_conj_mem p.inclusion (-(p.rootDatum.root a))
    s.normalizerPoint hg
  simp only [GroupScheme.constantPoint_self,
    SimpleReflectionRepresentative.weylAction_normalizerPoint, map_neg,
    RootPairing.reflection_apply_self, neg_neg] at hc
  have hfix := hw (s.point * g * s.point⁻¹) hc
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul,
    show s.point * g * s.point⁻¹ * s.point = s.point * g by group,
    map_mul, Units.val_mul, ← Matrix.mulVec_mulVec] at hfix
  exact Matrix.mulVec_injective_of_isUnit (Units.isUnit (ρ.rationalMatrix s.point)) hfix

/-- The degree-one root coefficient is nonzero on a reflected highest vector of pairing one. -/
theorem coefficientMatrix_one_reflected_ne_zero
    {lam : characterLattice p.torus} (h : p.IsHighestWeight ρ lam)
    (hpair : p.rootDatum.toLinearMap lam (p.rootDatum.coroot a) = 1)
    (s : p.SimpleReflectionRepresentative a)
    {v : n → k} (hv : v ∈ p.representationWeightSpace ρ lam) (hv0 : v ≠ 0) :
    coefficientMatrix (ρ.restrict x.hom) 1 *ᵥ
      ((ρ.rationalMatrix s.point : Matrix n n k) *ᵥ v) ≠ 0 := by
  classical
  intro hzero
  have hvfix : ∀ g : rationalPoints G,
      g ∈ (RelativeRoot.subgroup p.inclusion (p.rootDatum.root a)).carrier (Over.mk (𝟙 _)) →
      (ρ.rationalMatrix g : Matrix n n k) *ᵥ v = v := by
    intro g hg
    exact x.rationalMatrix_mulVec_eq_self_of_dividedPower_eq_zero ρ
      (fun m hm => x.dividedPower_eq_zero_of_highestWeight ρ h hv hm) hg
  have hwzero : ∀ m : ℕ, 0 < m → dividedPower (ρ.restrict x.hom) m
      ((ρ.rationalMatrix s.point : Matrix n n k) *ᵥ v) = 0 := by
    intro m hm
    by_cases hm1 : m = 1
    · subst m
      rw [dividedPower_eq_toLin]
      exact hzero
    · exact x.dividedPower_reflected_eq_zero_of_one_lt ρ h hpair s hv (by omega)
  have hwfix : ∀ g : rationalPoints G,
      g ∈ (RelativeRoot.subgroup p.inclusion (p.rootDatum.root a)).carrier (Over.mk (𝟙 _)) →
      (ρ.rationalMatrix g : Matrix n n k) *ᵥ
        ((ρ.rationalMatrix s.point : Matrix n n k) *ᵥ v) =
          (ρ.rationalMatrix s.point : Matrix n n k) *ᵥ v := by
    intro g hg
    exact x.rationalMatrix_mulVec_eq_self_of_dividedPower_eq_zero ρ hwzero hg
  have hneg : ∀ g : rationalPoints G,
      g ∈ (RelativeRoot.subgroup p.inclusion (-(p.rootDatum.root a))).carrier
        (Over.mk (𝟙 _)) →
      (ρ.rationalMatrix g : Matrix n n k) *ᵥ v = v := by
    intro g hg
    exact rationalMatrix_negRoot_mulVec_eq_self_of_root_fixed_reflection ρ s hwfix hg
  have hcan : (ρ.rationalMatrix x.reflectionRepresentative.point : Matrix n n k) *ᵥ v = v := by
    rw [x.reflectionRepresentative_point]
    simp only [map_mul, Units.val_mul, ← Matrix.mulVec_mulVec,
      hneg _ x.oppositeFactorPair_spec.2.1, hvfix _ x.unitPoint_mem,
      hneg _ x.oppositeFactorPair_spec.1]
  have hv' := x.reflectionRepresentative.rationalMatrix_mem_representationWeightSpace ρ lam hv
  rw [hcan] at hv'
  have hne : p.rootDatum.reflection a lam ≠ lam := by
    intro heq
    rw [RootPairing.reflection_apply] at heq
    change lam - p.rootDatum.toLinearMap lam (p.rootDatum.coroot a) •
      p.rootDatum.root a = lam at heq
    rw [hpair, one_smul, sub_eq_self] at heq
    exact p.rootDatum.ne_zero a heq
  let := p.isSplitTorus.isAffineHom
  let χ := (rationalCharacters.equivCharacterLattice p.torus).symm lam
  let ψ := (rationalCharacters.equivCharacterLattice p.torus).symm (p.rootDatum.reflection a lam)
  have hψχ : ψ ≠ χ := fun he =>
    hne ((rationalCharacters.equivCharacterLattice p.torus).symm.injective he)
  have hproj := (ρ.restrict p.inclusion).characterProjector_of_mem χ χ hv
  have hproj' := (ρ.restrict p.inclusion).characterProjector_of_mem χ ψ hv'
  rw [ite_eq_left rfl] at hproj
  rw [ite_eq_right hψχ] at hproj'
  exact hv0 (hproj.symm.trans hproj')

end SplitPinning.NormalizedRootParametrization

/-- Pairing-one simple-root coefficient nonvanishing over an arbitrary field. -/
def SplitSimpleRootHighestCoefficientArbitraryFieldStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    (p : SplitPinning G) (d : ℕ) (ρ : MatrixRepresentation G (Fin d))
    (lam : characterLattice p.torus), p.IsHighestWeight ρ lam →
    ∀ (a : p.base.support),
      p.rootDatum.toLinearMap lam (p.rootDatum.coroot a) = 1 →
    ∀ (x : p.NormalizedRootParametrization a) (s : p.SimpleReflectionRepresentative a)
      (v : Fin d → k), v ∈ p.representationWeightSpace ρ lam → v ≠ 0 →
        MatrixRepresentation.AdditiveDividedPowers.coefficientMatrix (ρ.restrict x.hom) 1 *ᵥ
          ((ρ.rationalMatrix s.point : Matrix (Fin d) (Fin d) k) *ᵥ v) ≠ 0

theorem splitSimpleRootHighestCoefficientArbitraryField :
    SplitSimpleRootHighestCoefficientArbitraryFieldStatement.{u} := by
  intro k _ G _ p d ρ lam h a hpair x s v hv hv0
  exact x.coefficientMatrix_one_reflected_ne_zero ρ h hpair s hv hv0

end Langlands.GroupScheme
