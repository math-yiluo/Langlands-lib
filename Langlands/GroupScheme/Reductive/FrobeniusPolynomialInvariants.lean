import Langlands.Algebra.PolynomialFrobeniusDescent
import Langlands.GroupScheme.Reductive.FrobeniusPointCongruence

/-! # Frobenius descent of actual origin-invariant polynomial coordinates -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxRecDepth 2048

namespace Langlands.GroupScheme.FrobeniusPolynomialInvariants

open AffineCoordinates FrobeniusCovariantInvariants
open Langlands.Algebra.PolynomialFrobeniusDescent

variable {k : Type u} [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    (p : ℕ) [ExpChar k p] (r : ℕ)

local instance {K : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom K.X.hom] :
    IsAffine K.X.left := isAffine_of_isAffineHom K.X.hom

/-- Actual origin invariance implies the universal polynomial congruence
condition, using affine spectra of arbitrary coefficient algebras as tests. -/
theorem universalPowerInvariant_of_originInvariant {σ : Type}
    (e : algebra G ≃ₐ[k] MvPolynomial σ k) {b : algebra G}
    (hb : ∀ (V : Over (Spec (CommRingCat.of k))) (g h : V ⟶ G.X),
      IsOriginTestPoint G p r V h →
        pointAlgebraHom G V (g * h) b = pointAlgebraHom G V g b) :
    UniversalPowerInvariant (p ^ r) (e b) := by
  intro A _ _ f g hfg
  let B : CommAlgCat (CommRingCat.of k) := CommAlgCat.of _ A
  let ε := ((algΓAlgSpecAdjunction (CommRingCat.of k)).counit.app (op B)).unop.hom
  let φ : algebra G ⟶ B := CommAlgCat.ofHom (f.comp e.toAlgHom)
  let ψ : algebra G ⟶ B := CommAlgCat.ofHom (g.comp e.toAlgHom)
  have hcon : FrobeniusPointCongruence.Congruent G p r _
      (algPoint G φ) (algPoint G ψ) := by
    intro a
    rw [pointAlgebraHom_algPoint, pointAlgebraHom_algPoint]
    change ε (f (e a)) ^ p ^ r = ε (g (e a)) ^ p ^ r
    exact (map_pow ε _ _).symm.trans
      ((congrArg ε (hfg (e a))).trans (map_pow ε _ _))
  have he := FrobeniusPointCongruence.pointAlgebraHom_eq_of_congruent G hb hcon
  rw [pointAlgebraHom_algPoint, pointAlgebraHom_algPoint] at he
  exact counit_unop_injective B he

/-- An actual origin-invariant function in polynomial coordinates is a
polynomial in characteristic-power variables, with unchanged coefficients. -/
theorem exists_expand_of_originInvariant {σ : Type}
    (e : algebra G ≃ₐ[k] MvPolynomial σ k) {b : algebra G}
    (hb : ∀ (V : Over (Spec (CommRingCat.of k))) (g h : V ⟶ G.X),
      IsOriginTestPoint G p r V h →
        pointAlgebraHom G V (g * h) b = pointAlgebraHom G V g b) :
    ∃ H : MvPolynomial σ k, e b = MvPolynomial.expand (p ^ r) H :=
  exists_expand_of_universalPowerInvariant p r
    (universalPowerInvariant_of_originInvariant G p r e hb)

variable {G}
    {H : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom H.X.hom]

/-- Restriction along an actual subgroup homomorphism preserves origin
invariance and hence gives polynomial Frobenius descent on that subgroup. -/
theorem exists_expand_of_subgroup_originInvariant {σ : Type}
    (j : H ⟶ G) (e : algebra H ≃ₐ[k] MvPolynomial σ k) {b : algebra G}
    (hb : ∀ (V : Over (Spec (CommRingCat.of k))) (g : V ⟶ G.X) (h : V ⟶ H.X),
      IsOriginTestPoint H p r V h →
        pointAlgebraHom G V (g * (h ≫ j.hom.hom)) b = pointAlgebraHom G V g b) :
    ∃ F : MvPolynomial σ k,
      e ((AffineHomImageHopfAdapter.pullback j).hom b) = MvPolynomial.expand (p ^ r) F := by
  apply exists_expand_of_originInvariant H p r e
  intro V g h hh
  have he := hb V (g ≫ j.hom.hom) h hh
  rw [← MonObj.mul_comp, AffineHomImageHopfAdapter.pointAlgebraHom_pullback,
    AffineHomImageHopfAdapter.pointAlgebraHom_pullback] at he
  exact he

end Langlands.GroupScheme.FrobeniusPolynomialInvariants

namespace Langlands.GroupScheme.Dynamic

open AffineCoordinates FrobeniusCovariantInvariants FrobeniusPolynomialInvariants

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
    [Smooth G.X.hom] (hT : IsSplitTorus T.toGrp)

local instance {K : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom K.X.hom] :
    IsAffine K.X.left := isAffine_of_isAffineHom K.X.hom

local notation "U" => Standard.unipotentScheme i (-ν) ∅
local notation "iU" => Standard.unipotentHom i (-ν) ∅
local notation "P" => Affine.parabolicScheme (CommGroupScheme.groupHom ν ≫ i)
local notation "iP" => Affine.parabolicHom (CommGroupScheme.groupHom ν ≫ i)

local instance : IsAffineHom (Affine.parabolicScheme
    (CommGroupScheme.groupHom ν ≫ i)).X.hom :=
  (Affine.isClosedSubgroup_parabolicHom (CommGroupScheme.groupHom ν ≫ i)).isAffineHom

variable (coords : Standard.UnipotentPolynomialCoordinates i (-ν) hT)
    (χ : algebra (Affine.parabolicScheme (CommGroupScheme.groupHom ν ≫ i)))

/-- Restriction of the entire covariant space to the actual opposite
unipotent group, expressed in its constructed polynomial coordinates. -/
def oppositeUnipotentPolynomialRestriction :
    leftCovariantSubspace (G := G) (H := P) iP χ →ₗ[k]
      MvPolynomial (Fin coords.dimension) k :=
  coords.polynomialEquiv.toLinearEquiv.toLinearMap.comp (oppositeUnipotentRestriction i ν χ)

/-- Polynomial coordinates preserve the injectivity of full opposite-cell
restriction on the entire covariant space. -/
theorem oppositeUnipotentPolynomialRestriction_injective
    (hG : IsConnectedReductive G) :
    Function.Injective (oppositeUnipotentPolynomialRestriction i ν hT coords χ) :=
  coords.polynomialEquiv.injective.comp
    (oppositeUnipotentRestriction_injective i ν hG hT χ)

variable (p : ℕ) [ExpChar k p] (r : ℕ)

/-- Intrinsic origin invariance of the original coordinate gives the
characteristic-power expansion of its actual opposite-cell restriction. -/
theorem oppositeUnipotentPolynomialRestriction_exists_expand
    {f : leftCovariantSubspace (k := k) (G := G) (H := P) iP χ}
    (hf : ∀ (V : Over (Spec (CommRingCat.of k))) (g : V ⟶ G.X) (h : V ⟶ (U).X),
      IsOriginTestPoint U p r V h →
        pointAlgebraHom G V (g * (h ≫ (iU).hom.hom)) (f : algebra G) =
          pointAlgebraHom G V g (f : algebra G)) :
    ∃ F : MvPolynomial (Fin coords.dimension) k,
      oppositeUnipotentPolynomialRestriction i ν hT coords χ f =
        MvPolynomial.expand (p ^ r) F := by
  exact exists_expand_of_subgroup_originInvariant p r iU
    ((lieCoordinateAlgEquiv U).trans coords.polynomialEquiv) hf

/-- Failure of fixed-height injectivity produces a nonzero original kernel
vector whose opposite-cell polynomial is the expansion of a nonzero polynomial
with zero constant coefficient. No exclusion of that vector is assumed. -/
theorem exists_nonzero_expand_of_not_injective
    (hG : IsConnectedReductive G)
    (hnot : ¬ Function.Injective
      (oppositeUnipotentFrobeniusRestriction i ν χ p r)) :
    ∃ (f : leftCovariantSubspace (k := k) (G := G) (H := P) iP χ)
      (F : MvPolynomial (Fin coords.dimension) k),
      f ≠ 0 ∧ oppositeUnipotentFrobeniusRestriction i ν χ p r f = 0 ∧
      oppositeUnipotentPolynomialRestriction i ν hT coords χ f =
        MvPolynomial.expand (p ^ r) F ∧ F ≠ 0 ∧ F.coeff 0 = 0 := by
  obtain ⟨f, hf, hz, hinv⟩ :=
    exists_originInvariant_of_not_injective i ν χ p r hT hnot
  obtain ⟨F, hF⟩ :=
    oppositeUnipotentPolynomialRestriction_exists_expand i ν hT coords χ p r hinv
  refine ⟨f, F, hf, hz, hF, ?_, ?_⟩
  · intro hFzero
    apply hf
    apply oppositeUnipotentPolynomialRestriction_injective i ν hT coords χ hG
    rw [hF, hFzero, map_zero, map_zero]
  · have hcoeff :
        (oppositeUnipotentPolynomialRestriction i ν hT coords χ f).coeff 0 = 0 :=
      (coords.quotientMap_eq_zero_iff p r
        (oppositeUnipotentRestriction i ν χ f)).mp hz 0 zero_le
    rw [hF, MvPolynomial.coeff_expand_zero _ (pow_ne_zero _ (expChar_ne_zero k p))]
      at hcoeff
    exact hcoeff

end Langlands.GroupScheme.Dynamic
