import Langlands.GroupScheme.IdentityJetRestriction
import Langlands.RingTheory.Smooth.SectionJetTotalDeterminant
import Langlands.LinearAlgebra.SplitBasisSemilinear

/-! # Actual jet basis matrices under affine restriction -/

noncomputable section

universe u w

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry Opposite

namespace Langlands.GroupScheme.IdentityJet

open Algebra.SectionJet.Coordinates
open Langlands.LinearAlgebra
open CoordinateWeights

variable {S : Scheme.{u}} (G : GroupScheme S) [IsAffineHom G.X.hom]

attribute [local instance] sectionAlgebra

omit [IsAffineHom G.X.hom] in
/-- Actual function restriction commutes with restriction of base scalars. -/
theorem functionRestriction_algebraMap {U V : S.affineOpens} (h : V.1 ≤ U.1)
    (r : Γ(S, U)) :
    IdentityCotangent.functionRestriction G h
        (algebraMap Γ(S, U) Γ(G.X.left, G.X.hom ⁻¹ᵁ U) r) =
      algebraMap Γ(S, V) Γ(G.X.left, G.X.hom ⁻¹ᵁ V)
        ((S.presheaf.map (homOfLE h).op).hom r) :=
  (ConcreteCategory.congr_hom (G.X.hom.naturality (homOfLE h).op) r).symm

omit [IsAffineHom G.X.hom] in
/-- Actual function restriction commutes with polynomial evaluation, after
restriction of every coefficient. -/
theorem functionRestriction_aeval {σ : Type w} {U V : S.affineOpens}
    (h : V.1 ≤ U.1) (z : σ → Γ(G.X.left, G.X.hom ⁻¹ᵁ U))
    (p : MvPolynomial σ Γ(S, U)) :
    IdentityCotangent.functionRestriction G h (MvPolynomial.aeval z p) =
      MvPolynomial.aeval (fun i => IdentityCotangent.functionRestriction G h (z i))
        (MvPolynomial.map (S.presheaf.map (homOfLE h).op).hom p) := by
  rw [MvPolynomial.map_aeval, MvPolynomial.aeval_def, MvPolynomial.eval₂_map]
  have heq :
      (IdentityCotangent.functionRestriction G h).comp
          (algebraMap Γ(S, U) Γ(G.X.left, G.X.hom ⁻¹ᵁ U)) =
        (algebraMap Γ(S, V) Γ(G.X.left, G.X.hom ⁻¹ᵁ V)).comp
          (S.presheaf.map (homOfLE h).op).hom :=
    RingHom.ext (functionRestriction_algebraMap G h)
  exact congrArg
    (fun f => MvPolynomial.eval₂ f
      (fun i => IdentityCotangent.functionRestriction G h (z i)) p) heq

/-- The higher actual layer sends each source monomial basis vector to the
evaluation of the same monomial in the restricted actual lifts. -/
theorem layerRestriction_layerBasis {σ : Type w} [Fintype σ] [DecidableEq σ]
    [Smooth G.X.hom] {U V : S.affineOpens} (h : V.1 ≤ U.1)
    (z : σ → Γ(G.X.left, G.X.hom ⁻¹ᵁ U))
    (b : Module.Basis σ Γ(S, U) (RingHom.ker (augmentation G U)).Cotangent)
    (hz : ∀ i, augmentation G U (z i) = 0)
    (hzb : ∀ i, AugmentedAlgebra.classMap (augmentation G U) (z i) = b i)
    (n : ℕ) (e : HomogeneousPolynomial.MonomialIndex σ (n + 1)) :
    layerRestriction G n h (layerBasis z b hz hzb n e) =
      homogeneousToLayer (fun i => IdentityCotangent.functionRestriction G h (z i))
        (fun i => augmentation_functionRestriction_eq_zero G h (hz i)) n
        (HomogeneousPolynomial.monomialBasis σ (n + 1) Γ(S, V) e) := by
  apply Subtype.ext
  change (layerRestriction G n h
    (homogeneousToLayer z hz n (HomogeneousPolynomial.monomialBasis σ (n + 1) Γ(S, U) e))).val = _
  rw [layerRestriction_homogeneousToLayer_val, homogeneousToLayer_val,
    functionRestriction_aeval]
  congr 2
  simp only [HomogeneousPolynomial.monomialBasis_val, MvPolynomial.map_monomial, map_one]

variable [Smooth G.X.hom] {σ : Type w} [Fintype σ] [DecidableEq σ]
    {U V : S.affineOpens} (h : V.1 ≤ U.1)
    (bU : Module.Basis σ Γ(S, U) (RingHom.ker (augmentation G U)).Cotangent)
    (bV : Module.Basis σ Γ(S, V) (RingHom.ker (augmentation G V)).Cotangent)

/-- The actual cotangent restriction matrix in two specified affine bases. -/
def cotangentRestrictionMatrix : Matrix σ σ Γ(S, V) :=
  bV.toMatrix (fun j => IdentityCotangent.restriction G ‹Smooth G.X.hom› h (bU j))

omit [DecidableEq σ] in
private theorem linearForm_restriction_eq_column (j : σ) :
    linearForm (bV.repr (IdentityCotangent.restriction G ‹Smooth G.X.hom› h (bU j))) =
      HomogeneousPolynomial.column (cotangentRestrictionMatrix G h bU bV) j := by
  rw [linearForm, Finsupp.linearCombination_apply]
  rw [Finsupp.sum_fintype
    (bV.repr (IdentityCotangent.restriction G ‹Smooth G.X.hom› h (bU j)))
    (fun i (r : Γ(S, V)) => r • (MvPolynomial.X i : MvPolynomial σ Γ(S, V)))
    (fun i => zero_smul Γ(S, V) _)]
  simp only [HomogeneousPolynomial.column, cotangentRestrictionMatrix,
    Module.Basis.toMatrix_apply, MvPolynomial.smul_eq_C_mul]

variable
    (zU : σ → Γ(G.X.left, G.X.hom ⁻¹ᵁ U))
    (hzU : ∀ i, augmentation G U (zU i) = 0)
    (hzbU : ∀ i, AugmentedAlgebra.classMap (augmentation G U) (zU i) = bU i)
    (zV : σ → Γ(G.X.left, G.X.hom ⁻¹ᵁ V))
    (hzV : ∀ i, augmentation G V (zV i) = 0)
    (hzbV : ∀ i, AugmentedAlgebra.classMap (augmentation G V) (zV i) = bV i)

/-- Actual restricted layer vectors are given by the homogeneous polynomial
representation of the actual cotangent restriction matrix. -/
theorem layerRestriction_layerBasis_action (n : ℕ)
    (e : HomogeneousPolynomial.MonomialIndex σ (n + 1)) :
    layerRestriction G n h (layerBasis zU bU hzU hzbU n e) =
      homogeneousEquivLayer zV bV hzV hzbV n
        (HomogeneousPolynomial.action (cotangentRestrictionMatrix G h bU bV) (n + 1)
          (HomogeneousPolynomial.monomialBasis σ (n + 1) Γ(S, V) e)) := by
  rw [layerRestriction_layerBasis]
  symm
  change homogeneousToLayer zV hzV n
      (homogeneousSubstitution
        (fun j => ⟨HomogeneousPolynomial.column (cotangentRestrictionMatrix G h bU bV) j,
          HomogeneousPolynomial.column_isHomogeneous _ j⟩) (n + 1)
        (HomogeneousPolynomial.monomialBasis σ (n + 1) Γ(S, V) e)) = _
  apply homogeneousToLayer_substitution
  intro j
  change AugmentedAlgebra.classMap (augmentation G V)
      (MvPolynomial.aeval zV
        (HomogeneousPolynomial.column (cotangentRestrictionMatrix G h bU bV) j)) = _
  rw [← linearForm_restriction_eq_column G h bU bV j, aeval_linearForm,
    Finsupp.apply_linearCombination]
  have hv : (AugmentedAlgebra.classMap (augmentation G V) ∘ zV) = bV := funext hzbV
  rw [hv]
  exact (bV.linearCombination_repr _).trans
    ((congrArg (IdentityCotangent.restriction G ‹Smooth G.X.hom› h) (hzbU j)).symm.trans
      (IdentityCotangent.restriction_classMap G ‹Smooth G.X.hom› h (zU j)))

/-- The actual semilinear layer matrix is the homogeneous polynomial matrix of
the actual cotangent restriction. -/
theorem layerBasis_restrictionMatrix (n : ℕ) :
    (layerBasis zV bV hzV hzbV n).toMatrix
        (fun e => layerRestriction G n h (layerBasis zU bU hzU hzbU n e)) =
      HomogeneousPolynomial.representation (cotangentRestrictionMatrix G h bU bV) (n + 1) := by
  ext e f
  rw [Module.Basis.toMatrix_apply,
    layerRestriction_layerBasis_action G h bU bV zU hzU hzbU zV hzV hzbV]
  change (HomogeneousPolynomial.monomialBasis σ (n + 1) Γ(S, V)).repr
      ((homogeneousEquivLayer zV bV hzV hzbV n).symm
        (homogeneousEquivLayer zV bV hzV hzbV n
          (HomogeneousPolynomial.action (cotangentRestrictionMatrix G h bU bV) (n + 1)
            (HomogeneousPolynomial.monomialBasis σ (n + 1) Γ(S, V) f)))) e = _
  rw [LinearEquiv.symm_apply_apply, HomogeneousPolynomial.representation,
    LinearMap.toMatrix_apply]

/-- The actual layer restriction determinant is a positive-degree symmetric
power of the actual cotangent restriction determinant. -/
theorem layerBasis_restrictionMatrix_det (n : ℕ) :
    ((layerBasis zV bV hzV hzbV n).toMatrix
        (fun e => layerRestriction G n h (layerBasis zU bU hzU hzbU n e))).det =
      (cotangentRestrictionMatrix G h bU bV).det ^
        HomogeneousPolynomial.exponent σ (n + 1) := by
  rw [layerBasis_restrictionMatrix G h bU bV zU hzU hzbU zV hzV hzbV,
    HomogeneousPolynomial.det_representation]

variable
    (sU : ∀ n, Algebra.SectionJet.Quotient (augmentation G U) n →ₗ[Γ(S, U)]
      Algebra.SectionJet.Quotient (augmentation G U) (n + 1))
    (hsU : ∀ n x, Algebra.SectionJet.truncate (augmentation G U) n (sU n x) = x)
    (sV : ∀ n, Algebra.SectionJet.Quotient (augmentation G V) n →ₗ[Γ(S, V)]
      Algebra.SectionJet.Quotient (augmentation G V) (n + 1))
    (hsV : ∀ n x, Algebra.SectionJet.truncate (augmentation G V) n (sV n x) = x)

/-- The actual affine restriction matrix for total adapted jet bases has the
cotangent determinant power, with unrelated source and target splittings. -/
theorem totalBasis_restrictionMatrix_det (n : ℕ) :
    ((totalBasis zV bV hzV hzbV sV hsV n).toMatrix
        (fun j => restriction G n h (totalBasis zU bU hzU hzbU sU hsU n j))).det =
      (cotangentRestrictionMatrix G h bU bV).det ^ jetExponent σ n := by
  classical
  induction n with
  | zero =>
    have hone : restriction G 0 h (1 : Algebra.SectionJet.Quotient (augmentation G U) 0) = 1 := by
      simpa only [map_one] using restriction_mk G 0 h
        (1 : Γ(G.X.left, G.X.hom ⁻¹ᵁ U))
    have hvec : (fun j => restriction G 0 h (totalBasis zU bU hzU hzbU sU hsU 0 j)) =
        (totalBasis zV bV hzV hzbV sV hsV 0 : JetIndex σ 0 →
          Algebra.SectionJet.Quotient (augmentation G V) 0) := by
      funext j
      have hUj : totalBasis zU bU hzU hzbU sU hsU 0 j = 1 := by
        change (Algebra.SectionJet.zeroEquiv (augmentation G U)).symm
          (Module.Basis.singleton (ULift.{w} (Fin 1)) Γ(S, U) j) = 1
        rw [Module.Basis.singleton_apply, map_one]
      have hVj : totalBasis zV bV hzV hzbV sV hsV 0 j = 1 := by
        change (Algebra.SectionJet.zeroEquiv (augmentation G V)).symm
          (Module.Basis.singleton (ULift.{w} (Fin 1)) Γ(S, V) j) = 1
        rw [Module.Basis.singleton_apply, map_one]
      rw [hUj, hVj, hone]
    rw [hvec, Module.Basis.toMatrix_self, Matrix.det_one, jetExponent, pow_zero]
  | succ n ih =>
    calc
      _ = ((totalBasis zV bV hzV hzbV sV hsV n).toMatrix
            (fun j => restriction G n h (totalBasis zU bU hzU hzbU sU hsU n j))).det *
          ((layerBasis zV bV hzV hzbV n).toMatrix
            (fun e => layerRestriction G n h (layerBasis zU bU hzU hzbU n e))).det := by
        exact SplitBasis.adaptedBasis_semilinearMatrix_det
          (Algebra.SectionJet.truncate (augmentation G U) n).toLinearMap (sU n) (hsU n)
          (Algebra.SectionJet.truncate (augmentation G V) n).toLinearMap (sV n) (hsV n)
          (restriction G (n + 1) h) (restriction G n h) (restriction_truncate G n h)
          (totalBasis zU bU hzU hzbU sU hsU n) (layerBasis zU bU hzU hzbU n)
          (totalBasis zV bV hzV hzbV sV hsV n) (layerBasis zV bV hzV hzbV n)
      _ = _ := by
        rw [ih, layerBasis_restrictionMatrix_det G h bU bV zU hzU hzbU zV hzV hzbV,
          jetExponent, pow_add]

end Langlands.GroupScheme.IdentityJet
