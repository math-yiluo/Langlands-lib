import Langlands.GroupScheme.Rational.SteinbergFactorGaloisTransport

/-! # Rational-coordinate transport from compatible whole simple-root maps -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 20000

section Galois

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]

local instance : IsAffineHom
    ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom := by
  change IsAffineHom (pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

namespace SplitPinning.NormalizedRootParametrization

variable {p : SplitPinning ((GroupScheme.baseChange (algebraBaseMap k K)).obj G)}
    {a : p.base.support} (x : p.NormalizedRootParametrization a)

/-- Evaluating a coefficient curve at a field element agrees with the actual
rational point, under the published coefficient comparison. -/
theorem coefficientCurve_evaluate_rationalPoint (c : K) :
    Lie.affineMap G
        ((MvPolynomial.aeval (fun _ : Fin 1 => c)).restrictScalars k)
        (x.coefficientCurve k K G) =
      GaloisPointComparison.baseChangeCoeffEquiv k K G
        (x.toRootParametrization.rationalPoint c) := by
  rw [x.coefficientCurve_evaluate]
  have h :
      x.point ((algSpec (CommRingCat.of K)).obj
          (Opposite.op (CommAlgCat.of K K))) ((Scheme.ΓSpecIso (CommRingCat.of K)).inv c) =
        toUnit _ ≫ x.toRootParametrization.rationalPoint c := by
    rw [RootParametrization.toUnit_comp_rationalPoint]
    change _ = x.point _ _
    congr 1
    change _ = (Spec.map (CommRingCat.ofHom (algebraMap K K))).appTop _
    simp
  rw [h, Lie.affineBaseChangeEquiv_constantPoint]
  change Lie.affineMap G (AlgHom.id k K) _ = _
  exact Lie.affineMap_id G _

end SplitPinning.NormalizedRootParametrization

namespace PolynomialGalois

/-- Conjugate root coordinates while reindexing by the simple-root action. -/
def rootCoordinateConjugate {A : Type u}
    (ρ : (K ≃ₐ[k] K) →* Equiv.Perm A)
    (σ : K ≃ₐ[k] K) (d : A → K) : A → K :=
  fun a => σ (d ((ρ σ).symm a))

theorem rootCoordinateConjugate_one {A : Type u}
    (ρ : (K ≃ₐ[k] K) →* Equiv.Perm A) (d : A → K) :
    rootCoordinateConjugate k K ρ 1 d = d := by
  funext a
  change (1 : K ≃ₐ[k] K) (d ((ρ 1).symm a)) = d a
  rw [map_one]
  rfl

/-- Evaluation and coefficient conjugation commute after conjugating the
evaluation parameter. -/
theorem aeval_comp_conjugate (σ : K ≃ₐ[k] K) (c : K) :
    ((MvPolynomial.aeval (fun _ : Fin 1 => σ c)).restrictScalars k).comp
        (lineConjugate k K σ) =
      σ.toAlgHom.comp
        ((MvPolynomial.aeval (fun _ : Fin 1 => c)).restrictScalars k) := by
  apply AlgHom.coe_ringHom_injective
  apply MvPolynomial.ringHom_ext <;> intro d <;>
    simp [AlgHom.comp_apply, lineConjugate]

end PolynomialGalois

namespace SplitPinning

variable {p : SplitPinning ((GroupScheme.baseChange (algebraBaseMap k K)).obj G)}

/-- Whole-map compatibility transports every rational root coordinate. -/
theorem RootMapsGaloisCompatible.rationalPoints
    (x : p.NormalizedSimpleRootParametrizations)
    (ρ : (K ≃ₐ[k] K) →* Equiv.Perm p.base.support)
    (hx : RootMapsGaloisCompatible k K p x ρ)
    (σ : K ≃ₐ[k] K) (a : p.base.support) (c : K) :
    GaloisPointComparison.rationalConjugate k K G σ
        ((x a).toRootParametrization.rationalPoint c) =
      (x (ρ σ a)).toRootParametrization.rationalPoint (σ c) := by
  apply (GaloisPointComparison.baseChangeCoeffEquiv k K G).injective
  rw [GaloisPointComparison.baseChangeCoeffEquiv_rationalConjugate]
  change Lie.affineMap G σ.toAlgHom _ = _
  rw [← (x a).coefficientCurve_evaluate_rationalPoint k K G,
    ← (x (ρ σ a)).coefficientCurve_evaluate_rationalPoint k K G]
  let ev : MvPolynomial (Fin 1) K →ₐ[k] K :=
    (MvPolynomial.aeval (fun _ : Fin 1 => c)).restrictScalars k
  let evσ : MvPolynomial (Fin 1) K →ₐ[k] K :=
    (MvPolynomial.aeval (fun _ : Fin 1 => σ c)).restrictScalars k
  change Lie.affineMap G σ.toAlgHom (Lie.affineMap G ev _) =
    Lie.affineMap G evσ _
  calc
    _ = Lie.affineMap G (σ.toAlgHom.comp ev)
        ((x a).coefficientCurve k K G) :=
      (Lie.affineMap_comp G ev σ.toAlgHom _).symm
    _ = Lie.affineMap G (evσ.comp (PolynomialGalois.lineConjugate k K σ))
        ((x a).coefficientCurve k K G) :=
      congrArg (fun f => Lie.affineMap G f ((x a).coefficientCurve k K G))
        (PolynomialGalois.aeval_comp_conjugate k K σ c).symm
    _ = Lie.affineMap G evσ (Lie.affineMap G
        (PolynomialGalois.lineConjugate k K σ) ((x a).coefficientCurve k K G)) :=
      Lie.affineMap_comp G _ evσ _
    _ = _ := congrArg (Lie.affineMap G evσ) (hx σ a)

end SplitPinning

end Galois

end Langlands.GroupScheme
