import Langlands.GroupScheme.AffinePointAutomorphisms
import Langlands.Shimura.Unitary.RationalGroupScheme

noncomputable section
open CategoryTheory Opposite AlgebraicGeometry Algebra
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.Shimura.AlgebraInvolution

universe u
variable {R S A : Type u} [CommRing R] [CommRing S] [Algebra R S]
  [Ring A] [Algebra R A] (σ : AlgebraInvolution R A)

/-- Coefficient automorphisms act on the actual scalar-extended similitude group. -/
def coefficientAut (s : S ≃ₐ[R] S) : MulAut (σ.baseChange S).similitudes :=
  (σ.similitudeFunctor.mapIso (CommAlgCat.isoMk s)).groupIsoToMulEquiv

/-- This automorphism is precisely the already constructed coefficient-change map. -/
theorem coefficientAut_apply (s : S ≃ₐ[R] S) (x : (σ.baseChange S).similitudes) :
    σ.coefficientAut s x = σ.baseChangeMap (CommAlgCat.ofHom s.toAlgHom) x := rfl

/-- The underlying algebra unit is changed by s tensor identity. -/
theorem coefficientAut_underlying (s : S ≃ₐ[R] S) (x : (σ.baseChange S).similitudes) :
    ((σ.coefficientAut s x).val.1 : S ⊗[R] A) =
      changeCoefficients s.toAlgHom (x.val.1 : S ⊗[R] A) := rfl

/-- The common similitude multiplier is transformed by the same coefficient automorphism. -/
theorem coefficientAut_multiplier (s : S ≃ₐ[R] S) (x : (σ.baseChange S).similitudes) :
    (σ.baseChange S).multiplier (σ.coefficientAut s x) =
      Units.map s.toMonoidHom ((σ.baseChange S).multiplier x) := rfl

@[simp] theorem coefficientAut_one : σ.coefficientAut (1 : S ≃ₐ[R] S) = 1 := by
  apply MulEquiv.ext
  intro x
  exact congrArg (fun f : σ.similitudeFunctor.obj (CommAlgCat.of R S) ⟶
    σ.similitudeFunctor.obj (CommAlgCat.of R S) => f x)
      (σ.similitudeFunctor.map_id (CommAlgCat.of R S))

theorem coefficientAut_mul (s t : S ≃ₐ[R] S) :
    σ.coefficientAut (s * t) = σ.coefficientAut s * σ.coefficientAut t := by
  apply MulEquiv.ext
  intro x
  exact congrArg (fun f : σ.similitudeFunctor.obj (CommAlgCat.of R S) ⟶
    σ.similitudeFunctor.obj (CommAlgCat.of R S) => f x)
      (σ.similitudeFunctor.map_comp (CommAlgCat.ofHom t.toAlgHom)
        (CommAlgCat.ofHom s.toAlgHom))

/-- The coefficient action as a homomorphism into automorphisms of the similitude group. -/
def coefficientAutHom : (S ≃ₐ[R] S) →* MulAut (σ.baseChange S).similitudes where
  toFun := σ.coefficientAut
  map_one' := σ.coefficientAut_one
  map_mul' := σ.coefficientAut_mul

namespace SchemeModel
variable {κ : Type u} [Fintype κ] (b : Module.Basis κ R A)

/-- The coordinate identification intertwines actual scheme pullback and tensor coefficient change. -/
theorem affinePointsEquiv_coefficientAut (s : S ≃ₐ[R] S)
    (x : (algSpec (CommRingCat.of R)).obj (op (CommAlgCat.of R S)) ⟶
      (groupScheme b σ).X) :
    affinePointsEquiv b σ (CommAlgCat.of R S)
        (GroupScheme.affinePointAut (groupScheme b σ) s x) =
      σ.coefficientAut s (affinePointsEquiv b σ (CommAlgCat.of R S) x) :=
  affinePointsEquiv_naturality b σ (CommAlgCat.ofHom s.toAlgHom) x

end SchemeModel
end Langlands.Shimura.AlgebraInvolution

namespace Langlands.Shimura.CentralSimpleUnitaryData

variable {E K A : Type} [Field E] [NumberField E] [NumberField.IsTotallyReal E]
  [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
  [Algebra E K] [IsQuadraticExtension E K] [Ring A] [Algebra K A] [Algebra E A]
  [IsScalarTower E K A] [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ K A]
  {n : ℕ} (D : CentralSimpleUnitaryData E K A n)

/-- The action of Aut(C/Q) on actual complex points of the rational Harris group scheme. -/
def complexPointGaloisAction : (ℂ ≃ₐ[ℚ] ℂ) →* MulAut
    ((algSpec (CommRingCat.of ℚ)).obj (op (CommAlgCat.of ℚ ℂ)) ⟶ D.rationalGroupScheme.X) :=
  GroupScheme.affinePointAutHom D.rationalGroupScheme

omit [IsScalarTower E K A] in
/-- In scalar-extended algebra coordinates, Galois acts on coefficients, including the multiplier. -/
theorem complexPointGaloisAction_coordinates (s : ℂ ≃ₐ[ℚ] ℂ)
    (x : (algSpec (CommRingCat.of ℚ)).obj (op (CommAlgCat.of ℚ ℂ)) ⟶
      D.rationalGroupScheme.X) :
    D.rationalAffinePointsEquiv (CommAlgCat.of ℚ ℂ) (D.complexPointGaloisAction s x) =
      D.toSecondKindInvolution.rationalInvolution.coefficientAut s
        (D.rationalAffinePointsEquiv (CommAlgCat.of ℚ ℂ) x) :=
  AlgebraInvolution.SchemeModel.affinePointsEquiv_coefficientAut
    D.toSecondKindInvolution.rationalInvolution D.rationalBasis s x

end Langlands.Shimura.CentralSimpleUnitaryData
