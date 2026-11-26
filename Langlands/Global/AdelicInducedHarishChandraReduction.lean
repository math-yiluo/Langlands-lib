import Langlands.Global.AdelicInducedHarishChandraStatement
import Langlands.Global.AdelicTwistedConvolution

/-! # Finite-dimensional reduction for the uniform Harish-Chandra equations -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

/-- For each base parameter there is one bi-finite test kernel whose transported actions
preserve a fixed finite-dimensional space containing the original form. The action at the
base parameter is injective on that space. -/
def InducedHarishChandraFiniteModelStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G P M U : GroupScheme (Spec (CommRingCat.of F)))
    (A : CommGroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [IsAffine P.X.left]
    (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left] (iU : U ⟶ P) (l : M ⟶ P)
    (a : A.toGrp ⟶ M) (r : ParabolicRootPresentation p l a)
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    (_hA : IsSplitTorus A.toGrp) (_hT : IsSplitTorus r.data.T.toGrp),
    IsConnectedReductive G → LeviSubgroup.IsGeometricUnipotentRadical iU →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) (hK : IsIwasawaCompact p K) {N d : ℕ}
      (rho : MatrixRepresentation G (Fin N))
      (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth) (φ : AdelicGroupPoints F G → ℂ),
      IsMaximalCompactSubgroup F G K → IsClosedSubgroup rho →
      ∀ (hφ : IsAutomorphicFunctionOn F G hsmooth hcalc (parabolicQuotientSubgroup F p iU l)
        (K.comap (ofInfinite F G).toMonoidHom) rho φ)
        (lam₀ : ComplexCharacterParameter F P),
        ∃ (h : AdelicGroupPoints F G → ℂ) (hh : IsAdelicTestFunction F G h)
          (S : Submodule ℂ C(AdelicGroupPoints F G, ℂ)),
          IsInfiniteSubgroupFiniteFunction F G (K.comap (ofInfinite F G).toMonoidHom) h ∧
          IsInfiniteSubgroupFiniteFunction F G (K.comap (ofInfinite F G).toMonoidHom)
            (fun x => h x⁻¹) ∧
          FiniteDimensional ℂ S ∧ (⟨φ, hφ.2.1.1⟩ : C(AdelicGroupPoints F G, ℂ)) ∈ S ∧
          ∃ hS : ∀ lam, ∀ v ∈ S, hK.twistedConvolutionEnd hsmooth hh lam v ∈ S,
            Function.Injective ((hK.twistedConvolutionEnd hsmooth hh lam₀).restrict (hS lam₀))

/-- The finite-dimensional model implies the uniform equations for exactly the given family
of twists. The proof uses entire matrix entries and the characteristic polynomial. -/
theorem inducedHarishChandraEquations_of_finiteModel
    (hModel : InducedHarishChandraFiniteModelStatement.{u}) :
    InducedHarishChandraEquationsStatement.{u} := by
  intro F _ _ G P M U A _ _ _ _ p _ iU l a r _ _ _ hA hT hG hU K hK N d
    rho hsmooth hcalc φ hmax hrho hφ n e s₀
  obtain ⟨h, hh, S, hRight, hLeft, hdim, hφS, hS, hInj⟩ :=
    hModel F G P M U A p iU l a r hA hT hG hU K hK rho hsmooth hcalc φ hmax hrho hφ (e s₀)
  let : FiniteDimensional ℂ S := hdim
  exact hK.hasConvolutionEquationAt_parameterTwist_of_finiteDimensional
    hsmooth hh hRight hLeft e.toLinearMap s₀ ⟨φ, hφ.2.1.1⟩ S hφS (fun s => hS (e s)) hInj

end Langlands.Global
