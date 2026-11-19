import Langlands.GroupScheme.InnerCocycleDescent
import Langlands.GroupScheme.Rational.NumberFieldOrthogonalHasseReduction
import Langlands.GroupScheme.Reductive.GeometricAdjoint
import Langlands.GroupScheme.Reductive.GeometricSimplyConnected

/-! # Reduction of number-field Hasse injectivity to the arithmetic kernels -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

namespace Cocycle

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} {U : Over (Spec (CommRingCat.of F))}

/-- Triviality on the actual pullback of a cover to every completion. -/
def LocallyTrivial (ξ : Cocycle G U) : Prop :=
  ∀ v : Global.Place F,
    let b := algebraBaseMap F (Global.placeCompletion F v)
    let r := (Over.mapPullbackAdj b).counit.app U
    (ξ.baseChange b _ r).IsTrivial

theorem InnerTwist.difference_locallyTrivial {ξ ζ : Cocycle G U}
    (D : ξ.InnerTwist) (h : ξ.LocallyCohomologous ζ) : (D.difference ζ).LocallyTrivial := by
  intro v
  exact D.baseChange_difference_isTrivial ζ _ _ _ (h v)

end Cocycle

/-- The simply connected arithmetic kernel on the actual finite Galois covers. -/
def NumberFieldSimplyConnectedGaloisHasseKernelStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F))),
    IsSimplyConnected G →
    ∀ (L : Type u) [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
      (ξ : Cocycle G (Over.mk (algebraBaseMap F L))),
      ξ.LocallyTrivial → ξ.IsTrivial

/-- The adjoint arithmetic kernel on the actual finite Galois covers. -/
def NumberFieldAdjointGaloisHasseKernelStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F))),
    IsAdjoint G →
    ∀ (L : Type u) [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
      (ξ : Cocycle G (Over.mk (algebraBaseMap F L))),
      ξ.LocallyTrivial → ξ.IsTrivial

private theorem cohomologous_of_inner_kernel
    {F L : Type u} [Field F] [NumberField F] [Field L] [Algebra F L]
    {G : GroupScheme (Spec (CommRingCat.of F))} (hG : IsSemisimple G)
    (ξ ζ : Cocycle G (Over.mk (algebraBaseMap F L))) (hlocal : ξ.LocallyCohomologous ζ)
    (h : ∀ (H : GroupScheme (Spec (CommRingCat.of F))),
      ((GroupScheme.baseChange (algebraBaseMap F L)).obj H ≅
        (GroupScheme.baseChange (algebraBaseMap F L)).obj G) →
      ∀ (ν : Cocycle H (Over.mk (algebraBaseMap F L))), ν.LocallyTrivial → ν.IsTrivial) :
    ξ.Cohomologous ζ := by
  obtain ⟨hs, hf, _⟩ := fieldExtension_fpqc F L
  let p := algebraBaseMap F L
  have hGL := isSemisimpleFieldExtension F L G hG
  let : IsAffineHom ((GroupScheme.baseChange p).obj G).X.hom := hGL.isConnectedReductive.isAffineHom
  have hA : IsAffine ((GroupScheme.baseChange p).obj G).X.left :=
    isAffine_of_isAffineHom ((GroupScheme.baseChange p).obj G).X.hom
  let : IsAffine (Over.mk (algebraBaseMap F L)).left :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of L)))
  let D := ξ.innerTwist hA hf hs
  let e : (GroupScheme.baseChange p).obj D.obj ≅ (GroupScheme.baseChange p).obj G :=
    ξ.innerTwistIso hA hf hs
  exact (D.cohomologous_iff_difference_isTrivial ζ).mpr
    (h D.obj e (D.difference ζ) (D.difference_locallyTrivial hlocal))

/-- The two arithmetic kernels and quadratic isometry give finite-Galois Hasse injectivity. -/
theorem numberFieldGaloisHassePrinciple_of_arithmetic
    (hsc : NumberFieldSimplyConnectedGaloisHasseKernelStatement.{u})
    (had : NumberFieldAdjointGaloisHasseKernelStatement.{u})
    (hq : NumberFieldQuadraticIsometryStatement.{u}) : NumberFieldGaloisHassePrincipleStatement.{u} := by
  intro F _ _ G hG L _ _ _ _ ξ ζ hlocal
  rcases hG with hG | hG | hG
  · apply cohomologous_of_inner_kernel hG.isSemisimple ξ ζ hlocal
    intro H e ν hν
    have hg := (isSimplyConnected_fieldExtension_iff (K := L) G).mpr hG
    have hh := (isSimplyConnected_fieldExtension_iff (K := L) H).mp
      ((isSimplyConnected_iff_of_iso e).mpr hg)
    exact hsc F H hh L ν hν
  · apply cohomologous_of_inner_kernel hG.isSemisimple ξ ζ hlocal
    intro H e ν hν
    have hg := (isAdjoint_fieldExtension_iff (K := L) G).mpr hG
    have hh := (isAdjoint_fieldExtension_iff (K := L) H).mp ((isAdjoint_iff_of_iso e).mpr hg)
    exact had F H hh L ν hν
  · exact numberFieldOrthogonalGaloisHasse_of_quadratic hq F G hG L ξ ζ hlocal

/-- The same arithmetic inputs suffice for the unchanged finite-separable target. -/
theorem numberFieldHassePrinciple_of_arithmetic
    (hsc : NumberFieldSimplyConnectedGaloisHasseKernelStatement.{u})
    (had : NumberFieldAdjointGaloisHasseKernelStatement.{u})
    (hq : NumberFieldQuadraticIsometryStatement.{u}) : NumberFieldHassePrincipleStatement.{u} :=
  numberFieldHassePrinciple_of_galois (numberFieldGaloisHassePrinciple_of_arithmetic hsc had hq)

end Langlands.GroupScheme
