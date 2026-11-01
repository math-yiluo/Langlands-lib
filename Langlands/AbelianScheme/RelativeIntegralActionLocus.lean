import Langlands.Algebra.FiniteFreeRingHomLocus
import Langlands.AbelianScheme.RelativeIntegralActions

/-! # A relative integral action locus from a represented endomorphism presheaf -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Module Opposite

universe u uI uO

namespace Langlands.AbelianScheme

open Langlands.GroupScheme.Cartier

variable {S : Scheme.{u}} (B : Langlands.AbelianScheme S)
    {I : Type uI} [Fintype I] {O : Type uO} [Ring O] (b : Basis I ℤ O)
    (E : Over S)
    (e : (locallyNoetherianTestInclusion S).op ⋙
        relativeHomFunctor B.toCommGroupScheme B.toCommGroupScheme ⋙
          forget AddCommGrpCat.{u} ≅
      (locallyNoetherianTestInclusion S).op ⋙ yoneda.obj E)
    (hpow : IsLocallyNoetherian (∏ᶜ fun _ : I => E).left)

/-- The actual equalizer imposing the finite unit and multiplication equations. -/
abbrev relativeIntegralActionLocus : Over S :=
  FiniteFreeRingHom.locus b (relativeEndRingFunctor B)
    (fun T : Over S => IsLocallyNoetherian T.left) E e hpow

/-- The equation locus is a subobject of the finite endomorphism-tuple space. -/
def relativeIntegralActionLocusInclusion :
    relativeIntegralActionLocus B b E e hpow ⟶ ∏ᶜ fun _ : I => E :=
  equalizer.ι _ _

instance relativeIntegralActionLocusInclusion_mono :
    Mono (relativeIntegralActionLocusInclusion B b E e hpow) :=
  inferInstanceAs (Mono (equalizer.ι _ _))

/-- The locus classifies actual integral actions over every locally noetherian test. -/
def relativeIntegralActionLocusHomEquiv
    (T : ObjectProperty.FullSubcategory (fun T : Over S => IsLocallyNoetherian T.left)) :
    (T.obj ⟶ relativeIntegralActionLocus B b E e hpow) ≃
      (O →+* CategoryTheory.End ((baseChange T.obj.hom).obj B)) :=
  (FiniteFreeRingHom.locusHomEquiv b (relativeEndRingFunctor B)
    (fun T : Over S => IsLocallyNoetherian T.left) E e hpow T).trans
      (integralActionEquiv b ((baseChange T.obj.hom).obj B)).symm

/-- On a basis vector, the classified action is the decoded coordinate of the locus map. -/
theorem relativeIntegralActionLocusHomEquiv_apply_basis
    (T : ObjectProperty.FullSubcategory (fun T : Over S => IsLocallyNoetherian T.left))
    (f : T.obj ⟶ relativeIntegralActionLocus B b E e hpow) (i : I) :
    relativeIntegralActionLocusHomEquiv B b E e hpow T f (b i) =
      e.inv.app (op T)
        ((f ≫ relativeIntegralActionLocusInclusion B b E e hpow) ≫
          Pi.π (fun _ : I => E) i) := by
  exact integralActionEquiv_symm_apply_basis b ((baseChange T.obj.hom).obj B)
    (FiniteFreeRingHom.locusHomEquiv b (relativeEndRingFunctor B)
      (fun T : Over S => IsLocallyNoetherian T.left) E e hpow T f) i

/-- The natural comparison on the unchanged full locally noetherian test category. -/
def relativeIntegralActionLocusIso :
    (locallyNoetherianTestInclusion S).op ⋙ relativeIntegralActionFunctor B b ≅
      (locallyNoetherianTestInclusion S).op ⋙
        uliftYoneda.{max uI uO}.obj (relativeIntegralActionLocus B b E e hpow) :=
  FiniteFreeRingHom.actionLocusIso b (relativeEndRingFunctor B)
    (fun T : Over S => IsLocallyNoetherian T.left) E e hpow

end Langlands.AbelianScheme
