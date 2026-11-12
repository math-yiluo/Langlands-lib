import Langlands.Cohomology.ExactBaseChange.ResolutionMap
import Langlands.AlgebraicGeometry.Modules.HigherDirectImageBaseChange
import Langlands.AlgebraicGeometry.Modules.OpenCartesianDirectImageBaseChange
import Langlands.AlgebraicGeometry.Modules.DerivedRestrictionVanishing
import Langlands.Cohomology.AcyclicResolution.ExactComparison
import Langlands.Cohomology.ExactBaseChange.ResolutionProof

/-!
# Base change of higher direct images along open immersions

For a cartesian square `j' ≫ f = f_V ≫ j` with `j` an open immersion, the base change
transformation of higher direct images is an isomorphism at every module in every degree. The
proof applies the resolution compatibility statement to an injective resolution `I` of `M` and
its pullback `j'^* I`, whose terms are flasque, with `ψ` the identity.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules.FlatBaseChange

open Langlands.Cohomology Langlands.Cohomology.AcyclicResolution
open Langlands.Cohomology.ExactBaseChange
open Langlands.AlgebraicGeometry.Modules.DerivedSections

/-- The restriction of a flasque module along an open immersion is flasque. -/
lemma isFlasque_restrictFunctor {X U : Scheme.{u}} (i : U ⟶ X) [IsOpenImmersion i]
    (N : X.Modules) [TopCat.Presheaf.IsFlasque N.presheaf] :
    TopCat.Presheaf.IsFlasque ((Scheme.Modules.restrictFunctor i).obj N).presheaf where
  epi k := by
    rw [show k = k.unop.op from rfl, Scheme.Modules.restrict_map N i k.unop]
    exact TopCat.Presheaf.IsFlasque.epi _

/-- The pullback of an injective module along an open immersion has vanishing positive higher
direct images. -/
lemma isZero_higherDirectImage_pullback_injective {X U V : Scheme.{u}} (i : U ⟶ X)
    [IsOpenImmersion i] (g : U ⟶ V) (J : X.Modules) [Injective J] (r : ℕ) :
    IsZero ((higherDirectImage g (r + 1)).obj ((Scheme.Modules.pullback i).obj J)) := by
  have := PushforwardInjectiveAcyclic.isFlasque_of_injective J
  have := isFlasque_restrictFunctor i J
  exact (isZero_higherDirectImage_of_isFlasque g r _).of_iso
    ((higherDirectImage g (r + 1)).mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback i).app J)).symm

/-- **Open immersion base change.** For a cartesian square `j' ≫ f = f_V ≫ j` with `j` an
open immersion and exact pullbacks, the base change transformation of higher direct images is an
isomorphism at every module in every degree. -/
theorem isIso_higherDirectImageBaseChange_of_isOpenImmersion
    {X Y V XV : Scheme.{u}} (f : X ⟶ Y) (j : V ⟶ Y) (fV : XV ⟶ V) (j' : XV ⟶ X)
    [IsOpenImmersion j] (h : IsPullback j' fV f j)
    [PreservesFiniteLimits (Scheme.Modules.pullback j)]
    [PreservesFiniteLimits (Scheme.Modules.pullback j')]
    (M : X.Modules) (n : ℕ) :
    IsIso ((higherDirectImageBaseChangeNatTrans j f fV j' h.w n).app M) := by
  have : IsOpenImmersion j' := MorphismProperty.of_isPullback h.flip inferInstance
  let I := injectiveResolution M
  let α := Scheme.Modules.pullback j'
  let τ := pushforwardBaseChangeNatTrans j f fV j' h.w
  let ψ := 𝟙 ((α.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)
  have hΦ : ∀ q, IsIso ((resolutionBaseChangeMap τ ψ).f q) := by
    intro q
    simp only [resolutionBaseChangeMap_f, ψ, HomologicalComplex.id_f]
    exact isIso_pushforwardBaseChange_of_isOpenImmersion j f fV j' h _
  have : IsIso (resolutionBaseChangeMap τ ψ) := HomologicalComplex.Hom.isIso_of_components _
  exact (resolutionCompatibility.{u, u, u, u, u + 1, u + 1, u + 1, u + 1} _ _ _ _ _ _ _ _ τ M
    I.cocomplex _ I.ι (mapResolutionAugmentation α I.ι) ψ
    (Category.comp_id _) (resolutionBaseChangeMap τ ψ) (fun _ => rfl)).2
    (fun q r => (Scheme.Modules.pushforward f).isZero_rightDerived_obj_injective_succ r _)
    (fun q r => isZero_higherDirectImage_pullback_injective j' fV _ r) inferInstance n

end Langlands.AlgebraicGeometry.Modules.FlatBaseChange
