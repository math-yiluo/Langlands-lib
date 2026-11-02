import Langlands.Cohomology.ExactBaseChange
import Langlands.AlgebraicGeometry.Modules.DerivedRestriction

/-!
# Base change transformations for higher direct images along exact pullbacks

For a commutative square `g' ≫ f = f' ≫ g` of schemes, with `f : X ⟶ Y`, `g : Y' ⟶ Y`,
`f' : X' ⟶ Y'` and `g' : X' ⟶ X`:

* `pushforwardBaseChangeNatTrans g f f' g' w : f_* ⋙ g^* ⟶ g'^* ⋙ f'_*` bundles the base change
  morphisms `pushforwardBaseChange g f f' g' w M : g^* f_* M ⟶ f'_* g'^* M`, which are natural in
  `M` (`pushforwardBaseChange_naturality`).
* If the pullbacks `g^*` and `g'^*` preserve finite limits (explicit instance assumptions),
  `higherDirectImageBaseChangeNatTrans g f f' g' w n : Rⁿ f_* ⋙ g^* ⟶ g'^* ⋙ Rⁿ f'_*` is
  `ExactBaseChange.baseChangeNatTrans` for this transformation. Its components are given by
  `higherDirectImageBaseChangeNatTrans_app`.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.Cohomology

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections

variable {X Y X' Y' : Scheme.{u}} (g : Y' ⟶ Y) (f : X ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
  (w : g' ≫ f = f' ≫ g)

/-- The base change morphisms `g^* f_* M ⟶ f'_* g'^* M` are natural in `M`. -/
@[reassoc]
lemma pushforwardBaseChange_naturality {M N : X.Modules} (u : M ⟶ N) :
    (Scheme.Modules.pullback g).map ((Scheme.Modules.pushforward f).map u) ≫
        pushforwardBaseChange g f f' g' w N =
      pushforwardBaseChange g f f' g' w M ≫
        (Scheme.Modules.pushforward f').map ((Scheme.Modules.pullback g').map u) := by
  have hu := (Scheme.Modules.pullbackPushforwardAdjunction g').unit.naturality u
  have hσ := (pushforwardSquareIso g f f' g' w).hom.naturality
    ((Scheme.Modules.pullback g').map u)
  simp only [Functor.id_map, Functor.comp_map] at hu hσ
  rw [pushforwardBaseChange, pushforwardBaseChange,
    ← Adjunction.homEquiv_naturality_left_symm, ← Adjunction.homEquiv_naturality_right_symm]
  congr 1
  rw [← Functor.map_comp_assoc, hu, Functor.map_comp, Category.assoc, hσ, Category.assoc]

/-- The base change morphisms `pushforwardBaseChange g f f' g' w M`, as a natural transformation
`f_* ⋙ g^* ⟶ g'^* ⋙ f'_*`. -/
def pushforwardBaseChangeNatTrans :
    Scheme.Modules.pushforward f ⋙ Scheme.Modules.pullback g ⟶
      Scheme.Modules.pullback g' ⋙ Scheme.Modules.pushforward f' where
  app M := pushforwardBaseChange g f f' g' w M
  naturality _ _ u := pushforwardBaseChange_naturality g f f' g' w u

/-- The component of `pushforwardBaseChangeNatTrans g f f' g' w` at `M` is
`pushforwardBaseChange g f f' g' w M`. -/
lemma pushforwardBaseChangeNatTrans_app (M : X.Modules) :
    (pushforwardBaseChangeNatTrans g f f' g' w).app M = pushforwardBaseChange g f f' g' w M :=
  rfl

variable [PreservesFiniteLimits (Scheme.Modules.pullback g)]
  [PreservesFiniteLimits (Scheme.Modules.pullback g')]

/-- The base change transformation `Rⁿ f_* ⋙ g^* ⟶ g'^* ⋙ Rⁿ f'_*` of higher direct images,
for pullbacks `g^*` and `g'^*` preserving finite limits: `ExactBaseChange.baseChangeNatTrans` for
`pushforwardBaseChangeNatTrans g f f' g' w`. -/
def higherDirectImageBaseChangeNatTrans (n : ℕ) :
    higherDirectImage f n ⋙ Scheme.Modules.pullback g ⟶
      Scheme.Modules.pullback g' ⋙ higherDirectImage f' n :=
  ExactBaseChange.baseChangeNatTrans (pushforwardBaseChangeNatTrans g f f' g' w) n

/-- The component of `higherDirectImageBaseChangeNatTrans g f f' g' w n` at `M`: the inverse of
the component of `LeftExactHomology.derivedNatTrans g^* f_* n`, followed by the component of
`NatTrans.rightDerived (pushforwardBaseChangeNatTrans g f f' g' w) n` and the comparison
`compComparison f'_* (Iso.refl (g'^* ⋙ f'_*)) M hM n`. -/
lemma higherDirectImageBaseChangeNatTrans_app (n : ℕ) (M : X.Modules) :
    (higherDirectImageBaseChangeNatTrans g f f' g' w n).app M =
      inv ((LeftExactHomology.derivedNatTrans (Scheme.Modules.pullback g)
          (Scheme.Modules.pushforward f) n).app M) ≫
        (NatTrans.rightDerived (pushforwardBaseChangeNatTrans g f f' g' w) n).app M ≫
          AcyclicResolution.compComparison (Scheme.Modules.pushforward f')
            (Iso.refl (Scheme.Modules.pullback g' ⋙ Scheme.Modules.pushforward f')) M
            (fun q => isZero_rightDerived_succ_of_preservesHomology _ M q) n :=
  ExactBaseChange.baseChangeNatTrans_app _ n M

end Langlands.AlgebraicGeometry.Modules.DerivedSections
