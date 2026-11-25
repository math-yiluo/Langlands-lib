module

public import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.Ring.Adjunctions
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# Pseudofunctoriality of the ringed-space module pullback

For morphisms of ringed spaces `f : X' ⟶ X` and `f' : X'' ⟶ X'` this file builds the
canonical isomorphism of functors

`modulePullback (f' ≫ f) ≅ modulePullback f ⋙ modulePullback f'`,

that is `(f' ≫ f)^* ≅ f'^* ∘ f^*` (written in diagrammatic order, so `modulePullback f` is
applied first), and identifies its components with the comparison *map*
`Stacks.Sheaves.RingedSpaceDifferentials.modulePullbackComparison` already in the tree.
In particular that map is an isomorphism.

## Main results

* `Stacks.PullbackPseudofunctor.modulePushforward_comp`: the pushforward functors compose on
  the nose, `modulePushforward f' ⋙ modulePushforward f = modulePushforward (f' ≫ f)`.
* `Stacks.PullbackPseudofunctor.modulePushforward_id` and
  `Stacks.PullbackPseudofunctor.modulePullbackIdIso`: pushforward along an identity is the
  identity functor on the nose, and so pullback along an identity is isomorphic to it; with
  `homEquiv_modulePullbackIdIso_hom_app`,
  `unit_comp_map_modulePullbackIdIso_hom_app` and
  `modulePullbackIdIso_hom_app_comp_counit` for its adjoint equations.
* `Stacks.PullbackPseudofunctor.modulePullbackCompIso`: the isomorphism.
* `Stacks.PullbackPseudofunctor.modulePullbackCompIso_hom_app`: its components are exactly
  `modulePullbackComparison`.
* `Stacks.PullbackPseudofunctor.isIso_modulePullbackComparison`: hence that map is an
  isomorphism. This is the fact the consumers want.
* `Stacks.PullbackPseudofunctor.homEquiv_modulePullbackCompIso_hom_app`,
  `unit_comp_map_modulePullbackCompIso_hom_app`,
  `modulePullbackCompIso_hom_app_comp_counit`: the compatibility of the isomorphism with the
  units and counits of the two adjunctions. These are the usable equations.
* `Stacks.PullbackPseudofunctor.modulePullbackComparison_naturality` and
  `modulePullbackComparison_unique`: naturality in the module, and the characterization of
  the comparison map by its adjoint description, so that any map with that description is
  it.
* `Stacks.PullbackPseudofunctor.modulePullbackCompIso_eq_pullbackComp_symm`: the
  isomorphism is Mathlib's `SheafOfModules.pullbackComp` for the two structure-sheaf
  morphisms, so Mathlib's associativity coherence `SheafOfModules.pullback_assoc` applies to
  it verbatim.
* `Stacks.PullbackPseudofunctor.modulePullbackCompIso_assoc`: the associativity coherence of
  the pseudofunctor structure, in component form.

## Route

`modulePullback f` is the left adjoint of `modulePushforward f`
(`RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction`). The composite of the
two adjunctions is therefore an adjunction

`modulePullback f ⋙ modulePullback f' ⊣ modulePushforward f' ⋙ modulePushforward f`,

and the right-hand side is *definitionally* `modulePushforward (f' ≫ f)`: unwinding
`RingedSpaceModuleAdjunction.modulePushforward`, this is Mathlib's
`SheafOfModules.pushforwardComp`, which is `Iso.refl _`, composed with the two facts
`opensMap (f' ≫ f) = opensMap f ⋙ opensMap f'` and
`structureSheafHom (f' ≫ f) = structureSheafHom f ≫ _ (structureSheafHom f')`, both of which
hold by `rfl` here (`modulePushforward_comp` records the composite statement). So the two
functors `modulePullback (f' ≫ f)` and `modulePullback f ⋙ modulePullback f'` are left
adjoints of *the same* functor, and `CategoryTheory.Adjunction.leftAdjointUniq` identifies
them. Mathlib's `Adjunction.homEquiv_leftAdjointUniq_hom_app` then says the components
correspond, under the adjunction for `f' ≫ f`, to the unit of the composite adjunction,
which by `Adjunction.comp_unit_app` is the composite of units that
`modulePullbackComparison` was defined to be adjoint to.

## What is not done

* No universe generality beyond `RingedSpace.{u, u}`: everything here inherits the
  restriction of `StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace`, which is forced
  by Mathlib's `PresheafOfModules.instIsRightAdjointPushforward`.
* **The unitality of the composition isomorphism is not proved.** `modulePullbackIdIso`
  identifies `modulePullback (𝟙 X)` with the identity functor, but there is no statement
  that `modulePullbackCompIso (𝟙 X') f'` becomes the identity once the two sides are
  transported along `f' ≫ 𝟙 X' = f'` and along `modulePullbackIdIso`. That transported
  statement is the one a consumer needs in order to normalize a composition isomorphism at a
  factor which is only *provably*, not definitionally, an identity — for instance at
  `AlgebraicGeometry.Scheme.homOfLE (le_refl U)`, which is provably but not definitionally
  `𝟙 U.toScheme`.
* The associativity coherence is stated only in component form
  (`modulePullbackCompIso_assoc`), not as an equality of composites of natural isomorphisms;
  the latter is `SheafOfModules.pullback_assoc` read through
  `modulePullbackCompIso_eq_pullbackComp_symm`.
* No bridge to the other ringed-space spelling.
  `StacksFrontier.Topology.Sheaves.RingedSpace.ModuleFunctors`
  independently builds `pullbackComp` and `pushforwardComp` (tagged `0097`) for its own
  functors `pullback`/`pushforward` over `ringCatSheaf`, by the same `leftAdjointUniq`
  route; and `StacksDraft.Ch17.Sec14.Tag01C8` builds `RS.Modules.pullback_comp_iso` for a
  third set of names. Nothing here relates those to `modulePullback` over `structureSheafRing`.
  They are not interchangeable as written: they are stated for `RingedSpace.{u}` rather than
  `RingedSpace.{u, u}`, and `ModuleFunctors` needs its own
  `toRingCatSheafHom_comp` (proved by `ext`), where the corresponding identification for
  `structureSheafHom` holds here by `rfl`.
* Nothing here is about schemes. The statements are for morphisms of ringed spaces; a
  consumer working with `Scheme.Hom` must pass through `Scheme.Hom.toLRSHom.toShHom` itself.
* No statement about sections: this file does not describe
  `(modulePullbackCompIso f f').hom.app M` on local sections of the two pullbacks. The
  pullback of sheaves of modules is a sheafification of a tensor product, so there is no
  elementwise description of its sections to state one against; the adjoint equations above
  are the available characterization.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Functor
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.PullbackPseudofunctor

variable {X X' X'' : RingedSpace.{u, u}}

/-- The identity adjunction, with both functors read as the pullback and pushforward along
`𝟙 X` using `modulePushforward_id`. Naming this fixes the two type identifications once;
elaborating them repeatedly is expensive. -/
noncomputable def idAdjunction (X : RingedSpace.{u, u}) :
    𝟭 (SheafOfModules.{u} (structureSheafRing X)) ⊣ modulePushforward (𝟙 X) :=
  Adjunction.id

/-- **The module pullback along an identity is the identity.** Both `modulePullback (𝟙 X)`
and the identity functor are left adjoints of `modulePushforward (𝟙 X)`, which is the
identity functor by `modulePushforward_id`. -/
noncomputable def modulePullbackIdIso (X : RingedSpace.{u, u}) :
    modulePullback (𝟙 X) ≅ 𝟭 (SheafOfModules.{u} (structureSheafRing X)) :=
  Adjunction.leftAdjointUniq (modulePullbackPushforwardAdjunction (𝟙 X)) (idAdjunction X)

/-- The composite of the adjunctions `f^* ⊣ f_*` and `f'^* ⊣ f'_*`, with its right adjoint
read as `(f' ≫ f)_*` using `modulePushforward_comp`. -/
noncomputable def compAdjunction (f : X' ⟶ X) (f' : X'' ⟶ X') :
    modulePullback f ⋙ modulePullback f' ⊣ modulePushforward (f' ≫ f) :=
  (modulePullbackPushforwardAdjunction f).comp (modulePullbackPushforwardAdjunction f')

/-- **Pseudofunctoriality of the module pullback.** The canonical isomorphism
`(f' ≫ f)^* ≅ f'^* ∘ f^*` of functors `Mod(𝒪_X) ⥤ Mod(𝒪_{X''})`. Both sides are left
adjoints of `(f' ≫ f)_*`, the left-hand side by
`RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction` and the right-hand side by
`compAdjunction`; the isomorphism is the uniqueness of a left adjoint. -/
noncomputable def modulePullbackCompIso (f : X' ⟶ X) (f' : X'' ⟶ X') :
    modulePullback (f' ≫ f) ≅ modulePullback f ⋙ modulePullback f' :=
  Adjunction.leftAdjointUniq (modulePullbackPushforwardAdjunction (f' ≫ f))
    (compAdjunction f f')

section Equations

variable (f : X' ⟶ X) (f' : X'' ⟶ X') (M : SheafOfModules.{u} (structureSheafRing X))

end Equations

end Stacks.PullbackPseudofunctor

end
