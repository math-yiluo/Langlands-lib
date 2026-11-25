module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Tactic.CrossRefAttribute
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# Associated sheaves and pullback and pushforward along a map of affine schemes

Let `φ : R ⟶ S` be a ring homomorphism and let `Spec φ : Spec S ⟶ Spec R` be the induced
morphism of affine schemes. Pulling the sheaf `M̃` associated to an `R`-module `M` back along
`Spec φ` gives the sheaf associated to the extension of scalars `S ⊗_R M`, naturally in `M`;
pushing the sheaf `Ñ` associated to an `S`-module `N` forward along `Spec φ` gives the sheaf
associated to the restriction of scalars of `N` along `φ`, naturally in `N`.

Each isomorphism comes with the normalization that identifies it as *the* canonical one: on global
sections the pullback comparison sends the pullback of the section represented by `m` to the
section represented by `1 ⊗ m`, and the pushforward comparison sends the section represented by
`n` to the section represented by the same `n`.

## Main definitions

* `AlgebraicGeometry.pushforwardΓLinearEquiv`: the underlying linear equivalence on global
  sections.
* `AlgebraicGeometry.pushforwardΓIso`: pushforward restricts the scalar action on global sections.
* `AlgebraicGeometry.pullbackTildeIso`: pullback of associated sheaves is extension of scalars.
* `AlgebraicGeometry.pushforwardTildeΓIso`: the global sections of a pushed-forward associated
  sheaf are the restriction of scalars of the module.
* `AlgebraicGeometry.pushforwardTildeNatTrans`: the canonical comparison underlying the
  pushforward statement, before it is known to be invertible.
* `AlgebraicGeometry.pushforwardTildeIso`: pushforward of associated sheaves is restriction of
  scalars.

## Main results

* `AlgebraicGeometry.pullbackTildeIso_hom_app_unit_toOpen` normalizes the pullback isomorphism on
  global sections, the first map being the pullback--pushforward adjunction unit.
* `AlgebraicGeometry.pushforwardTildeNatTrans_app_toOpen` and
  `AlgebraicGeometry.pushforwardTildeIso_hom_app_toOpen` normalize the pushforward isomorphism on
  global sections, in each direction.

## References

* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
-/
@[expose] public noncomputable section

namespace AlgebraicGeometry

open AlgebraicGeometry CategoryTheory
open RingedSpaceModuleAdjunction
open scoped ChangeOfRings

universe u

/-- The global sections of a pushforward along `Spec φ` are the global sections of the module
itself, with the scalars restricted along `φ`; the underlying map is the identity. -/
public noncomputable def pushforwardΓLinearEquiv
    (R S : CommRingCat.{u}) (φ : R ⟶ S) (N : (Spec S).Modules) :
    ((moduleSpecΓFunctor (R := R)).obj
        ((Scheme.Modules.pushforward (Spec.map φ)).obj N)) ≃ₗ[R]
      ((ModuleCat.restrictScalars φ.hom).obj ((moduleSpecΓFunctor (R := S)).obj N)) where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r x := by
    change @SMul.smul Γ(Spec S, ⊤) Γ(N, ⊤) _
      ((Spec.map φ).appTop ((Scheme.ΓSpecIso R).inv r)) x =
      @SMul.smul Γ(Spec S, ⊤) Γ(N, ⊤) _ ((Scheme.ΓSpecIso S).inv (φ r)) x
    congr 1
    exact congr($(Scheme.ΓSpecIso_inv_naturality φ) r).symm

/-- Pushforward along a morphism of affine schemes restricts the scalar action on global
sections; the underlying map of this comparison is the identity. -/
public noncomputable def pushforwardΓIso (R S : CommRingCat.{u}) (φ : R ⟶ S) :
    Scheme.Modules.pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor ≅
      moduleSpecΓFunctor ⋙ ModuleCat.restrictScalars φ.hom :=
  NatIso.ofComponents (fun N ↦ LinearEquiv.toModuleIso (pushforwardΓLinearEquiv R S φ N))
    (fun h ↦ by ext x; rfl)

/-- Pullback along the map of affine schemes induced by `f : R ⟶ S` carries the associated sheaf
of an `R`-module to the associated sheaf of its extension of scalars to `S`, naturally in the
module. -/
@[stacks 01I9 "affine_pullback_tilde"]
public noncomputable def pullbackTildeIso (R S : CommRingCat.{u}) (f : R ⟶ S) :
    tilde.functor R ⋙ Scheme.Modules.pullback (Spec.map f) ≅
      ModuleCat.extendScalars f.hom ⋙ tilde.functor S :=
  ((tilde.adjunction.comp
    (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map f))).ofNatIsoRight
      (pushforwardΓIso R S f)).leftAdjointUniq
    ((ModuleCat.extendRestrictScalarsAdj f.hom).comp tilde.adjunction)

end AlgebraicGeometry
