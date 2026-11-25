/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Abelian.Images
import WeilConjectures.AlgebraicGeometry.ClosedImmersionDisjointIdealTwistMono
import WeilConjectures.AlgebraicGeometry.ClosedImmersionDisjointIdealTwistImage

/-! # Restricting a disjoint ideal times an invertible module

Source: Stacks Project, Varieties Remark 09NW and the local trivialization argument in
Lemma 09NX (blueprint: lem-sc-closed-immersion-disjoint-ideal-twist).
-/

@[expose] public section

universe u
open CategoryTheory MonoidalCategory Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- If an ideal has zero intersection with the ideal of a closed immersion, restriction
identifies its product with an invertible module with the product of its image ideal
and the pulled-back module, for every linear tensor-power comparison `e`.

Source: Stacks Project, Varieties Remark 09NW, final sentence, and Lemma 09NX, displayed
conductor equality (blueprint: lem-sc-closed-immersion-disjoint-ideal-twist).

Proof:
1. Put N = M.tensorPow m; this is invertible and hence locally trivial.
First use the canonical tensor-pullback adjunction. On an affine open Spec A where N
is trivial, the closed immersion has ring map A -> B = A/J, and the ideal sheaf I has
sections K. The hypothesis says K intersection J = 0. Multiplication K tensor A -> A
has image K; the adjoint ideal inclusion B tensor K -> B has image KB = (K+J)/J.
Thus restriction of the multiplication images is K -> KB, a surjection with kernel
K intersection J = 0. On opens disjoint from the closed image, J is the unit ideal,
so K = 0 and both sides are zero. Such trivializing affine opens cover the scheme.
2. The local corestrictions are the restrictions of the ambient adjunction unit,
so agree on overlaps because the image inclusions are monomorphisms. They glue to
rho; its compatibility equation follows locally, and it is an isomorphism since
it is an isomorphism on the trivializing affine basis. This is an argument about
sheaves, not a claim that sections commute with tensor products on arbitrary opens.
3. For any other adjunction on the same pullback and pushforward functors, uniqueness
of left adjoints gives a natural isomorphism to the canonical pullback. The adjoint
ideal map changes by precomposition with its component on I, hence has the same
image ideal. Its component on N is linear and invertible, so preserves the product
by that image ideal. Transport rho by this component; the comparison formula for
adjunction units gives the displayed compatibility and preserves IsIso.
4. Evaluating the inverse sheaf morphism on any open gives the inverse of rho.app U,
so these maps are bijective even on non-affine opens. The argument includes I = 0,
J = 0, an empty closed subscheme, m = 0, and empty affine opens. -/
theorem closedImmersion_disjointIdeal_twist {Y X : Scheme.{u}} (i : X ⟶ Y)
    [IsClosedImmersion i] (I : Y.IdealSheafData)
    (hzero : ∀ U : Y.Opens, I.idealOfOpens U ⊓ i.ker.idealOfOpens U = ⊥)
    (M : Y.Modules) [M.IsInvertible] (m : ℕ)
    (e : (tensorPullback i).obj (M.tensorPow m) ≅
      ((tensorPullback i).obj M).tensorPow m) :
    let adj := Classical.choice (nonempty_tensorPullbackAdjunction i)
    let φ := (adj.homEquiv I.toModules (SheafOfModules.unit X.ringCatSheaf)).symm
      (I.toModulesι ≫ SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom)
    let μ := I.toModulesι ▷ M.tensorPow m ≫ (λ_ (M.tensorPow m)).hom
    let μ₁ := image.ι φ ▷ ((tensorPullback i).obj M).tensorPow m ≫
      (λ_ (((tensorPullback i).obj M).tensorPow m)).hom
    ∃ ρ : image μ ⟶ (pushforward i).obj (image μ₁),
      ρ ≫ (pushforward i).map (image.ι μ₁) = image.ι μ ≫ adj.unit.app (M.tensorPow m) ≫
        (pushforward i).map e.hom ∧ ∀ U : Y.Opens, Function.Bijective (ρ.app U) := by
  dsimp only
  let adj := Classical.choice (nonempty_tensorPullbackAdjunction i)
  let φ := (adj.homEquiv I.toModules (SheafOfModules.unit X.ringCatSheaf)).symm
    (I.toModulesι ≫ SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom)
  let μ := I.toModulesι ▷ M.tensorPow m ≫ (λ_ (M.tensorPow m)).hom
  let μ₁ := image.ι φ ▷ ((tensorPullback i).obj M).tensorPow m ≫
    (λ_ (((tensorPullback i).obj M).tensorPow m)).hom
  let a := image.ι μ ≫ adj.unit.app (M.tensorPow m) ≫ (pushforward i).map e.hom
  let b := (pushforward i).map (image.ι μ₁)
  have : Mono (image.ι μ ≫ adj.unit.app (M.tensorPow m)) :=
    closedImmersion_disjointIdeal_twist_mono i I hzero M m
  have : Mono a := by
    dsimp only [a]
    rw [← Category.assoc]
    infer_instance
  have : Mono b := inferInstance
  have h := closedImmersion_disjointIdeal_twist_image i I M m e
  have hab : Subobject.mk a = Subobject.mk b := by
    simpa only [imageSubobject_mono] using h
  let q := Subobject.isoOfMkEqMk a b hab
  refine ⟨q.hom, ?_, ?_⟩
  · change q.hom ≫ b = a
    simp [q]
  · intro U
    exact (appLinearEquivOfIso q U).bijective

end AlgebraicGeometry.Scheme.Modules
