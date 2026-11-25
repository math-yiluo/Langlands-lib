/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMaps
public import Mathlib.AlgebraicGeometry.OpenImmersion
import WeilConjectures.AlgebraicGeometry.Open.OpenRestrictionCompactSupportCube
import WeilConjectures.SixFunctors.Etale.Derived.ClopenTransfer

/-! # Restriction of the canonical exceptional base-change mate

Source: blueprint `proposition-exceptional-inverse-image-smooth-morphism--6`, coherences (i) and
(iii).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

attribute [local irreducible] openRestrictionGraphIso openRestrictionCompactSupportIso

set_option maxRecDepth 100000

/-- Restriction to an open of the original base preserves the canonical base-change square.
Source: blueprint `proposition-exceptional-inverse-image-smooth-morphism--6`, proof, coherences (i)
and (iii).

Proof: write D(T) for the ordinary unbounded etale derived category, L for exact
inverse image, F for compact support, and R for its right adjoint. Restrict the chosen
compactification of f along j, and base change that diagram along c. Proper exchange
and degreewise open-extension exchange give the two compact-support maps. Compare
compactifications by the graph-factorization construction of unbounded compact-support
composition; this requires no quasi-compactness of f or p. Normalize those comparisons
by the identity on the source open. Their cocycle law
and horizontal proper-exchange pasting identify the two maps on the cube.

The open-composition identification j! Fp = Ff a! is obtained on the same diagram:
proper/open interchange moves j! through the proper factor, and composition combines
the two open extensions. Taking right adjoints gives an isomorphism
lambda_f : La* Rf = Rp Lj*. Construct lambda_f' in the same way. These constructions
use exact extension by zero for j and a and do not require those opens to be
quasi-compact. Unlike the named exceptional base-change maps, they do not use a
chosen compact-support comparison for j or a.

Transpose the cube equation under the exceptional adjunctions, using the counit
equation defining the mate. With sigma : La'* Lg'* = Lb* La* from w and
tau : Lc* Lj* = Lj'* Lg* from sqj, the resulting equation at K is

  La'* beta(f,g)_K ; lambda_f'(Lg* K)
    = sigma(Rf K) ; Lb*(lambda_f(K)) ; beta(p,c)_(Lj* K) ; Rp'(tau(K)).

Here semicolons mean composition from left to right. This equality follows from
injectivity of the adjunction Hom bijection: after applying Fp' and composing with
its counit, both sides are inverse compact-support exchange followed by the pullback
of the same original counit. Naturality moves the open-composition comparisons past
that counit; their intermediate factors cancel by the cocycle identity above.
All factors other than beta(p,c) are isomorphisms. The hypothesis makes that last
factor invertible as well, and cancellation with lambda_f' proves the claim.
Only f' and p' must be quasi-compact, to type the two named base-change maps. Empty
schemes, the zero coefficient ring, identity restrictions, and arbitrary unbounded K
are covered by the same identities.
(blueprint: lem-asd-exceptional-base-change-open-restriction) -/
theorem isIso_leftDerivedUpperStar_map_baseChange_of_open_restriction
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y X' Y' U V U' V' : Scheme.{u}}
    {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
    [HasCompactification f] [HasCompactification f'] [QuasiCompact f']
    (sq : IsPullback g' f' f g)
    {j : U ⟶ Y} [IsOpenImmersion j] {a : V ⟶ X} {p : V ⟶ U}
    (sqU : IsPullback a p f j) [HasCompactification p]
    {c : U' ⟶ U} {j' : U' ⟶ Y'} (sqj : IsPullback c j' j g)
    {b : V' ⟶ V} {p' : V' ⟶ U'} (sq' : IsPullback b p' p c)
    [HasCompactification p'] [QuasiCompact p']
    {a' : V' ⟶ X'} (sqV : IsPullback a' p' f' j')
    (w : b ≫ a = a' ≫ g')
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (h : IsIso ((rightDerivedUpperShriekBaseChangeMap Λ sq').app
      ((L((j)^*[ModuleCat.{u + 1} Λ])).obj K))) :
    IsIso ((L((a')^*[ModuleCat.{u + 1} Λ])).map
      ((rightDerivedUpperShriekBaseChangeMap Λ sq).app K)) := by
  have : IsOpenImmersion a := MorphismProperty.of_isPullback sqU.flip inferInstance
  have : IsOpenImmersion j' := MorphismProperty.of_isPullback sqj inferInstance
  have : IsOpenImmersion a' := MorphismProperty.of_isPullback sqV.flip inferInstance
  have sqA : IsPullback b a' a g' := by
    apply IsPullback.of_bot (t := sq) _ w
    have outer := sq'.paste_vert sqj
    simpa only [← sqU.w, ← sqV.w] using outer
  let A := ModuleCat.{u + 1} Λ
  let af := rightDerivedUpperShriekAdjunction Λ f
  let ap := rightDerivedUpperShriekAdjunction Λ p
  let af' := rightDerivedUpperShriekAdjunction Λ f'
  let ap' := rightDerivedUpperShriekAdjunction Λ p'
  let aj := derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ j
  let aa := derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ a
  let aj' := derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ j'
  let aa' := derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ a'
  have hc := mateEquiv_whiskerTop_conjugateEquiv
    (aa.comp af) (ap.comp aj) (aa'.comp af') (ap'.comp aj')
    (openRestrictionCompactSupportIso Λ sqU).hom
    (openRestrictionCompactSupportIso Λ sqV).hom _ _
    (openRestrictionCompactSupport_cube Λ sq sqU sqj sq' sqV sqA)
  rw [mateEquiv_hcomp, mateEquiv_hcomp] at hc
  dsimp only [aa, aa', aj, aj'] at hc
  rw [mateEquiv_derivedOpenImmersionLowerShriekBaseChangeIso,
    mateEquiv_derivedOpenImmersionLowerShriekBaseChangeIso] at hc
  have hk := congrArg (fun t ↦ t.app K) hc
  dsimp only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.hComp,
    TwoSquare.mk, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.comp_obj] at hk
  simp only [Category.id_comp, Category.comp_id, Category.assoc] at hk
  change (L((b)^*[A])).map ((openRestrictionExceptionalIso Λ sqU).hom.app K) ≫
      (rightDerivedUpperShriekBaseChangeMap Λ sq').app ((L((j)^*[A])).obj K) ≫
      (R(p')^![Λ]).map ((derivedSquareUpperStarIso A sqj.toCommSq).inv.app K) =
    (derivedSquareUpperStarIso A sqA.toCommSq).inv.app ((R(f)^![Λ]).obj K) ≫
      (L((a')^*[A])).map ((rightDerivedUpperShriekBaseChangeMap Λ sq).app K) ≫
      (openRestrictionExceptionalIso Λ sqV).hom.app ((L((g)^*[A])).obj K) at hk
  have hiso : IsIso ((derivedSquareUpperStarIso A sqA.toCommSq).inv.app
      ((R(f)^![Λ]).obj K) ≫
      (L((a')^*[A])).map ((rightDerivedUpperShriekBaseChangeMap Λ sq).app K) ≫
      (openRestrictionExceptionalIso Λ sqV).hom.app ((L((g)^*[A])).obj K)) := by
    rw [← hk]
    infer_instance
  exact (isIso_comp_right_iff _ _).mp ((isIso_comp_left_iff _ _).mp hiso)

end AlgebraicGeometry.Etale
