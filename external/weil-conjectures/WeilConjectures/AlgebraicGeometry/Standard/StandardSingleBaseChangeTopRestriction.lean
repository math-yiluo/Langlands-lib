/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Standard.StandardSingleBaseChangeMap
import WeilConjectures.AlgebraicGeometry.Standard.StandardSingleBaseChangeTopRestrictionAux

/-! # Removing a redundant top-open restriction from the single comparison

Source: Stacks Project, Tags 08HY and 0D5S.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- The canonical single-module comparison is compatible with the top-open isomorphism.
Source: Stacks Project, Tag 08HY, counit description of base change, and Tag 0D5S,
composition of derived pullback.
(blueprint: lem-pc-standard-single-base-change-top-restriction).

Proof: Write j for the top-open inclusion of Y and N for its restriction of M.
Restriction along j is an exact equivalence. The canonical single pullback map for j,
followed by the single image of the adjoint-uniqueness isomorphism from tensor
pullback to restriction, is therefore an isomorphism Lj*(M[0]) = N[0]. The unit of
Lj* adjoint to Rj_* is also invertible. Apply Rp_* to their composite, then the
right-adjoint mate of derived pullback composition for j and p. This gives e on
B, before applying Lg*: its image under Lg* must be used in the equation.

The pullback universal property gives an isomorphism from the pullback of j;p and g
to the pullback of p and g. Tensor pullback composition and its comparison with
restriction identify the two pulled-back modules. The same derived unit and
composition construction on this isomorphism gives t in the indicated direction.
Transpose the claimed equality under the second-projection derived adjunction.
Expand standardSingleBaseChangeMap as the derived mate followed by the single
pullback counit. Naturality moves the source unit past the mate. The composition
counit equation for single pullback identifies the coefficient arrows. Associativity
of the pinned derived composition comparisons identifies the two pullback paths;
the adjunction triangle identities cancel the units. The resulting transposes are
equal, hence so are the original arrows. Every comparison used is canonical; the
argument does not invert g's counit, assume relative flatness, or choose a complex.
It applies to empty schemes and zero modules since all steps are functorial
isomorphisms and adjunction identities. -/
theorem standardSingleBaseChange_topRestriction_comparison
    {Y B A : Scheme.{u}} (p : Y ⟶ B) (M : Y.Modules) (g : A ⟶ B) :
    letI := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))
    let j := (⊤ : Y.Opens).ι
    let N := M.restrict j
    ∃ (e : (schemeDerivedDirectImage p).obj
          ((DerivedCategory.singleFunctor _ 0).obj M) ≅
        (schemeDerivedDirectImage (j ≫ p)).obj
          ((DerivedCategory.singleFunctor _ 0).obj N))
      (t : (schemeDerivedDirectImage (pullback.snd (j ≫ p) g)).obj
          ((DerivedCategory.singleFunctor _ 0).obj
            (Scheme.Modules.tensorPullbackObj (pullback.fst (j ≫ p) g) N)) ≅
        (schemeDerivedDirectImage (pullback.snd p g)).obj
          ((DerivedCategory.singleFunctor _ 0).obj
            (Scheme.Modules.tensorPullbackObj (pullback.fst p g) M))),
      standardSingleBaseChangeMap p M g =
        (derivedPullback g).map e.hom ≫
          standardSingleBaseChangeMap (j ≫ p) N g ≫ t.hom := by
  dsimp
  let e := standardSingleBaseChange_topRestriction_sourceIso p M
  exact ⟨e, standardSingleBaseChange_topRestriction_compatibility p M g e rfl⟩

end AlgebraicGeometry
