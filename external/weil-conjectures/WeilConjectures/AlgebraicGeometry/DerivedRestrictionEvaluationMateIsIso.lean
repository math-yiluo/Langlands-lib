/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CanonicalDerivedTensorHom
import WeilConjectures.AlgebraicGeometry.DerivedRestrictionEvaluationMatePostcompBijective

/-! # Invertibility of the restricted evaluation mate
Source: Stacks Project, Tags 08DJ, 08DL and 08BS.
(blueprint: lem-sc-derived-restriction-evaluation-mate-is-iso).
-/

@[expose] public section

set_option autoImplicit false
universe uX wD
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
namespace AlgebraicGeometry.Scheme

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

/-- Currying restricted evaluation gives an isomorphism for any natural tensor comparison.
Source: Stacks Project, Tags 08DJ and 08DL; Tag 08BS (exact extension by zero).
(blueprint: lem-sc-derived-restriction-evaluation-mate-is-iso).

Proof: let J be derived extension by zero from U. It is exact, left adjoint to
restriction R, and its unit A -> R(J(A)) is invertible. The counit J(R(B)) -> B
is invertible precisely on complexes supported on U. Tensoring a complex
supported on U with any complex is again supported on U: outside U its stalk
complex is acyclic, and a K-flat representative computes the tensor stalkwise.
For a test object A on U, the adjoint of
  A tensor R(L) -> R(J(A)) tensor R(L) -> R(J(A) tensor L),
where the second arrow is the inverse tensor comparison, is consequently an
isomorphism J(A tensor R(L)) -> J(A) tensor L. Indeed its restriction is the
composite of the tensor comparison inverse and the unit, both invertible, and
both objects are supported on U, where restriction reflects isomorphisms.
For f : A -> R(H(L,E)), let q : J(A) -> H(L,E) be its adjoint. Under the
adjunction and tensor-Hom bijections, precomposition by that tensor isomorphism
sends f to the transpose of
  (unit_A tensor identity); t(J(A),L).inv; R(e_X(q)).
Tensor-Hom naturality writes e_X(q) as (q tensor identity); e_X(identity).
Naturality of t for (q, identity) moves R(q tensor identity) past t.inv, and
the adjunction identity unit_A; R(q) = f then gives
  (f tensor identity); t(H(L,E),L).inv; R(e_X(identity)).
By the definition of the displayed mate and tensor-Hom naturality on U, this
is e_U(f; mate). Hence postcomposition by the mate is a composite of bijections:
the adjunction inverse, e_X, precomposition by the tensor isomorphism, the
adjunction forward and e_U inverse. It is bijective for every A. Yoneda proves
that the mate is invertible.
This argument allows arbitrary natural tensor comparisons; it needs neither a
unit coherence axiom nor a particular choice on K-flat representatives. For
the empty open all objects are zero and the same adjunction argument applies. -/
theorem derivedRestriction_evaluationMate_isIso
    (X : Scheme.{uX}) (U : X.Opens)
    [HasDerivedCategory.{wD} (SheafOfModules.{uX} (moduleRings X.toRingedSpace))]
    [∀ V : X.Opens,
      HasDerivedCategory.{wD} (SheafOfModules.{uX} ((moduleRings X.toRingedSpace).over V))]
    [HasDerivedCategory.{wD} (SheafOfModules.{uX} (moduleRings U.toScheme.toRingedSpace))] :
    let R := ((SheafOfModules.overFunctor.{uX} (moduleRings X.toRingedSpace) U) ⋙
      Equivalence.functor
        (C := SheafOfModules.{uX} ((moduleRings X.toRingedSpace).over U))
        (D := SheafOfModules.{uX} (moduleRings U.toScheme.toRingedSpace))
        (Modules.overEquiv U)).mapDerivedCategory
    let H := derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
      X.toRingedSpace.sheaf
    ∀ (t : ∀ K L : schemeDerivedCategory X, R.obj (K ⊗ L) ≅ R.obj K ⊗ R.obj L),
      (∀ K K' L L' (a : K ⟶ K') (b : L ⟶ L'),
        R.map (a ⊗ₘ b) ≫ (t K' L').hom =
          (t K L).hom ≫ (R.map a ⊗ₘ R.map b)) →
      ∀ L E, IsIso ((schemeDerivedTensorHomEquiv U.toScheme
        (R.obj (H.obj (op L, E))) (R.obj L) (R.obj E)).symm
          ((t (H.obj (op L, E)) L).inv ≫
            R.map (schemeDerivedTensorHomEquiv X (H.obj (op L, E)) L E (𝟙 _)))) :=
  by
    dsimp
    intro t ht L E
    apply isIso_of_yoneda_map_bijective
    intro A
    exact derivedRestriction_evaluationMate_postcomp_bijective X U t ht L E A

end AlgebraicGeometry.Scheme
