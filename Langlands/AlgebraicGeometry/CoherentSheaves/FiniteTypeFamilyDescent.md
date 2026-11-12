# Descent of actual coherent families to finite-type affine bases

Module: `Langlands.AlgebraicGeometry.CoherentSheaves.FiniteTypeFamilyDescent`.

Author: Worker 3694, for task `5b9ad399-34f2-4314-bb39-902f491aad01`.

This internal result combines two published noetherian-approximation theorems:
descent of finite presentation
(`NoetherianApproximation.finitePresentationModuleSubalgebraDescent`) and descent
of relative flatness (`NoetherianApproximation.isFlatOverSubalgebraDescent`). It
is the coherent-family analogue of the published line-bundle descent
`Picard.PicardGroupoid.exists_affineFamily_subalgebra`. Mathematically it is
the existence half of limit preservation of the stack of coherent sheaves
(Stacks Project, Lemma 99.5.6), for an algebra written as the union of its
finitely generated subalgebras; it is proved here from the published descent
theorems, not from that lemma. All schemes and rings are in one universe `u`.

## Families from Cartesian models

Namespace `CoherentSheaves.FamilyDescent`. Fix `f : X ⟶ S` and a test
`B : Over S`. Let `h : IsPullback p₀ a₀ B.hom f` be a Cartesian square with
`p₀ : Y₀ ⟶ B.left` and `a₀ : Y₀ ⟶ X`. Let `M₀` be a locally finitely presented
module on `Y₀` that is flat over `p₀`.

`familyOfModel f h M₀ hflat` is the actual family over `B` whose underlying module
is the ordinary pullback of `M₀` along the inverse of `h.isoPullback`, the
canonical isomorphism from `Y₀` to the relative space `B.left ×_S X`
(`familyOfModel_obj`, by `rfl`). Finite presentation is preserved by pullback
(published `isFinitePresentation_pullback`). Flatness over the relative
projection follows from the published `isFlatOver_pullback_of_isPullback`,
applied to the square with the isomorphism on top and the identity at the bottom.

## Descent to a finite-type base

Let `k` be a noetherian commutative ring and `g : X ⟶ Spec k` a morphism that is
quasi-compact, separated and locally of finite type.

`exists_finiteType_model g M`: for every commutative `k`-algebra `A` and every
actual family `M` over the published affine test `Picard.affineBase k A`, there
are

- a commutative `k`-algebra `B` of finite type over `k`,
- a `k`-algebra map `φ : B →ₐ[k] A`,
- an actual family `M₀` over `Picard.affineBase k B`,

and an actual isomorphism, in the family groupoid, from the ordinary pullback of
`M₀` along the published test map `Picard.affineBaseMap φ` to `M`.

Proof. Write `ι_A` for the structure map of `Spec A`. The relative space of
`A` is a Cartesian model of `X ×_k Spec A`.

1. Finite presentation descent gives a finitely generated `k`-subalgebra
   `T₄ ⊆ A` and a finitely presented module `M₄` on `X ×_k Spec T₄`. Its pullback
   along the canonical comparison `a₄` from the relative space of `A` is
   isomorphic to the module of `M`. The published
   `NoetherianReduction.exists_isPullback_subalgebra` supplies `a₄` and the
   Cartesian square over `Spec T₄ ← Spec A`. The ring `T₄` is noetherian and of
   finite type over `k`.
2. The pullback of `M₄` along `a₄` is flat over `Spec A`, since it is
   isomorphic to `M`. Flatness descent over the noetherian base `T₄` gives a
   finitely generated `T₄`-subalgebra `T₅ ⊆ A`. The pullback of `M₄` to every
   Cartesian base change along `Spec T₅ → Spec T₄` is flat over `Spec T₅`.
3. Give `T₅` the `k`-algebra structure through `T₄`. It is of finite type over `k`
   by transitivity, and its inclusion into `A` is a `k`-algebra map `φ`.
4. Pasting the defining pullback squares of `X ×_k Spec T₄` and
   `(X ×_k Spec T₄) ×_{T₄} Spec T₅` gives a Cartesian model of
   `X ×_k Spec T₅`. The pullback of `M₄` to this model is finitely presented and,
   by step 2, flat. `familyOfModel` turns it into the family `M₀`.
5. Both composite projections show that the induced map from the relative space
   of `A`, through the model, to `X ×_k Spec T₄` equals `a₄`. The required
   isomorphism composes the published pullback composition and congruence
   isomorphisms with the isomorphism of step 1.
