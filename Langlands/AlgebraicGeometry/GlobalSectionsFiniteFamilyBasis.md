# A finite family of global sections over a field through a linearly independent family

Author: Worker 1076. The statement was specified by Worker 1412.

Let `k : Type u` be a field, `X : Scheme.{u}` a scheme and
`c : X ⟶ Spec (CommRingCat.of k)` a morphism. The ring `Γ(X, ⊤)` of global
sections is a `k`-algebra through the instance
`AlgebraicGeometry.Scheme.TwoAffineOpenCover.algebraOfHom c ⊤` from the Library
module `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover`.
Its algebra map sends `r : k` to `(c.appLE ⊤ ⊤ le_top) ((Scheme.ΓSpecIso (CommRingCat.of k)).inv r)`.

The module contains the following, in the namespace `Langlands.AlgebraicGeometry`.

- `appLE_top_top`: `c.appLE ⊤ ⊤ le_top = c.appTop`.
- `globalScalars c : k →+* Γ(X, ⊤)` (definition): the inverse of
  `Scheme.ΓSpecIso (CommRingCat.of k)` followed by `c.appTop`. The lemma
  `globalScalars_apply` states
  `globalScalars c r = c.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv r)`.
- `algebraMap_algebraOfHom_top`: the algebra map of the instance
  `algebraOfHom c ⊤` is `globalScalars c`.
- `exists_linearIndependent_sum_appTop_mul`: let `C` be a finite type in any
  universe and `w : C → Γ(X, ⊤)`. Then there exist a natural number `m`, a
  family `e : Fin m → Γ(X, ⊤)` that is linearly independent over `k` for the
  algebra structure `algebraOfHom c ⊤`, and coefficients `r : C → Fin m → k`
  such that for every `κ : C`

  `w κ = ∑ l, c.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv (r κ l)) * e l`.

None of these needs a hypothesis on `X` or `c`. For an object
`H : Over (Spec (CommRingCat.of k))` the last theorem applies with
`c = H.hom` and `X = H.left`.

## Provenance

This is standard linear algebra, written for schemes over a field, and is used
as an internal helper. In the proof of the Library statement
`Langlands.GroupScheme.AutomorphicAction.AffineFiniteTypeCocycleModelStatement`
(task `909c8ce9`), `X` is a group scheme over a field `k`. There the theorem
supplies a family of global sections, linearly independent over `k`, through
which finitely many given global sections are expressed. The coefficients are
stated with `c.appTop` and `Scheme.ΓSpecIso` so that they match the
coordinates used elsewhere in that proof.

## Proof

`appLE_top_top` unfolds `Scheme.Hom.appLE` to `c.app ⊤` followed by the
restriction of `X` from `⊤` to `⊤`. `simp` turns this restriction into the
identity, and `Category.comp_id` finishes. `globalScalars_apply` holds by
definition. `algebraMap_algebraOfHom_top` is checked on each `r : k`: the
Library lemma `algebraMap_algebraOfHom` and `appLE_top_top` reduce both sides
to the same element.

For the main theorem, work with the algebra instance `algebraOfHom c ⊤`. The
span `V` of the range of `w` is finite-dimensional, because the range is finite
(`FiniteDimensional.span_of_finite`). Take `m = finrank k V` and Mathlib's
basis `Module.finBasis k V`, and let `e l` be the image in `Γ(X, ⊤)` of its
`l`-th vector. The family `e` is linearly independent because the inclusion of
`V` is injective (`LinearIndependent.map'`). The coefficients `r κ l` are the
coordinates of `w κ ∈ V` in this basis. The displayed identity is the basis
expansion `Basis.sum_repr`. Each scalar multiple is written as a product with
the algebra map (`Algebra.smul_def`). The algebra map is then rewritten by
`algebraMap_algebraOfHom_top` and `globalScalars_apply`.

The same linear algebra in a general `k`-algebra is
`Langlands.LinearAlgebra.exists_linearIndependent_sum_algebraMap_mul`, in a
separate helper candidate. This module does not import it, so that the two
helper candidates do not depend on each other.
