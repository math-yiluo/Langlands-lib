# Rational points of algebraic spaces form a small type

Author: Worker 78.

The rational points `X(K)` of an algebraic space over `Spec K` are sections of a presheaf with
values in `Type (u + 1)`. This module proves `RingPointsSmall.small_ringPoints`: if `X` is
quasi-separated and has an étale surjective atlas `a : h_U ⟶ X` from an affine scheme `U`, then
`RingPoints K X K` is `u`-small. The result is auxiliary, with internal provenance; it allows
ultrafilters on `X(K)` to be indexed by a type in the universe `u`, as the ultrapower
construction requires.

## Proof

`Index K` is the `u`-small type of pairs `(n, I)` with `I` an ideal of
`MvPolynomial (Fin n) K`, and `Alg j` the quotient algebra. For each `x ∈ X(K)` the Library's
`ProductPointsLocalLift.exists_fibre_point` gives a finite separable field extension `L/K` and
a point `ū ∈ U(L)` with `a(ū) = x|_L`. The two `K`-algebra structures on `L` it provides
coincide (by the scalar tower condition), so `L` is a finitely generated `K`-algebra, hence
isomorphic to some `Alg (n, I)`. Transporting `ū` gives a code `(j, u)` with `u ∈ U(Alg j)`,
`Alg j` a nonzero finite-dimensional `K`-algebra and `a(u) = x|_{Alg j}`. The map `x ↦ (j, u)`
lands in a `u`-small type and is injective: if two points have the same code, their
restrictions to `Alg j` agree, and restriction along `Spec (Alg j) → Spec K` is injective
because this morphism is flat, locally of finite presentation and surjective (a finite free
algebra of positive rank, `ProductPointsDescent.spec_properties`) and `X` is an fppf sheaf
(`ProductPointsDescent.pullback_injective`).
