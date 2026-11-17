# Exponent weight spaces under a change of coordinate torus

Module `Langlands.GroupScheme.Reductive.AffineSplitRootSpaceTransport`. The statement and its
proof are in namespace `Langlands.GroupScheme`; the lemmas are in namespace
`Langlands.GroupScheme.LocalSplitCell`.

## Statement

`AffineSplitRootSpaceTransportStatement : Prop` (universe `u`) says the following. Let `R` be
any commutative ring and `H` a group scheme over `Spec R` with affine structure map. Let
`i' : 𝔾_m^{I'} → H` be a homomorphism from a coordinate split torus. Let
`e : RootPairing.Equiv P Q` be an equivalence between root data `P` on `I → ℤ` and `Q` on
`I' → ℤ`. Suppose every root space `splitTorus.exponentWeightSpace I' H i' (Q.root α)` is free of
rank one over `R`. Then for every root `α` of `P`, the root space
`splitTorus.exponentWeightSpace I H (precompTorus e.weightEquiv i') (P.root α)` of the
precomposed torus is free of rank one over `R`.

`affineSplitRootSpaceTransport : AffineSplitRootSpaceTransportStatement.{u}` proves it. It is
`nonempty_exponentWeightSpace_precompTorus` below, with the statement's binders.

## Main results

```
theorem exponentWeightSpace_precompTorus (e : (I → ℤ) ≃ₗ[ℤ] (I' → ℤ))
    (i' : splitTorus (Spec (CommRingCat.of R)) I' ⟶ H) (m : I → ℤ) :
    splitTorus.exponentWeightSpace I H (precompTorus e i') m =
      splitTorus.exponentWeightSpace I' H i' (e m)

theorem nonempty_exponentWeightSpace_precompTorus {J J' : Type u}
    {P : RootDatum J (I → ℤ) (I → ℤ)} {Q : RootDatum J' (I' → ℤ) (I' → ℤ)}
    (e : RootPairing.Equiv P Q) (i' : splitTorus (Spec (CommRingCat.of R)) I' ⟶ H)
    (hfree : ∀ α : J', Nonempty
      (splitTorus.exponentWeightSpace I' H i' (Q.root α) ≃ₗ[CommRingCat.of R]
        CommRingCat.of R))
    (α : J) :
    Nonempty (splitTorus.exponentWeightSpace I H (precompTorus e.weightEquiv i') (P.root α)
      ≃ₗ[CommRingCat.of R] CommRingCat.of R)
```

Here `R` is an arbitrary commutative ring, `H` is a group scheme over `Spec R` with affine
structure map, and `i' : 𝔾_m^{I'} → H` is a homomorphism from a coordinate split torus.
`precompTorus e i'` (module `LocalSplitCommonTorus`) is the composite
`𝔾_m^I ≅ 𝔾_m^{I'} → H` of the torus isomorphism `exponentEquivIso e`, which pulls the
character with exponent `e m` back to the character with exponent `m`, with `i'`.
`splitTorus.exponentWeightSpace I H i m` (module `Torus.RelativeAdjointWeights`) is the
submodule of `Lie(H)(R)` on which `Ad(i(t))` acts by the monomial `t^m` for all points `t` over
all `R`-algebras.

`exponentWeightSpace_precompTorus` says that the exponent-`m` weight space of the precomposed
torus is the exponent-`e m` weight space of `i'`.

`nonempty_exponentWeightSpace_precompTorus` applies this to an equivalence of root data
`e : P ≃ Q`. If every root space of `i'` for `Q` is free of rank one, then so is every root
space of `precompTorus e.weightEquiv i'` for `P`. This is the hypothesis of the target
`AffineSplitIsomorphismTheoremStatement` on root spaces, moved along the change of torus
used to reduce the Isomorphism Theorem to the case of a common torus (as in the published
`localSplitIsomorphismTheorem_of_weylRelations`).

## Provenance

Internal lemmas for the proof of `AffineSplitIsomorphismTheoremStatement` (Conrad,
*Reductive group schemes* (2014), Theorem 6.1.17). They record how the weight-space
decomposition of the Lie algebra changes when the torus is reparametrized by a lattice
isomorphism. No external source is formalized here.

## Proofs

`exponentWeightSpace_precompTorus`. Both sides are rewritten as character weight spaces
with `splitTorus.exponentWeightSpace_eq_weightSpace_exponentCharacter`. Let `φ` be the
torus isomorphism `exponentEquivIso e`. By `splitTorus.exponentHom_comp_exponentCharacter`,
`φ ≫ χ_{e m} = χ_m`, so also `φ⁻¹ ≫ χ_m = χ_{e m}`, and `φ⁻¹ ≫ (φ ≫ i') = i'`.
For the two inclusions, test the weight equation of one side at the point `t ≫ φ⁻¹`
(respectively `t ≫ φ`) and use `Lie.characterValue_comp`, which evaluates a pulled-back
character at a point as the original character at the pushed-forward point.

`nonempty_exponentWeightSpace_precompTorus`. By Mathlib's
`RootPairing.Hom.root_weightMap_apply`, `e.weightEquiv (P.root α) = Q.root (e.indexEquiv α)`.
So the root space of `P.root α` for the precomposed torus equals the root space of
`Q.root (e.indexEquiv α)` for `i'`. The required linear equivalence is
`LinearEquiv.ofEq` of this equality followed by the one supplied by `hfree`.
