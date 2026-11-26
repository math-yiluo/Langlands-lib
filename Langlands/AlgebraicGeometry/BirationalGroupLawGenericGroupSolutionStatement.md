# Birational group laws that are group laws on the generic fibre

The module `Langlands.AlgebraicGeometry.BirationalGroupLawGenericGroupSolutionStatement`
states the last assertion of Bosch, Lütkebohmert and Raynaud, *Néron Models* (1990), §5.1
Theorem 5, printed p. 114 (literature ID `bosch-lutkebohmert-raynaud-1990-neron-models`,
file SHA-256 `16d0701b4192ae9db91d083c1df69c0492b00a994aee7bcb0abca365d859d529`; printed
page `p` is PDF page `p + 7`), in the form proved there from the existence of a solution.
The module states a proposition and proves nothing.

## The proposition

`BirationalGroupLawGenericGroupSolutionStatement.{u}` quantifies over a discrete valuation
ring `R` in universe `u`, a scheme `X` and `f : X ⟶ Spec R` which is smooth, separated,
locally of finite type, quasi-compact and surjective, and a representative
`m : BirationalGroupLaw f` of an `R`-birational group law (module
`Langlands.AlgebraicGeometry.BirationalGroupLaw`). It assumes

1. every point `p` of `X ×_R X` lying over the generic point of `Spec R` (its image is not
   the closed point) lies in `m.domain`, in the image of the universal left translation of
   `m` and in the image of the universal right translation of `m`;
2. `Nonempty m.Solution`: `m` has a solution.

It asserts that there is a solution `σ : m.Solution` with `σ.domain = ⊤`.

Hypothesis 1 is word for word the hypothesis of the second clause of
`Langlands.AlgebraicGeometry.BirationalGroupLawSolutionStatement`, and the conclusion is that
clause's conclusion; the Markdown of that module explains why hypothesis 1 expresses that the
generic fibre `X_K` is a group scheme under `m_K`.

## Correspondence with the source

BLR 5.1/5 ends: "If (in the case where the base `S` consists of a valuation ring) the generic
fibre `X_K` of `X` is a group scheme under the law `m_K`, the above assertion is true for
`X' = X`." Its proof (printed p. 114) starts from a solution `X' ↪ X̄`, whose existence is the
first assertion of 5.1/5:

- by uniqueness of solutions over `K` (5.1/3) the rational map `τ : X ⇢ X̄` induced by
  `X' ⊆ X` restricts to an isomorphism `X_K ≅ X̄_K`, so `τ` is defined in codimension at
  most 1, hence everywhere by Weil's extension theorem 4.4/1 (printed p. 109);
- the pull-back by `τ` of a generator of the top differential forms of `X̄` generates them
  on `X' ∪ X_K`, hence in codimension at most 1, hence everywhere, so `τ` is étale (2.2/10);
- being birational, `τ` is an open immersion by Zariski's Main Theorem (2.3/2').

The proposition takes the existence of a solution as hypothesis 2, as this proof does.

- Only the discrete valuation ring case is stated, as in BLR.
- Smooth, separated, faithfully flat and of finite type: `Smooth` gives flatness,
  `Surjective` gives faithful flatness, and `LocallyOfFiniteType` with `QuasiCompact` is
  finite type.
- `σ.domain = ⊤` is BLR's `X' = X`: the whole of `X` embeds as an `R`-dense open subscheme
  of the group, and the group law restricts to `m`.

## Use

With the existence of solutions this gives the second clause of
`Langlands.AlgebraicGeometry.BirationalGroupLawSolutionStatement`.
