# Proof: unirationality of connected group varieties

Worker 5705, with Worker 295 (author of the reduction this proof applies).

`Langlands.GroupScheme.connectedGroupUnirationality` proves exactly
`Langlands.GroupScheme.ConnectedGroupUnirationalityStatement.{u}`, in every
universe `u` and with no additional hypotheses. For every field `k` and every
group scheme `G` over `Spec k`:

1. if `k` is perfect and `G` is smooth, affine and connected over `k`, then
   `IsUnirational k G.X`;
2. if `IsConnectedReductive G`, then `IsUnirational k G.X`, for every field
   `k`, including finite and imperfect fields.

The statement's Lean and Markdown files, and the files they import, are imported
unchanged from the Library.

## The Lean proof

The proof is one term. It applies three published theorems:

- `connectedGroupUnirationalityReduction`
  (module [`Rational.ConnectedGroupUnirationalityReduction`](ConnectedGroupUnirationalityReduction.md))
  proves `ConnectedGroupUnirationalityReductionStatement.{u}`
  (module [`Rational.ConnectedGroupUnirationalityReductionStatement`](ConnectedGroupUnirationalityReductionStatement.md)),
  the implication
  `TorusUnirationalityStatement.{u} → SplitUnipotentAffineSpaceStatement.{u} →
  ConnectedGroupUnirationalityStatement.{u}`;
- `torusUnirationality`
  (module [`Torus.TorusUnirationalityProof`](../Torus/TorusUnirationalityProof.md))
  proves `TorusUnirationalityStatement.{u}`, whose second part makes every torus
  over every field unirational;
- `splitUnipotentAffineSpaceStatement`
  (module [`Unipotent.SplitAffineSpaceProof`](../Unipotent/SplitAffineSpaceProof.md))
  proves `SplitUnipotentAffineSpaceStatement.{u}`: an affine group over a field
  with a split series of length `n` is isomorphic to affine `n`-space over that
  field.

Applying the reduction to the two premise proofs, in this order, gives the
target. All three theorems are used at the same universe `u` as the target.

## Route of the reduction

The reduction's own Markdown gives the details; in outline:

- **Reductive groups over infinite fields.** The published torus domination
  theorem gives a torus with a dense-image morphism to `G`; the torus is
  unirational, and unirationality passes along dense-image morphisms.
- **Reductive groups over finite fields.** `G` is quasi-split. A cocharacter
  of a maximal split torus whose centralizer is a torus gives an open
  immersion from the product of two split unipotent contracting subgroups and
  that torus into `G`. Split unipotent groups are affine spaces, hence
  unirational; products of unirational schemes are unirational; an open
  immersion from a nonempty source into the irreducible group `G` has dense
  image.
- **Smooth connected affine groups over perfect fields.** Over a perfect field
  the unipotent radical `U` is split unipotent and the quotient `G/U` is
  connected reductive, hence unirational by the previous two cases. Torsors
  under split unipotent groups over affine bases have sections, so the
  quotient map `G → G/U` has a scheme section `σ : G/U → G`, and
  `(u, x) ↦ u σ(x)` is a surjective morphism `U × G/U → G` from a unirational
  scheme.

Milne proves Theorem 17.93 through Cartan subgroups (Corollary 17.92 and
17.84); this proof does not use Cartan subgroups. For part 1 it follows the
quotient route indicated in Milne's Remark 17.94(a).

## Source

James S. Milne, *Algebraic Groups* (2017), registered source
`milne-2017-algebraic-groups`: Theorem 17.93, printed p.382 (the statement
proved here) and Remark 17.94(a), also printed p.382 (the quotient route for
part 1).
The registered official errata snapshot
`milne-2017-algebraic-groups-errata-2026-11-02` has no correction to 17.93 or
17.94.
