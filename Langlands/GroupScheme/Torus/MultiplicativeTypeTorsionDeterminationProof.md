# Proof: groups of multiplicative type are determined by their torsion subgroups

`Langlands.GroupScheme.multiplicativeTypeTorsionDetermination` proves
`Langlands.GroupScheme.MultiplicativeTypeTorsionDeterminationStatement.{u}` (SGA 3, Exposé IX,
Corollaires 4.8 a), 4.8 b) and 4.9) for every universe `u`, every scheme `S` and all groups,
homomorphisms and subgroups as in the statement, with no extra hypotheses. The statement and
its notation are explained in
[`MultiplicativeTypeTorsionDeterminationStatement`](MultiplicativeTypeTorsionDeterminationStatement.md).

The theorem is a single application:
`TorsionDetermination.statement_of_diagonalizableCoreCase` (module `Reduction`) turns the
core case for the group-algebra models into the statement. The core case is
`TorsionDetermination.isIso_left_of_diagonalizable` (module `Diagonalizable`), whose type is
exactly the hypothesis `DiagonalizableCoreCase.{u}`. The immersion hypothesis enters that
lemma as an instance argument, so the proof term first puts it into the local context.

## Structure of the proof

The whole proof rests on one lemma. Call an immersion `j : Z ⟶ G.X.left` into a group
scheme *torsion-closed* if the points of `G` that factor through `j` are closed under
multiplication and include every point `x` with `x ^ n = 1`, `n > 0`. The lemma says that
every torsion-closed immersion into a group of multiplicative type is an isomorphism.

1. **Assembly** ([`TorsionDetermination/Assembly`](TorsionDetermination/Assembly.md)).
   The three parts of the statement follow from the lemma
   (`statement_of_torsionClosedImmersionIsIso`):
   - 4.9 applies it to the subgroup `h` itself;
   - 4.8 b) applies it to the intersection `H₁ ∩ H₂`, a pullback, as a subscheme of `H₁`,
     and symmetrically of `H₂`;
   - 4.8 a) applies it to the equalizer of `u` and `v` as a subscheme of `H`.
2. **Transport and descent** ([`TorsionDetermination/Descent`](TorsionDetermination/Descent.md)).
   Being torsion-closed is preserved by pullback along homomorphisms and by base change.
   The existence of a lift of the identity point through a monomorphism descends along fppf
   covers, because the fppf topology is subcanonical.
3. **Reduction** ([`TorsionDetermination/Reduction`](TorsionDetermination/Reduction.md)).
   Using the fppf cover in the definition of `IsMultiplicativeType` and then affine open
   covers, the lemma reduces to the group-algebra models `Diagonalizable.groupScheme R Λ =
   Spec R[Λ]` over affine bases `Spec R`, with `Λ` finitely generated. The proof transports
   along the isomorphisms `diagonalizableBaseChangeIso` and
   `Diagonalizable.relativeModelIso`.
4. **Core case** ([`TorsionDetermination/Diagonalizable`](TorsionDetermination/Diagonalizable.md),
   with [`TorsionDetermination/Algebra`](TorsionDetermination/Algebra.md) and
   [`TorsionDetermination/FieldPointLift`](TorsionDetermination/FieldPointLift.md)).
   This is `isIso_left_of_diagonalizable`: a torsion-closed immersion into `Spec R[Λ]` is an
   isomorphism. It first shows that the immersion is surjective. Over every field, torsion
   points are dense in a split torus, and a twisting argument handles the remaining
   characters. Then the immersion is a closed immersion into an affine scheme. It is
   injective on global sections, since torsion characters `R[Λ] → R[Λ/nΛ]` detect every
   nonzero element.

## Modules

All helper declarations are in the namespace `Langlands.GroupScheme.TorsionDetermination`.

- `Langlands.GroupScheme.Torus.TorsionDetermination.Descent`
- `Langlands.GroupScheme.Torus.TorsionDetermination.Assembly`
- `Langlands.GroupScheme.Torus.TorsionDetermination.Reduction`
- `Langlands.GroupScheme.Torus.TorsionDetermination.Algebra`
- `Langlands.GroupScheme.Torus.TorsionDetermination.FieldPointLift`
- `Langlands.GroupScheme.Torus.TorsionDetermination.Diagonalizable`
- `Langlands.GroupScheme.Torus.MultiplicativeTypeTorsionDeterminationProof` (this module)

## Relation to the source

SGA 3, Exposé IX (Gille–Polo recomposed edition, registered as
`sga3-expose-ix-gille-polo-2009`), p.47–48 (margin 57–58). SGA 3 deduces 4.9 from the density
theorem 4.7 (the torsion subgroups `ₙG` are schematically dense in `G`), together with the
fact that subgroup schemes over a field are closed. It reduces 4.8 b) to 4.9 via
`H₁ ∩ H₂`, and 4.8 a) to 4.8 b) via graphs. The proof here follows the same reductions for
4.8 b). For 4.8 a) it uses the equalizer instead of the graphs. It does not prove 4.7 as
stated. The core case instead proves the two density facts it needs, for the fibres over
fields and for the coordinate ring `R[Λ]`. Like SGA 3's proof of 4.7, it reaches the
diagonalizable case by faithfully flat descent.
