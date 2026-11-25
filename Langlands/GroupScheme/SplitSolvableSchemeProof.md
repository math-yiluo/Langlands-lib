# A split solvable group is affine space times a split torus

`Langlands.GroupScheme.splitSolvableSchemeProductStatement.{u}` proves exactly
the published proposition
`Langlands.GroupScheme.SplitSolvableSchemeProductStatement.{u}` from
[`SplitSolvableSchemeStatement`](SplitSolvableSchemeStatement.md), with no
additional hypotheses. Let k be a field and G a split solvable group over
`Spec k`. Let i : U ⟶ G be a closed unipotent subgroup with normal range, and
q : G ⟶ D an fppf quotient by range i onto a group of multiplicative type. Then
for some r and m: U.X ≅ 𝔸^r over `Spec k`, D ≅ G_m^m as group schemes, and
G.X ≅ 𝔸^r ⊗ (G_m^m).X over `Spec k`.

## Source

J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite Type over
a Field* (Cambridge University Press, 2017), source ID
`milne-2017-algebraic-groups`, Corollary 16.56, printed p.344 (one-based PDF
p.360). The statement Markdown records the correspondence between Milne's
corollary and the Lean statement.

## Proof

The proof is one term. It combines two theorems:

- `SplitSolvableCanonical.canonicalExtension_split`, from
  [`SplitSolvableCanonicalExtension`](SplitSolvableCanonicalExtension.md): for a
  split solvable G and data (U, D, i, q) as above, U is split unipotent and D is
  a split torus. It is proved by induction on the length of the series of G.
- `SplitSolvableScheme.splitSolvableSchemeProduct_of_split`, from
  [`SplitSolvableSchemeFromCanonical`](SplitSolvableSchemeFromCanonical.md):
  that conclusion, for all fields and all such data, implies the target. It
  follows Milne's route: the quotient map has a section (16.55(b)), which splits
  G.X as U.X ⊗ D.X, then U.X ≅ 𝔸^r (14.66), and D is reindexed to
  `splitTorus (Spec k) (ULift (Fin m))`.

The first theorem is passed to the second as its hypothesis. The normality
hypothesis of the statement is not needed by either.
