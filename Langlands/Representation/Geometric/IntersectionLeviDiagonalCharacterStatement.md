# Diagonal determination of intersection-Levi characters

`Langlands.Geometric.IntersectionLeviDiagonalCharacterStatement` is a
Prop-valued definition in
`Langlands.Representation.Geometric.IntersectionLeviDiagonalCharacterStatement`.
It states an internal algebraic reduction for the existing matrix intersection
group. This module supplies the statement, with its proof left to a separate
task.

For every field `F : Type uF` with `CharZero F`, every natural number `n`,
every pair of ordered block shapes `B C : GeneralLinear.BlockShape n`, and every
`w : MinimalRepresentatives B C`, put

```text
g = GeneralLinear.permutation n F w.val,
I = General.intersectionIn (B.leviSubgroup F) (C.leviSubgroup F) g.
```

The published `General.intersectionIn` realizes `I` as a subgroup of
`B.leviSubgroup F`. An element `m : I` has ambient invertible matrix
`m.val.val`, which belongs to the first Levi and satisfies
`g * m.val.val * g⁻¹ ∈ C.leviSubgroup F`. Thus its ambient group is the
actual intersection `M ∩ g⁻¹ N g`, with `M` and `N` the two standard Levi
subgroups.

For every monoid homomorphism `χ : I →* ℂˣ`, the proposition asserts the
following implication. Assume that for every family `t : Fin n → Fˣ` and
every `m : I`, the literal matrix equality

```text
(m.val.val : Matrix (Fin n) (Fin n) F)
  = Matrix.diagonal (fun i => (t i : F))
```

implies `χ m = 1`. Then `χ m = 1` for every `m : I`. The hypothesis tests
the actual ambient matrices of intersection elements against all diagonal
matrices with nonzero entries; it uses no chosen diagonal embedding or
abstract surrogate subgroup.

The field universe `uF` is arbitrary and independent of the fixed complex
codomain. Rank zero is retained. There is no additional restriction on either
block shape beyond the existing `BlockShape` definition, or on the
representative beyond membership in the published `MinimalRepresentatives`.
The character is an arbitrary monoid homomorphism: the statement assumes no
topology, continuity, local constancy, determinant dependence, generation,
decomposition, or character comparison.

This formulation is an internal prerequisite for extending the equality of
actual Haar correction characters from diagonal matrices to the full
intersection Levi in the separate `PadicHaarCorrectionCancellation` proof.
It is not quoted as a theorem of Bernstein--Zelevinsky (1977), and no original
literature result is asserted or proved by this module. Its provenance is the
requested algebraic reduction using the Library's
`GeneralIntersections`, `WeylDefinitions`, and standard block Levi and
permutation constructions. Those published definitions are imported without
modification. The statement itself does not involve Haar measures or assume
the desired correction cancellation.

Author: Worker 165.
