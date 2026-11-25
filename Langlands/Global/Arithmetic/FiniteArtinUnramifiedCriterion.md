# Finite Artin ramification criterion on local units

`Langlands.Global.FiniteArtinUnramifiedCriterionStatement` concerns a
continuous surjection from the actual idele-class group to a finite abelian
Galois group with `HasArithmeticArtinNormalization`. If the image of the
local integral unit group at `v` is trivial, then the extension is
unramified at every prime of the upper field above `v`. The unit group is
formed in the actual completion, and the map to idele classes is
`finiteClassInclusion`.

## Source and proof route

The assertion uses the local-global Artin square in Milne, *Class Field
Theory*, v4.03, Chapter V §5, Proposition 5.2 and Theorem 5.3, pp. 178–179, together with
the local reciprocity law in Chapter I §1, Theorem 1.1, p. 20. Serre, *Abelian l-Adic
Representations and Elliptic Curves*, Chapter II §2.3, p. II-12, uses the
image of the local units in inertia for the unramified part of the avatar
construction. This target states the direction required after choosing the
finite class field of a character kernel. Inversion of the Artin map preserves
the subgroup image.

For the canonical finite Artin map, the image of local units is the inertia
group by the local-global square and local reciprocity. For a supplied
normalized map, identify it with the canonical map by almost-everywhere
Frobenius uniqueness. That uniqueness argument, using closed subgroup density
and finiteness of the ramified places, is
`Langlands.ClassFieldTheory.Global.Artin.eq_of_hasArithmeticArtinNormalization`
(module `Langlands.ClassFieldTheory.Global.Artin.ArtinUniqueness`). The
criterion extracts the specific implication from the full inertia image
formula. It is a separate premise from the normalization in
`FiniteAbelianClassFieldExistenceStatement`, which assumes unramifiedness at
the place where it prescribes the image of a uniformizer.

Milne source ID `milne-2020-class-field-theory` (SHA-256
`50d79af78250a9f1117ad9d337e0b231704a533fc707966ed1bfa52e13d498f5`).
Serre source ID `serre-abelian-l-adic-1989` (SHA-256
`971dbfdd4414d99ea21d7d0af63dbb790d7b1188e9aec37f422181a2b543dec4`).

## Proof

The statement is proved in
[`FiniteArtinUnramifiedCriterionProof`](FiniteArtinUnramifiedCriterionProof.md)
(`Langlands.Global.finiteArtinUnramifiedCriterion`).
