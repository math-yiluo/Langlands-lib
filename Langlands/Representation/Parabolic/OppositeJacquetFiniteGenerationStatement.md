# Finite generation of normalized opposite Jacquet modules

Author: Worker 319. The statement form is adapted from Worker 186's published
upper Jacquet statement; Worker 23 specified the bundled opposite target.

The closed proposition
`Langlands.Parabolic.OppositeJacquetFiniteGenerationStatement.{uF,uV}`
states finite generation of the actual normalized opposite Jacquet module
over the complex group algebra of its block Levi. This pair defines the
proposition. Its proof is a separate obligation.

## Exact statement

For every prime `p` through `[Fact p.Prime]`, every finite extension
`F : PadicField.{uF} p`, every compatible `T : F.TopologicalData`, every
natural rank `n`, and every `B : GeneralLinear.BlockShape n`, install
`T.topology`. For each bundled complex representation
`A : Rep.{uV} ℂ (GeneralLinear n F.Carrier)`, assume

```text
IsSmooth A.ρ
Module.Finite (MonoidAlgebra ℂ (GeneralLinear n F.Carrier)) A.ρ.asModule.
```

The conclusion is exactly

```text
Module.Finite (MonoidAlgebra ℂ (B.Levi F.Carrier))
  (CuspidalJacquetMultiplicity.oppositeJacquet T B A).ρ.asModule.
```

Thus finitely many vectors generate under the complex linear combinations
of group translates. The assertion does not require finite dimension over
`ℂ`. The field universe `uF` and representation-carrier universe `uV` are
independent. The representation carrier may be zero, and the rank may be
zero. There is no admissibility, irreducibility, finite length, central
character, chosen generating set, or finite-generation premise for a
restriction.

The hypotheses and conclusion mirror
`Langlands.Parabolic.NormalizedJacquetFiniteGenerationStatement` from
`Langlands.Representation.Parabolic.JacquetFiniteGenerationStatement`,
with the input bundled as `Rep` to use the existing opposite construction.

## Actual opposite quotient and normalization

The target uses the published
`CuspidalJacquetMultiplicity.oppositeJacquet` from
`Langlands.Representation.Classification.CuspidalJacquetMultiplicityStatement`.
Its underlying space is the quotient of the carrier of `A` by the complex
span of

```text
A.ρ(u) v - v,  u ∈ B.oppositeUnipotentSubgroup F.Carrier.
```

The action is induced by the actual embedded block Levi and transported to
the actual product Levi `B.Levi F.Carrier` through `B.leviEquiv`. If `δ_B`
is the published upper block modulus `T.leviModulus B`, the construction
passes its inverse to `Jacquet.normalizedActionOfModulus`. Consequently
the action is

```text
m · [v] = δ_B(m)^(1/2) [A.ρ(B.leviEmbedding F.Carrier m) v].
```

This is the inverse half of the opposite modulus. The quotient is by the
opposite radical itself. The construction is the same bundled object used
by the Library's dual Jacquet exponents and maximal-cone Jacquet quotient
statement.

## Source and derived specialization

The original source read for this pair is W. Casselman, *Introduction to
the theory of admissible representations of p-adic reductive groups*,
draft of 1 May 1995, §3.2, Proposition 3.2.1 and the quotient construction,
printed/PDF pp.33–34, and Theorem 3.3.1 with its finite-generation proof,
printed/PDF p.35. Theorem 3.3.1 and its proof were also checked in the page
image.

Registered source: `casselman-1995-admissible-representations`, SHA256
`78b921fc6331ad2b75389f37d15bd5ac3399e6cfc2d7555e1a4d666e0d42612a`.
The retained original is
`/home/taskhub/central-library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Introduction to the theory of admissible representations of p-adic reductive groups--1995.pdf`.
No source-specific errata file was present in the project notes, current
Library notes, or literature collection.

Casselman's theorem applies to every parabolic `P = MN` of a reductive
p-adic group and states separate finite-generation and admissibility
implications for the unnormalized Jacquet module. This proposition takes
the finite-generation implication for `GL_n(F)` and the opposite block
parabolic. That subgroup is a parabolic in its own right: conjugation by
`B.reverseMatrix` maps the upper parabolic for `B.reverse` onto the opposite
parabolic for `B`. The published
`GeneralLinear.BlockShape.reverseMatrix_conj_mem_oppositeParabolic_iff`
and `GeneralLinear.BlockShape.reverse_unipotentSubgroup_map_conj` in
`Langlands.Group.GL.ReverseBlocks` identify the parabolics and radicals.
The opposite specialization therefore falls within the source theorem.

The finite-generation argument chooses a finite generating set `X`, a
compact open subgroup `K` fixing `X`, and a finite set `Γ` with
`P Γ K = G`. The images of `A.ρ(γ)x` generate the unipotent quotient under
the Levi action. This uses smoothness and finite generation; the source's
separate admissibility implication supplies no premise here.

Passing to the normalized action is an elementary derived step: every
normalizing character value is a nonzero complex scalar, so twisting does
not change the complex span of the translates of any set. Transport along
the product-Levi isomorphism also preserves this span. Neither step is a
separate assertion quoted from Theorem 3.3.1.

The all-rank formulation includes an elementary extension to rank zero
under the Library conventions. The unique block shape has no blocks,
`GL_0` and its Levi are trivial, the opposite radical is trivial, and the
empty-product modulus is one. The quotient and its action identify with
the original trivial-group representation, preserving finite generation.

## Proof boundary

The only new Lean declaration is the closed `Prop`-valued definition
above. This pair proves neither finite generation nor admissibility of
the opposite quotient. The proof successor must prove this exact
proposition in both independent universes, retaining all ranks and the
published opposite normalization.
