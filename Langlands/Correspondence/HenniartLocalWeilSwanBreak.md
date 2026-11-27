# Swan conductors of local Weil classes from their last breaks

`Langlands.Henniart.LocalNumerical.weilSwanConductor` takes a continuous
irreducible complex Weil class over a nonarchimedean local field in either
characteristic. It is the positive rank times the last upper break, valued
in \(\mathbb R\). The field, its chosen separable closure, and the
representation carrier have independent universes.

`weilSwanConductor_eq_rank_mul_lastBreak` computes this value on any
representative. `weilSwanConductor_eq_presentation` identifies it with the
rational Swan sum, cast to \(\mathbb R\), of every finite inertia presentation
with surjective restriction. The first identity uses invariance of the
last break under an intertwiner. The second applies
`Ramification.Local.weilIrreducibleSwanBreak` and reads the rank from the
isomorphism class.

`hasWeilSwan_iff_eq_weilSwanConductor` identifies the natural exponent \(s\)
of the refined strata with this value. The Artin sum is the Swan sum plus
the codimension of inertia invariants. In the reverse direction continuity
supplies a finite inertia presentation. At a positive last break the upper
fixed space at that break is zero, so the fixed space at upper index zero
is also zero. The tame codimension is then the whole rank \(n\). If \(s\)
is the natural value of the Swan sum, the Artin sum has the natural witness
\(s+n\), and subtracting the rank recovers \(s\). At break zero the Swan sum
vanishes and the tame codimension itself supplies the natural Artin witness.
It is at most the rank, so truncated subtraction gives zero.

`isTrivialAt_iff_of_hasWeilSwan` then says that a representative with
natural Swan exponent \(s\) is trivial on the upper group at \(b>0\)
exactly when \(s<nb\). The strict inequality comes from the positive
threshold theorem for the last break and multiplication by the positive
rank.

The natural subtraction convention comes from Henniart,
`henniart-1988-numerical`, SHA-256
`3de93884b6c4b26106d614e648cfb7f293f9f40a66ef352c0751e222a602f25c`,
§1.2, p. 498. The cutoff is the comparison range of §5.1, p. 512.
The formulas above derive the numerical comparison from the Library's
actual finite inertia and upper-break constructions.

[Local Weil orbit counts](HenniartLocalNumerical.md) ·
[Upper-break comparison](../LocalFactor/Ramification/LocalWeilBreakProof.md) ·
[P-adic exponent comparison](HenniartWeilSwanBreak.md)
