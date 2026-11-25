# Statement: a clopen diagonalizable lift over a strictly Henselian base

`Langlands.GroupScheme.MultiplicativeTypeStrictHenselianLiftStatement.{u}` is a
statement-only, `Prop`-valued definition of an intermediate lifting result in
the proof of Conrad's fibral criterion. It is a prerequisite for
`MultiplicativeTypeFibralCriterionStatement`; this file contains no proof.

For every commutative Henselian local ring `A` with separably closed residue
field `k`, let `H` be a flat, locally finitely presented affine group scheme over
`Spec A`. Assume that every geometric fibre of `H` has multiplicative type in
the Library's field-level sense. For every finitely generated abelian group
`M` and every given isomorphism
`e : (D_A(M))_k ≅ H_k`, the proposition asserts the existence of a group-scheme
homomorphism `j : D_A(M) → H` whose special fibre is exactly `e.hom` and whose
underlying scheme map is both an open immersion and a closed immersion.

Here `D_A(M)` is `RelativeMultiplicativeType.diagonalizable (Spec A) M`, and
special fibres use `Spec.algebraMap A (IsLocalRing.ResidueField A)`. The input
isomorphism uses the actual base change of `D_A(M)`, so no choice of
base-change comparison is implicit in the equality of special-fibre maps.
All rings, schemes and character groups are in universe `u`. The ring need not
be Noetherian or complete, `H` need not be smooth or commutative, and `M` may
have torsion. The conclusion does not say that `j` is surjective.

## Source and extraction

Brian Conrad, *Reductive group schemes* (2014), registered source
`conrad-2014-reductive-group-schemes`, SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`,
proof of Theorem B.4.1, printed pp.298–299 (one-based PDF pages 298–299).

On p.298 the proof reduces to `S = Spec A` with `A` strictly Henselian, chooses
an isomorphism `j_k : D_k(M) ≅ H_k`, and claims that it lifts to an open and
closed immersion `j : D_A(M) → H`. The rest of pp.298–299 constructs this lift:
pass to a Noetherian approximation, lift over the completion using Theorem
B.3.2, and descend by comparing restrictions to finite torsion subgroups.
The source then proves surjectivity separately using either connected fibres
or locally constant torsion orders; neither argument is part of this statement.

This is an extracted intermediate assertion, with the diagonalization of the
special fibre supplied as input. The source discusses weakening the lifting
input to multiplicative type of the special fibre alone, but its subsequent
power-map argument on p.298 explicitly uses multiplicative type of every fibre.
The present statement retains the all-geometric-fibres hypothesis already
available in the fibral criterion. It does not assert that stronger
special-fibre-only variant. As noted at the start of the source's §B.4 on
p.297, using geometric fibres or residue-field fibres for the
multiplicative-type condition is equivalent.

The three morphism hypotheses are the Library encoding of the source's fppf
affine group. `HenselianLocalRing A` together with
`IsSepClosed (IsLocalRing.ResidueField A)` encodes the strictly Henselian local
base. Requiring the lifted special-fibre map to equal the prescribed `e.hom`
expresses the source's lifting of the chosen `j_k`.
