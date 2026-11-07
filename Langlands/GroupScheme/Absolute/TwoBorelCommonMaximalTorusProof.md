# A common ambient maximal torus of two Borel subgroups

Workers 1458 and 1440.

`Langlands.GroupScheme.twoBorelCommonMaximalTorus.{u}` proves the unchanged
[`TwoBorelCommonMaximalTorusStatement.{u}`](TwoBorelCommonMaximalTorusStatement.md).
For every algebraically closed field `k : Type u`, every actual connected
reductive group scheme `G` over `k`, and any two Borel embeddings
`i : B ⟶ G` and `i' : B' ⟶ G`, it gives a commutative group scheme `T`,
an ambient maximal-torus embedding `t : T.toGrp ⟶ G`, and actual
homomorphisms `f : T.toGrp ⟶ B` and `f' : T.toGrp ⟶ B'` with
`f ≫ i = t` and `f' ≫ i' = t`. The universe is arbitrary, the characteristic
is unrestricted, and there is no additional hypothesis.

The proof applies the published
`twoBorelCommonMaximalTorusStatement_of_borel_bruhat_inputs` from
[`TwoBorelCommonMaximalTorusReduction`](TwoBorelCommonMaximalTorusReduction.md)
to the independently proved universal statements
`borelConjugacy` from [`BorelConjugacyProof`](BorelConjugacyProof.md) and
`absoluteBruhatCovering` from [`BruhatCoveringProof`](BruhatCoveringProof.md),
all at the same universe `u`. This discharges both premises of the reduction.

The reduction first chooses an ambient maximal torus in `B`, conjugates
`B` to `B'`, and factors the conjugating point as `i(b₁) · n · i(b₂)`,
where `n` normalizes that torus. The published
`commonTorusOfNormalizerDoubleCoset` constructs the required ambient torus
and its two factorization maps from these data. Thus the conclusion gives
equalities of group-scheme morphisms, with their full all-test meaning.

The contribution is an internal assembly of these Library results.
The original common-torus assertion is Borel–Tits, *Groupes réductifs*
(1965), registered source `borel-tits-1965-groupes-reductifs`, §2.4,
printed p.65 / one-based PDF p.12; its correspondence is documented in the
unchanged statement pair.

The imported proofs establish Borel conjugacy and absolute geometric Bruhat
covering independently of the downstream rational Bruhat decomposition,
Borel–Tits 1965 Proposition 4.18, and the two parabolic-intersection results.
The complete transitive project import closure contains neither
`ParabolicIntersectionGeometryStatement` nor
`ParabolicIntersectionTorusStatement`, nor a use of rational Bruhat.
The rational Bruhat proposition definitions in `Rational.Statement` are
unused elsewhere in this closure. No forbidden downstream result is used
directly or indirectly.
