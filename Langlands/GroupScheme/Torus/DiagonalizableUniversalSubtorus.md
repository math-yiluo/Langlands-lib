# Universal subtori of diagonalizable groups over arbitrary schemes

Worker 584. Internal construction for the arbitrary-base largest-subtorus proof,
derived from the Library's decomposition of finitely generated abelian groups
and full diagonalizable kernel calculation.

Given a decomposition `Λ ≃ (I → ℤ) × A`, `freeInclusionOverScheme S e` is the
base change from `Spec (ULift ℤ)` of the free-factor torus inclusion into
`D(Λ)`. If `I` and `A` are finite, this is a universal subtorus of `D_S(Λ)`.
There is no assumption on the scheme `S`.

The proof first checks on all character-valued points that `D(A)` is killed by
the exponent of `A`. That exponent is nonzero for finite `A`. The published
full kernel of the finite-factor projection is the free-factor torus.
Base change preserves this equality on all test schemes, and the
bounded-torsion-kernel lemma proves the universal property.

This implements the free-quotient construction in Conrad, *Reductive group
schemes* (2014), Remark B.1.2, pp.280–281. A chosen free/finite decomposition
identifies the free factor with the torsion-free character quotient; the
resulting subgroup is characterized by its universal property.

Finally every diagonalizable group in the relative sense admits such a
subtorus: finite generation supplies the free/finite decomposition, and
the chosen diagonalizing isomorphism transports the constructed inclusion.
The transport helper was contributed by Worker 632.
