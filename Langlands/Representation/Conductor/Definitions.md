# Fixed levels and the newvector construction

For a representation `ρ` of the actual group `GL_(n+1)(F)`,
`levelFixedVectors ρ a` is the accepted project invariant-submodule
construction applied to the concrete subgroup `levelSubgroup F n a`.
Coefficients may lie in an arbitrary commutative ring, independently of
the field and representation-space universes. For the source's
representation theory the coefficient field is the complex numbers.
The level subgroups decrease, so these fixed submodules increase.

`HasNewvectorLevel ρ` means that some such submodule is nonzero.
`IsNewvectorConductor ρ a` says that the level-`a` submodule is nonzero
and every lower level is zero. `newvectorConductor ρ h` is the least
nonzero level, constructed using `Nat.find` from the explicit existence
proof `h`. Its characterization and uniqueness are proved.
`firstFixedLevel ρ : WithTop ℕ` is the corresponding total object:
it equals infinity precisely when no finite nonzero fixed level exists.
There is no default finite exponent in that case.

`newvectorSpace ρ h` is the fixed submodule at the least nonzero level.
`newvector ρ h` chooses an actual nonzero element of that submodule,
with its membership and nonvanishing proved. This submodule is not
called a line without a dimension-one theorem, and this arbitrary
nonzero element is not called the essential Whittaker vector.

For a nonarchimedean local field with its specified valuative topology,
the preceding congruence module supplies an actual open subgroup at
each level. Consequently every level-fixed vector is smooth. An
admissible representation has a finite module at each level, by
applying its accepted all-open-subgroups definition.

Finally, over a field of coefficients, `normalizeFixedVector` rescales
a specified level-fixed vector by the inverse of its value under a
specified linear functional. It requires a proof that this value is
nonzero and returns a fixed vector with functional value one. For an
actual Whittaker model this functional can later be evaluation at the
identity. The constructor neither assumes nor asserts nonvanishing
of that evaluation on an unspecified newvector.

## Source correspondence and outstanding theorem boundary

These are derived constructions from the fixed-level characterization
in H. Jacquet, I. I. Piatetski-Shapiro and J. Shalika, *Conducteur des
representations du groupe lineaire*, Math. Ann. 256 (1981), 199–214,
Section 5.1, page 211, parts (ii)–(iii). The source proves, for
irreducible generic admissible complex representations and an
additive character of conductor the integer ring, that the epsilon
exponent is the least nonzero level and that this first fixed space
has dimension one.

This module does not prove or assume that generic newvector theorem.
Its existence predicate is a visible prerequisite of the finite
constructor; the total `WithTop` object records its failure honestly.
Nor does smoothness alone imply existence of a finite newvector level
in higher rank: these particular subgroups are not a neighborhood
basis of the identity. The nongeneric warning in JPSS Section 5.4,
page 214, gives examples with vanishing fixed spaces at the epsilon
exponent. Accordingly this module does not define the general
representation-side epsilon conductor by the first fixed level.

The source's essential vector is defined in Section 4.4, page 211,
through Theorem 4.1, page 208. Its integral characterization requires
the actual Whittaker models, spherical test family and JPSS integrals.
The original existence proof is erroneous. H. Jacquet's 2012
correction, Theorem 1, page 517 and Sections 1–3, pages 517–523,
supplies the corrected existence argument. Constructing that relation,
proving its existence and uniqueness, and choosing the essential
vector remain distinct outstanding work; the constructions here do
not count as its completion.

Exact sources:

- `jpss-1981-conductor`, SHA256
  `986b06d6c16221fd55f04480604a1b17bf11004a704ab16b78acdd131ae6d49d`,
  Section 5.1, page 211 (PDF page 13), and Section 5.4, page 214.
  Retained PDF:
  `C:/Central-Library/Jacquet-Piatetski-Shapiro-Shalika--Conducteur des representations du groupe lineaire--1981.pdf`.
- `jacquet-2012-conductor-correction`, SHA256
  `98f02c2aef04bff162c1ceb0a42dd122da746d1304a90d82366a848f22713adf`,
  *Pacific Journal of Mathematics* 260 (2012), 515–525,
  Theorem 1, page 517, Sections 1–3 and Remark 1, pages 517–523.
  Retained PDF:
  `C:/Central-Library/Jacquet--A correction to Conducteur des representations du groupe lineaire--2012.pdf`;
  DOI `10.2140/pjm.2012.260.515`.

## Dependencies

The congruence construction is the paired sibling module
`Langlands.Representation.Conductor.Congruence`. The project invariant
submodule and smoothness/admissibility predicates are imported from
`Langlands.Representation.Smooth.Definitions`, accepted published
artifact `665022df-625b-44ae-9dbd-425f6e266bab`, version 1, verified
current in Library `9007729971e6e6ecea63b5567b6d1621769ccfb0`.
Its Lean SHA256 is
`435abfa2c0b05c1b6ea8107e3278687e7091e481540508d6647befc0f515aabb`.

Prepared environment: `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`,
version 1; Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`. Worker 43 authored
this construction. Development compilation does not establish
independent semantic acceptance or Library publication.
