# Generic nonzero morphisms between inductions sharing a standard Levi

Authors: Worker 194 and Worker 192.

`rationalSameLeviGenericNonzeroIntertwiner` proves
`Langlands.Aubert.General.RationalPointFamily.RationalSameLeviGenericNonzeroIntertwinerStatement.{u, v}`
(module `Aubert.General.RationalSameLeviGenericIntertwinerStatement`), with exactly
that type and no extra hypotheses.

Take a connected reductive group over a nonarchimedean local field, a generic
cocharacter, root subsets `I, J`, and a point `g` with `x ∈ L_J ↔ g⁻¹ x g ∈ L_I`. Let
`σ` be an irreducible admissible smooth complex representation of the literal Levi
`L_J`. Then there is a nonzero polynomial in the published unramified coordinates of
`L_J` such that, for every unramified character `χ` in its principal open, some
morphism from the normalized induction of `σ.twist χ` along `P_J` to the conjugate
induction along `g P_I g⁻¹` is nonzero.

## Proof

The proof is the composition of two results.

1. `RepresentedParabolic.representedSameLeviGenericNonzeroIntertwiner` (module
   `Aubert.General.RepresentedSameLeviGenericIntertwinerProof`, by Worker 192) proves
   the version for actual represented parabolics `P = MN` and `Q = MU` with one Levi
   scheme. It follows Renard, *Représentations des groupes réductifs p-adiques*,
   VII.3: generic `PQ`-regularity of the twist, then the algebraic intertwiner of
   VII.3.4. No analytic continuation of intertwining integrals is used. Its Markdown
   lists its helper modules.
2. `rationalSameLeviGenericNonzeroIntertwiner_of_represented` (module
   `Aubert.General.RationalSameLeviGenericIntertwinerReduction`, by Worker 194)
   derives the target from the represented version. It realizes `P_J` as the standard
   represented parabolic and `g P_I g⁻¹` as the standard represented parabolic `P_I`
   composed with the inner automorphism of `g`. The shared Levi scheme is `L_J`,
   embedded in the second parabolic through a scheme isomorphism `L_J ≅ L_I` obtained
   from equality of rational points. The reduction then identifies both represented
   inductions with the literal normalized inductions, and the principal open loci
   through the published character homeomorphism.

The proof does not use a same-Levi isomorphism theorem, equality of induced
Grothendieck classes, composition-factor identities or Weyl-conjugacy results for
Grothendieck classes.

## Files of this proof

New modules, each with its Markdown:

- `Aubert.General.RationalSameLeviGenericIntertwinerProof` (this file) and
  `Aubert.General.RationalSameLeviGenericIntertwinerReduction`, by Worker 194.
- `Aubert.General.RepresentedSameLeviGenericIntertwinerProof`,
  `Aubert.General.RepresentedSameLeviGenericRegularity`,
  `Aubert.General.RepresentedSameLeviRegularIntertwiner`,
  `Aubert.General.SameLeviPieceDisplacementStatement`,
  `Aubert.General.SameLeviPieceDisplacementProof`,
  `LanglandsClassification.SimpleCorootFaceExistence`,
  `Intertwining.CentralActionQuotientFiniteness` and
  `Intertwining.PieceActionQuotientFiniteness`, by Worker 192.
- `Plancherel.UnramifiedMonomialSeparation`, by Worker 194.

The represented interface `RepresentedSameLeviGenericNonzeroIntertwinerStatement`
(module `Aubert.General.RepresentedSameLeviGenericIntertwinerStatement`) is already
in the Library.
