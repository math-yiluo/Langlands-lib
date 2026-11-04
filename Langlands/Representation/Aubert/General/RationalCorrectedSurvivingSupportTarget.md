# Fixed-order support target for the corrected Aubert filtration

Author: Worker 76. The precise four-field consumer interface and conditional
assembly are due to Worker 969. The source-boundary audit includes Worker 164's
reconciliation and Worker 6's bounded ownership checks.

`RationalCorrectedSurvivingSupportStatement.{u}` in
`Langlands.Aubert.General.RationalPointFamily` is a proposition definition.
`SurvivingSupportTarget` in `Langlands.Aubert.General.CorrectedFiltration` is
its generic proposition template. Neither definition proves its proposition or
asserts a theorem for arbitrary subgroup families.

## Exact assertion

Fix the actual standard rational-point parabolics `P`, the actual torus-point
subgroup `T`, and the root-compatible Coxeter system `cs` of `N_G(T)/Z_G(T)`.
For every `I`, removed-root set `s`, valid list position `j`, and actual
normalizer lift `m` of the inverse of
`w = Support.rankOrderedElement cs.length j hj`, suppose `w` is minimal in the
whole Weyl double coset `W_(S \ s) w W_I`. The conclusion supplies the existing
`SurvivingSupportHypotheses P T cs I s j m`, with exactly these four fields:

- `groupSupport P T cs I s j` is open in the actual rational-point group.
- `groupSupport P T cs I s (j + 1)` is open in that group.
- The upper support is stable under left multiplication by `P_(S \ s)`.
- The upper support minus the lower support equals
  `{p * m⁻¹ * q | p ∈ P_(S \ s), q ∈ P_I}`.

The actual `groupSupport` is the union of `P_empty n P_I` over all normalizer
lifts whose Weyl classes belong to `modifiedSupport cs (S \ s) I j`. This
modified support is the two-sided core of the first `j` entries of the
implemented decreasing-Coxeter-length list. The position, all tie choices,
two-sided core, inverse lift and both consecutive supports are literal existing
Library definitions. Existence of a different open-prefix enumeration does not
meet this statement. The assertion is independent of a representation `E`,
cuspidal support, finite length and coefficient-carrier universes.

The generic template is definitionally the `hsupp` input of
`CorrectedFiltration.correctedGradedTransitionTarget_of_orbitData`. This pair
adds no assertion about the other inputs of that conditional assembly.

## Rational scope and unchanged consumer premises

The rational wrapper repeats the structural and topology premises of
`RationalCorrectedGradedTransitionStatement`: every nonarchimedean local field,
a connected reductive group scheme, an actual maximal split torus and generic
cocharacter, canonical `pointTopology`, and the displayed locally compact,
nonarchimedean and Hausdorff group instances. Its named premises are
`StandardCocharacterStatement`, `StandardParabolicOrderStatement`,
`StandardLeviIntersectionStatement`, relative roots, actual point normalizer
and centralizer comparisons, closed standard radicals and Levis, and their
compact-limit condition. It retains the root-length, positive-simple-reflection
and actual Levi-Weyl comparisons for `cs`.

Some of these shared premises do not occur in the final geometric support
expression. They are retained to make this an exact consumer obligation under
the existing graded-transition signature. They supply no new support,
intersection, modulus, Bruhat-topology or representation-theoretic premise.
The group quotient uses the full torus centralizer, including nonsplit cases.
Positive characteristic, non-quasisplit groups and empty simple-root sets are
included. Only the field universe `u` occurs; there is no representation-carrier
universe parameter in this geometric statement. No existing target or import
is changed.

## Provenance and retained proof work

This is an internal derived prerequisite isolated from the conditional
support-to-grade assembly, not a verbatim statement of a source theorem.
The governing corrected complex is Aubert's 1996 erratum, printed
pp.4687–4688/PDF pp.1–2, with the two-sided support and minimal-double-coset
repair in Ban–Jantzen 2016, Section 4, printed pp.160–162/PDF pp.8–10. Its
translation to the implemented fixed order and actual point topology is a
proof obligation.

Renard 2026 V.4.1–V.4.5, printed pp.118–120/PDF pp.124–126, provides the
structural Bruhat and semistandard double-coset source context. Renard II.3.3,
printed pp.44–45/PDF pp.50–51, supplies an existential open-orbit ordering,
used in VI.5.1, printed pp.161–163/PDF pp.167–169. Those statements do not
alone identify this particular decreasing-length order and its two-sided cores.
The published `notes/aubert/corrected-filtration-topology-audit.md` records the
bounded original-source reading and that distinction. A proof of this target
must establish the actual fixed-order comparison and all four fields rather
than introducing their truth as another allowed external structural input.

The source identities are:

- `aubert-1996-duality-erratum`, SHA-256
  `d76b3ef9ea2310d1a3129da990c1abd6c304027e3e939a5a1f06c666978c145f`.
- `ban-jantzen-2016-duality`, SHA-256
  `7885375b64f6146a16d2b7807447bb913e411bf73735877aca2d62f80dd4dac4`.
- `renard-2026-representations-groupes-reductifs-padiques`, SHA-256
  `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

The existing conditional orbit integral, support-to-grade reduction, rational
assembly and cheap topology adapters stay with Workers 969 and 1255. The
separate general proper-intersection orbit comparison, rational S1/S2,
squared intersection-modulus identity, actual quotient compactness,
full-smooth exactness and terminal comparison remain separate obligations.
This target changes none of their ownership or status. An exact proof successor
can be published after independent acceptance and publication of this pair.
