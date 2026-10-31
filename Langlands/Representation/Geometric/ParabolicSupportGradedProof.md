# Natural graded pieces of the parabolic support-image filtration

`Langlands.Geometric.padicParabolicSupportGradedTheorem.{uF,uV}` proves
exactly the published proposition
`Langlands.Geometric.PadicParabolicSupportGradedTheorem.{uF,uV}`.
Its complete type is that proposition, with independent field and
representation-carrier universes. The statement and its imported definitions
are unchanged.

The theorem retains every prime, actual finite p-adic extension, supplied
compatible topology, positive rank, pair of block shapes, finite enumeration
of minimal permutations, and actual ordered double-coset decomposition with
the prescribed permutation matrices. It uses the supplied source and target
refinements and both full triples of standard-intersection equalities.
The conclusion identifies each successive quotient of the specified
`parabolicJacquetSupportFiltration` with exactly the corresponding
`geometricPieceFunctor`. These are natural isomorphisms on the full category
`SmoothRep.{0,uF,uV} ℂ (B.Levi F.Carrier)`, with target
`Rep.{max uF uV} ℂ (C.Levi F.Carrier)`.

The implemented proof composes published natural comparisons at each original
index `i`. It first installs the field topology, valuative relation, local-field
structure, and the resulting Hausdorff, locally compact, nonarchimedean and
sigma-compact structures on the actual general linear group. Closedness of
the two actual parabolics allows specialization of
`closedSubgroupMackeyFiltration` to the supplied ordering.

Write `J_C` for
`Parabolic.normalizedCoinvariantsFunctor C (T.leviModulus C)`.
The three isomorphisms used in the final composite are as follows.

1. `padicParabolicSupportJacquetComparison` supplies `eJ`, from the actual
   successive quotient of the normalized Jacquet image filtration to the
   corresponding induction-support quotient followed by `J_C`. This published
   result proves the required image and quotient exactness for support
   subspaces stable under the target parabolic.
2. The proof constructs `eSupport` from that induction-support quotient to
   the actual compact orbit functor precomposed with normalized inducing
   covariance. It composes the inverse of
   `parabolicSupportGradedCompactSmoothIso` with the Mackey isomorphism `eM`
   precomposed by `B.smoothInducingFunctor (T.leviHalfCharacter B)`.
   The compact/smooth comparison uses the proved compactness of the actual
   parabolic quotient. The equality `orbitPiece_eq_rawOrbitPiece` forgets the
   already established smoothness of the covariance input. The hypothesis
   `hs i` then rewrites the representative to the permutation matrix of `e i`.
   Precomposition and the graded quotient identifications are definitional.
3. `padicParabolicOrbitJacquetComparison` supplies `eO` for the same minimal
   representative and the supplied refinements. Its source is exactly
   `eSupport`'s target followed by `J_C`, by the definition of
   `parabolicOrbitJacquetFunctor`. Its target is the literal normalized
   `geometricPieceFunctor` required at index `i`.

The closing witness is
`eJ ≪≫ Functor.isoWhiskerRight eSupport J_C ≪≫ eO`.
Whiskering and composition preserve naturality for every source intertwiner.
All support steps, their images, their quotient denominators, and their
indexing are the original ones. The orbit convention is `P_B * w⁻¹ * P_C`,
with inducing covariance conjugated by `w⁻¹`. The local comparison already
cancels the positive induction half modulus against the inverse Jacquet
half modulus and the intermediate correction factors. Its exact target
therefore has no residual character. No comparison theorem remains an
additional premise, and no dimension, admissibility or length restriction
is imposed.

This proof is an internal assembly of the published support/Jacquet exactness,
compact/smooth support transport, closed-subgroup Mackey comparison, and local
normalized orbit comparison. The original mathematical source is Bernstein
and Zelevinsky, *Induced representations of reductive p-adic groups I* (1977),
registered as `bernstein-zelevinsky-1977-induced-i`, SHA-256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
Section 5.2 (printed p.460) allows the supplied orbit ordering;
sections 5.3–5.4 (p.461) describe the support filtration and orbit quotients;
sections 5.5–5.17 (pp.461–467) construct the local comparison; section 6.4
(pp.468–469) cancels its normalizing correction character for the minimal
inverse permutation representatives.

The theorem assumes the ordering, enumeration and intersection refinements
specified by its published target. Their existence and the separate host
geometric lemma are outside this proof's conclusion.
