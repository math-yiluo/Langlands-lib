# Compact domination of actual Whittaker coefficients

This is an internal deduction from the published compactness of the rational
upper-unipotent adelic quotient and the bound `norm_whittaker_le`. It asserts
no multiplicity-one conclusion.

For each compact set Q of actual adelic group points, the first theorem chooses
one compact set K before the additive character, rational-invariant function,
or real bound B. A bound by B on K bounds the actual normalized Whittaker
integral at every point of Q. No continuity assumption on the invariant
function is needed for this implication.

The proof uses `LeftCosetSpace.exists_isCompact_cover` to choose a compact
subset of the unipotent group meeting every rational left orbit. The image
of its product with Q under multiplication is compact. Rational invariance
transfers a bound on this image to every unipotent translate of a point of Q.
The published norm bound for the normalized Whittaker integral finishes the
proof. No compactness or continuity property of a chosen quotient section
is asserted or used.

The second theorem maps the compact set into the actual adelic matrix group
via `GeneralLinearGroupPoints.adelicHomeomorph` and applies the first theorem
to the actual cusp functions. Its compact set is uniform over realizations,
characters, and vectors. These are precisely the evaluation functions and
Whittaker coefficients already used in the Library's reconstruction theorem.

This compact domination supplies one step in the intended application of
Shalika's compact Sobolev estimate (1974, Lemma 5.6). It does not establish that
estimate, a comparison of derivative norms, smooth Hilbert continuity,
compatible globalizations, or uniqueness of Whittaker functionals.
