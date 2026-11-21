# Pointwise exhaustion by Arthur truncation on a regular ray

`Langlands.Global.ArthurTruncation.TruncationRayStatement` is a consequence
of `TruncationFinitenessStatement` for the actual adelic `truncation` of
`ArthurTruncation.lean`. It uses the same number field, connected reductive
group, maximal split torus, generic cocharacter, reflection data, compact
subgroup Iwasawa for the minimal parabolic, and bijective character restriction.
Let `v` be a real cocharacter direction on which all simple relative roots
are strictly positive. For any complex function `φ` invariant under left
translation by `G(F)`, and for each fixed `x ∈ G(𝔸_F)`, there is a threshold
beyond which `truncation (n • v) φ x = φ x` for every natural `n`.
`cocharacter_simple_pos` verifies the direction condition for the real image
of the chosen generic cocharacter, with the positive-root convention of the
Library. With no simple roots the condition is vacuous.

## Provenance and scope

Derived from the truncation formula in §2, p. 312, of E. Lapid, *On Arthur's
asymptotic inner product formula of truncated Eisenstein series*, Clay Math.
Proc. 13 (2011), pp. 309–331 (PDF p. 321 in the source registered as
`lapid-2011-asymptotic-inner-product-truncated-eisenstein`). The proof of
Lemma 9, p. 327 (PDF p. 336), uses a stronger identity, uniform on specified
Siegel regions. The present proof uses finiteness at parameter zero to obtain
eventual equality at each point instead. This suffices for almost-everywhere
convergence in the measure-theoretic `TruncationPairingLimitStatement`: apply
the pointwise result to each chosen representative `y.out` of the rational
quotient. The threshold may depend on `x`. There is no assertion here of the
uniform Siegel-region identity, square integrability, agreement with Hilbert
space projections, or a formula for the limit of truncated pairings.

## Implemented proof

- `fullWeight_pos_of_simple_pos` identifies the full weights with
  `ArthurCombinatorics.weightCoordinate` on the coroot span via
  `ArthurRelative.weight_coe`. Projection to this span leaves root evaluations
  unchanged. The inverse-Cartan positivity lemma `weightCoordinate_pos` then
  gives strict positivity of each full fundamental weight on `v`.
- `ArthurRelative.tauHat_eq` tests positivity of the full weights indexed by
  the simple roots missing from the parabolic. At parameter `n • v`, each such
  test subtracts a nonnegative multiple of a positive weight from the
  original evaluation. Thus every coset where the cutoff is nonzero already
  belongs to the finite support at parameter zero. For a proper parabolic,
  choose one missing simple root. For each coset in that finite support, its
  weight evaluation is eventually nonpositive as `n` increases. Taking the
  finite intersection over cosets, then over proper standard parabolics,
  makes all proper-parabolic summands vanish.
- The parabolic for the full simple-root set represents `G`, so its rational
  coset space has one element. Its unipotent subgroup is trivial, so the
  constant-term integral against normalized quotient Haar is the value of
  `φ` itself. The sign and the cutoff are both `1`. The one coset
  representative acts trivially on `φ` by left rational invariance.

`truncationRay` proves the statement with finiteness as an explicit premise;
it does not prove cutoff finiteness. No growth or measurability assumption on
`φ` is needed for this pointwise identity.
