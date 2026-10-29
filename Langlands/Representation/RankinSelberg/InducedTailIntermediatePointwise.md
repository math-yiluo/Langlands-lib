# Conditional localized pointwise intermediate-tail comparison

Supporting work by Worker 318 for JPSS section 9.3, printed 456–457.
This module proves assembly lemmas using the independently published
localization theorem. It does not prove the extension theorem, induced
Whittaker type, a quotient integration formula or the final span inclusion.

The first lemma applies a supplied proof of the exact extension proposition
to the literal canonical normalized upper induction, including the two
specified `ULift` conjugations and independent block universes. If the head
rank is `d+c`, the proved full-rank matrix adapter changes the extension
formula into the diagonal lower-chart formula. The coefficient remains in
the actual coefficient image of that same canonical induction. No
Whittaker-type claim about the induced representation is inferred.

The leading rank is `n+1`, the test rank is `n+1+d` with `d>0`, and the
full rank is `n+1+d+c` with `c=c₀+1`. The input is an actual full Whittaker
coefficient with its stated diagonal extension formula, an actual inverse
test coefficient of a smooth representation, and a Schwartz last-row cutoff
which preserves that test coefficient on the identity extension. Full
Whittaker type is an explicit premise. The module imports and applies the
published `lowerBlockWhittakerLocalization` theorem.

Smoothness gives rectangular and lower-triangular neighborhoods on which
the specified test coefficient is unchanged, uniformly in the leading
matrix. The lower-triangular neighborhood is intersected with the actual
determinant-norm-one locus. The published localization theorem then chooses
compact open additive and multiplicative subgroups inside these neighborhoods,
and a new coefficient in the same actual full coefficient image.

On the product of these subgroups, the implemented proof uses the localization
formula, smooth test invariance, the exact rank casts to `appendIdentity`,
invariance of the determinant under reindexing, and determinant norm one.
The cutoff hypothesis removes the last-row factor. The extension
half-modulus, full spectral weight and explicit density `|det g|^(-d)`
combine to the tail spectral weight by the previously proved cancellation
identity. Off the product, the localized full coefficient vanishes.
Together these cases give the complete weighted pointwise equality with
both subgroup indicators. The density is an explicit function in this
identity; no measure change or almost-everywhere claim is inferred from it.

`exists_localized_integrand_comparison` assembles this calculation for the
actual descended full and tail integrands, with the test-to-tail gap written
as `d=k+1`. It takes a diagonal extension for every Schwartz function as its
extension premise. It transports the inverse test coefficient and its smooth
representation along the numerical rank equality, applies the published
last-row cutoff theorem, and uses the proved identity-extension evaluation
to recover a cutoff for the original coefficient. It then chooses the full
extension and applies the preceding localization calculation. The full
integrand uses the transported full coefficient; the tail integrand uses
the original inverse test function recast as standard at `ψ.scale (-1)`,
and the original standard tail function recast as inverse at that character.
The pointwise rank adapters prove their displayed evaluation formulas.
No cutoff-existence or localization premise remains in this wrapper.
Diagonal extension and full Whittaker type are still explicit premises.

The field, full representation and test representation universes are
independent. The constructed coefficient retains actual coefficient-image
membership. No unspecified function or representation identification is
used. The theorem is conditional support for future assembly and supplies
no proof of any of its retained mathematical premises.

Provenance is internal derivation from the published coordinate and
coefficient-model APIs, the published localization theorem and the explicitly
supplied extension hypothesis; the first pointwise lemma also takes a supplied
cutoff, while the actual-integrand wrapper uses the published cutoff theorem.
The motivating original is the registered
`jpss-1983-rankin-selberg`,
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`,
SHA-256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
