# Congruence-quotient compatibility and the integral avatar

For the actual completion `L_λ`, write `O_λ` for its completed integer ring
and `𝔪_λ` for its maximal ideal. `CompletionUnitQuotient λ n` is the units
of `O_λ / 𝔪_λ^(n+1)` with the discrete topology. Its finiteness follows
from compactness and openness of the ideal power. `completionUnitReduction`
is the continuous map on units induced by the quotient, and
`completionUnitTransition` uses the canonical quotient map from a higher
power to a lower power. Their compatibility is proved on the underlying
quotient rings.

`HeckeAvatarInverseLimitStatement` assumes unique geometric lifts with the
same finite exceptional set at every reduction of an integral idele-class
character. It asserts coherence of those finite characters under the
actual transition maps and gives an actual continuous character of the
absolute Galois group into the completed integer units. Its reductions
are the specified finite characters, and the integral character satisfies
the same inertia and geometric Frobenius comparison at every good place.

## Source and proof route

This is a finite-level implementation of Serre, *Abelian l-Adic
Representations and Elliptic Curves*, Chapter II §2.3, pp. II-11–II-12, and
§2.5, pp. II-18–II-20. Serre uses the abelian Galois quotient directly.
Here the uniqueness of each finite lift gives compatibility under all
reductions of its coefficients, with one fixed good-place set. This needs
no tower compatibility for newly chosen class fields. It uses the proved
compatibility of transitions with reduction, and the fact that the
matching predicate is preserved by postcomposition.

For the limit, use `Langlands.ClassField.Global.isAdicComplete_adicCompletionIntegers`
and the identification of an adically complete ring with its compatible
residue sequences. Passing to units uses the compatible sequences of
values and of their inverses. The completed integer units are compact
since the integer ring is compact Hausdorff and multiplication is
continuous. Joint injectivity of the reductions gives a topological
embedding into the product of finite discrete groups by compactness.
Thus the map reconstructed from the continuous finite characters is
continuous. Joint injectivity also gives both good-place identities from
all the congruences. Composing with the continuous
inclusion of completed integer units gives a character into `L_λ^×`.

Source ID `serre-abelian-l-adic-1989` (SHA-256
`971dbfdd4414d99ea21d7d0af63dbb790d7b1188e9aec37f422181a2b543dec4`).
