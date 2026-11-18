# The shifted-chamber full constant-term polynomial bound

This internal adapter isolates the estimate used as step (1) in Waldspurger
(2003), Lemma VI.2.3, printed pp.299–300. The registered source is
`waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
The definitions and proofs are derived internal adapters on existing actual
rational-point objects.

`HasRationalConstantTermPolynomialBound` records the full-family polynomial
estimate on a shifted closed chamber required by the actual positive-decay
assembly. `HasRationalXiLeviComparison` records the comparison of the ambient
Xi with the standard-Levi Xi times the constant-term half modulus and a
polynomial height factor on every point of the actual minimal closed chamber.

`minimalLeviSqrtModulus` is the square root of the actual minimal radical
modulus on `M₀(F)`. `standardLeviSqrtModulusOnMinimal` is the square root of
the actual standard-Levi minimal modulus restricted to `M₀(F)`.

The module proves the exact factorization of the positive minimal half modulus
into the norm of the complex constant-term half modulus and the standard-Levi
minimal half modulus. From full-minimal-Levi ambient upper and Levi lower
estimates it derives the Xi comparison. Those estimates are explicit
intermediate premises; the module does not assert that they are already
proved on the full minimal Levi in the Library.

The threshold adapter takes the actual equality between the original function
and the half-modulus times its full constant term, a common original Xi bound,
and the Xi comparison. It takes norms of the equality, applies the two bounds,
and cancels the strictly positive half-modulus norm. All family parameters and
all points of the shifted closed chamber remain in the result.

The exact upper Xi target is owned by Task 5326 and remains unproved at the
time this supporting unit was written. Extending its uniformizer-chamber scope and the published
lower bound to the full minimal-Levi chamber is a separate remaining comparison
obligation. This adapter is supporting progress and does not prove the final
orbit-decay theorem.

The comparisons retain all supplied actual Iwasawa and compact data, the
connected-reductive/maximal-split/generic data, and `J` inside the simple roots
for the modulus-factorization proof. No chamber is replaced by a strict chamber
or by a lattice section in these statements. The threshold and original
function families have an arbitrary independent parameter universe.
