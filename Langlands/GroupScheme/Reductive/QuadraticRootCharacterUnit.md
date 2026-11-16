# Root-character units from quadratic units

This internal calculation uses the published fixed-exponent character and cocharacter maps and the global-function interpretation of multiplicative-group points. It applies over any commutative ring and on every test scheme, with no nontriviality, reducedness, affineness of the test, or characteristic premise.

For an integral vector `nu` and a global unit `tau` on the test, `torusPoint` is the inverse multiplicative-group point equivalence applied to `tau`, followed by the actual cocharacter with vector `nu`. Evaluating the actual character with vector `a` gives `tau` raised to the integer dot product of `a` and `nu`.

If that dot product is two and the underlying function satisfies `tau² - 1 = tau`, the root-character value minus one equals `tau` and is therefore a unit. The dot-product equation is an explicit premise; the calculation does not derive it from root-datum or fibre hypotheses. In particular the proof also applies over the zero ring. This supplies the elementary character calculation needed when applying a quadratic fppf-cover construction to relative root-group commutators.
