# Evaluating a smoothed distribution after test pushforward

Let \(G\) be a locally compact, totally disconnected Hausdorff topological group
with a Borel measure \(\nu\) finite on compact sets and positive on nonempty open
sets. Let \(p:X\to G\) be a continuous map from a topological space with a measure
\(\mu\), and suppose \(P\) is a test pushforward for \(p\) with these measures.
For any distribution \(D\) on \(G\) and tests \(f\) on \(X\) and \(g\) on \(G\),
`smoothedPushforwardEvaluation` proves
\[
D\big((Pf)*_\nu g\big)=\int_X f(x)\,D(L_{p(x)}g)\,d\mu(x),
\qquad L_a g(z)=g(a^{-1}z).
\]

A shear of the product test exhibits convolution as a partial integral.
The finite-tensor Fubini identity for distributions changes evaluation of this
partial integral into an integral of the translated-test evaluations. Those
evaluations form a locally constant function of the translating element.
On the compact image of the support of \(f\), a target test agrees with that
function. This suffices to apply the pushforward identity because the pushforward
test is supported in the same compact image.

This gives the integration step for compact smoothing in semisimple descent.
See Clozel, *Characters of nonconnected, reductive p-adic groups*, §3.4,
Lemma 5, p. 154.
