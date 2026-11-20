# Extracting transverse derivatives of smooth product tests

For open sets \(U\subset E\) and \(V\subset W\) in real normed spaces,
`transverseProductJetCLM i` sends an \(F\)-valued smooth compactly supported
test on \(U\times V\) to a test on \(U\) valued in continuous
\(i\)-multilinear maps \(W^i\to F\). Its value at \(x\) on a tuple \(v\)
is the iterated Fréchet derivative at \((x,0)\) evaluated on the directions
\((0,v_k)\). The multilinear maps so obtained are symmetric, by symmetry
of iterated derivatives of smooth functions.

The construction iterates Mathlib's continuous derivative of tests and
uncurries after each step. Restriction to the zero section has support in
the preimage of the original compact support under \(x\mapsto(x,0)\).
This preimage is compact because the zero section is a closed embedding.
The inclusion has operator norm at most one, so the linear chain rule
bounds each fixed-support seminorm of the restriction by the original
seminorm of the same order. The universal property of the test topology
gives continuity on the full test space. Precomposition of the
multilinear values with the normal inclusion is continuous and gives
the displayed evaluation formula.

This internal construction provides continuous coefficient maps for
studying distributions supported on a zero section.
