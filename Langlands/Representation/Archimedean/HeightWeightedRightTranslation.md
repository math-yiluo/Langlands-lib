# Height-weighted right translation on continuous functions

Let `A` be a normed ring. On the complex Banach space of continuous functions on the unit group that vanish at infinity, `HeightWeightedRightTranslation.representation d` acts by right translation with weight
\[
  (R_d(g)F)(x)=\left(\frac{H(xg)}{H(x)}\right)^d F(xg),\qquad
  H(x)=\max(1,\|x\|,\|x^{-1}\|).
\]
This is the action on a function represented after division by `H^d`. The ratio law gives the representation identity. Submultiplicativity bounds the operator norm by `H(g)^d` and ensures that translation preserves vanishing at infinity.

`HeightWeightedRightTranslationStatement` gives joint continuity when the ambient normed ring is proper. A compact height sublevel set provides a neighborhood of the translating element with a common ratio bound. Outside a compact set of arguments, the entire neighborhood of translates is small by vanishing at infinity. On the compact set, joint pointwise continuity and compactness give uniform convergence as the translation parameter tends to its limit. This proves continuity of each orbit in the sup norm. The local operator norm bound then gives joint continuity in the vector and the translating element.

This is the Banach action used to place real Whittaker functions of common polynomial growth in a single representation.

`continuous_orbit` is the sup-norm continuity statement for a fixed vector.
