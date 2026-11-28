# Concordance of smoothing powers at a split infinite place

`infiniteSplitSmoothingPowers` proves `InfiniteSplitSmoothingPowersStatement`.
At an infinite place \(w\) of a number field \(K\), suppose the completed
tensor algebra \(K_w\otimes_K L\) of a finite field extension splits into
\(m+1\) copies of \(K_w\). The supplied splitting must carry the local action
of the chosen \(K\)-automorphism of \(L\) to the cyclic shift.

Fix a Haar measure on \(\mathrm{GL}_n(K_w)\) and a continuous compactly
supported function on that group. The upper test is the tensor of \(m+1\)
copies of this function in the split matrix coordinates. The lower test is
its \((m+1)\)-fold convolution. Both are continuous and compactly supported.
The upper Haar measure is the pullback of the product of \(m+1\) copies of
the lower Haar measure. With these same measures, the two tests remain
concordant after taking their \((k+1)\)-fold convolution powers for every
\(k \geq 0\).

The coefficient equivalence is continuous in both directions by the module
topology on the completed tensor algebra. Its induced matrix group
isomorphism carries the upper measure to `splitContinuousHaar`. An induction
on \(k\) uses change of variables in convolution to identify the upper power
with the pullback of the split power. The proof then transports
`splitSmoothingPowers` by `areConcordant_pullback_ringEquiv`, using the
intertwining of the Galois action and the cyclic shift.

Arthur and Clozel use these split tensors and their matching convolutions
in the proof of Chapter 1, Theorem 4.5, printed pp. 43–44. The identity for
powers follows from the split comparison and change of variables.
