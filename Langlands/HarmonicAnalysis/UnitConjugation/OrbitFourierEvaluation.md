# Evaluation of a lattice character orbit by an invariant distribution

Let `R` be a normed ring whose additive group is locally compact and second countable with a compact open exhaustion and its Borel σ-algebra. Let `L` be a compact open additive subgroup, `e` a self-dual bicharacter, and `μ` an additive Haar measure. The test `latticeCharacterTest` is `x ↦ e(x,z)` on `L`, extended by zero. It is the Fourier transform of the indicator of `z + L*` divided by the positive volume of the annihilator `L*`.

`OrbitFourierEvaluationStatement` evaluates a scalar multiple of a finite sum of lattice character tests whose frequencies lie in one orbit of dual-lattice cosets. The unit subgroup in the orbit definition preserves the lattice and the bicharacter. For a conjugation-invariant distribution `T` and a representative `z` of the orbit, the evaluation of the character sum, multiplied by the volume of `L*`, equals the evaluation of the Fourier transform of the coset indicator, multiplied by the scalar and the number of terms in the sum. For a nonempty sum with nonzero scalar, either evaluation vanishes exactly when the other does.

A shift by an element of `L*` leaves the character test unchanged. Conjugating the frequency pulls the test back by inverse conjugation, so every term has the same evaluation by `T`. The proof sums these values and uses the Fourier coset formula and the double-annihilator identity. The character expansion and its scalar are supplied by the statement's hypotheses.

This is the distribution evaluation in Clozel, *Characters of non-connected, reductive p-adic groups*, Canadian Journal of Mathematics 39 (1987), §3.8, Lemma 15, printed pp. 165–166. A character expanded using frequency `−z` gives the same identity with the coset centered at `−z`.
