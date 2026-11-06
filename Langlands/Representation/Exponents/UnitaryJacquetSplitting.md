# Splitting normalized Jacquet characteristic spaces by real part

Author: Worker 17.

This internal algebraic unit implements the direct-sum step used in David
Renard, *Représentations des groupes réductifs p-adiques*, French edition
dated 9 July 2026, VII.2.3, printed p.229 / PDF p.235. The registered source
is `renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
It is a derived algebraic decomposition of the published
`unitaryJacquetPart` and `nonunitaryJacquetPart`, for every actual parabolic
and its rational Levi, matching radical and split component.

The two reindexing lemmas express the underlying submodules as suprema over
the actual normalized Jacquet exponent subtype, separated according to
whether `Plancherel.SplitTorus.normalizedRealPart` is zero. The theorem
`unitaryJacquetPart_disjoint_nonunitaryJacquetPart` applies the published
independence of normalized Jacquet characteristic spaces to these disjoint
sets of exponents. This uses the modular, compactly generated lattice of
submodules and does not assume admissibility.

The theorem `unitaryJacquetPart_sup_nonunitaryJacquetPart` partitions the
full family of exponents into zero and nonzero real parts. Their sum is
therefore exactly the span of all normalized Jacquet characteristic spaces.
The next theorem identifies complementarity with this span being the whole
Jacquet module. Finally,
`unitaryJacquetPart_isCompl_nonunitaryJacquetPart_of_admissible` obtains
spanning from the published decomposition theorem when the actual
normalized Jacquet module is admissible.

The construction `unitaryJacquetProdEquivOfAdmissible` turns this
complementarity into a complex linear equivalence from the product of
the unitary and nonunitary submodules to the actual normalized Jacquet
module. Its formula is addition of the two underlying vectors. Its
inverse therefore gives the unique decomposition into the two parts;
the construction uses Mathlib's `Submodule.prodEquivOfIsCompl`. It
retains the same explicit Jacquet-module admissibility premise.

The final theorem explicitly assumes Jacquet-module admissibility. This
module does not prove preservation of admissibility by Jacquet functors,
temperedness of the unitary part, or any of the three exact VII.2.3–VII.2.4
targets. Those remain separate obligations. All field and carrier universes,
canonical point topology, local compactness and nonarchimedean hypotheses
of the published objects are retained, and no finite-length or
irreducibility hypothesis is imposed.
