# Smooth compactly supported symmetric families are dense, conditionally

`Langlands.Global.symmetricFamilyDensityBridge` proves the implication `Langlands.Global.SymmetricFamilyDensityBridgeStatement`. Its five premises, in order, are:

1. `IntertwiningImaginaryUnitarityStatement` (the continued Gram identities),
2. `IntertwiningCocycleStatement.{0}`,
3. `IntertwiningSquareIntegrableExpansionStatement` (qualifying finite expansions in square-integrable inducing forms),
4. `InducedRestrictionMemLpStatement`,
5. `IntertwiningRepresentativeIndependenceStatement`.

The conclusion is `SymmetricFamilyDensityStatement` without any change in its binders: for the supplied finite family of presented parabolics over a number field in `Type`, any operators satisfying `IsImaginaryIntertwiningOperator` have the stated density in `symmetricFamilySpace`. This means the complex span of the symmetric families admitting an `IsSmoothCompactFamily` presentation has topological closure equal to the whole symmetric space. The presentation is almost everywhere in the spectral variable and then almost everywhere in the restriction variables, with smooth compactly supported scalar coefficients and fixed square-integrable inducing forms in each component. The theorem does not assume that the index family is the standard family, that it consists of a single association class, or that it is free of repeated parabolics.

## Implemented proof

Write \(H_i\) for `inducedHilbertSpace`, \(\nu_i\) for `spectralMeasure (n i)`, and \(n_{P_i}=\sum_j |T(i,j)|\). The identity Weyl map in each self-enumeration ensures \(n_{P_i}>0\); the component measures \(n_{P_i}^{-1}\nu_i\) are finite on compact sets. `HilbertDensityCriteria` gives a dense spanning set of the ambient product: one-component families supported in index \(i_0\) with value \([x\mapsto c(x)h]\), where \(c\) is smooth and compactly supported and \(h\) is the class of a single square-integrable inducing form.

For every such generator the proof constructs a family with component \(j\) represented by
\[
   F_j(y)=\frac{1}{n_{P_{i_0}}}\sum_{t\in T(i_0,j)}
      c(\tau_t^{-1}y)\,\mathrm{Mop}_{i_0,j,t}(\tau_t^{-1}y)h.
\]
Here \(\tau_t\) is the real Weyl coordinate map, bundled as a continuous linear equivalence and a measure-preserving measurable equivalence. The assumed Lebesgue measure preservation gives equal dimensions and invertibility and also preserves the normalized spectral measures. The identity \(w(i\mu)=i(w\mu)\) and injectivity of the imaginary embedding transfer composition of the complex parameter maps to the real ones.

* **Smooth presentation.** `exists_smooth_symmetrized_component` uses a finite expansion of each intertwiner on the form giving \(h\). The coefficients are holomorphic on their named coordinate domains, which contain the imaginary slice; `contDiff_comp_imaginaryParameter` restricts them to real smooth functions. Pullback along \(\tau_t^{-1}\) and multiplication by the pulled-back \(c\) give smooth compactly supported coefficients. Each transported summand is in `Lp`, since it is a finite sum of continuous compactly supported scalar functions times fixed Hilbert vectors. The proof reindexes the finite dependent sum of expansion terms by `Fin`, and the restriction-class equality gives `IsSmoothCompactFamily`'s iterated almost-everywhere representation.
* **Symmetry.** Postcomposition with a Weyl map from \(i\) to \(j\) gives a bijection \(T(i_0,i)\simeq T(i_0,j)\), using the enumeration and inverse Weyl map. The composition result in `AdelicImaginaryIntertwiningProperties` applies to \(h\) and this enumeration, so reindexing the sum gives pointwise symmetry of the chosen representatives. Measure preservation carries it to the almost-everywhere symmetry of the `Lp` classes.
* **Pairing with symmetric families.** For any symmetric \(\Theta\), pair \(\Theta_j\) with a transported summand and change variables back by \(\tau_t\). Symmetry replaces \(\Theta_j(\tau_t x)\) by \(\mathrm{Mop}_{i_0,j,t}(x)\Theta_{i_0}(x)\), and inner-product preservation removes the intertwiner from the pairing. The sum thus gives the original one-component pairing multiplied by \(\sum_j |T(i_0,j)|/n_{P_j}=1\). This is the row form of the Library's Weyl counting identity, using equality of the pair counts under reversal. The equality includes terms with empty Weyl sets.

The ambient product is complete since the induced Hilbert spaces are closed spans in `L²`. Projecting onto the **closed span of the smooth symmetric families** shows that a symmetric vector differs from its projection by a vector orthogonal to the dense generators: the pairing identities extend by continuity to the closure of the symmetric space and apply to the difference. This is `subset_topologicalClosure_span_of_inner_eq`; passing to the subtype topology gives the desired density. The argument requires neither closedness of the symmetric space in this step nor construction of an orthogonal projection onto it.

## Provenance and limits

The formula for symmetrizing a single-component generator is adapted from the proof of Delorme, *On the spectral theorem of Langlands*, Advances in Mathematics 426 (2023), 109107, §6, (6.2) and the proof of Lemma 6.2, pp. 21–22 (PDF pp. 21–22). There the formula for \(F_Q\) is used to put a basic wave packet in the image of the Eisenstein map. That lemma is not a density or orthogonal-projection theorem. Here the smooth presentation, equality of Hilbert space pairings, and density are established separately in the supplied family. The weights \(n_P^{-1}\) are those of Arthur, *An introduction to the trace formula* (2005), §7, Theorem 7.2(b), p. 35 (PDF p. 47 of the registered proceedings), rather than Delorme's normalization for the standard family.

The result supplies the density component of the Library's `SpectralTransformReductionStatement` when the five premises are available. It neither discharges those premises nor proves the wave-packet isometry, closed invariant range, or the exact `SpectralTransformStatement`.
