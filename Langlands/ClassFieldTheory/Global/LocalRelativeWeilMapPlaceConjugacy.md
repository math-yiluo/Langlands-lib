# Conjugacy of local-to-relative Weil maps at different places

`Langlands.ClassFieldTheory.Global.RelativeWeilGroup.exists_conj_of_isLocalRelativeWeilMap` proves that two local maps \(W_{F_v}\to W_{E/F}\) satisfying `IsLocalRelativeWeilMap` at places \(w,w'\) over \(v\) are conjugate in \(W_{E/F}\). The reciprocity candidates belong to their respective completions. The proof applies to any class family.

`globalClosureEmbedding` embeds \(E\) into \(\overline{F_v}\) using the completion at a chosen place. Normality and `AlgHom.restrictNormal'` give an automorphism \(\sigma\) of \(E/F\) relating the two embeddings. The images of the completions are spanned over \(F_v\) by the corresponding images of \(E\), by `finiteTensorMap_surjective`. Pullback along the closure embeddings defines `completionComparison` and its \(p\)-adic algebra map `completionComparisonPadic`, from \(E_{w'}\) to \(E_w\). The map is continuous by finite dimensionality, and `valued_lt_one_iff_tendsto` identifies the corresponding prime ideals.

`reciprocityUnits_completionComparison` transports geometric reciprocity for two elements with the same image in \(W_{F_v}\). It uses `reciprocityUnits_extensionWeilMap` for the degree-one comparison, `FiniteGaloisTower.extensionWeilMap_comp` for the composition of local Weil maps, and `reciprocityUnits_finiteGaloisAbsoluteConjugation` for the tower correction, which fixes the embedded completion.

`projection_surjective` lifts \(\sigma^{-1}\) to \(s\in W_{E/F}\). The defining properties of the local map at \(w'\) hold for `conjugateLocalMap s ι`, using the comparison of the embeddings for Galois projection and `ideleClassEquiv_ofAdicCompletion_of_eq` for the idèle-class restriction. `localRelativeWeilMapConjugacy` at \(w'\) then gives an idèle-class conjugation. Its product with \(s\) gives the asserted conjugating element.

The construction is a finite-level comparison of the local-to-global maps of Tate, *Number theoretic background*, §§1.5–1.6 and §2.1, printed pp. 8–9. The registered source `tate-1979-number-theoretic-background` has SHA-256 `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
