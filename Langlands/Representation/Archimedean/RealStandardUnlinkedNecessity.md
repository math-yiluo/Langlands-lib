# Unlinkedness for irreducible generic unitary real standard modules

Lean module: `Langlands.Representation.Archimedean.RealStandardUnlinkedNecessity`.

`RealStandardMoeglinUnlinkedNecessityStatement` says that an irreducible generic infinitesimally unitary real standard module of rank `n` has pairwise unlinked Mœglin data in its given parameter list. The theorem `realStandard_moeglinUnlinked_of_unitaryGeneric` proves it. The list need not be in Langlands order and may include induced blocks of weight zero. The proof uses `exists_realStandard_ordered_unlinked`, which for a list of nondegenerate blocks produces a Langlands-ordered, unlinked permutation carrying an injective standard intertwiner into the original module.

## Proof

The growth argument applies to a Jacquet witness whether or not the full list of blocks is ordered. Irreducibility forces the proper slow-growth quotient to be the original module. Its Whittaker functional and infinitesimal character give maximal faithfulness by `Kostant.realWhittakerMaximallyFaithful`, contradicting the lower bound `realStandardCentralGrowth`. The upper bound has degree `n(n-1)-1`, the lower bound `n(n-1)`, and the root position in the Jacquet witness implies `n ≥ 2`.

An adjacent decreasing pair of nondegenerate blocks, if linked, gives such a witness: twist both by `(rank post - rank pre)/2` and apply the two-block theorem and induction in stages. The common twist preserves both the order of the two real exponents and linkage. No ordering of the prefix or suffix enters this step.

An adjacent inversion `x, y` becomes a decreasing pair in the Hermitian-dual parameter. The Hermitian-dual blocks have Mœglin exponents `-conj t`, with the original parities and absolute weights. Reversing two data and taking their Hermitian duals conjugates the differences that occur in the linkage tests. All right-hand sides of those tests are real, so linkage of `y, x` would give linkage of the dual of `x` followed by the dual of `y`. The adjacent-pair obstruction therefore gives `AreRealBlocksUnlinked y x`.

Apply the published unlinked swap from the decreasing pair `y, x` to the inverted pair `x, y`. Its injective intertwiner makes the new list a parameter of the same irreducible module, and `realStandardParameter_model` transfers the three module hypotheses to the new standard module. Each such step decreases `realInversionCount`. Compose the intertwiners and stop when the list is ordered. At that point `realLinkedLanglandsQuotientNotLarge` precludes linked data: the largest proper submodule is zero by irreducibility and the module is maximally faithful by genericity.

For weight-zero blocks, first expand each into its two character blocks. The Library proves that this preserves the function model, total rank, and list of Mœglin data. Apply the sorting result to the expanded, nondegenerate list. Pairwise unlinkedness is invariant under permutation because linkage is symmetric. Hence it holds for the original list of data as well.

## Provenance

This order-free consequence is derived from the published Library growth comparison, `realPairLinkedJacquetFunctional`, `realLinkedJacquetFunctionalInStages` and `realStandard_hermitianDual_parameter`. The linkage and swap conventions are from C. Mœglin, *Representations of GL(n) over the real field*, Proc. Sympos. Pure Math. 61 (1997), §8, p. 163, and Theorem 10b and its proof, pp. 164–165 (PDF pp. 172–174). The maximal-faithfulness input is B. Kostant, *On Whittaker vectors and representation theory*, Invent. Math. 48 (1978), Theorem 3.9, p. 142 (PDF p. 42); compare D. Vogan, *Gelfand–Kirillov dimension for Harish-Chandra modules*, Invent. Math. 48 (1978), Theorem 6.2 and the proof of (a) ⇒ (f), pp. 89 and 93 (PDF pp. 15 and 19). Infinitesimal unitarity is the form condition in Knapp–Vogan (1995), (0.5), p. 6 (PDF p. 28). The module does not assert a classification of unitary representations.
