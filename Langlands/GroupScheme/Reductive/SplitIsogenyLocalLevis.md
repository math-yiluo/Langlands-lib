# Isogenies of corresponding rank-one Levi subgroups

This derived unit restricts a root-datum isogeny to corresponding cocharacter
centralizers and realizes that restriction when the source centralizer has
semisimple rank at most one. Its ambient groups are connected reductive over an
arbitrary field, with specified split maximal tori and actual root data.

For an isogeny `f : P′ → P` and a source cocharacter `ν`, the corresponding
cocharacter is `f.coweightMap ν`. The transpose equation gives
`⟨α′, f.coweightMap ν⟩ = q(α′) ⟨f.indexEquiv α′, ν⟩`.
Since the root factor is positive, these pairings vanish simultaneously.
`RootDatumIsogeny.orthogonal` restricts the root correspondence to these
orthogonal indices, retaining both original lattice maps and every root factor.
Reducedness is inherited from the ambient root datum.

`not_linearIndependent_of_images` reflects dependence of two corresponding
roots. Reducedness relates the two source roots by a sign. The original
injective weight map then gives a nontrivial integral relation between the two
target roots, with coefficients formed from their positive root factors.

`exists_centralizer_isogeny` permits any closed representatives of the two
dynamic centralizers and any torus factorizations. Published centralizer
reductivity and the centralizer root calculation identify their root data with
the orthogonal restrictions. The explicit rank-one direction condition on the
source cocharacter gives pairwise root dependence in the source centralizer;
the dependence lemma gives it in the target centralizer. The actual rank-one
realization theorem then supplies a finite, flat, surjective group morphism
commuting with the original prescribed torus morphism.

The argument derives from the published cocharacter-centralizer root-data
construction and the rank-one realization construction. It adds no perfectness,
separability or smoothness condition on the kernel. All universes and all root
factors are retained. General-rank gluing and fixed-torus extension remain
separate obligations.
