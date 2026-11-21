# Reductive groups over henselian local rings with finite residue field

`Langlands.GroupScheme.henselianFiniteResidueQuasiSplit` proves
`HenselianFiniteResidueQuasiSplitStatement.{u}` for every universe `u`.
For a reductive group scheme `G` over a henselian local ring `R` with finite
residue field, it gives a relative Borel subgroup over `R` and a finite étale
local `R`-algebra over which `G` is split in the sense of the statement.
[Statement and source comparison](HenselianQuasiSplitStatement.md)

The proof applies `henselianFiniteResidueQuasiSplit_of_inputs` to
`relativeBorelScheme` and `henselianFiniteEtaleRefinement`. For the first
conclusion, the finite-field quasi-splitness theorem gives a Borel subgroup
of the closed fibre. Its classifying point on the smooth scheme of Borel
subgroups lifts to a section by henselian smooth lifting. Pulling the
universal Borel back along this section gives the Borel over `R`. This is
the lifting argument in Conrad, *Reductive group schemes* (2014),
Corollary 5.2.14, p. 159 (`conrad-2014-reductive-group-schemes`).
[Borel representability](BorelSchemeProof.md)
[Henselian Borel lifting](HenselianBorelReduction.md)

For the splitting conclusion, the reduction takes an affine étale
neighbourhood of the closed point carrying a closed fibrewise maximal
coordinate split torus. Finite étale refinement gives a finite étale local
`R`-algebra whose spectrum maps to this neighbourhood over `Spec R`.
The reduction pulls back the torus and supplies the fibrewise root datum
and the rank-one linear isomorphisms for its root spaces over the local
algebra.
[Splitting reduction](HenselianFiniteEtaleSplitReduction.md)
[Finite étale refinement](../../CommutativeAlgebra/HenselianFiniteEtaleRefinementProof.md)
