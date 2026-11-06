# Actual reduced translations under split-torus base change

This internal construction applies the published actual lattice and root
base-change results to the reduced translation spaces used by
`KPApartmentData`. It makes no new assertion from the original literature.

Let `k → K` be any field extension, let `S` be a supplied split torus over
`k`, and let `i : S.toGrp ⟶ G` be a homomorphism to an affine group of
locally finite type. All fields and schemes have the arbitrary universe
parameter `u`. The target torus and homomorphism are their actual scheme
pullbacks. No valuation, completeness, local-field, reductivity,
characteristic, or maximal-split-torus hypothesis is needed.

`splitCocharacterBaseChange` tensors the published actual cocharacter
lattice equivalence with `ℝ` over `ℤ`. Its pure-tensor formula identifies
the map with scheme-theoretic cocharacter base change.
`eval_splitCocharacterBaseChange` follows by tensor induction from the
published integral lattice-pairing base-change formula.

The module directly reuses the published `rootsBaseChangeEquiv` and its
`rootsBaseChangeEquiv_apply` formula for the definitionally identical
`relativeRoots`. The published
`mem_roots_baseChange_iff` and the character lattice equivalence show that
the real cocharacter map preserves and reflects the common kernel of all
actual relative roots. Its surjectivity identifies the image of the old
annihilator with the whole target annihilator. No root comparison equality
is assumed.

`splitTranslationBaseChange` is the induced real-linear equivalence
between `TranslationSpace i` and `TranslationSpace` of the pulled-back
homomorphism. These are the original quotients by `rootAnnihilator`. Its
representative formula uses the same real cocharacter map, and
`rootForm_splitTranslationBaseChange` proves that all actual root forms
commute with this quotient equivalence.

This construction retains the supplied split torus. Its pullback may
fail to be maximal split in the enlarged group. The construction does not
enlarge that torus, extend a root-datum valuation, compare normalizer
actions, select an apartment class, identify affine roots, or construct a
building comparison for a supplied integral model. Those obligations
remain open for `IntegralModel.BuildingComparisonStatement`.
