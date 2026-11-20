# Étale moduli of closed tori with a fixed centralizer

`EtaleFixedCentralizerTorusRepresentabilityStatement.{u}` uses a locally
noetherian base and a smooth separated quasi-compact ambient group with affine
geometrically connected residue fibres. It assumes affine pullbacks on local
Artinian affine tests and adic-limit bijectivity of the ordinary actual closed
torus-subgroup presheaf. For a fixed smooth closed ambient subgroup with
geometrically connected fibres, it constructs an étale universal family of
closed tori whose ambient centralizer is precisely that subgroup.

The fixed subgroup inherits the adic condition and the affineness needed on
Artinian tests. It therefore has a separated étale parameter for central
closed tori. The ambient centralizer of its universal torus contains the
pulled-back fixed subgroup. Both are smooth, and the ambient centralizer has
geometrically connected fibres. Restrict to the open where their ranges
agree. Conversely, any actual torus with the given centralizer is a closed
central torus of that centralizer. Its unique central parameter lands in the
open by the all-test range comparison. Monicity and the natural family
comparisons yield literal subgroup equality and uniqueness on every test.

This implements the fixed-centralizer part of Raynaud, SGA 3, Exposé XV,
Theorem 8.9(a), Gille–Polo recomposition, PDF pp. 62–63, with the stated
adic-limit and Artinian affine inputs.
