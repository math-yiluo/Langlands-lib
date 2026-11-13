# Open-subgroup Hecke inclusion: proof

The theorem `Langlands.Hecke.Homomorphism.openSubgroupHeckeInclusion` proves
exactly the published proposition `OpenSubgroupHeckeInclusionStatement`,
with its original group universe and independent module-carrier universe and
without additional hypotheses.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
9 July 2026 edition, III.2.6, final Remark, printed p.77 / PDF p.83, together
with the nondegenerate-module comparison recalled at the end of I.2.3,
printed p.18 / PDF p.24. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

The proof assembles the two helper modules `OpenSubgroupHeckeBasics` and
`OpenSubgroupPseudo`. The first compares the ambient and subgroup modular
characters by evaluating regular Haar pushforward identities on a compact open
subgroup contained in the open subgroup. Cancellation of its finite nonzero
mass gives both relative-character triviality clauses.

For arbitrary supplied Haar measures, the second module constructs the natural
isomorphism `OpenSubgroup.pseudoFIsoF`. Its comparison sends a regular tensor to
the orbit map of its contraction. The canonical right action, expressed as
convolution through the Haar-normalized inclusion, identifies every
nondegenerate Hom element with such an orbit map. Contraction injectivity and
naturality give a natural isomorphism. This argument retains the independent
carrier universe and does not require a restriction hypothesis on the measures.

For the final clause, choose `openHeckeInclusion`, the first helper's
Haar-normalized zero extension. The target's measure restriction hypothesis
identifies the subgroup measure with the ambient comap, so `openDensity_eq_one`
makes the normalization scalar one. The inclusion therefore agrees pointwise
with the original function on the subgroup. Vanishing outside the subgroup,
surjectivity onto functions supported there and the two canonical multiplication
identities are the corresponding proved helper lemmas. The statement's original
Lean/Markdown pair and its import closure are unchanged.
