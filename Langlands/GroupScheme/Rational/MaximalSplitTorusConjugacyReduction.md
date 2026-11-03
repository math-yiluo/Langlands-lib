# Reduction of maximal split torus conjugacy to a closed subgroup

`MaximalSplitToriAreConjugate G` says that every pair of maximal split tori
of a group scheme `G` over a field are rationally conjugate, allowing an
isomorphism of the torus sources. The conjugating point, source isomorphism,
and equation are those of the published `SubgroupConjugate` definition.
This is an internal interface for the proof of
`SmoothMaximalSplitTorusConjugacyStatement`, obtained by fixing the field and
ambient group in that published proposition. It imposes no smoothness,
affineness, connectedness, or reductivity condition by itself.

The accompanying lemmas prove the following formal reductions.

- `MaximalSplitToriAreConjugate.of_iso` transports the property across an
  isomorphism of ambient groups by first composing both embeddings with the
  inverse isomorphism, then transporting their conjugacy back.
- `subgroupConjugate_of_closed_factorizations` treats two ambient maximal
  split tori that factor through one closed subgroup. Their factorizations
  are maximal split tori of that subgroup by
  `IsMaximalSplitTorus.of_comp`. Conjugacy there pushes forward to conjugacy
  in the ambient group.
- `subgroupConjugate_of_conjugate_closed_factorizations` allows each torus
  to be moved into the subgroup by its own ambient rational point. Ambient
  isomorphisms preserve maximality, and transitivity and symmetry of
  `SubgroupConjugate` combine the three conjugacies.
- `MaximalSplitToriAreConjugate.of_closed_overgroup` packages the preceding
  argument when every ambient maximal split torus admits such a conjugate
  factorization through the fixed closed subgroup.
- `smoothMaximalSplitTorusConjugacyStatement_iff` is the definitional
  equivalence with the published universal smooth connected affine
  statement.

These are internal deductions from the published maximality and conjugacy
interfaces; they do not assert the geometric existence of the closed
subgroup, of its conjugating factorizations, or of conjugacy inside it.
Those remain separate prerequisites of the Borel–Tits proof. In particular,
none of the reductions assumes an unproved reductive conjugacy statement.
