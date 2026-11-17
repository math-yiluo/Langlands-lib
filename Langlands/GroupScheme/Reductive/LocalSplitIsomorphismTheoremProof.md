# Proof of the Isomorphism Theorem for split reductive groups over a local ring

This module proves the published statement `LocalSplitIsomorphismTheoremStatement.{u}`
(module `LocalSplitIsomorphismTheoremStatement`), unchanged, as the theorem
`localSplitIsomorphismTheorem`. The statement covers every commutative local ring `R` and has
no further hypotheses on `R`. It says that two reductive group schemes over `Spec R`, each with
affine structure morphism and a closed coordinate split torus that is maximal on every
residue-field fibre and carries a fibrewise root datum, are isomorphic when the two root data
are equivalent. The precise form is in `LocalSplitIsomorphismTheoremStatement.md`.

## Results

- `localSplitWeylConjugation : LocalSplitWeylConjugationStatement.{u}`. For two such groups
  with the same root datum, a base with descending words, and Weyl-normalized simple-root data
  that are rank-one normal, conjugation by the simple Weyl points rescales the two Weyl
  families by common units.
- `localSplitIsomorphismTheorem : LocalSplitIsomorphismTheoremStatement.{u}`.

## Proof

The proof only assembles published theorems.

1. `localSplitWeylConjugation` applies `localSplitWeylConjugation_of_partner` (module
   `LocalSplitWeylConjugationReduction`) to two published rank-one theorems:
   - `localSplitRootPartnerUniqueness` (module `LocalSplitRootPairUniqueness`): the partner
     of a root parametrization with a Weyl point acting by `s_a` is unique;
   - `localSplitRootPairRescaling` (module `LocalSplitRootPairRescaling`): rescaling such a
     pair by `κ` and `κ⁻¹` keeps a Weyl point acting by `s_a`.

   The two hypotheses of `localSplitWeylConjugation_of_partner` are these statements, with
   the implicit parametrizations introduced.
2. `localSplitIsomorphismTheorem` applies `localSplitIsomorphismTheorem_of_weylRelations`
   (module `LocalSplitIsomorphismAssembly`) to three inputs:
   - `localSplitSimpleRootGroupLocal` (module `LocalSplitSimpleRootGroupLocal`): the simple
     root relations;
   - `localSplitWeylCommutator_of_weylConjugation localSplitRankOneNormal
     localSplitWeylConjugation` (module `LocalSplitWeylCommutatorReduction`, with
     `localSplitRankOneNormal` from `LocalSplitRankOneNormal`): the commutator relations of
     the Weyl families;
   - `localSplitWeylNegSimple_of_rankOne localSplitRankOneNormal localSplitRankOneBruhat
     localSplitWeylConjugation` (module `LocalSplitNegSimple`, with `localSplitRankOneBruhat`
     from `LocalSplitRankOneBruhat`): the negative simple relations.

The proof uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Provenance

This is the Isomorphism Theorem of SGA 3, Exp. XXIII, §4 (théorème d'isomorphisme), in the case
of a local base. The route through big-cell relations and Weyl families follows the structure of the
proof in SGA 3, Exp. XXIII, §2–§4, and Conrad, *Reductive group schemes* (2014), §6.1–6.2. The
two groups are compared through common relations instead of an a priori homomorphism, as
documented in the imported modules.
