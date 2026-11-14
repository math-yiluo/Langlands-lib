# Sharp conjugacy of maximally split maximal tori over the unramified closure: the proof

`Langlands.Geometry.Building.unramifiedSharpTorusConjugacy` proves the published statement
`Langlands.Geometry.Building.UnramifiedSharpTorusConjugacyStatement.{u}` (module
`Langlands.Geometry.Building.UnramifiedSharpTorusConjugacyStatement`). The universe `u` is
arbitrary and the statement is used unchanged.

## What is proved

Let `F : Type u` be a nonarchimedean local field and `K = UnramifiedClosure F`. Take group
schemes `H`, `D`, `C` over `Spec K` and morphisms `d : D ⟶ H`, `π : C ⟶ D` with
`IsSimplyConnectedDerivedCover d π`, so `H` is connected reductive. Take two maximally split
maximal torus inclusions `i : T.toGrp ⟶ H` and `i' : T'.toGrp ⟶ H`. Then there are
`g ∈ simplyConnectedImage d π` and an isomorphism `e : T.toGrp ≅ T'.toGrp` with
`i ≫ (H.innerIso g).hom = e.hom ≫ i'`. The theorem adds no hypotheses on the field, the
group, the cover or the tori.

## The implemented proof

The proof is a single term that composes results already published in the Library:

```lean
theorem unramifiedSharpTorusConjugacy : UnramifiedSharpTorusConjugacyStatement.{u} :=
  unramifiedSharpTorusConjugacy_of_structure maximalSplitTorusConjugacy
    simplyConnectedCentralizerProduct quasiSplitMaximalTorusCentralizer
    (unramifiedQuasiSplit_of_henselianDiscrete henselianDiscreteQuasiSplit)
```

`unramifiedSharpTorusConjugacy_of_structure`, in
`Langlands.Geometry.Building.UnramifiedSharpTorusConjugacyReduction`, proves the target from
four statements. Each one is supplied by a published theorem without premises:

1. `MaximalSplitTorusConjugacyStatement`: proved by `maximalSplitTorusConjugacy`
   (`Langlands.GroupScheme.Rational.MaximalSplitTorusConjugacyProof`). It says that in a
   connected reductive group over any field, two maximal split tori are conjugate by a
   rational point. It also says that a splitting of a maximal split torus has the split rank
   as its number of factors.
2. `SimplyConnectedCentralizerProductStatement`: proved by `simplyConnectedCentralizerProduct`
   (`Langlands.GroupScheme.Rational.SimplyConnectedCentralizerProductProof`). Fix a maximal
   split torus with centralizer `Z`. Every rational point `g` of the group is a product
   `g = (π ≫ d)(c) · j(z)` with `c ∈ C(k)` and `z ∈ Z(k)`.
3. `QuasiSplitMaximalTorusCentralizerStatement`: proved by `quasiSplitMaximalTorusCentralizer`
   (`Langlands.GroupScheme.Rational.QuasiSplitMaximalTorusCentralizerProof`). In a quasi-split
   group, a maximal torus that contains a maximal split torus represents the centralizer of
   that split torus.
4. `UnramifiedQuasiSplitStatement`: every connected reductive group over
   `UnramifiedClosure F` is quasi-split. It is obtained as
   `unramifiedQuasiSplit_of_henselianDiscrete henselianDiscreteQuasiSplit`:
   - `unramifiedQuasiSplit_of_henselianDiscrete`
     (`Langlands.Geometry.Building.UnramifiedQuasiSplitReduction`) specializes the generic
     Henselian statement to `UnramifiedClosure F`. It uses the Library's proofs that the
     valuation subring is Henselian and that its residue field is algebraically closed.
   - `henselianDiscreteQuasiSplit`
     (`Langlands.GroupScheme.Rational.HenselianDiscreteQuasiSplitProof`) proves
     `HenselianDiscreteQuasiSplitStatement` without premises. That statement says every
     connected reductive group over a Henselian discretely valued field with algebraically
     closed residue field is quasi-split.

Inside the reduction, after `intro`, quasi-splitness of `H` comes from input 4 applied to
`hcover.isConnectedReductive`. Then `exists_cover_conjugacy_of_quasi_split_maximal_tori`
applies input 3 to each torus, which identifies it with the centralizer of its maximal split
subtorus. Inputs 1 and 2 then give a conjugating element in `simplyConnectedImage d π`
together with the isomorphism `e`.

The development check of this module passed with no errors or warnings. The theorem depends
only on the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Provenance

The statement is the structural input to the independence part of Kaletha–Prasad,
*Bruhat–Tits Theory: A New Approach* (2023), Lemma 2.6.24 (printed p.105). The
quasi-splitness input matches Corollary 2.3.8 (printed p.81). The source mathematics is in the
published modules listed above. This file only assembles them.
