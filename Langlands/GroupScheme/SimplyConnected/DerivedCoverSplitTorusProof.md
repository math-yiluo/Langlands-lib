# Maximal split tori through the simply connected cover of a derived subgroup

Author: Worker 4101.

The theorem `Langlands.GroupScheme.simplyConnectedDerivedCoverSplitTorus`
proves the published proposition
`SimplyConnectedDerivedCoverSplitTorusStatement.{u}` from
[`DerivedCoverSplitTorusStatement`](DerivedCoverSplitTorusStatement.md).
Its type is exactly that proposition, at arbitrary universe `u`.

## What is proved

Let `k : Type u` be any field, including an imperfect field or one of
positive characteristic. Let `d : D ⟶ G` and `π : C ⟶ D` satisfy
`IsSimplyConnectedDerivedCover d π`. Let `i : S.toGrp ⟶ G` be a maximal
split torus. The theorem gives the two layers of witnesses from the target.

- **Derived torus.** A maximal split torus `j : S_D.toGrp ⟶ D` and a
  homomorphism `e : S_D ⟶ S` of commutative group schemes. `groupHom e` is
  a closed subgroup, and `j ≫ d = groupHom e ≫ i`.
- **Covering torus.** A maximal split torus `i_C : S_C.toGrp ⟶ C` and a
  homomorphism `f : S_C ⟶ S_D`. Here `i_C ≫ π = groupHom f ≫ j`,
  `groupHom f` is a central isogeny, and
  `i_C ≫ π ≫ d = groupHom (f ≫ e) ≫ i`.
- **Cocharacters.** `(cocharacterMapInt (f ≫ e)).baseChange ℚ` and
  `cocharacterMapReal (f ≫ e)` are injective. Their ranges equal the ranges
  of the corresponding maps of `e`.

All maps are the published `RealTorusSpace.cocharacterMapInt` and
`RealTorusSpace.cocharacterMapReal` on the actual cocharacter lattices. The
theorem does not say that `f ≫ e` is surjective onto `S` or onto its
cocharacters. It gives no integral statement for `f ≫ e`, and it says
nothing about `k`-points.

## The Lean proof

The proof applies one published implication to three published theorems.

1. `simplyConnectedDerivedCoverSplitTorusStatement_of_inputs`, from
   [`DerivedCoverSplitTorusAssembly`](DerivedCoverSplitTorusAssembly.md),
   proves the target from three propositions:
   `DerivedMaximalSplitTorusStatement.{u}`,
   `SimplyConnectedCoverSplitTorusStatement.{u}` and
   `SplitTorusIsogenyCocharacterStatement.{u}`.
2. The first input is
   `derivedMaximalSplitTorus_of_smoothMaximalSplitTorusConjugacy
   smoothMaximalSplitTorusConjugacy`.
   `smoothMaximalSplitTorusConjugacy`, from
   [`Rational.SmoothMaximalSplitTorusConjugacyProof`](../Rational/SmoothMaximalSplitTorusConjugacyProof.md),
   proves `SmoothMaximalSplitTorusConjugacyStatement.{u}`. That statement
   says that maximal split tori of a smooth connected affine group over a
   field are conjugate by a rational point (Borel–Tits; CGP C.2.3). The
   reduction `derivedMaximalSplitTorus_of_smoothMaximalSplitTorusConjugacy`,
   from
   [`Derived.MaximalSplitTorusConjugacyReduction`](../Derived/MaximalSplitTorusConjugacyReduction.md),
   turns this conjugacy into the derived statement. It takes a maximal
   split torus of `D` and extends it to a maximal split torus of `G`. It
   conjugates that torus onto `i` and uses normality of the derived
   subgroup to move the torus of `D` along.
3. The second input is `simplyConnectedCoverSplitTorus`, from
   [`SplitTorusProof`](SplitTorusProof.md). It lifts a maximal split torus
   of `D` through the cover `π`, and the restriction to the lifted torus is
   a central isogeny.
4. The third input is `splitTorusIsogenyCocharacter`, from
   [`Rational.SplitTorusIsogenyCocharacterProof`](../Rational/SplitTorusIsogenyCocharacterProof.md).
   For an isogeny of split tori it gives integral injectivity with finite
   cokernel, and rational and real bijectivity.

The assembly uses the hypothesis as follows. It applies the derived input
to `G`, using the connected reductivity and `IsDerivedSubgroup d` parts of
`IsSimplyConnectedDerivedCover d π`. It applies the cover input to `D` and
`j`, using the `IsSimplyConnectedCover π` part. It applies the isogeny
input to `f`. Splitness of `S_C` and `S_D` comes from the
maximal-split-torus predicates, and `IsIsogeny (groupHom f)` comes from the
central isogeny.

The ambient square `i_C ≫ π ≫ d = groupHom (f ≫ e) ≫ i` follows from the
two squares by associativity. The cocharacter conclusions use
`RealTorusSpace.cocharacterMap_comp_injective_range`. That lemma writes the
maps of `f ≫ e` as composites. It uses injectivity of the maps of the
closed immersion `e`, which on the rational side needs flatness of `ℚ` over
`ℤ`, and bijectivity of the maps of `f`. Bijectivity of `f` gives the
range equalities.

## Scope and provenance

The theorem has no hypotheses beyond those of the published statement. It
adds no perfectness, separability, characteristic or semisimplicity
assumption on `G`. The only axioms used are `propext`, `Classical.choice`
and `Quot.sound`.

This module is an internal composition of published Library theorems. It
adds no new mathematical assertion and no new source citation. The source
provenance of the target is recorded in the statement's Markdown, and that
of each input in its own paired Markdown.
