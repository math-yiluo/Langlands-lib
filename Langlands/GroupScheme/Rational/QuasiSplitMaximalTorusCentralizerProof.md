# Proof: maximal tori containing a maximal split torus in quasi-split groups

Author: Worker 4696.

`Langlands.GroupScheme.quasiSplitMaximalTorusCentralizer` proves exactly the
published proposition
`Langlands.GroupScheme.QuasiSplitMaximalTorusCentralizerStatement.{u}` of
[`QuasiSplitMaximalTorusCentralizerStatement`](QuasiSplitMaximalTorusCentralizerStatement.md),
at an arbitrary universe `u`. The statement is used unchanged. Take any field
`k : Type u` (any characteristic, perfect or not) and any `G` with
`IsQuasiSplit G`. Take any maximal torus inclusion `i : T → G`, any ambient
maximal split torus `a : A → G` and any actual map `f : A → T` with
`f ≫ i = a`. Then the original `i` represents `torusCentralizer a`. The
representation includes monicity of `i` and equality of its range with the
whole centralizer subgroup functor on every test scheme and every refinement.
No hypothesis is added to the target. In particular there is no perfectness,
characteristic, rational-point density, chosen Borel containment or
structural-theorem premise.

The theorem depends only on the axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Implemented proof

The module makes two applications of published conditional results. Each takes
published unconditional proofs as its inputs.

```lean
theorem quasiSplitTorusCentralizerExistence :
    QuasiSplitTorusCentralizerExistenceStatement.{u} := by
  intro k _ G hG
  obtain ⟨A, a, ha, C, c, hc, hcl, hC⟩ :=
    hG.exists_maximalSplitTorus_with_torusCentralizer dynamicCentralizerReductive
      parabolicDynamic
  exact ⟨A, a, C, c, ha, hc, hcl, hC⟩

theorem quasiSplitMaximalTorusCentralizer :
    QuasiSplitMaximalTorusCentralizerStatement.{u} :=
  quasiSplitMaximalTorusCentralizer_of_exists_torusCentralizer
    quasiSplitTorusCentralizerExistence maximalSplitTorusConjugacy
```

### Step 1: `quasiSplitTorusCentralizerExistence`

This theorem proves the published internal proposition
`QuasiSplitTorusCentralizerExistenceStatement.{u}` (module
[`QuasiSplitMaximalTorusCentralizerReduction`](QuasiSplitMaximalTorusCentralizerReduction.md)).
For every quasi-split `G` over every field `k : Type u`, that proposition asks
for an actual maximal split torus `a₀ : A₀ → G` whose whole centralizer
`torusCentralizer a₀` is represented by a closed subgroup inclusion
`j₀ : C → G` with `C` a torus.

The proof applies the published
`IsQuasiSplit.exists_maximalSplitTorus_with_torusCentralizer` (module
[`QuasiSplitCentralizerTorus`](QuasiSplitCentralizerTorus.md)) to two published
proofs:

- `dynamicCentralizerReductive` (module
  [`Dynamic.CentralizerReductiveProof`](../Dynamic/CentralizerReductiveProof.md))
  proves `DynamicCentralizerReductiveStatement.{u}`: every closed representative
  of the dynamic centralizer of a cocharacter of a connected reductive field
  group is connected reductive.
- `parabolicDynamic` (module
  [`Absolute.ParabolicDynamicProof`](../Absolute/ParabolicDynamicProof.md))
  proves `ParabolicDynamicStatement.{u}` (Milne, Theorem 25.1, in the Library's
  formulation): a closed subgroup of a connected reductive field group is
  parabolic exactly when its range is `Dynamic.parabolic χ` for a cocharacter
  `χ` over `k`.

The result has the same data as the existence proposition, in a different
order of existential quantifiers. The proof destructures it and repackages it
in the required order. The applied published theorem works as follows; see the
cited Markdown for details.

1. `IsQuasiSplit G` supplies an actual field-defined geometric Borel
   `b : B → G`. It is parabolic and closed, and `B` is solvable.
2. `IsGeometricBorelSubgroup.exists_maximalSplitTorus_centralizer_le_range`
   (module [`QuasiSplitAdaptedSplitTorus`](QuasiSplitAdaptedSplitTorus.md))
   uses `parabolicDynamic` to write the range of `b` as `Dynamic.parabolic χ`.
   The cocharacter `χ` factors through an actual maximal split torus
   `a₀ : A₀ → G`, obtained by maximal split extension of its image. The whole
   centralizer of `a₀` lies in the dynamic centralizer of `χ`, hence in
   `Dynamic.parabolic χ`, which is the range of `b`.
3. `torusCentralizerTorusDataOfSolvableContainment` chooses a closed
   representative `j₀ : C → G` of `torusCentralizer a₀`, using the published
   `fieldCentralizerRepresentability`. The centralizer equals the dynamic
   centralizer of the published `centralizingCocharacter` of `a₀`. So
   `dynamicCentralizerReductive` makes `C` connected reductive. The containment
   of step 2 factors `j₀` monically through the solvable `B`, so `C` is
   solvable. The published `IsConnectedReductive.isTorus_of_isSolvableGroupScheme`
   then makes `C` a torus.

### Step 2: `quasiSplitMaximalTorusCentralizer`

The published `quasiSplitMaximalTorusCentralizer_of_exists_torusCentralizer`
(module
[`QuasiSplitMaximalTorusCentralizerReduction`](QuasiSplitMaximalTorusCentralizerReduction.md))
derives the target from `QuasiSplitTorusCentralizerExistenceStatement.{u}` and
`MaximalSplitTorusConjugacyStatement.{u}`. The proof supplies Step 1 for the
first premise. For the second it supplies the published
`maximalSplitTorusConjugacy` (module
[`MaximalSplitTorusConjugacyProof`](MaximalSplitTorusConjugacyProof.md)), which
proves rational conjugacy of maximal split tori in connected reductive groups
over every field. The applied reduction proceeds as follows.

1. For the supplied quasi-split `G`, Step 1 gives `a₀ : A₀ → G` and a closed
   torus representative `j₀ : C → G` of its centralizer.
2. Ordinary conjugacy, applied with the reductivity field of `IsQuasiSplit G`,
   gives a rational point `g` and an isomorphism `e : A₀ ≅ A` with
   `a₀ ≫ (G.innerIso g).hom = e.hom ≫ a`.
3. `torusCentralizer_of_iso_square` transports the representation to
   `j₀ ≫ (G.innerIso g).hom`, a closed torus representative of
   `torusCentralizer a`.
4. `IsMaximalTorus.isRepresentedBy_torusCentralizer_of_isTorus` (module
   [`TorusCentralizerTorusComparison`](TorusCentralizerTorusComparison.md))
   finishes the proof. It applies to the original supplied `i`, `f` and
   `f ≫ i = a`. Since `T` is commutative and contains `A`, the range of `i` lies
   in the centralizer, so `i` factors through the closed torus representative.
   The factor is a maximal torus inclusion into a torus, hence an isomorphism.
   Therefore `i` itself represents `torusCentralizer a`.

## Provenance

This is derived content: a composition of published Library results, with no
new source claim. The target's sources are documented in its Markdown:
Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), Fact 2.6.22 and
Remark 2.6.25(2), with Definition 2.6.2. The route differs from the classical
Borel–Tits argument, which identifies the centralizer of a maximal split torus
with a Levi factor of a minimal parabolic and uses that in the quasi-split case
the minimal parabolics are Borel subgroups. Here the
geometric input is only that a reductive centralizer contained in a solvable
subgroup is a torus. One adapted maximal split torus is moved to the arbitrary
supplied one by ordinary conjugacy.
