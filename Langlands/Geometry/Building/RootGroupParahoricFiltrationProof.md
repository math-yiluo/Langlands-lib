# Proof of `U_a(F) ∩ P_x ⊆ U_{a,x,0}` for the actual parahoric data

The theorem `Langlands.Geometry.Building.rootGroupParahoricFiltration.{u}`
proves exactly the published proposition
`Langlands.Geometry.Building.RootGroupParahoricFiltrationStatement.{u}` from
`Langlands.Geometry.Building.AffineIwahoriTitsInputStatements`. The universe
`u` is arbitrary. The hypotheses are those of the statement: a nonarchimedean
local field `F : Type u`, a group scheme `G` over `F` with
`[IsAffineHom G.X.hom]`, and `P : ParahoricBuildingData G` with
`P.apartment.SatisfiesApartmentAxioms P.centralizer`. The conclusion is

```
rootGroupPoints P.i α ⊓ P.parahoricAt x ≤ P.apartment.filtration x α 0
```

for every `α : relativeRoots P.i` and every point `x : P.Apartment`. In KP
notation this is `U_a(F) ∩ P_x ⊆ U_{a,x,0}`, the inclusion `⊆` of the equality
`U_a(k) ∩ P_z = U_{a,z,0}` that KP's proof of Lemma 7.4.13(1) cites from
Proposition 7.3.12 (Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach*,
2023). The Lean route below does not transcribe KP's proof. It assembles
published Library results.

## Implemented proof

The proof introduces the data and hypotheses of the statement and applies
one published theorem to two published unconditional results.

1. `ParahoricBuildingData.rootGroup_inf_parahoricAt_eq_filtration` (module
   `Langlands.Geometry.Building.PointParahoricRootIntersection`) proves the
   subgroup equality

   ```
   P.rootGroup a ⊓ P.parahoricAt x = P.filtration x a 0
   ```

   for every apartment point `x` and every `a ∈ relativeRoots P.i`. Its
   hypotheses are the apartment axioms, opposite factor pairs
   `RelativeRoot.HasRankOneFactorization P.i`, and the global proposition
   `RelativeRoot.DynamicRootOrderedProductStatement.{u}`. Here `P.rootGroup a`
   and `P.filtration x a r` are abbreviations of `rootGroupPoints P.i a` and
   `P.apartment.filtration x a r`. The left side is therefore the left side of
   the target, and the right side is the target's right side.
2. Opposite factor pairs come from `Langlands.GroupScheme.rootRankOneFactorization`
   (module `Langlands.GroupScheme.Rational.RootRankOneFactorizationProof`), a
   proof of `RootRankOneFactorizationStatement.{u}`. It is applied to `F`, `G`,
   the connected reductivity `P.isConnectedReductive`, the torus `P.S`, the
   inclusion `P.i` and its maximal splitness `P.isMaximalSplitTorus`. The
   instances `IsAffineHom G.X.hom` and `Mono P.i.hom.hom.left` in its
   conclusion are propositions, so they agree with the instances of `P`.
3. The ordered-product proposition is
   `Langlands.GroupScheme.RelativeRoot.dynamicRootOrderedProduct` (module
   `Langlands.GroupScheme.Rational.DynamicRootOrderedProductProof`), a proof
   of `DynamicRootOrderedProductStatement.{u}`.
4. The root `α` is a subtype element of `relativeRoots P.i`, so `α.2` is the
   required membership. The direction `≤` of the equality from step 1 is the
   target.

For the reader, the proof of step 1 runs as follows; its Markdown has the
details. For a generic cocharacter positive on `a`, point exchange writes an
element of `P_x` as a product of positive and negative depth-zero root-group
elements, a sharp normalizer-stabilizer element and an element of `Z(F)^0`.
For an element of `U_a(F)`, opposite-cell separation removes the normalizer
and negative factors. Injectivity of ordered products of root groups then
isolates the coordinate at `a` in `U_{a,x,0}`. Axiom V 4 covers the case
where `a` is twice an indivisible root.

## Provenance and scope

This is a deduction from existing Library definitions and proved theorems.
It adds no hypotheses, axioms or source assertions. Only the inclusion `⊆`
is stated and proved here. The reverse inclusion is also part of step 1. The
module proves none of the other inputs of the affine Iwahori–Tits assembly.
