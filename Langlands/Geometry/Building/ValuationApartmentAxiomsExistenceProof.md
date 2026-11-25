# Existence of actual valuation data satisfying the Chapter 7 apartment axioms: proof

Lean module: `Langlands.Geometry.Building.ValuationApartmentAxiomsExistenceProof`,
namespace `Langlands.Geometry.Building`.

## Statement

```
theorem Langlands.Geometry.Building.valuationApartmentAxiomsExistence :
    ValuationApartmentAxiomsExistenceStatement.{u}
```

The type is exactly the published proposition
`Langlands.Geometry.Building.ValuationApartmentAxiomsExistenceStatement.{u}` of
the module `Langlands.Geometry.Building.ValuationApartmentAxiomsExistenceStatement`,
at an arbitrary universe `u`, with no further hypothesis. Unfolded, it reads:

```
∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G),
  letI : IsAffineHom G.X.hom := hG.isAffineHom
  ∃ B : ValuationBuildingData G, B.SatisfiesApartmentAxioms
```

In words: for every connected reductive group `G` over a nonarchimedean local
field `F` there are valuation building data `B` (a maximal split torus, an
`N(F)`-stable equipollence class of compatible valuations of its root datum,
the actual centralizer, and V 6) whose apartment satisfies V 7 and AS 2–AS 5.

## Proof

The Lean proof is the single application

```
valuationApartmentAxiomsExistenceReduction
  (unramifiedQuasiSplit_of_henselianDiscrete Langlands.GroupScheme.henselianDiscreteQuasiSplit)
  quasiSplitIntegerApartmentExistence specialTorusExistence unramifiedValuationDescent
  valuationBuildingApartmentAxioms
```

of `valuationApartmentAxiomsExistenceReduction` (module
`Geometry.Building.UnramifiedValuationDescentStatement`), whose type
`ValuationApartmentAxiomsExistenceReductionStatement.{u}` is the implication
from five statements to the target. Each is discharged by theorems proved in
the Library without hypotheses:

1. `UnramifiedQuasiSplitStatement.{u}`: every connected reductive group over the
   maximal unramified extension `K` of `F` is quasi-split. It is
   `unramifiedQuasiSplit_of_henselianDiscrete` (module
   `Geometry.Building.UnramifiedQuasiSplitReduction`) applied to
   `Langlands.GroupScheme.henselianDiscreteQuasiSplit` (module
   `GroupScheme.Rational.HenselianDiscreteQuasiSplitProof`), quasi-splitness
   over Henselian discretely valued fields with algebraically closed residue
   field (KP Corollary 2.3.8).
2. `quasiSplitIntegerApartmentExistence` (module
   `Geometry.Building.QuasiSplitIntegerApartmentExistenceProof`): for a
   quasi-split group over a Henselian field with a surjective integer-valued
   valuation, every maximal split torus carries an `N`-stable class of
   valuations of the root datum with V 6.
3. `specialTorusExistence` (module `Geometry.Building.SpecialTorusExistenceProof`):
   KP Proposition 9.3.4, special tori exist.
4. `unramifiedValuationDescent` (module
   `Geometry.Building.UnramifiedValuationDescentProof`): KP Construction 9.6.1,
   Lemma 9.6.3 and Theorem 9.6.5, descent of the class from `K` to `F` with V 6.
5. `valuationBuildingApartmentAxioms` (module
   `Geometry.Building.ValuationBuildingApartmentAxiomsProof`): every valuation
   building datum satisfies V 7 and AS 2–AS 5.

Inside the reduction, a maximal split torus of `G` is put in a special torus,
the quasi-split class over `K` is descended to `F`, and the apartment axioms
are applied to the resulting datum; the steps are on the page of
`Geometry.Building.UnramifiedValuationDescentStatement`. The statement is not
modified and no hypothesis is added.

## Declarations

- `Langlands.Geometry.Building.valuationApartmentAxiomsExistence :
  ValuationApartmentAxiomsExistenceStatement.{u}`.

## Literature

T. Kaletha and G. Prasad, *Bruhat–Tits Theory: A New Approach* (2023):

- Chapter 9, the opening of §9.6, printed p. 364: for groups that are not
  quasi-split the material of Chapters 6 and 7 was conditional on the existence
  of valuations of root data, which §9.6 supplies.
- Theorem 9.6.5, printed p. 366: the functions `ϕ^x` of Construction 9.6.1 form
  a valuation of the root datum compatible with `ω`, equivariantly in `x`, with
  image an equipollence class; §9.6.6, printed p. 367, compares the affine root
  systems; §9.5, printed pp. 363–364, records where Axiom 4.1.6 is proved for
  the descended building.
- 4.1.28, printed p. 166: once the availability of valuations of root data is
  established in §9.6, the material of Chapters 6 and 7 becomes available for
  groups that are not quasi-split.

The authors' *Corrections and additions* (version of 1 November 2024), p. 33,
add AS 5 to the opening assumptions of Chapter 7.
