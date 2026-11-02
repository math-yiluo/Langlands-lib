# Complexes of inverse systems and the limit of the Hom complexes

Author: Worker 61. Built on the published modules
`Langlands.Cohomology.DiagramHomology` (`diagramHomologyIso`) and
`Langlands.Cohomology.DivisibleSystem.CompatibleHomComplex`
(`compatibleCochains`, `compatibleHomComplex`, `compatibleEval`,
`compatibleHomComplexIsoLimit`, `compatibleHomComplexIsoLimit_hom_π`). Through
these imports it uses `DivisibleSystem`, `DivisibleSystem.tower`,
`DivisibleSystem.obj`, `DivisibleSystem.degree` and
`SmoothRepComplexDivisibleSystem` (`Langlands.Cohomology.DivisibleSystem`),
`homTransition`, `homTransition_eq_iff`, `cochainTransition`,
`cochainTransition_v`, `homComplexSystem` and `homComplexLimit` (`HomSystem`),
and `LinearHomComplex.complex` (`Langlands.Cohomology.LinearHomComplex`). From
Mathlib it uses `HomologicalComplex.eval`, `HomologicalComplex.dNatTrans`,
`HomologicalComplex.asFunctor`, `HomologicalComplex.homologyFunctor`,
`CochainComplex.HomComplex` with its `Cochain`, `Cochain.mk` and `δ`,
`CochainComplex.HomComplex.homologyAddEquiv`,
`CochainComplex.HomComplex.CohomologyClass.homAddEquiv`,
`HomotopyCategory.quotient`, `ShortComplex.mapHomologyIso`,
`ShortComplex.homologyMapIso`, the instance stating that
`forget₂ (ModuleCat R) AddCommGrpCat` preserves homology
(`Mathlib.Algebra.Homology.ShortComplex.ModuleCat`),
`Iso.addCommGroupIsoToAddEquiv`, `Iso.toLinearEquiv` and
`HomologicalComplex.Hom.isoOfComponents`.

## Conventions

`R` is a ring, `C` an `R`-linear abelian category and `ℓ` a natural number.
`T` and `W` are `ℓ`-divisible systems of cochain complexes in `C`
(`DivisibleSystem (CochainComplex C ℤ) ℓ`). `T.tower : ℕᵒᵖ ⥤ CochainComplex C ℤ`
is the underlying inverse system, with levels `T m = T.tower.obj (op m)`;
`T.degree p` is the `ℓ`-divisible system `m ↦ (T m)^p` of degree `p` terms.
`ℕᵒᵖ ⥤ C` is the category of inverse systems in `C`; it is abelian and
`R`-linear by Mathlib's functor-category instances.

For complexes `K`, `L` in `C`, `LinearHomComplex.complex R K L` is the
published Hom complex of `R`-modules whose degree `n` term is Mathlib's module
`Cochain K L n` of graded morphisms of degree `n`, with differential `δ`.
Mathlib's `CochainComplex.HomComplex K L` is the same complex, with the same
terms and differential, as a complex of abelian groups.

For `m' ≤ m`, `homTransition` sends a morphism `T m ⟶ W m` to the unique
morphism `g : T m' ⟶ W m'` with `T.projection h ≫ g = f ≫ W.projection h`
(`homTransition_eq_iff`); `cochainTransition` applies it componentwise to
graded morphisms. `compatibleCochains R T W n` is the submodule of families
`z m : Cochain (T m) (W m) n` with `cochainTransition h (z m) = z m'` for all
`m' ≤ m`, and `compatibleHomComplex R T W` is the published complex of these
families. `homComplexSystem R T W` is the inverse system
`m ↦ Hom^•(T m, W m) = LinearHomComplex.complex R (T m) (W m)` and
`homComplexLimit R T W` its limit. The published
`compatibleHomComplexIsoLimit R T W : compatibleHomComplex R T W ≅
homComplexLimit R T W` composed with the limit projection to level `m` is the
evaluation `compatibleEval R T W m` at `m` (`compatibleHomComplexIsoLimit_hom_π`).

## Complexes of diagrams (namespace `Langlands.Cohomology`)

Here `J` is any category, `V` a category with zero morphisms and `c` a complex
shape.

- `diagramComplex F`: for a diagram of complexes `F : J ⥤ HomologicalComplex V c`,
  the complex in `J ⥤ V` whose degree `i` term is the diagram
  `j ↦ (F j)^i` (`F ⋙ HomologicalComplex.eval V c i`) and whose differential
  `i → i'` is the natural transformation `j ↦ d_{F j}^{i,i'}` (`F` whiskered
  with Mathlib's `HomologicalComplex.dNatTrans`). The shape condition and
  `d ≫ d = 0` are checked objectwise.
- `diagramComplex_X_obj`, `diagramComplex_X_map`, `diagramComplex_d_app`
  (`simp`, by `rfl`): the term of degree `i` at `j` is `(F j)^i`, its value on a
  morphism `a` of `J` is the degree `i` component of `F.map a`, and the
  differential at `j` is that of `F j`.
- `asFunctor_diagramComplex F` (by `rfl`): Mathlib's
  `HomologicalComplex.asFunctor`, which turns a complex of diagrams into a
  diagram of complexes, sends `diagramComplex F` back to `F`.
- `diagramComplexMap α`: the chain map `diagramComplex F ⟶ diagramComplex G`
  induced by a natural transformation `α : F ⟶ G`; in degree `i` it is `α`
  whiskered with the degree `i` evaluation (`simps` lemmas).
- `diagramComplexHomologyIso F q` (for `V = C` abelian): an isomorphism from
  the diagram `j ↦ H^q(F j)` (`F ⋙ homologyFunctor C c q`) to the degree `q`
  cohomology of `diagramComplex F` in `J ⥤ C`. It is the component at
  `diagramComplex F` of the published `diagramHomologyIso c q`;
  `diagramComplexHomologyIso_hom_app` (`simp`, by `rfl`) states that its
  component at `j` is the homology comparison isomorphism
  `ShortComplex.mapHomologyIso` for evaluation at `j`.

## Cohomology of the module-valued Hom complex (namespace `Langlands.Cohomology`)

Here `C` is an `R`-linear preadditive category and `K`, `L` are cochain
complexes in `C`.

- `linearHomComplexScIso R K L n`: the image of the degree `n` short complex of
  `LinearHomComplex.complex R K L` under the forgetful functor
  `forget₂ (ModuleCat R) AddCommGrpCat` is isomorphic to the degree `n` short
  complex of `CochainComplex.HomComplex K L`. All three components are
  identity isomorphisms; the two commutation conditions hold by `rfl` after
  extensionality, since both complexes have the differential `δ`.
- `linearHomComplexHomologyAddEquiv R K L n`: an additive equivalence from the
  degree `n` cohomology module of `LinearHomComplex.complex R K L` to the
  degree `n` cohomology group of `CochainComplex.HomComplex K L`. It is the
  inverse of the comparison isomorphism `ShortComplex.mapHomologyIso` for the
  forgetful functor (which preserves homology), followed by the homology
  isomorphism induced by `linearHomComplexScIso`, converted to an additive
  equivalence.
- `linearHomComplexHomologyHomotopyAddEquiv R K L n`: an additive equivalence
  from the degree `n` cohomology module of `LinearHomComplex.complex R K L` to
  the group of morphisms from `K` to `L⟦n⟧` in Mathlib's homotopy category
  `HomotopyCategory C (ComplexShape.up ℤ)` (morphisms between the images under
  `HomotopyCategory.quotient`). It is `linearHomComplexHomologyAddEquiv`
  followed by Mathlib's `CochainComplex.HomComplex.homologyAddEquiv` (degree
  `n` cohomology of `HomComplex K L` ≃+ cohomology classes of degree `n`
  cocycles) and `CochainComplex.HomComplex.CohomologyClass.homAddEquiv`
  (cohomology classes ≃+ morphisms `K ⟶ L⟦n⟧` in the homotopy category).

## The complex of inverse systems (namespace `Langlands.Cohomology.DivisibleSystem`)

- `towerComplex T` (`abbrev`): the cochain complex `diagramComplex T.tower` in
  `ℕᵒᵖ ⥤ C`. Its degree `p` term is the inverse system `m ↦ (T m)^p`, which
  is the tower of `T.degree p` (`towerComplex_X`, by `rfl`), and its
  differentials are those of the complexes `T m`.
- `towerComplexHomologyIso T q`: an isomorphism from the inverse system
  `m ↦ H^q(T m)` (`T.tower ⋙ homologyFunctor C (ComplexShape.up ℤ) q`) to the
  degree `q` cohomology of `towerComplex T`; it is `diagramComplexHomologyIso`
  for `T.tower`.

## The Hom complex between complexes of inverse systems

- `towerCochainEval T W z m`: for a cochain `z` of degree `n` from
  `towerComplex T` to `towerComplex W`, the cochain from `T m` to `W m` whose
  `(p, q)` component is the level `m` component of the morphism of inverse
  systems `z.v p q`; `towerCochainEval_v` (`simp`) records the components.
- `towerCochainEval_mem R z`: the family `m ↦ towerCochainEval T W z m` lies in
  `compatibleCochains R T W n`. By `cochainTransition_v` and
  `homTransition_eq_iff`, the compatibility for `m' ≤ m` in component `(p, q)`
  is the identity `T.projection ≫ (z.v p q)_{m'} = (z.v p q)_m ≫ W.projection`,
  which is the naturality of `z.v p q` for the morphism `m ⟶ m'` of `ℕᵒᵖ`.
- `compatibleCochainsComponent z p q hpq`: conversely, for a compatible family
  `z`, the morphism of inverse systems `m ↦ (z m).v p q` from the degree `p`
  term of `towerComplex T` to the degree `q` term of `towerComplex W`; its
  naturality is the compatibility of `z`, read through the same two lemmas
  (`simps` lemma for its components).
- `towerCochainLinearEquiv R T W n`: an `R`-linear equivalence between the
  cochains of degree `n` from `towerComplex T` to `towerComplex W` and
  `compatibleCochains R T W n`, given by `towerCochainEval` and
  `compatibleCochainsComponent`; additivity, `R`-linearity and both inverse
  laws are checked componentwise. `towerCochainLinearEquiv_apply_coe` (by `rfl`)
  states that its level `m` value is `towerCochainEval T W z m`.
- `δ_towerCochainEval T W n n' z m`: the differential of the Hom complex
  commutes with evaluation at `m`, since the differentials of `towerComplex T`
  and `towerComplex W` at level `m` are those of `T m` and `W m`.
- `towerHomComplexIso R T W`: an isomorphism of cochain complexes of
  `R`-modules from `LinearHomComplex.complex R (towerComplex T) (towerComplex W)`
  to `compatibleHomComplex R T W`, with degree `n` component
  `towerCochainLinearEquiv R T W n`; compatibility with the differentials is
  `δ_towerCochainEval`.
- `towerHomComplexIsoLimit R T W`: the isomorphism from the same Hom complex to
  `homComplexLimit R T W`, namely `towerHomComplexIso R T W` followed by the
  published `compatibleHomComplexIsoLimit R T W`.
- `towerHomComplexEval R T W m`: the chain map from
  `LinearHomComplex.complex R (towerComplex T) (towerComplex W)` to
  `Hom^•(T m, W m)` given in degree `n` by `towerCochainEval · m`;
  `towerHomComplexEval_f_apply` (`simp`, by `rfl`) records this.
- `towerHomComplexIsoLimit_hom_π R T W m` (`simp`, with a `reassoc` form): the
  forward morphism of `towerHomComplexIsoLimit R T W` followed by the limit
  projection to level `m` is `towerHomComplexEval R T W m`. Proof: by
  `compatibleHomComplexIsoLimit_hom_π` it is `towerHomComplexIso` followed by
  `compatibleEval R T W m`, which agrees with `towerHomComplexEval` on every
  cochain by `rfl`.
- `homComplexLimitHomologyAddEquiv R T W n`: an additive equivalence from the
  degree `n` cohomology module of `homComplexLimit R T W` to the group of
  morphisms from `towerComplex T` to `(towerComplex W)⟦n⟧` in Mathlib's homotopy
  category of cochain complexes in `ℕᵒᵖ ⥤ C`. It is the inverse of the
  cohomology isomorphism induced by `towerHomComplexIsoLimit R T W`, as an
  additive equivalence, followed by `linearHomComplexHomologyHomotopyAddEquiv`
  for `towerComplex T` and `towerComplex W`.

No hypothesis on `T` or `W` beyond being `ℓ`-divisible systems of complexes is
used; in particular no Mittag-Leffler, finiteness or projectivity condition
enters. The equivalences are unconditional.

## Smooth representations (namespace `Langlands.Cohomology`)

For a commutative ring `R` and a group `G` with a topology,
`smoothTowerComplex T` (`abbrev`) is `towerComplex T` for
`T : SmoothRepComplexDivisibleSystem R G ℓ`, a cochain complex in
`ℕᵒᵖ ⥤ SmoothRep R G`. All results above apply to it with `C = SmoothRep R G`.

## Provenance and interpretation

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), end of the proof of Proposition 4.10,
printed p.312 (one-based PDF page 14; Worker 61 read the rendered scanned
page). After checking the Mittag-Leffler condition for the complexes (4.10.2)
as `m` varies, Harris writes: "In fact, we have proved the stronger (integral)
statement

(4.10.4) `E_2^{i,j} = Ext^i(H_c^{2(n-1)-j}(M̆_N, 𝒪(n-1)), 𝒜_ℓ(GJ, 𝓛, H)) ⇒
H^{i+j}(S̄_{K(N)}, 𝓛̃)`."

This module prepares a formalization of such an integral statement for
`ℓ`-divisible systems, in our own formulation: the system `m ↦ T m` of
complexes at finite level `m` is regarded as one complex `towerComplex T` of
inverse systems, whose cohomology is the inverse system of the cohomology
objects `H^q(T m)`, and the cohomology of the inverse limit
`homComplexLimit R T W` of the Hom complexes at finite level (the object
studied by the published `HomComplexLimit` module) is identified with
morphisms in the homotopy category of complexes of inverse systems. Reading
the integral Ext groups of (4.10.4) as Ext groups computed in the category of
inverse systems is our interpretation, intended for a later module; it is not
stated by Harris on this page and is not used by any declaration here.

The constructions, statements and proofs are ours; the module is derived.
`diagramComplex` is the inverse direction of Mathlib's
`HomologicalComplex.asFunctor`; the levelwise computation of cohomology is the
published `diagramHomologyIso`, and the identification of Hom-complex
cohomology with morphisms in the homotopy category is Mathlib's.

## Scope

The module defines no Ext groups and no spectral sequence, and does not
formalize (4.10.4). It does not identify `homComplexLimit R T W` or the
morphisms in the homotopy category with morphisms in a derived category, and
it does not identify Harris's complexes (4.10.2), the cohomology
`H_c^{2(n-1)-j}(M̆_N, 𝒪(n-1))` or the space `𝒜_ℓ(GJ, 𝓛, H)` with the published
`ℓ`-divisible systems. The smooth abbreviation is a specialization; no
smooth-specific result is proved.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Dependencies are the modules named above, pinned to Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
