# Algebraic Künneth formula over a field

Lean module: `Langlands.Cohomology.ModuleComplex.FieldKunneth`
(namespace `Langlands.Cohomology.ModuleComplex.FieldKunneth`).

## Main result

For a field `K` and cochain complexes `C D : CochainComplex (ModuleCat.{u} K) ℕ`,

- `kunnethIso C D n :
  (HomologicalComplex.mapBifunctor C D (curriedTensor (ModuleCat K)) (ComplexShape.up ℕ)).homology n ≅
  ModuleCat.of K (DirectSum {ab : ℕ × ℕ // ab.1 + ab.2 = n} fun ab =>
    TensorProduct K (C.homology ab.1.1) (D.homology ab.1.2))`.

The left side is the degree-`n` cohomology of the total complex of the
external tensor product of `C` and `D`, with the sign convention of
`Langlands.Cohomology.ModuleComplex.TensorSignsUpNat` (differential
`d₁ + (-1)^p d₂` on the `(p, q)` summand). This is the classical algebraic
Künneth formula over a field: `Hⁿ(Tot(C ⊗ D)) ≅ ⨁_{a+b=n} Hᵃ(C) ⊗_K Hᵇ(D)`.
`kunnethIso` is a `def` (data, an isomorphism in `ModuleCat K`); it is built
with choices and no explicit formula for the map is claimed.

## Auxiliary declarations

General (any preadditive categories, any bifunctor `F` additive in each
variable and any total complex shape):

- `mapBifunctorMap_comp`, `mapBifunctorMap_id`: functoriality of
  `HomologicalComplex.mapBifunctorMap` in both variables.
- `mapBifunctorHomotopyEquiv e₁ e₂ : HomotopyEquiv (mapBifunctor K₁ K₂ F c) (mapBifunctor L₁ L₂ F c)`
  for homotopy equivalences `e₁ : HomotopyEquiv K₁ L₁`, `e₂ : HomotopyEquiv K₂ L₂`.
  The maps are `mapBifunctorMap e₁.hom e₂.hom` and `mapBifunctorMap e₁.inv e₂.inv`;
  the homotopies are obtained from Mathlib's `mapBifunctorMapHomotopy₁` and
  `mapBifunctorMapHomotopy₂` (`Mathlib/Algebra/Homology/BifunctorHomotopy.lean`)
  applied to the homotopies of `e₁` and `e₂`, composed with the functoriality
  lemmas above.
- `homologyIsoXOfDEqZero A hA n : A.homology n ≅ A.X n` for an `ℕ`-indexed
  cochain complex `A` whose differentials all vanish (in a category with
  homology).

Over a field `K`:

- instances `injective_moduleCat`, `projective_moduleCat`: every object of
  `ModuleCat K` is injective and projective (fields are semisimple rings;
  `Module.injective_of_isSemisimpleRing`, `Module.projective_of_isSemisimpleRing`).
- `homologyComplex C` (an `abbrev`): the complex with terms `C.homology n` and
  zero differentials.
- `homologySection C n : C.homology n ⟶ C.cycles n`, a chosen section of
  `C.homologyπ n` (`Projective.factorThru`), with
  `homologySection_homologyπ : homologySection C n ≫ C.homologyπ n = 𝟙 _`.
- `homologyComplexι C : homologyComplex C ⟶ C`, degreewise
  `homologySection C n ≫ C.iCycles n`.
- `cyclesMap_homologyComplexι`, `homologyMap_homologyComplexι`: the induced map
  on homology is the composite of the canonical isomorphisms
  `(homologyComplex C).homology n ≅ (homologyComplex C).cycles n ≅ C.homology n`
  (the latter via the section), so it is an isomorphism.
- instance `quasiIso_homologyComplexι`.
- `homotopyEquivHomologyComplex C : HomotopyEquiv (homologyComplex C) C`, from
  Mathlib's `CochainComplex.quasiIso_iff_of_injective`
  (`Mathlib/Algebra/Homology/DerivedCategory/KInjective.lean`): a
  quasi-isomorphism between `ℕ`-indexed cochain complexes of injective objects
  is a homotopy equivalence.
- `mapBifunctor_d_eq_zero`: the total complex of two complexes with zero
  differentials has zero differentials.
- `mapBifunctorXIso A B n :
  (mapBifunctor A B (curriedTensor (ModuleCat K)) (ComplexShape.up ℕ)).X n ≅
  ModuleCat.of K (DirectSum {ab : ℕ × ℕ // ab.1 + ab.2 = n} fun ab =>
    TensorProduct K (A.X ab.1.1) (B.X ab.1.2))`, which is Mathlib's
  `ModuleCat.coprodIsoDirectSum` (the degree-`n` term of the total complex is
  by definition the coproduct of the `A.X a ⊗ B.X b` with `a + b = n`).

## Proof of `kunnethIso`

`kunnethIso C D n` is the composite

1. the inverse of the homology isomorphism induced by the homotopy equivalence
   `mapBifunctorHomotopyEquiv (homotopyEquivHomologyComplex C) (homotopyEquivHomologyComplex D)`
   (`HomotopyEquiv.toHomologyIso`), identifying the cohomology of
   `Tot(C ⊗ D)` with that of `Tot(H(C) ⊗ H(D))`;
2. `homologyIsoXOfDEqZero`, using `mapBifunctor_d_eq_zero` for
   `H(C) = homologyComplex C` and `H(D) = homologyComplex D`;
3. `mapBifunctorXIso (homologyComplex C) (homologyComplex D) n`.

## Provenance

The statement is the standard Künneth formula for complexes of vector spaces
(used, for example, in the proof of Stacks Project Lemma 0BED, `varieties.tex`,
"Künneth formula" section). The Lean route (homology complex with zero
differential, quasi-isomorphism of complexes of injectives is a homotopy
equivalence, total complexes preserve homotopy equivalences) is a choice made
for this formalisation; it avoids constructing explicit splittings.
