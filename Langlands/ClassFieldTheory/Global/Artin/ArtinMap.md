# The global Artin map on the abelianized absolute Galois group

Module `Langlands.ClassFieldTheory.Global.Artin.ArtinMap`, name space
`Langlands.ClassFieldTheory.Global.Artin`. This file belongs to the Library; it names the global
Artin map of a number field on the Library's idèle classes, with values in the topological
abelianization of the absolute Galois group, and relates it to the arithmetic Artin maps of the
finite abelian extensions (`FiniteArtin`).

For a number field `K`, `geometricArtinMap K` is a continuous homomorphism from
`IdeleClasses K` (Mathlib's idèle class group) onto `Field.absoluteGaloisGroupAbelianization K`
(the quotient of `Gal(AlgebraicClosure K / K)` by the closure of its commutator subgroup). It is
surjective and its kernel is the connected component of the identity of the idèle class
group. It is in the **geometric** normalization: for every finite abelian extension `L` of `K`
inside `AlgebraicClosure K`, its restriction to `L` is the inverse of the arithmetic Artin map
`arithmeticFiniteArtin K L`, so a uniformizer at a place unramified in `L` goes to the inverse of
the arithmetic Frobenius. The finite extensions are those of the Library's local profinite
reciprocity, `Langlands.LocalClassField.FiniteAbelianExtension K`, with the restriction map
`abelianRestriction` (`Langlands/ClassFieldTheory/Local/Galois.lean`).

## Main declarations

Throughout, `K : Type u` and `[Field K] [NumberField K]`, except that the declarations before
`geometricArtinMap` other than `finiteAbelianExtension_numberField` assume only `[Field K]`;
`LocalClassField` is `Langlands.LocalClassField`, `FinitePlace` is
`Langlands.Global.FinitePlace`, and `𝓞` is `NumberField.RingOfIntegers`.

```lean
instance finiteAbelianExtension_isAbelianGalois (L : LocalClassField.FiniteAbelianExtension K) :
    IsAbelianGalois K L.field

instance finiteAbelianExtension_numberField [NumberField K]
    (L : LocalClassField.FiniteAbelianExtension K) : NumberField L.field

theorem le_separableClosure_of_isGalois (E : IntermediateField K (AlgebraicClosure K))
    [IsGalois K E] : E ≤ separableClosure K (AlgebraicClosure K)

theorem mem_maximalAbelianExtension_of_isAbelianGalois
    (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E] [IsAbelianGalois K E]
    (x : E) :
    (⟨x, le_separableClosure_of_isGalois E x.2⟩ : SeparableClosure K) ∈
      maximalAbelianExtension K

def nyllMaximalAbelianEmbedding (E : IntermediateField K (AlgebraicClosure K))
    [FiniteDimensional K E] [IsAbelianGalois K E] : E →ₐ[K] maximalAbelianExtension K

theorem nyllMaximalAbelianEmbedding_coe (E : IntermediateField K (AlgebraicClosure K))
    [FiniteDimensional K E] [IsAbelianGalois K E] (x : E) :
    (((nyllMaximalAbelianEmbedding E x : maximalAbelianExtension K) : SeparableClosure K) :
      AlgebraicClosure K) = x

theorem restrictNormalHom_restrictNormalHom_separableClosure
    (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E] [IsAbelianGalois K E]
    (σ : Gal(AlgebraicClosure K/K)) :
    letI := (nyllMaximalAbelianEmbedding E).toRingHom.toAlgebra
    letI := IsScalarTower.of_algHom (nyllMaximalAbelianEmbedding E)
    AlgEquiv.restrictNormalHom E
        (AlgEquiv.restrictNormalHom (maximalAbelianExtension K) (AlgEquiv.separableClosure σ)) =
      AlgEquiv.restrictNormalHom (K₁ := AlgebraicClosure K) E σ

def geometricArtinMap : IdeleClasses K →ₜ* Field.absoluteGaloisGroupAbelianization K :=
  GlobalClassFieldTheory.Reciprocity.mathlibGlobalArtin K

theorem geometricArtinMap_apply (x : IdeleClasses K) :
    geometricArtinMap K x = GlobalClassFieldTheory.Reciprocity.mathlibGlobalArtin K x

theorem geometricArtinMap_surjective : Function.Surjective (geometricArtinMap K)

theorem geometricArtinMap_ker :
    (geometricArtinMap K).toMonoidHom.ker = Subgroup.connectedComponentOfOne (IdeleClasses K)

theorem restrictNormalHom_eq_inv_arithmeticFiniteArtin
    (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E] [IsAbelianGalois K E]
    (x : IdeleClasses K) (σ : Field.absoluteGaloisGroup K)
    (hσ : LocalClassField.absoluteAbelianizationProjection K σ = geometricArtinMap K x) :
    letI := NumberField.of_module_finite K E
    AlgEquiv.restrictNormalHom (K₁ := AlgebraicClosure K) E σ =
      (arithmeticFiniteArtin K E x)⁻¹

theorem abelianRestriction_geometricArtinMap (L : LocalClassField.FiniteAbelianExtension K)
    (x : IdeleClasses K) :
    L.abelianRestriction (geometricArtinMap K x) = (arithmeticFiniteArtin K L.field x)⁻¹

theorem arithmeticFiniteArtin_eq_inv_abelianRestriction
    (L : LocalClassField.FiniteAbelianExtension K) (x : IdeleClasses K) :
    arithmeticFiniteArtin K L.field x = (L.abelianRestriction (geometricArtinMap K x))⁻¹

theorem abelianRestriction_geometricArtinMap_finiteClassInclusion_of_unit
    (L : LocalClassField.FiniteAbelianExtension K) (v : FinitePlace K)
    (w : FinitePlace L.field) (hw : w.asIdeal.LiesOver v.asIdeal)
    (hunram : Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal) (a : (FiniteCompletion K v)ˣ)
    (ha : a ∈ (v.adicCompletionIntegers K).units) :
    L.abelianRestriction (geometricArtinMap K (finiteClassInclusion K v a)) = 1

theorem abelianRestriction_geometricArtinMap_finiteClassInclusion_inv_isArithFrobAt
    (L : LocalClassField.FiniteAbelianExtension K) (v : FinitePlace K)
    (w : FinitePlace L.field) (hw : w.asIdeal.LiesOver v.asIdeal)
    (hunram : Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal) (π : (FiniteCompletion K v)ˣ)
    (hπ : Valued.v (π : FiniteCompletion K v) = WithZero.exp (-1 : ℤ)) :
    (NumberField.RingOfIntegers.mapAlgHom
      (L.abelianRestriction (geometricArtinMap K (finiteClassInclusion K v π)))⁻¹).IsArithFrobAt
        w.asIdeal
```

`maximalAbelianExtension K` is the NYLL library's maximal abelian extension, the fixed field in
`SeparableClosure K` (Mathlib's `separableClosure K (AlgebraicClosure K)` as a type) of the
closure of the commutator subgroup. In `abelianRestriction_geometricArtinMap` the two instances
above supply `IsAbelianGalois K L.field` (needed by `arithmeticFiniteArtin`) and
`NumberField L.field`; both are propositions, so any other proof of them gives the same terms.
The first five declarations are the glue of the proof; the last two are the normalization of
the map at the unramified places, read off from `FiniteArtinNormalization`.

The name carries the normalization, as the finite map `arithmeticFiniteArtin` and the Library's
local profinite reciprocity (`GeometricProfiniteReciprocityRelation`) carry theirs.

## Proofs

`geometricArtinMap K` is NYLL's `mathlibGlobalArtin K`, which NYLL states on Mathlib's
`NumberField.IdeleClassGroup (𝓞 K) K` (the Library's `IdeleClasses K` by `abbrev`) and Mathlib's
`Field.absoluteGaloisGroupAbelianization K`; surjectivity and the kernel are NYLL's
`mathlibGlobalArtin_surjective` and `mathlibGlobalArtin_ker`.

For the finite restrictions, let `E ⊆ AlgebraicClosure K` be finite abelian over `K` and let `σ`
lift `geometricArtinMap K x`.

1. `E` is separable over `K`, so it lies in `separableClosure K (AlgebraicClosure K)` (Mathlib's
   `le_separableClosure`); as a subfield of `SeparableClosure K` (Mathlib's
   `IntermediateField.restrict`, with `restrictAlgEquiv` to carry finiteness and abelianness) it
   lies in NYLL's maximal abelian extension (`finiteAbelianIntermediateField_le_maximalAbelianExtension`).
   This gives `nyllMaximalAbelianEmbedding E`, the identity on elements, and with it an algebra
   structure of `maximalAbelianExtension K` over `E` and a scalar tower.
2. Restricting `σ` to the separable closure (`AlgEquiv.separableClosure`), then to the maximal
   abelian extension, then to `E`, is restricting `σ` to `E`
   (`restrictNormalHom_restrictNormalHom_separableClosure`, from Mathlib's
   `AlgEquiv.restrictNormal_commutes` twice, since every embedding in the chain is the identity
   on elements of `AlgebraicClosure K`).
3. NYLL's `mathlibAbelianizationToMaximal_mk` says that NYLL's identification of the
   abelianization with `Gal(maximalAbelianExtension K / K)` sends the class of `σ` to the
   restriction of `AlgEquiv.separableClosure σ`. So the restriction of `σ` to `E` is
   `restrictNormalHom E (mathlibAbelianizationToMaximal K (mathlibGlobalArtin K x))`, which NYLL's
   `mathlibGlobalArtin_finiteProjection_of_scalarTower` computes as its geometric finite map
   `globalIdeleClassArtinMonoidHom` at the corresponding class of NYLL's idèle class group.
   NYLL's `globalIdeleClassArtinMonoidHom_eq_globalNormResidueMonoidHom` makes this its global
   norm-residue map, of which the arithmetic map is the inverse by definition
   (`arithmeticGlobalNormResidueMonoidHom_apply`); `arithmeticFiniteArtin_apply` and
   `inv_inv` conclude.
4. `abelianRestriction_geometricArtinMap` is step 3 for `E = L.field`, since
   `L.abelianRestriction` sends the class of `σ` to `restrictNormalHom L.field σ` by definition.
   The last two theorems follow from it and `arithmeticFiniteArtin_finiteClassInclusion_of_unit`,
   `arithmeticFiniteArtin_hasArithmeticArtinNormalization` (`FiniteArtinNormalization`).

## Declarations used

- From the NYLL copy: `GlobalClassFieldTheory.Reciprocity.mathlibGlobalArtin`,
  `mathlibGlobalArtin_surjective`, `mathlibGlobalArtin_ker`
  (`Nyll/ClassFieldTheory/GlobalClassFieldTheory/Reciprocity/MathlibTopologicalGlobalReciprocity.lean`);
  `mathlibGlobalArtin_finiteProjection_of_scalarTower` (`…/Reciprocity/MathlibGlobalArtinNaturality.lean`);
  `globalIdeleClassArtinMonoidHom_eq_globalNormResidueMonoidHom`
  (`…/Reciprocity/GlobalArtinCompatibility.lean`); `arithmeticGlobalNormResidueMonoidHom_apply`
  (`…/Reciprocity/ArithmeticNormalization.lean`); `ClassFieldTheory.mathlibAbelianizationToMaximal`,
  `mathlibAbelianizationToMaximal_mk` (`…/AlgebraicNumberTheory/Galois/MaximalAbelianBaseEquiv.lean`);
  `maximalAbelianExtension`, `finiteAbelianIntermediateField_le_maximalAbelianExtension`
  (`…/AlgebraicNumberTheory/Galois/AbsoluteAbelianization.lean`).
- From the Library: `arithmeticFiniteArtin`, `arithmeticFiniteArtin_apply` (`FiniteArtin`);
  `arithmeticFiniteArtin_finiteClassInclusion_of_unit`,
  `arithmeticFiniteArtin_hasArithmeticArtinNormalization` (`FiniteArtinNormalization`);
  `LocalClassField.FiniteAbelianExtension`, `abelianRestriction`,
  `absoluteAbelianizationProjection` (`Langlands/ClassFieldTheory/Local/Galois.lean`);
  `IdeleClasses`, `FinitePlace`, `FiniteCompletion`, `finiteClassInclusion`
  (`Langlands/Global/Adelic.lean`).
- From Mathlib: `le_separableClosure`, `AlgEquiv.separableClosure`, `IntermediateField.restrict`,
  `IntermediateField.restrictAlgEquiv`, `IntermediateField.mem_restrict`,
  `AlgEquiv.restrictNormal_commutes`, `AlgEquiv.restrictNormalHom_apply`,
  `IsScalarTower.of_algHom`, `IsAbelianGalois.of_algHom`, `NumberField.of_module_finite`.

## Sources

- Neukirch, *Algebraic Number Theory* (Springer, 1999), Chapter VI, §5: Theorem (5.5), p. 391
  (the global norm residue symbol `( , L|K) : C_K → G(L|K)^ab`, surjective with kernel
  `N_{L|K} C_L`); Proposition (5.6), p. 391 (compatibility with the local symbols); Exercise 1,
  p. 394 (`C_K / D_K ≅ G(K^ab|K)` for the connected component `D_K` of `C_K`). Neukirch's symbol
  is arithmetically normalized: Chapter IV, Proposition (5.7), p. 295, sends the Frobenius of an
  unramified extension to a prime element. `geometricArtinMap` composed with restriction is the
  inverse of Neukirch's symbol.
- Milne, *Class Field Theory* (v4.03, 2020), Chapter V, §5: Proposition 5.2, p. 178 (the global
  Artin map `φ_K : I_K → Gal(K^ab/K)` whose restrictions are the products of the local Artin
  maps), Theorem 5.3, pp. 178–179 (reciprocity law), Remark 5.7(a), p. 179 (surjectivity; the
  kernel on `C_K` is the connected component of `1`). Milne's local Artin maps are arithmetic:
  Chapter I, Theorem 1.1(a), p. 20, with `Frob_{L/K}` the element acting as `α ↦ α^q` on the
  residue field. `geometricArtinMap` is pointwise the inverse of Milne's `φ_K` on `C_K` (after
  NYLL's identification of the abelianization with `Gal(K^ab/K)`).
