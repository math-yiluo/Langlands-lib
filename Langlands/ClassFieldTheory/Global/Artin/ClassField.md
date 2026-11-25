# The class field of an open subgroup of the idèle class group

Module `Langlands.ClassFieldTheory.Global.Artin.ClassField`, name space
`Langlands.ClassFieldTheory.Global.Artin`. This file belongs to the Library; it states the
existence theorem and the uniqueness of class fields of the NYLL library (the copy under
`Nyll/`) for subfields of the Library's algebraic closure `AlgebraicClosure K`.

For a number field `K` and an open subgroup `H` of `IdeleClasses K`, `classField K H` is a
finite abelian subextension of `AlgebraicClosure K` whose arithmetic Artin map
(`arithmeticFiniteArtin`, `FiniteArtin`) has kernel exactly `H`, and it is the only finite
abelian subextension with this property. Along the way: isomorphic extensions have the same norm
group, and the norm group determines a finite abelian extension up to isomorphism, hence a finite
abelian subfield of `AlgebraicClosure K` itself.

## Main declarations

```lean
theorem ideleClassNorm_range_eq_of_algEquiv {K : Type u} [Field K] [NumberField K]
    {L : Type v} {L' : Type w} [Field L] [NumberField L] [Algebra K L]
    [Field L'] [NumberField L'] [Algebra K L'] (e : L ≃ₐ[K] L') :
    (_root_.ideleClassNorm K L').range = (_root_.ideleClassNorm K L).range

theorem nonempty_algEquiv_of_ideleClassNorm_range_eq {K : Type u} [Field K] [NumberField K]
    {L : Type v} {L' : Type w} [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    [IsAbelianGalois K L] [Field L'] [NumberField L'] [Algebra K L'] [FiniteDimensional K L']
    [IsAbelianGalois K L']
    (h : (_root_.ideleClassNorm K L).range = (_root_.ideleClassNorm K L').range) :
    Nonempty (L ≃ₐ[K] L')

theorem eq_of_ideleClassNorm_range_eq {K : Type u} [Field K] [NumberField K]
    (L E : IntermediateField K (AlgebraicClosure K))
    [FiniteDimensional K L] [IsAbelianGalois K L] [FiniteDimensional K E] [IsAbelianGalois K E] :
    letI := NumberField.of_module_finite K L
    letI := NumberField.of_module_finite K E
    (_root_.ideleClassNorm K L).range = (_root_.ideleClassNorm K E).range → L = E

theorem eq_of_arithmeticFiniteArtin_ker_eq {K : Type u} [Field K] [NumberField K]
    (L E : IntermediateField K (AlgebraicClosure K))
    [FiniteDimensional K L] [IsAbelianGalois K L] [FiniteDimensional K E] [IsAbelianGalois K E] :
    letI := NumberField.of_module_finite K L
    letI := NumberField.of_module_finite K E
    (arithmeticFiniteArtin K L).ker = (arithmeticFiniteArtin K E).ker → L = E
```

For `K : Type u`, `[Field K] [NumberField K]` and `H : OpenSubgroup (IdeleClasses K)`:

```lean
def nyllSubgroup : Subgroup (_root_.IdeleClassGroup K) :=
  H.toSubgroup.comap (nyllIdeleClassEquiv K).toMulEquiv.toMonoidHom

theorem nyllSubgroup_isClosed : IsClosed (nyllSubgroup K H : Set (_root_.IdeleClassGroup K))
instance nyllSubgroup_finiteIndex : (nyllSubgroup K H).FiniteIndex
theorem map_nyllSubgroup :
    (nyllSubgroup K H).map (nyllIdeleClassEquiv K).toMulEquiv.toMonoidHom = H.toSubgroup

abbrev nyllClassField : Type :=
  GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassField
    (nyllSubgroup K H) (nyllSubgroup_isClosed K H)

def nyllClassFieldEmbedding : nyllClassField K H →ₐ[K] AlgebraicClosure K
def classField : IntermediateField K (AlgebraicClosure K) :=
  (nyllClassFieldEmbedding K H).fieldRange
def nyllClassFieldEquiv : nyllClassField K H ≃ₐ[K] classField K H

instance classField_finiteDimensional : FiniteDimensional K (classField K H)
instance classField_isAbelianGalois : IsAbelianGalois K (classField K H)

theorem ideleClassNorm_classField_range :
    letI := NumberField.of_module_finite K (classField K H)
    (_root_.ideleClassNorm K (classField K H)).range = nyllSubgroup K H

theorem arithmeticFiniteArtin_classField_ker :
    letI := NumberField.of_module_finite K (classField K H)
    (arithmeticFiniteArtin K (classField K H)).ker = H.toSubgroup

theorem classField_eq_iff (L : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K L]
    [IsAbelianGalois K L] :
    letI := NumberField.of_module_finite K L
    classField K H = L ↔ (arithmeticFiniteArtin K L).ker = H.toSubgroup
```

`nyllClassField K H` is a field in universe `0` (NYLL's construction); `classField K H` is in the
universe of `K`. The embedding `nyllClassFieldEmbedding K H` is a choice (`IsAlgClosed.lift`),
but its image is not: the extension is normal, so every `K`-embedding into `AlgebraicClosure K`
has the same image, and `classField_eq_iff` characterizes `classField K H` without reference to
the embedding.

## Proofs

- *Norm groups of isomorphic extensions*: NYLL's
  `ordinaryIdeleClassNorm_range_map_congrOfAlgEquiv` for the pair of isomorphisms
  `(AlgEquiv.refl, e)`, with `ideleClassCongr_refl`.
- *The norm group determines the extension.* NYLL places each finite abelian extension `L` inside
  its maximal abelian extension `maximalAbelianExtension K ⊆ SeparableClosure K`, as a finite
  layer `finiteAbelianExtensionInMaximalAbelianExtension K L` isomorphic to `L` with the same norm
  group. For a finite layer `E` the preimage of its fixing subgroup under NYLL's maximal abelian
  Artin map is the norm group of `E` (`maximalAbelianGlobalArtin_comap_fixingSubgroup`), and that
  map is surjective. So equal norm groups give equal fixing subgroups, hence equal layers by the
  infinite Galois correspondence (`InfiniteGalois.fixedField_fixingSubgroup`), hence isomorphic
  extensions.
- *Subfields of the algebraic closure.* If `L` and `E` in `AlgebraicClosure K` are isomorphic over
  `K`, the image of `L` under the composite `K`-embedding `L ≅ E ⊆ AlgebraicClosure K` is `E`; as
  `L` is normal, the image of every `K`-embedding of `L` is `L` (`AlgHom.fieldRange_of_normal`).
  So `L = E`. With `arithmeticFiniteArtin_ker` (the kernel is the image of the norm group under an
  injective map) this gives `eq_of_arithmeticFiniteArtin_ker_eq`.
- *The class field.* `nyllSubgroup K H` is closed (preimage of a closed set) and of finite index
  (`openSubgroup_finiteIndex`, same index). NYLL's class field of it has norm group exactly
  `nyllSubgroup K H` (`closedFiniteIndexClassField_ideleClassNorm_range`) and is finite and abelian
  over `K`; these transfer along `nyllClassFieldEquiv`. The kernel of the arithmetic Artin map is
  then the image of `nyllSubgroup K H` under the comparison of idèle class groups, which is `H`.
  `classField_eq_iff` combines this with `eq_of_arithmeticFiniteArtin_ker_eq`.

## Declarations used

- From the NYLL copy: `maximalAbelianExtension`, `finiteAbelianExtensionInMaximalAbelianExtension`,
  `finiteAbelianExtensionEquivInMaximalAbelianExtension`
  (`Nyll/ClassFieldTheory/AlgebraicNumberTheory/Galois/AbsoluteAbelianization.lean`);
  `ideleClassNorm`, `ideleClassCongr`, `ordinaryIdeleClassNorm_range_map_congrOfAlgEquiv`
  (`…/Idele/ClassGroup/AlgEquiv.lean`), `ideleClassCongr_refl`
  (`…/Idele/ClassGroup/TowerAlgEquivNaturality.lean`);
  `GlobalClassFieldTheory.Reciprocity.maximalAbelianGlobalArtin`, `_surjective`,
  `finiteAbelianExtensionInMaximalAbelianExtension_ideleClassNorm_range`
  (`…/GlobalClassFieldTheory/Reciprocity/MaximalAbelianGlobalArtin.lean`, `MaximalAbelianKernel.lean`);
  `GlobalClassFieldTheory.GlobalClassFields.maximalAbelianGlobalArtin_comap_fixingSubgroup`
  (`…/GlobalClassFields/InfiniteAbelianClassFieldCorrespondence.lean`);
  `closedFiniteIndexClassField` with its instances over `K` and
  `closedFiniteIndexClassField_ideleClassNorm_range`
  (`…/GlobalClassFields/ClosedFiniteIndexClassFieldConstruction.lean`,
  `ClosedFiniteIndexClassFieldOriginalField.lean`).
- From the Library: `nyllIdeleClassEquiv` (`IdeleClassComparison`), `arithmeticFiniteArtin`,
  `arithmeticFiniteArtin_ker` (`FiniteArtin`), `openSubgroup_finiteIndex`
  (`OpenSubgroupFiniteIndex`), `IdeleClasses`.
- From Mathlib: `IsAlgClosed.lift`, `AlgEquiv.ofInjectiveField`, `AlgHom.fieldRange_of_normal`,
  `IsAbelianGalois.of_algHom`, `IntermediateField.equivOfEq`,
  `InfiniteGalois.fixedField_fixingSubgroup`, `NumberField.of_module_finite`.

## Sources

Neukirch, *Algebraic Number Theory*, Chapter VI, (6.1) (existence theorem: the correspondence
between finite abelian extensions and open subgroups of finite index of the idèle class group);
Milne, *Class Field Theory*, Chapter V, Theorem 5.5 and Corollary 5.6; Artin–Tate, *Class Field
Theory* (existence theorem).
