import Langlands.ClassFieldTheory.Global.Artin.FiniteArtinNormalization
import Langlands.ClassFieldTheory.Local.Galois
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Galois.AbsoluteAbelianization
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Galois.MaximalAbelianBaseEquiv
import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.ArithmeticNormalization
import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalArtinCompatibility
import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.MathlibGlobalArtinNaturality
import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.MathlibTopologicalGlobalReciprocity
import Mathlib.FieldTheory.SeparableClosure

/-!
# The global Artin map on the abelianized absolute Galois group

This file belongs to the Library. For a number field `K` it names the global Artin map
`geometricArtinMap K : IdeleClasses K →ₜ* Field.absoluteGaloisGroupAbelianization K` from the
Library's idèle classes onto the topological abelianization of the absolute Galois group, in
the **geometric** normalization, and proves that it is surjective, that its kernel is the
connected component of the identity, and that its restriction to every finite abelian
extension `L` of `K` inside `AlgebraicClosure K` (the Library's
`Langlands.LocalClassField.FiniteAbelianExtension K`) is the inverse of the arithmetic Artin
map `arithmeticFiniteArtin K L.field` of `FiniteArtin.lean`.

The map is the NYLL library's `GlobalClassFieldTheory.Reciprocity.mathlibGlobalArtin K`, which
is stated on Mathlib's idèle class group and Mathlib's `Field.absoluteGaloisGroupAbelianization`,
the very types of the Library. Surjectivity and the kernel are NYLL's. For the finite
restrictions, NYLL proves that the restriction of its map, read in the Galois group of its
maximal abelian extension `maximalAbelianExtension K ⊆ SeparableClosure K`, to a finite abelian
extension `L` embedded in it is its geometric finite Artin map; the glue here embeds a finite
abelian subextension of `AlgebraicClosure K` into NYLL's maximal abelian extension
(`nyllMaximalAbelianEmbedding`) and shows that restriction through `SeparableClosure K` and
NYLL's maximal abelian extension is restriction from `AlgebraicClosure K`.

## Main declarations

* `geometricArtinMap K`, `geometricArtinMap_surjective`, `geometricArtinMap_ker`.
* `restrictNormalHom_eq_inv_arithmeticFiniteArtin`: for a finite abelian subextension `E` of
  `AlgebraicClosure K` and a lift `σ` of `geometricArtinMap K x`, the restriction of `σ` to `E`
  is `(arithmeticFiniteArtin K E x)⁻¹`.
* `abelianRestriction_geometricArtinMap`: the same in the vocabulary of
  `FiniteAbelianExtension`, and `arithmeticFiniteArtin_eq_inv_abelianRestriction`.
* `abelianRestriction_geometricArtinMap_finiteClassInclusion_of_unit`,
  `abelianRestriction_geometricArtinMap_finiteClassInclusion_inv_isArithFrobAt`: local units
  at an unramified place go to `1`, and the inverse of the image of a uniformizer there is an
  arithmetic Frobenius.

## Sources

Neukirch, *Algebraic Number Theory*, Chapter VI, §5, Theorem (5.5) and Proposition (5.6)
(p. 391) and Exercise 1 (p. 394: `C_K / D_K ≅ G(K^ab|K)`); Milne, *Class Field Theory*,
Chapter V, Proposition 5.2, Theorem 5.3 and Remark 5.7(a) (pp. 178–179). Both normalize
arithmetically; `geometricArtinMap` is the inverse of their maps.
-/

noncomputable section

universe u

namespace Langlands.ClassFieldTheory.Global.Artin

open Langlands.Global
open scoped NumberField

section Instances

variable {K : Type u} [Field K]

/-- A finite abelian extension in the Library's vocabulary is abelian Galois over `K`. -/
instance finiteAbelianExtension_isAbelianGalois (L : LocalClassField.FiniteAbelianExtension K) :
    IsAbelianGalois K L.field :=
  ⟨⟩

/-- A finite abelian extension of a number field is a number field. -/
instance finiteAbelianExtension_numberField [NumberField K]
    (L : LocalClassField.FiniteAbelianExtension K) : NumberField L.field :=
  NumberField.of_module_finite K L.field

end Instances

section Embedding

variable {K : Type u} [Field K] [NumberField K]

omit [NumberField K] in
/-- A Galois subextension of `AlgebraicClosure K` lies in the separable closure. -/
theorem le_separableClosure_of_isGalois (E : IntermediateField K (AlgebraicClosure K))
    [IsGalois K E] : E ≤ separableClosure K (AlgebraicClosure K) :=
  le_separableClosure K (AlgebraicClosure K) E

omit [NumberField K] in
/-- An element of a finite abelian subextension of `AlgebraicClosure K`, read in the separable
closure, lies in NYLL's maximal abelian extension. -/
theorem mem_maximalAbelianExtension_of_isAbelianGalois
    (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E] [IsAbelianGalois K E]
    (x : E) :
    (⟨x, le_separableClosure_of_isGalois E x.2⟩ : SeparableClosure K) ∈
      maximalAbelianExtension K := by
  let h := le_separableClosure_of_isGalois E
  let E₁ : IntermediateField K (SeparableClosure K) := IntermediateField.restrict h
  let e : E ≃ₐ[K] E₁ := IntermediateField.restrictAlgEquiv h
  have : FiniteDimensional K E₁ := e.toLinearEquiv.finiteDimensional
  have : IsAbelianGalois K E₁ := IsAbelianGalois.of_algHom e.symm.toAlgHom
  exact finiteAbelianIntermediateField_le_maximalAbelianExtension K E₁
    ((IntermediateField.mem_restrict h _).2 x.2)

omit [NumberField K] in
/-- A finite abelian subextension of `AlgebraicClosure K` embeds into NYLL's maximal abelian
extension, a subfield of `SeparableClosure K`; the embedding is the identity on elements of
`AlgebraicClosure K`. -/
def nyllMaximalAbelianEmbedding (E : IntermediateField K (AlgebraicClosure K))
    [FiniteDimensional K E] [IsAbelianGalois K E] : E →ₐ[K] maximalAbelianExtension K where
  toFun x := ⟨⟨x, le_separableClosure_of_isGalois E x.2⟩,
    mem_maximalAbelianExtension_of_isAbelianGalois E x⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

omit [NumberField K] in
theorem nyllMaximalAbelianEmbedding_coe (E : IntermediateField K (AlgebraicClosure K))
    [FiniteDimensional K E] [IsAbelianGalois K E] (x : E) :
    (((nyllMaximalAbelianEmbedding E x : maximalAbelianExtension K) : SeparableClosure K) :
      AlgebraicClosure K) = x :=
  rfl

omit [NumberField K] in
/-- Restricting an automorphism of `AlgebraicClosure K` to the separable closure, then to NYLL's
maximal abelian extension, then to a finite abelian subextension `E` (embedded by
`nyllMaximalAbelianEmbedding`) is restricting it to `E` directly. -/
theorem restrictNormalHom_restrictNormalHom_separableClosure
    (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E] [IsAbelianGalois K E]
    (σ : Gal(AlgebraicClosure K/K)) :
    letI := (nyllMaximalAbelianEmbedding E).toRingHom.toAlgebra
    letI := IsScalarTower.of_algHom (nyllMaximalAbelianEmbedding E)
    AlgEquiv.restrictNormalHom E
        (AlgEquiv.restrictNormalHom (maximalAbelianExtension K) (AlgEquiv.separableClosure σ)) =
      AlgEquiv.restrictNormalHom (K₁ := AlgebraicClosure K) E σ := by
  let := (nyllMaximalAbelianEmbedding E).toRingHom.toAlgebra
  let := IsScalarTower.of_algHom (nyllMaximalAbelianEmbedding E)
  ext x
  have h1 := AlgEquiv.restrictNormal_commutes
    (AlgEquiv.restrictNormalHom (maximalAbelianExtension K) (AlgEquiv.separableClosure σ)) E x
  have h2 := congrArg
    (fun y : maximalAbelianExtension K => ((y : SeparableClosure K) : AlgebraicClosure K)) h1
  rw [AlgEquiv.restrictNormalHom_apply]
  change ((algebraMap E (maximalAbelianExtension K) _ : SeparableClosure K) :
    AlgebraicClosure K) = σ (x : AlgebraicClosure K)
  refine h2.trans ?_
  rw [AlgEquiv.restrictNormalHom_apply]
  rfl

end Embedding

section ArtinMap

variable (K : Type u) [Field K] [NumberField K]

/-- The global Artin map of a number field on the Library's idèle classes, onto the topological
abelianization of the absolute Galois group, in the geometric normalization: a uniformizer at a
place unramified in a finite abelian extension goes to the inverse of the arithmetic Frobenius
there (`abelianRestriction_geometricArtinMap_finiteClassInclusion_inv_isArithFrobAt`). It is the
NYLL library's `mathlibGlobalArtin K`. -/
def geometricArtinMap : IdeleClasses K →ₜ* Field.absoluteGaloisGroupAbelianization K :=
  GlobalClassFieldTheory.Reciprocity.mathlibGlobalArtin K

theorem geometricArtinMap_apply (x : IdeleClasses K) :
    geometricArtinMap K x = GlobalClassFieldTheory.Reciprocity.mathlibGlobalArtin K x :=
  rfl

theorem geometricArtinMap_surjective : Function.Surjective (geometricArtinMap K) :=
  GlobalClassFieldTheory.Reciprocity.mathlibGlobalArtin_surjective K

/-- The kernel of the global Artin map is the connected component of the identity of the idèle
class group. -/
theorem geometricArtinMap_ker :
    (geometricArtinMap K).toMonoidHom.ker = Subgroup.connectedComponentOfOne (IdeleClasses K) :=
  GlobalClassFieldTheory.Reciprocity.mathlibGlobalArtin_ker K

variable {K}

/-- If `σ` in the absolute Galois group lifts `geometricArtinMap K x`, its restriction to a finite
abelian subextension `E` of `AlgebraicClosure K` is the inverse of the arithmetic Artin map of
`E / K` at `x`. -/
theorem restrictNormalHom_eq_inv_arithmeticFiniteArtin
    (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E] [IsAbelianGalois K E]
    (x : IdeleClasses K) (σ : Field.absoluteGaloisGroup K)
    (hσ : LocalClassField.absoluteAbelianizationProjection K σ = geometricArtinMap K x) :
    letI := NumberField.of_module_finite K E
    AlgEquiv.restrictNormalHom (K₁ := AlgebraicClosure K) E σ =
      (arithmeticFiniteArtin K E x)⁻¹ := by
  let := NumberField.of_module_finite K E
  let := (nyllMaximalAbelianEmbedding E).toRingHom.toAlgebra
  let := IsScalarTower.of_algHom (nyllMaximalAbelianEmbedding E)
  rw [← restrictNormalHom_restrictNormalHom_separableClosure E σ,
    ← ClassFieldTheory.mathlibAbelianizationToMaximal_mk]
  change AlgEquiv.restrictNormalHom E (ClassFieldTheory.mathlibAbelianizationToMaximal K
    (LocalClassField.absoluteAbelianizationProjection K σ)) = _
  rw [hσ, geometricArtinMap,
    GlobalClassFieldTheory.Reciprocity.mathlibGlobalArtin_finiteProjection_of_scalarTower,
    GlobalClassFieldTheory.Reciprocity.globalIdeleClassArtinMonoidHom_eq_globalNormResidueMonoidHom,
    arithmeticFiniteArtin_apply,
    GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueMonoidHom_apply, inv_inv]
  rfl

/-- The restriction of the geometric Artin map to a finite abelian extension `L` is the inverse
of the arithmetic Artin map of `L / K`. -/
theorem abelianRestriction_geometricArtinMap (L : LocalClassField.FiniteAbelianExtension K)
    (x : IdeleClasses K) :
    L.abelianRestriction (geometricArtinMap K x) = (arithmeticFiniteArtin K L.field x)⁻¹ := by
  obtain ⟨σ, hσ⟩ := QuotientGroup.mk'_surjective
    (commutator (Field.absoluteGaloisGroup K)).topologicalClosure (geometricArtinMap K x)
  rw [← hσ]
  exact restrictNormalHom_eq_inv_arithmeticFiniteArtin L.field.toIntermediateField x σ hσ

/-- The arithmetic Artin map of a finite abelian extension `L` is the inverse of the restriction
of the geometric Artin map. -/
theorem arithmeticFiniteArtin_eq_inv_abelianRestriction
    (L : LocalClassField.FiniteAbelianExtension K) (x : IdeleClasses K) :
    arithmeticFiniteArtin K L.field x = (L.abelianRestriction (geometricArtinMap K x))⁻¹ := by
  rw [abelianRestriction_geometricArtinMap, inv_inv]

/-- At a finite place below a prime of `L` unramified over `K`, the restriction of the geometric
Artin map to `L` kills the local units. -/
theorem abelianRestriction_geometricArtinMap_finiteClassInclusion_of_unit
    (L : LocalClassField.FiniteAbelianExtension K) (v : Langlands.Global.FinitePlace K)
    (w : Langlands.Global.FinitePlace L.field) (hw : w.asIdeal.LiesOver v.asIdeal)
    (hunram : Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal) (a : (FiniteCompletion K v)ˣ)
    (ha : a ∈ (v.adicCompletionIntegers K).units) :
    L.abelianRestriction (geometricArtinMap K (finiteClassInclusion K v a)) = 1 := by
  rw [abelianRestriction_geometricArtinMap,
    arithmeticFiniteArtin_finiteClassInclusion_of_unit v w hw hunram a ha, inv_one]

/-- At a finite place below a prime `w` of `L` unramified over `K`, the inverse of the image of
any uniformizer under the restriction of the geometric Artin map is an arithmetic Frobenius at
`w`: the geometric normalization. -/
theorem abelianRestriction_geometricArtinMap_finiteClassInclusion_inv_isArithFrobAt
    (L : LocalClassField.FiniteAbelianExtension K) (v : Langlands.Global.FinitePlace K)
    (w : Langlands.Global.FinitePlace L.field) (hw : w.asIdeal.LiesOver v.asIdeal)
    (hunram : Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal) (π : (FiniteCompletion K v)ˣ)
    (hπ : Valued.v (π : FiniteCompletion K v) = WithZero.exp (-1 : ℤ)) :
    (NumberField.RingOfIntegers.mapAlgHom
      (L.abelianRestriction (geometricArtinMap K (finiteClassInclusion K v π)))⁻¹).IsArithFrobAt
        w.asIdeal := by
  rw [← arithmeticFiniteArtin_eq_inv_abelianRestriction]
  exact arithmeticFiniteArtin_hasArithmeticArtinNormalization v w hw hunram π hπ

end ArtinMap

end Langlands.ClassFieldTheory.Global.Artin
