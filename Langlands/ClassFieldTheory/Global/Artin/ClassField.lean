import Langlands.ClassFieldTheory.Global.Artin.FiniteArtin
import Langlands.ClassFieldTheory.Global.Artin.OpenSubgroupFiniteIndex
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Galois.AbsoluteAbelianization
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.AlgEquiv
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.TowerAlgEquivNaturality
import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldOriginalField
import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.InfiniteAbelianClassFieldCorrespondence
import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.MaximalAbelianKernel
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Normal.Basic

/-!
# The class field of an open subgroup of the idèle class group

This file belongs to the Library. For a number field `K` and an open subgroup `H` of the
Library's idèle class group `IdeleClasses K`, it constructs the class field of `H` as a finite
abelian subextension `classField K H` of `AlgebraicClosure K`, proves that the kernel of its
arithmetic Artin map is `H`, and proves that it is the only finite abelian subextension of
`AlgebraicClosure K` with this property.

The construction takes NYLL's class field of the corresponding closed subgroup of finite index
of NYLL's idèle class group (`GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassField`,
a field in universe `0` whose idèle-class norm group is that subgroup) and embeds it into
`AlgebraicClosure K`. The image does not depend on the embedding, because the extension is
normal; `classField_eq_iff` characterizes it intrinsically.

The uniqueness rests on the fact that the norm group determines a finite abelian extension
up to isomorphism (`nonempty_algEquiv_of_ideleClassNorm_range_eq`): NYLL places each finite
abelian extension inside its maximal abelian extension of `K`, without changing the norm group
(`finiteAbelianExtensionInMaximalAbelianExtension_ideleClassNorm_range`), and there the fixing
subgroup of a finite layer is the preimage of the norm group under the maximal abelian Artin
map, which is surjective (`maximalAbelianGlobalArtin_comap_fixingSubgroup`). Two normal
subfields of `AlgebraicClosure K` that are isomorphic over `K` are equal.

## Main declarations

* `ideleClassNorm_range_eq_of_algEquiv`: isomorphic extensions have the same norm group.
* `nonempty_algEquiv_of_ideleClassNorm_range_eq`, `eq_of_ideleClassNorm_range_eq`,
  `eq_of_arithmeticFiniteArtin_ker_eq`.
* `classField K H : IntermediateField K (AlgebraicClosure K)`, with instances
  `FiniteDimensional K (classField K H)` and `IsAbelianGalois K (classField K H)`.
* `arithmeticFiniteArtin_classField_ker`, `classField_eq_iff`.

## Sources

Neukirch, *Algebraic Number Theory*, VI (6.1) and (6.2); Milne, *Class Field Theory*,
V Theorem 5.5 and Corollary 5.6.
-/

noncomputable section

universe u v w

namespace Langlands.ClassFieldTheory.Global.Artin

open Langlands.Global

section NormGroup

variable {K : Type u} [Field K] [NumberField K]

/-- Two finite extensions of `K` that are isomorphic over `K` have the same idèle-class norm
group. -/
theorem ideleClassNorm_range_eq_of_algEquiv {L : Type v} {L' : Type w} [Field L] [NumberField L]
    [Algebra K L] [Field L'] [NumberField L'] [Algebra K L'] (e : L ≃ₐ[K] L') :
    (_root_.ideleClassNorm K L').range = (_root_.ideleClassNorm K L).range := by
  have h := ordinaryIdeleClassNorm_range_map_congrOfAlgEquiv (K := K) (K' := K) (L := L)
    (L' := L') (AlgEquiv.refl : K ≃ₐ[ℚ] K) (e.restrictScalars ℚ) (fun x => e.commutes x)
  have hid : (ideleClassCongr (AlgEquiv.refl : K ≃ₐ[ℚ] K)).toMonoidHom =
      MonoidHom.id (_root_.IdeleClassGroup K) :=
    MonoidHom.ext fun c => ideleClassCongr_refl c
  rw [hid, Subgroup.map_id] at h
  exact h.symm

/-- Two finite abelian extensions of `K` with the same idèle-class norm group are isomorphic
over `K`. -/
theorem nonempty_algEquiv_of_ideleClassNorm_range_eq {L : Type v} {L' : Type w} [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L] [Field L']
    [NumberField L'] [Algebra K L'] [FiniteDimensional K L'] [IsAbelianGalois K L']
    (h : (_root_.ideleClassNorm K L).range = (_root_.ideleClassNorm K L').range) :
    Nonempty (L ≃ₐ[K] L') := by
  have h1 := GlobalClassFieldTheory.GlobalClassFields.maximalAbelianGlobalArtin_comap_fixingSubgroup K
    (finiteAbelianExtensionInMaximalAbelianExtension K L)
  have h2 := GlobalClassFieldTheory.GlobalClassFields.maximalAbelianGlobalArtin_comap_fixingSubgroup K
    (finiteAbelianExtensionInMaximalAbelianExtension K L')
  have h3 :=
    GlobalClassFieldTheory.Reciprocity.finiteAbelianExtensionInMaximalAbelianExtension_ideleClassNorm_range
      K L
  have h4 :=
    GlobalClassFieldTheory.Reciprocity.finiteAbelianExtensionInMaximalAbelianExtension_ideleClassNorm_range
      K L'
  dsimp only at h1 h2 h3 h4
  have hfix : (finiteAbelianExtensionInMaximalAbelianExtension K L).toIntermediateField.fixingSubgroup =
      (finiteAbelianExtensionInMaximalAbelianExtension K L').toIntermediateField.fixingSubgroup := by
    apply Subgroup.comap_injective
      (GlobalClassFieldTheory.Reciprocity.maximalAbelianGlobalArtin_surjective K)
    exact h1.trans (h3.trans (h.trans (h4.symm.trans h2.symm)))
  have hEE' : (finiteAbelianExtensionInMaximalAbelianExtension K L).toIntermediateField =
      (finiteAbelianExtensionInMaximalAbelianExtension K L').toIntermediateField := by
    have := congrArg IntermediateField.fixedField hfix
    rwa [InfiniteGalois.fixedField_fixingSubgroup, InfiniteGalois.fixedField_fixingSubgroup] at this
  exact ⟨((finiteAbelianExtensionEquivInMaximalAbelianExtension K L).trans
    (IntermediateField.equivOfEq hEE')).trans
      (finiteAbelianExtensionEquivInMaximalAbelianExtension K L').symm⟩

/-- Two finite abelian subextensions of `AlgebraicClosure K` with the same idèle-class norm
group are equal. -/
theorem eq_of_ideleClassNorm_range_eq (L E : IntermediateField K (AlgebraicClosure K))
    [FiniteDimensional K L] [IsAbelianGalois K L] [FiniteDimensional K E] [IsAbelianGalois K E] :
    letI := NumberField.of_module_finite K L
    letI := NumberField.of_module_finite K E
    (_root_.ideleClassNorm K L).range = (_root_.ideleClassNorm K E).range → L = E := by
  let := NumberField.of_module_finite K L
  let := NumberField.of_module_finite K E
  intro h
  obtain ⟨φ⟩ := nonempty_algEquiv_of_ideleClassNorm_range_eq h
  have hrange : (E.val.comp φ.toAlgHom).fieldRange = E := by
    ext x
    rw [AlgHom.mem_fieldRange]
    constructor
    · rintro ⟨y, rfl⟩
      exact (φ y).property
    · intro hx
      exact ⟨φ.symm ⟨x, hx⟩, by simp⟩
  exact (AlgHom.fieldRange_of_normal (E.val.comp φ.toAlgHom)).symm.trans hrange

end NormGroup

section Kernel

variable {K : Type u} [Field K] [NumberField K]

/-- Two finite abelian subextensions of `AlgebraicClosure K` whose arithmetic Artin maps have
the same kernel are equal. -/
theorem eq_of_arithmeticFiniteArtin_ker_eq (L E : IntermediateField K (AlgebraicClosure K))
    [FiniteDimensional K L] [IsAbelianGalois K L] [FiniteDimensional K E] [IsAbelianGalois K E] :
    letI := NumberField.of_module_finite K L
    letI := NumberField.of_module_finite K E
    (arithmeticFiniteArtin K L).ker = (arithmeticFiniteArtin K E).ker → L = E := by
  let := NumberField.of_module_finite K L
  let := NumberField.of_module_finite K E
  intro h
  rw [arithmeticFiniteArtin_ker, arithmeticFiniteArtin_ker] at h
  exact eq_of_ideleClassNorm_range_eq L E
    (Subgroup.map_injective (nyllIdeleClassEquiv K).toMulEquiv.injective h)

end Kernel

section ClassField

variable (K : Type u) [Field K] [NumberField K] (H : OpenSubgroup (IdeleClasses K))

/-- The subgroup of NYLL's idèle class group corresponding to an open subgroup of the Library's
idèle class group. -/
def nyllSubgroup : Subgroup (_root_.IdeleClassGroup K) :=
  H.toSubgroup.comap (nyllIdeleClassEquiv K).toMulEquiv.toMonoidHom

theorem nyllSubgroup_isClosed : IsClosed (nyllSubgroup K H : Set (_root_.IdeleClassGroup K)) :=
  (H.isClosed).preimage (nyllIdeleClassEquiv K).continuous

instance nyllSubgroup_finiteIndex : (nyllSubgroup K H).FiniteIndex := by
  have := openSubgroup_finiteIndex K H
  have hindex : (nyllSubgroup K H).index = H.toSubgroup.index :=
    H.toSubgroup.index_comap_of_surjective (nyllIdeleClassEquiv K).surjective
  exact ⟨hindex ▸ Subgroup.FiniteIndex.index_ne_zero⟩

theorem map_nyllSubgroup :
    (nyllSubgroup K H).map (nyllIdeleClassEquiv K).toMulEquiv.toMonoidHom = H.toSubgroup :=
  Subgroup.map_comap_eq_self_of_surjective (nyllIdeleClassEquiv K).surjective _

/-- NYLL's class field of the subgroup `nyllSubgroup K H`, a field in universe `0`. -/
abbrev nyllClassField : Type :=
  GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassField
    (nyllSubgroup K H) (nyllSubgroup_isClosed K H)

/-- A `K`-embedding of NYLL's class field into the algebraic closure of `K`. -/
def nyllClassFieldEmbedding : nyllClassField K H →ₐ[K] AlgebraicClosure K :=
  IsAlgClosed.lift

/-- The class field of an open subgroup `H` of the idèle class group: the finite abelian
subextension of `AlgebraicClosure K` whose arithmetic Artin map has kernel `H`
(`arithmeticFiniteArtin_classField_ker`, `classField_eq_iff`). -/
def classField : IntermediateField K (AlgebraicClosure K) :=
  (nyllClassFieldEmbedding K H).fieldRange

/-- NYLL's class field is isomorphic over `K` to `classField K H`. -/
def nyllClassFieldEquiv : nyllClassField K H ≃ₐ[K] classField K H :=
  AlgEquiv.ofInjectiveField (nyllClassFieldEmbedding K H)

instance classField_finiteDimensional : FiniteDimensional K (classField K H) :=
  (nyllClassFieldEquiv K H).toLinearEquiv.finiteDimensional

instance classField_isAbelianGalois : IsAbelianGalois K (classField K H) :=
  IsAbelianGalois.of_algHom (nyllClassFieldEquiv K H).symm.toAlgHom

/-- The idèle-class norm group of the class field is the subgroup of NYLL's idèle class group
corresponding to `H`. -/
theorem ideleClassNorm_classField_range :
    letI := NumberField.of_module_finite K (classField K H)
    (_root_.ideleClassNorm K (classField K H)).range = nyllSubgroup K H := by
  let := NumberField.of_module_finite K (classField K H)
  rw [ideleClassNorm_range_eq_of_algEquiv (nyllClassFieldEquiv K H)]
  exact GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassField_ideleClassNorm_range
    (nyllSubgroup K H) (nyllSubgroup_isClosed K H)

/-- The kernel of the arithmetic Artin map of the class field of `H` is `H`. -/
theorem arithmeticFiniteArtin_classField_ker :
    letI := NumberField.of_module_finite K (classField K H)
    (arithmeticFiniteArtin K (classField K H)).ker = H.toSubgroup := by
  let := NumberField.of_module_finite K (classField K H)
  rw [arithmeticFiniteArtin_ker, ideleClassNorm_classField_range, map_nyllSubgroup]

/-- The class field of `H` is the only finite abelian subextension of `AlgebraicClosure K` whose
arithmetic Artin map has kernel `H`. -/
theorem classField_eq_iff (L : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K L]
    [IsAbelianGalois K L] :
    letI := NumberField.of_module_finite K L
    classField K H = L ↔ (arithmeticFiniteArtin K L).ker = H.toSubgroup := by
  let := NumberField.of_module_finite K L
  constructor
  · rintro rfl
    exact arithmeticFiniteArtin_classField_ker K H
  · intro h
    exact eq_of_arithmeticFiniteArtin_ker_eq (classField K H) L
      ((arithmeticFiniteArtin_classField_ker K H).trans h.symm)

end ClassField

end Langlands.ClassFieldTheory.Global.Artin
