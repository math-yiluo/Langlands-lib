import Langlands.ClassFieldTheory.Global.Artin.IdeleClassComparison
import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.ArithmeticNormalization
import Mathlib.FieldTheory.KrullTopology

/-!
# The arithmetic Artin map of a finite abelian extension on the Library's idèle classes

This file belongs to the Library. It states the global Artin map of the NYLL library for a
finite abelian extension of number fields on the Library's `IdeleClasses K`, in the
arithmetic normalization, together with its surjectivity, continuity and kernel.

NYLL's map `GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueMonoidHom K L`
lives on NYLL's own idèle class group and is, by its definition, the inverse of NYLL's
geometric norm-residue symbol. Composed with the comparison `nyllIdeleClassEquiv` it becomes
`arithmeticFiniteArtin K L` on the Library's group. The word `arithmetic` in the name records
the normalization: a uniformizer at a place unramified in `L` goes to the arithmetic
Frobenius (`FiniteArtinNormalization.lean`).

## Main declarations

* `arithmeticFiniteArtin K L : IdeleClasses K →* (L ≃ₐ[K] L)`.
* `arithmeticFiniteArtin_surjective`, `arithmeticFiniteArtin_continuous` (for the Krull
  topology, which is discrete), `arithmeticFiniteArtin_continuous_bot` (for `⊥`, the form
  the published statements use).
* `arithmeticFiniteArtin_ker`: the kernel is the image of NYLL's idèle-class norm group
  `(_root_.ideleClassNorm K L).range`.
* `arithmeticFiniteArtin_finiteClassInclusion`: at a finite place it is NYLL's chosen local
  Artin map in arithmetic normalization.
* `arithmeticFiniteArtinBot`: the map as a continuous homomorphism for the `⊥` topology.
-/

noncomputable section

universe u v

namespace Langlands.ClassFieldTheory.Global.Artin

open Langlands.Global

variable (K : Type u) (L : Type v) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]

/-- The Artin map of a finite abelian extension of number fields on the Library's idèle
classes, in arithmetic normalization: NYLL's arithmetic global norm-residue map composed with
the comparison of idèle class groups. -/
def arithmeticFiniteArtin : IdeleClasses K →* (L ≃ₐ[K] L) :=
  (GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueMonoidHom K L).comp
    (nyllIdeleClassEquiv K).symm.toMulEquiv.toMonoidHom

theorem arithmeticFiniteArtin_apply (x : IdeleClasses K) :
    arithmeticFiniteArtin K L x =
      GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueMonoidHom K L
        ((nyllIdeleClassEquiv K).symm x) :=
  rfl

theorem arithmeticFiniteArtin_surjective : Function.Surjective (arithmeticFiniteArtin K L) :=
  (GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueMonoidHom_surjective K L).comp
    (nyllIdeleClassEquiv K).symm.surjective

/-- Continuity for the Krull topology of `L ≃ₐ[K] L` (discrete, since `L / K` is finite). -/
theorem arithmeticFiniteArtin_continuous : Continuous (arithmeticFiniteArtin K L) :=
  (GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueMonoidHom_continuous K L).comp
    (nyllIdeleClassEquiv K).symm.continuous

omit [NumberField K] [NumberField L] [IsAbelianGalois K L] in
/-- The Krull topology of the Galois group of a finite extension is the discrete topology
`⊥`. -/
theorem krullTopology_eq_bot : krullTopology K L = ⊥ :=
  DiscreteTopology.eq_bot

/-- Continuity for the topology `⊥` on `L ≃ₐ[K] L`, the form used by the published
statements. -/
theorem arithmeticFiniteArtin_continuous_bot :
    letI : TopologicalSpace (L ≃ₐ[K] L) := ⊥
    Continuous (arithmeticFiniteArtin K L) := by
  have h : @Continuous _ _ _ (krullTopology K L) (arithmeticFiniteArtin K L) :=
    arithmeticFiniteArtin_continuous K L
  rw [krullTopology_eq_bot] at h
  exact h

/-- The arithmetic Artin map as a continuous homomorphism for the topology `⊥` on
`L ≃ₐ[K] L`. -/
def arithmeticFiniteArtinBot :
    letI : TopologicalSpace (L ≃ₐ[K] L) := ⊥
    IdeleClasses K →ₜ* (L ≃ₐ[K] L) :=
  letI : TopologicalSpace (L ≃ₐ[K] L) := ⊥
  { toMonoidHom := arithmeticFiniteArtin K L
    continuous_toFun := arithmeticFiniteArtin_continuous_bot K L }

theorem arithmeticFiniteArtinBot_toMonoidHom :
    letI : TopologicalSpace (L ≃ₐ[K] L) := ⊥
    (arithmeticFiniteArtinBot K L).toMonoidHom = arithmeticFiniteArtin K L :=
  rfl

/-- The kernel is the image of NYLL's idèle-class norm group. -/
theorem arithmeticFiniteArtin_ker :
    (arithmeticFiniteArtin K L).ker =
      ((_root_.ideleClassNorm K L).range).map (nyllIdeleClassEquiv K).toMulEquiv.toMonoidHom := by
  ext x
  rw [MonoidHom.mem_ker, arithmeticFiniteArtin_apply, ← MonoidHom.mem_ker,
    GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueMonoidHom_ker,
    Subgroup.mem_map_equiv]
  rfl

/-- At a finite place, the arithmetic Artin map is NYLL's chosen local Artin map in arithmetic
normalization. -/
theorem arithmeticFiniteArtin_finiteClassInclusion (v : Langlands.Global.FinitePlace K)
    (x : (FiniteCompletion K v)ˣ) :
    arithmeticFiniteArtin K L (finiteClassInclusion K v x) =
      GlobalClassFieldTheory.Reciprocity.arithmeticChosenFinitePlaceArtinMonoidHom K L v x := by
  rw [arithmeticFiniteArtin_apply, nyllIdeleClassEquiv_symm_finiteClassInclusion,
    ← GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueMonoidHom_comp_finitePlaceIdeleClass
      K L v]
  rfl

end Langlands.ClassFieldTheory.Global.Artin
