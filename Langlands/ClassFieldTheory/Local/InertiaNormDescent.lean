import Langlands.Galois.Local.InertiaFixedFieldUnramifiedProof
import Langlands.FieldTheory.FiniteTowerDescentProof
import Mathlib.Algebra.CharP.IntermediateField

/-! The directed family of actual unramified stages and compatible finite models. -/
noncomputable section

namespace Langlands.ClassFieldTheory.Local.InertiaNormDescent

open Langlands Langlands.LocalClassField

universe u

variable (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p)

abbrev U := IntermediateField.fixedField
  (F.absoluteInertia F.canonicalTopologicalData)

abbrev Stage :=
  {D : FiniteIntermediateExtension F.Carrier //
    IsGalois F.Carrier D.field ∧
      F.canonicalTopologicalData.ramificationIndex =
        (D.asPadicField (p := p)).canonicalTopologicalData.ramificationIndex}

theorem stage_le (i : Stage p F) : i.1.field ≤ U p F := by
  let : IsGalois F.Carrier i.1.field := i.2.1
  exact (PadicField.inertiaFixedFieldUnramifiedExhaustion p F).1 i.1 i.2.2

def stageField (i : Stage p F) : Subfield (U p F) :=
  i.1.field.toSubfield.comap (U p F).val.toRingHom

instance : Nonempty (Stage p F) := by
  obtain ⟨D, hGal, hram, _⟩ :=
    (PadicField.inertiaFixedFieldUnramifiedExhaustion p F).2 ∅ (by simp)
  exact ⟨D, hGal, hram⟩

theorem stage_cover (x : U p F) : ∃ i : Stage p F, x ∈ stageField p F i := by
  classical
  obtain ⟨D, hGal, hram, hmem⟩ :=
    (PadicField.inertiaFixedFieldUnramifiedExhaustion p F).2 {x.1}
      (by simp)
  exact ⟨⟨D, hGal, hram⟩, hmem x.1 (by simp)⟩

private theorem le_of_basis_mem
    (D : FiniteIntermediateExtension F.Carrier)
    (K : IntermediateField F.Carrier (AlgebraicClosure F.Carrier))
    (h : ∀ j, ((Module.finBasis F.Carrier D.field) j :
      AlgebraicClosure F.Carrier) ∈ K) : D.field ≤ K := by
  intro x hx
  let y : D.field := ⟨x, hx⟩
  have heq := congrArg (fun z : D.field => (z : AlgebraicClosure F.Carrier))
    ((Module.finBasis F.Carrier D.field).sum_repr y)
  simp only [IntermediateField.coe_sum, IntermediateField.coe_smul] at heq
  change (y : AlgebraicClosure F.Carrier) ∈ K
  rw [← heq]
  exact K.sum_mem fun j _ => K.smul_mem (h j)

theorem stage_directed : Directed (· ≤ ·) (stageField p F) := by
  classical
  intro i j
  let bi := Module.finBasis F.Carrier i.1.field
  let bj := Module.finBasis F.Carrier j.1.field
  let si : Finset (AlgebraicClosure F.Carrier) :=
    Finset.univ.image fun k => (bi k : AlgebraicClosure F.Carrier)
  let sj : Finset (AlgebraicClosure F.Carrier) :=
    Finset.univ.image fun k => (bj k : AlgebraicClosure F.Carrier)
  have hs : ∀ x ∈ si ∪ sj, x ∈ U p F := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hx
      exact stage_le p F i (bi k).2
    · obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hx
      exact stage_le p F j (bj k).2
  obtain ⟨D, hGal, hram, hmem⟩ :=
    (PadicField.inertiaFixedFieldUnramifiedExhaustion p F).2 (si ∪ sj) hs
  have hi : i.1.field ≤ D.field := le_of_basis_mem p F i.1 D.field fun k =>
    hmem _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩))
  have hj : j.1.field ≤ D.field := le_of_basis_mem p F j.1 D.field fun k =>
    hmem _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩))
  exact ⟨⟨D, hGal, hram⟩, fun _ hx => hi hx, fun _ hx => hj hx⟩

def stageEquiv (i : Stage p F) : stageField p F i ≃+* i.1.field where
  toFun x := ⟨x.1.1, x.2⟩
  invFun x := ⟨⟨x.1, stage_le p F i x.2⟩, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

def stageOverBase (i : Stage p F) : IntermediateField F.Carrier (U p F) :=
  i.1.field.comap (U p F).val

abbrev stageAlgebra (i : Stage p F) : Algebra F.Carrier (stageField p F i) :=
  (stageOverBase p F i).toSubalgebra.algebra

def stageAlgEquiv (i : Stage p F) :
    letI := stageAlgebra p F i
    stageField p F i ≃ₐ[F.Carrier] i.1.field := by
  letI := stageAlgebra p F i
  exact { stageEquiv p F i with commutes' := fun _ => rfl }

theorem stage_finite (i : Stage p F) :
    letI := stageAlgebra p F i
    FiniteDimensional F.Carrier (stageField p F i) := by
  let := stageAlgebra p F i
  exact Module.Finite.equiv (stageAlgEquiv p F i).symm.toLinearEquiv

/-- Compatible finite models specialized to the actual inertia fixed field
and its directed family of finite unramified Galois stages. -/
theorem finite_models
    (E L : Type u) [Field E] [Field L]
    [Algebra (U p F) E] [FiniteDimensional (U p F) E]
    [Algebra E L] [FiniteDimensional E L] [IsGalois E L] :
    letI : Algebra (U p F) L :=
      ((algebraMap E L).comp (algebraMap (U p F) E)).toAlgebra
    letI : IsScalarTower (U p F) E L := IsScalarTower.of_algebraMap_eq' rfl
    ∀ (i₀ : Stage p F) (sE : Finset E) (sL : Finset L),
      ∃ i : Stage p F, stageField p F i₀ ≤ stageField p F i ∧
        letI : Algebra (stageField p F i) (U p F) := Algebra.ofSubsemiring (stageField p F i)
        letI : Algebra (stageField p F i) E := Algebra.ofSubsemiring (stageField p F i)
        letI : Algebra (stageField p F i) L := Algebra.ofSubsemiring (stageField p F i)
        letI : IsScalarTower (stageField p F i) (U p F) E := IsScalarTower.of_algebraMap_eq' rfl
        letI : IsScalarTower (stageField p F i) (U p F) L := IsScalarTower.of_algebraMap_eq' rfl
        letI : IsScalarTower (stageField p F i) E L := IsScalarTower.of_algebraMap_eq' rfl
        ∃ B : IntermediateField (stageField p F i) E,
          letI : Algebra (stageField p F i) B := B.toSubalgebra.algebra
          letI : Algebra B L := Algebra.ofSubsemiring B
          letI : IsScalarTower B E L := IsScalarTower.of_algebraMap_eq' rfl
          letI : IsScalarTower (stageField p F i) B L := IsScalarTower.of_algebraMap_eq' rfl
          ∃ C : IntermediateField B L,
            letI : Algebra B C := C.toSubalgebra.algebra
            letI : Algebra (stageField p F i) C := IntermediateField.algebra' C
            letI : IsScalarTower (stageField p F i) C L := IsScalarTower.of_algebraMap_eq' rfl
            FiniteDimensional (stageField p F i) B ∧ Algebra.IsSeparable (stageField p F i) B ∧
            Module.finrank (stageField p F i) B = Module.finrank (U p F) E ∧
            FiniteDimensional B C ∧ IsGalois B C ∧
            Module.finrank B C = Module.finrank E L ∧
            FiniteDimensional (stageField p F i) C ∧
            Module.finrank (stageField p F i) C = Module.finrank (U p F) L ∧
            B.LinearDisjoint (U p F) ∧
            IntermediateField.adjoin (U p F) (B : Set E) = ⊤ ∧
            (C.restrictScalars (stageField p F i)).LinearDisjoint (U p F) ∧
            IntermediateField.adjoin (U p F) (C : Set L) = ⊤ ∧
            C.LinearDisjoint E ∧
            IntermediateField.adjoin E (C : Set L) = ⊤ ∧
            (∀ x ∈ sE, x ∈ B) ∧ (∀ x ∈ sL, x ∈ C) ∧
            (algebraMap C L).comp (algebraMap B C) =
              (algebraMap E L).comp (algebraMap B E) := by
  let : CharZero F.Carrier := Algebra.charZero_of_charZero (Padic p) F.Carrier
  let : CharZero (U p F) := inferInstance
  exact FieldTheory.finiteTowerDirectedUnionDescent (U p F) E L
    (Stage p F) (stageField p F) (stage_directed p F) (stage_cover p F)

end Langlands.ClassFieldTheory.Local.InertiaNormDescent
