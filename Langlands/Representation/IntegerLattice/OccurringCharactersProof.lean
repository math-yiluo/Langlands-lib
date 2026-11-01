import Langlands.Representation.IntegerLattice.OccurringCharactersStatement
import Langlands.Representation.IntegerLattice.GeneralizedWeightSupportProof
import Langlands.Representation.IntegerLattice.GeneralizedWeightProof
import Mathlib.Data.Fintype.EquivFin

/-! # Full-lattice eigencharacters and their finite complete enumeration -/

set_option autoImplicit false

namespace Langlands

universe u

namespace IntegerLattice

/-- Every lattice point is the product of all integer powers of the generators. -/
theorem lattice_eq_prod_generators {d : ℕ} (n : Lattice d) :
    n = ∏ i : Fin d, (generator d i) ^ n.toAdd i := by
  apply Multiplicative.toAdd.injective
  ext i
  simp [generator, toAdd_prod, toAdd_zpow, Finset.sum_apply, Pi.single_apply]

/-- A character of the actual lattice is determined by its generator values. -/
theorem coordinateCharacter_reconstruction {d : ℕ} (χ : Lattice d →* ℂˣ) :
    coordinateCharacter (fun i => χ (generator d i)) = χ := by
  apply MonoidHom.ext
  intro n
  change (∏ i : Fin d, χ (generator d i) ^ n.toAdd i) = χ n
  calc
    (∏ i : Fin d, χ (generator d i) ^ n.toAdd i) =
        χ (∏ i : Fin d, (generator d i) ^ n.toAdd i) := by simp
    _ = χ n := congrArg χ (lattice_eq_prod_generators n).symm

/-- Different coordinate labels yield different actual lattice characters. -/
theorem coordinateCharacter_injective {d : ℕ} :
    Function.Injective (coordinateCharacter (d := d)) := by
  intro b c h
  funext i
  simpa only [coordinateCharacter_generator] using
    congrArg (fun χ : Lattice d →* ℂˣ => χ (generator d i)) h

/-- Generator eigenvector equations extend to every positive and negative
integer lattice point, on this same vector and without a dimension assumption. -/
theorem commonEigenvector_iff_coordinateCharacter {d : ℕ} {V : Type u}
    [AddCommGroup V] [Module ℂ V] (A : CommutingInvertibleTuple d V)
    (c : Fin d → ℂˣ) (v : V) :
    (∀ i : Fin d, (A.1 i : Module.End ℂ V) v = (c i : ℂ) • v) ↔
      ∀ n : Lattice d,
        tupleRepresentationEquiv d V A n v = (coordinateCharacter c n : ℂ) • v := by
  constructor
  · intro hv
    let ρ := tupleRepresentationEquiv d V A
    let χ := coordinateCharacter c
    let S : Subgroup (Lattice d) :=
      { carrier := {n | ρ n v = (χ n : ℂ) • v}
        one_mem' := by simp
        mul_mem' := by
          intro n m hn hm
          change ρ n v = (χ n : ℂ) • v at hn
          change ρ m v = (χ m : ℂ) • v at hm
          change ρ (n * m) v = (χ (n * m) : ℂ) • v
          simp only [map_mul, Module.End.mul_apply, hm, map_smul, hn, Units.val_mul,
            smul_smul, mul_comm (χ m : ℂ) (χ n : ℂ)]
        inv_mem' := by
          intro n hn
          change ρ n v = (χ n : ℂ) • v at hn
          change ρ n⁻¹ v = (χ n⁻¹ : ℂ) • v
          apply ρ.inv_apply_eq_iff.mpr
          simp only [map_smul, hn, map_inv, Units.val_inv_eq_inv_val, smul_smul,
            inv_mul_cancel₀ (χ n).ne_zero, one_smul] }
    have hgen (i : Fin d) : generator d i ∈ S := by
      change ρ (generator d i) v = (χ (generator d i) : ℂ) • v
      simpa only [ρ, χ, tupleRepresentationEquiv_generator, coordinateCharacter_generator]
        using hv i
    intro n
    change n ∈ S
    rw [lattice_eq_prod_generators n]
    exact S.prod_mem fun i _ => S.zpow_mem (hgen i) _
  · intro hv i
    simpa only [tupleRepresentationEquiv_generator, coordinateCharacter_generator]
      using hv (generator d i)

end IntegerLattice

open IntegerLattice

/-- Reconstruction and injectivity for all natural ranks. -/
theorem integerLatticeCoordinateCharacterReconstruction :
    IntegerLatticeCoordinateCharacterReconstructionStatement := by
  intro d
  exact ⟨coordinateCharacter_reconstruction, coordinateCharacter_injective⟩

/-- The arbitrary-dimensional same-vector comparison with the full lattice. -/
theorem commutingTupleCommonEigenvectorCharacter :
    CommutingTupleCommonEigenvectorCharacterStatement.{u} := by
  intro d V _ _ A c v
  exact commonEigenvector_iff_coordinateCharacter A c v

/-- One finite list identifies both actual nonzero generalized-weight blocks
and all full-lattice characters occurring on nonzero vectors. -/
theorem commutingTupleOccurringCharacterEnumeration :
    CommutingTupleOccurringCharacterEnumerationStatement.{u} := by
  classical
  intro d V _ _ _ A
  let S : Set (Fin d → ℂˣ) := {b | generalizedWeightBlock A b ≠ ⊥}
  have hS : S.Finite := by
    simpa only [S, generalizedWeightBlock] using
      (commutingTupleGeneralizedWeightDecomposition d V A).1
  let : Fintype S := hS.fintype
  let e : Fin (Fintype.card S) ≃ S := (Fintype.equivFin S).symm
  let c : Fin (Fintype.card S) → Fin d → ℂˣ := fun j => (e j).val
  have hcinj : Function.Injective c := Subtype.val_injective.comp e.injective
  have hc (b : Fin d → ℂˣ) :
      generalizedWeightBlock A b ≠ ⊥ ↔ ∃ j : Fin (Fintype.card S), c j = b := by
    constructor
    · intro hb
      refine ⟨e.symm ⟨b, hb⟩, ?_⟩
      exact congrArg Subtype.val (e.apply_symm_apply ⟨b, hb⟩)
    · rintro ⟨j, rfl⟩
      exact (e j).property
  refine ⟨Fintype.card S, c, coordinateCharacter_injective.comp hcinj, hc, ?_⟩
  intro χ
  constructor
  · rintro ⟨v, hv0, hv⟩
    let b : Fin d → ℂˣ := fun i => χ (generator d i)
    have hb : ∀ i : Fin d, (A.1 i : Module.End ℂ V) v = (b i : ℂ) • v := by
      intro i
      simpa only [b, tupleRepresentationEquiv_generator] using hv (generator d i)
    have hblock := (commutingTupleGeneralizedWeightSupport d V A b).mpr ⟨v, hv0, hb⟩
    obtain ⟨j, hj⟩ := (hc b).mp hblock
    exact ⟨j, (congrArg coordinateCharacter hj).trans (coordinateCharacter_reconstruction χ)⟩
  · rintro ⟨j, hj⟩
    obtain ⟨v, hv0, hv⟩ := (commutingTupleGeneralizedWeightSupport d V A (c j)).mp
      ((hc (c j)).mpr ⟨j, rfl⟩)
    refine ⟨v, hv0, ?_⟩
    rw [← hj]
    exact (commonEigenvector_iff_coordinateCharacter A (c j) v).mp hv

/-- Renard C.III's full-lattice eigencharacter comparisons and finite
complete list of distinct occurring characters. -/
theorem renardCIIIOccurringCharacters : RenardCIIIOccurringCharactersStatement.{u} :=
  ⟨integerLatticeCoordinateCharacterReconstruction,
    commutingTupleCommonEigenvectorCharacter, commutingTupleOccurringCharacterEnumeration⟩

end Langlands
