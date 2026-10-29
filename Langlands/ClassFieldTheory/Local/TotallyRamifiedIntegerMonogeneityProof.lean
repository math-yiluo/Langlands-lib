import Langlands.ClassFieldTheory.Local.TotallyRamifiedIntegerMonogeneityStatement
import Langlands.ClassFieldTheory.Local.NYLL.RelativeIntegerStructureProof
import Langlands.ClassFieldTheory.Local.PrimeBreakUnramifiedBaseChangeSupport
import Mathlib.RingTheory.Nakayama

/-! Algebraic generation by every supplied uniformizer, using finite residue
expansions and Nakayama's lemma. -/

noncomputable section

namespace Langlands.LocalClassField

open IsLocalRing IsDiscreteValuationRing

universe u v

private theorem integerAdjoin_eq_top_of_residue_representatives
    {A : Type u} {B : Type v} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [CommRing B] [IsDomain B]
    [IsDiscreteValuationRing B] [Algebra A B] [Module.Finite A B]
    (hinj : Function.Injective (algebraMap A B)) (π : B)
    (hπ : maximalIdeal B = Ideal.span {π})
    (hrep : ∀ b : B, ∃ a : A, b - algebraMap A B a ∈ maximalIdeal B) :
    Algebra.adjoin A {π} = (⊤ : Subalgebra A B) := by
  let C := Algebra.adjoin A {π}
  have hπC : π ∈ C := Algebra.subset_adjoin (Set.mem_singleton π)
  have happ : ∀ (n : ℕ) (b : B), ∃ c ∈ C, ∃ z : B, b = c + π ^ n * z := by
    intro n
    induction n with
    | zero =>
      intro b
      exact ⟨0, C.zero_mem, b, by simp⟩
    | succ n ih =>
      intro b
      obtain ⟨a, ha⟩ := hrep b
      rw [hπ, Ideal.mem_span_singleton] at ha
      obtain ⟨y, hy⟩ := ha
      obtain ⟨c, hc, z, hz⟩ := ih y
      refine ⟨algebraMap A B a + π * c,
        C.add_mem (C.algebraMap_mem a) (C.mul_mem hπC hc), z, ?_⟩
      calc
        b = algebraMap A B a + π * y := by linear_combination hy
        _ = algebraMap A B a + π * c + π ^ (n + 1) * z := by
          rw [hz, pow_succ]
          ring
  obtain ⟨θ, hθ⟩ := exists_irreducible A
  have hθmap : algebraMap A B θ ≠ 0 := by
    intro h
    exact hθ.ne_zero (hinj (by simpa only [map_zero] using h))
  have hπirr : Irreducible π := (irreducible_iff_uniformizer π).mpr hπ
  obtain ⟨n, ε, hε⟩ := eq_unit_mul_pow_irreducible hθmap hπirr
  let I := (maximalIdeal A).map (algebraMap A B)
  have hθI : algebraMap A B θ ∈ I :=
    Ideal.mem_map_of_mem _ (show θ ∈ maximalIdeal A from hθ.not_isUnit)
  have hpow : π ^ n ∈ I := by
    apply (I.unit_mul_mem_iff_mem ε.isUnit).mp
    rwa [← hε]
  have hspan : (⊤ : Submodule A B) ≤
      C.toSubmodule ⊔ maximalIdeal A • (⊤ : Submodule A B) := by
    intro b _
    obtain ⟨c, hc, z, hz⟩ := happ n b
    apply Submodule.mem_sup.mpr
    refine ⟨c, hc, π ^ n * z, ?_, hz.symm⟩
    rw [Ideal.smul_top_eq_map]
    exact I.mul_mem_right z hpow
  have htop : (⊤ : Submodule A B) ≤ C.toSubmodule :=
    Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top
      (by rw [jacobson_eq_maximalIdeal ⊥ bot_ne_top]) hspan
  exact top_unique fun b _ => htop (Submodule.mem_top : b ∈ (⊤ : Submodule A B))

/-- Every supplied order-one element generates the actual relative integer ring. -/
theorem totallyRamifiedIntegerMonogeneity : TotallyRamifiedIntegerMonogeneity.{u,v} := by
  intro p hp F L hFL hbase hfinite
  let TF := F.canonicalTopologicalData
  let TL := L.canonicalTopologicalData
  let := PadicField.TopologicalData.relativeIntegerAlgebra TF TL
  dsimp only
  intro htotal π hπ
  let := TF.topology
  let := TF.valuativeRel
  let := TF.localField
  let := TL.topology
  let := TL.valuativeRel
  let := TL.localField
  let := PadicField.TopologicalData.relativeIntegerFieldAlgebra (E := L) TF
  let : Module.Finite TF.Integers TL.Integers :=
    (NYLL.relativeIntegerStructure p F L TF TL).2
  have hinj : Function.Injective (algebraMap TF.Integers TL.Integers) := by
    intro x y hxy
    apply Subtype.ext
    exact (algebraMap F.Carrier L.Carrier).injective (congrArg Subtype.val hxy)
  apply integerAdjoin_eq_top_of_residue_representatives hinj
    (TL.coordinateUniformizer π hπ) (TL.maximalIdeal_eq_span_coordinateUniformizer π hπ)
  have hsurj := primeBreakResidueMap_surjective_of_total F L htotal
  intro b
  obtain ⟨a, ha⟩ := hsurj (TL.residue b)
  obtain ⟨a, rfl⟩ := residue_surjective a
  refine ⟨a, ?_⟩
  rw [← residue_eq_zero_iff, map_sub, sub_eq_zero]
  exact ha.symm

end Langlands.LocalClassField
