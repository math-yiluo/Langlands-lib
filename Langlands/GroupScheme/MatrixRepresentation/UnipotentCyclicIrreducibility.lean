import Langlands.GroupScheme.MatrixRepresentation.MinimalStableSubrepresentation
import Langlands.GroupScheme.Reductive.InvariantLinearForm
import Langlands.GroupScheme.Reductive.CharZeroSemisimplicity.TangentStability

/-! # Irreducibility from a unipotent fixed line and a spanning orbit -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.MatrixRepresentation

variable {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  {n : Type} [Fintype n] [DecidableEq n]

/-- Supplied data of a nonzero cyclic vector spanning the entire fixed space
of a unipotent group acting through an actual group-scheme morphism. -/
structure UnipotentCyclicVector (ρ : MatrixRepresentation G n) (i : H ⟶ G) where
  unipotent : IsUnipotent H
  vector : n → k
  ne_zero : vector ≠ 0
  fixed_space : (ρ.restrict i).fixedSubmodule = Submodule.span k {vector}
  orbit_span :
    Submodule.span k (Set.range fun g => ρ.rationalRepresentation g vector) = ⊤

/-- Every nonzero all-test stable subspace contains a nonzero vector fixed by a
supplied unipotent subgroup, on every relative scheme test. -/
theorem IsStableSubspace.exists_nonzero_subgroup_fixedVector [IsAffineHom G.X.hom]
    {ρ : MatrixRepresentation G n} {W : Submodule k (n → k)}
    (hW : ρ.IsStableSubspace W) (hW0 : W ≠ ⊥)
    (i : H ⟶ G) (hH : IsUnipotent H) :
    ∃ w : n → k, w ∈ W ∧ w ≠ 0 ∧ (ρ.restrict i).IsFixedVector w := by
  classical
  obtain ⟨d, B, C, hCB, hcols, hproj⟩ := exists_subspace_split_coordinates W
  have hs := hW.isStableCoordinates B C hcols hproj
  have hsH : (ρ.restrict i).IsStableCoordinates B C := by
    intro T x
    simpa only [pointMatrix_restrict] using hs T (x ≫ i.hom.hom)
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  have hCv : C *ᵥ v ≠ 0 := by
    intro hz
    apply hv0
    calc
      v = B *ᵥ (C *ᵥ v) := by rw [Matrix.mulVec_mulVec, hproj v hv]
      _ = 0 := by rw [hz, Matrix.mulVec_zero]
  obtain ⟨j, -⟩ := Function.ne_iff.mp hCv
  let : Nonempty (Fin d) := ⟨j⟩
  obtain ⟨w, hw0, hwfix⟩ :=
    hH (Fin d) ((ρ.restrict i).restrictCoordinates B C hCB hsH)
  have hrange : LinearMap.range B.mulVecLin = W :=
    range_coordinateInclusion_eq W B C hcols hproj
  refine ⟨B *ᵥ w, ?_, ?_,
    (ρ.restrict i).isFixedVector_mulVec_restrictCoordinates B C hCB hsH hwfix⟩
  · rw [← hrange]
    exact ⟨w, rfl⟩
  · intro hz
    apply hw0
    exact coordinateInclusion_injective (R := CommRingCat.of k) B C hCB
      (hz.trans (Matrix.mulVec_zero B).symm)

/-- A supplied unipotent subgroup whose entire fixed space is a single nonzero
line detects irreducibility when the rational orbit of that line spans the
entire coordinate space. No characteristic or algebraic-closedness hypothesis
is needed for this all-test stability conclusion. -/
theorem isIrreducible_of_unipotent_fixedLine_spanningOrbit [IsAffineHom G.X.hom]
    (ρ : MatrixRepresentation G n) (i : H ⟶ G) (hH : IsUnipotent H)
    (v : n → k) (hv : v ≠ 0)
    (hline : (ρ.restrict i).fixedSubmodule = Submodule.span k {v})
    (horbit : Submodule.span k (Set.range fun g => ρ.rationalRepresentation g v) = ⊤) :
    ρ.IsIrreducible := by
  refine ⟨⟨v, 0, hv⟩, ?_⟩
  intro W hW
  by_cases hW0 : W = ⊥
  · exact Or.inl hW0
  right
  obtain ⟨w, hwW, hw0, hwfix⟩ := hW.exists_nonzero_subgroup_fixedVector hW0 i hH
  have hwline : w ∈ Submodule.span k {v} := by
    rw [← hline]
    exact hwfix
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hwline
  have ha0 : a ≠ 0 := by
    intro hz
    apply hw0
    rw [← ha, hz, zero_smul]
  have hvW : v ∈ W := by
    have h := W.smul_mem a⁻¹ hwW
    rw [← ha, smul_smul, inv_mul_cancel₀ ha0, one_smul] at h
    exact h
  apply top_unique
  rw [← horbit]
  apply Submodule.span_le.mpr
  rintro _ ⟨g, rfl⟩
  exact hW.rationalMatrix_mulVec_mem g hvW

/-- Supplied unipotent cyclic fixed-line data certify all-test irreducibility
of the original representation on its entire coordinate space. -/
theorem UnipotentCyclicVector.isIrreducible [IsAffineHom G.X.hom]
    {ρ : MatrixRepresentation G n} {i : H ⟶ G} (D : UnipotentCyclicVector ρ i) :
    ρ.IsIrreducible :=
  isIrreducible_of_unipotent_fixedLine_spanningOrbit ρ i D.unipotent
    D.vector D.ne_zero D.fixed_space D.orbit_span

section RationalIrreducibility

variable [IsAlgClosed k] [IsReduced G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffineHom G.X.hom]

/-- Under rational-point detection of stability, the same fixed-line and
spanning-orbit criterion proves irreducibility of the actual rational-point
representation on the entire coordinate space. -/
theorem rationalRepresentation_isIrreducible_of_unipotent_fixedLine_spanningOrbit
    (ρ : MatrixRepresentation G n) (i : H ⟶ G) (hH : IsUnipotent H)
    (v : n → k) (hv : v ≠ 0)
    (hline : (ρ.restrict i).fixedSubmodule = Submodule.span k {v})
    (horbit : Submodule.span k (Set.range fun g => ρ.rationalRepresentation g v) = ⊤) :
    ρ.rationalRepresentation.IsIrreducible := by
  have hρ := isIrreducible_of_unipotent_fixedLine_spanningOrbit ρ i hH v hv hline horbit
  let := hρ.1
  refine { exists_pair_ne := ?_, eq_bot_or_eq_top := ?_ }
  · refine ⟨⊥, ⊤, ?_⟩
    intro he
    have hh : (⊥ : Submodule k (n → k)) = ⊤ :=
      congrArg Subrepresentation.toSubmodule he
    exact bot_ne_top hh
  · intro W
    have hW : ρ.IsStableSubspace W.toSubmodule :=
      isStableSubspace_of_rationalMatrix ρ W.toSubmodule
        (fun g _ hx => W.apply_mem_toSubmodule g hx)
    rcases hρ.2 W.toSubmodule hW with he | he
    · exact Or.inl (Subrepresentation.toSubmodule_injective he)
    · exact Or.inr (Subrepresentation.toSubmodule_injective he)

/-- Supplied unipotent cyclic fixed-line data certify irreducibility of the
original entire rational-point representation under rational stability detection. -/
theorem UnipotentCyclicVector.rationalRepresentation_isIrreducible
    {ρ : MatrixRepresentation G n} {i : H ⟶ G} (D : UnipotentCyclicVector ρ i) :
    ρ.rationalRepresentation.IsIrreducible :=
  rationalRepresentation_isIrreducible_of_unipotent_fixedLine_spanningOrbit ρ i D.unipotent
    D.vector D.ne_zero D.fixed_space D.orbit_span

end RationalIrreducibility

end Langlands.GroupScheme.MatrixRepresentation
