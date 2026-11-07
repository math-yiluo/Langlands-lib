import Langlands.Representation.Jacquet.CanonicalLiftDefinitions
import Langlands.Representation.Smooth.FixedVectors.DetectionConsequencesProof
import Langlands.Representation.Unitary.UnitarizabilityContinuationProof

/-! # Matrices of the actual compact-average compression -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Renard.AlgebraicFamily.CompactCompressionMatrices

open Matrix CategoryTheory

universe uG uV un

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (A : SmoothRep.{0, uG, uV} ℂ G)
variable (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
variable {n : Type un} [Fintype n]
variable (e : Module.Basis n ℂ (fixedVectors A.representation K.toSubgroup))

/-- Coordinates of acting by `g` followed by the normalized compact average. -/
def fixedMatrix (g : G) : Matrix n n ℂ :=
  Matrix.of fun i j =>
    e.equivFun (Jacquet.compressedAction A.representation A.isSmooth K hK g (e j)) i

theorem fixedMatrix_mulVec (g : G) (x : n → ℂ) :
    e.equivFun (Jacquet.compressedAction A.representation A.isSmooth K hK g
      (e.equivFun.symm x)) = fixedMatrix A K hK e g *ᵥ x := by
  funext i
  simp [fixedMatrix, Matrix.mulVec, dotProduct, map_sum, mul_comm]

/-- Compact averaging preserves every actual invariant subspace. -/
theorem averageMap_mem (S : Subrepresentation A.representation)
    {v : A} (hv : v ∈ S) :
    Compact.averageMap A.representation A.isSmooth K hK v ∈ S := by
  let C := SmoothRep.subrepresentation A S
  let i := SmoothRep.hom (SmoothRep.subtype A S)
  have h := LinearMap.congr_fun
    (Compact.averageMap_commute C.representation A.representation
      C.isSmooth A.isSmooth K hK i) (⟨v, hv⟩ : C)
  exact h ▸ (Compact.averageMap C.representation C.isSmooth K hK
    (⟨v, hv⟩ : C)).property

/-- An irreducible representation has an irreducible compression family,
including when its fixed-vector space is zero. -/
theorem fixedMatrix_isIrreducible (hirr : A.IsIrreducible) :
    UnitarizabilityContinuation.IsIrreducibleFamily (fixedMatrix A K hK e) := by
  intro U hU
  by_cases hbot : U = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨x, hxU, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  let p : A →ₗ[ℂ] fixedVectors A.representation K.toSubgroup :=
    (Compact.averageMap A.representation A.isSmooth K hK).codRestrict
      (fixedVectors A.representation K.toSubgroup)
      (Compact.averageMap_mem_fixedVectors A.representation A.isSmooth K hK)
  let crd : G → A →ₗ[ℂ] (n → ℂ) := fun g =>
    e.equivFun.toLinearMap ∘ₗ p ∘ₗ A.representation g
  let S : Submodule ℂ A := ⨅ g, U.comap (crd g)
  have hmemS : ∀ v, v ∈ S ↔ ∀ g, e.equivFun (p (A.representation g v)) ∈ U := by
    intro v
    simp [S, Submodule.mem_iInf, crd]
  have hS : ∀ h, ∀ v ∈ S, A.representation h v ∈ S := by
    intro h v hv
    rw [hmemS] at hv ⊢
    intro g
    have := hv (g * h)
    rwa [map_mul, Module.End.mul_apply] at this
  have hu : (e.equivFun.symm x : A) ∈ S := by
    rw [hmemS]
    intro g
    change e.equivFun (Jacquet.compressedAction A.representation A.isSmooth K hK g
      (e.equivFun.symm x)) ∈ U
    rw [fixedMatrix_mulVec]
    exact hU g x hxU
  rcases hirr.eq_bot_or_eq_top (⟨S, hS⟩ : Subrepresentation A.representation) with h | h
  · exfalso
    have h' := congrArg Subrepresentation.toSubmodule h
    change S = ⊥ at h'
    rw [h'] at hu
    apply hx0
    have h1 : e.equivFun.symm x = 0 := Subtype.ext ((Submodule.mem_bot ℂ).mp hu)
    have h2 := congrArg e.equivFun h1
    rwa [LinearEquiv.apply_symm_apply, map_zero] at h2
  · have h' := congrArg Subrepresentation.toSubmodule h
    change S = ⊤ at h'
    rw [eq_top_iff]
    intro y _
    have hy : (e.equivFun.symm y : A) ∈ S := h' ▸ Submodule.mem_top
    rw [hmemS] at hy
    have := hy 1
    change e.equivFun (Jacquet.compressedAction A.representation A.isSmooth K hK 1
      (e.equivFun.symm y)) ∈ U at this
    simpa only [Jacquet.compressedAction_one, LinearMap.id_apply,
      LinearEquiv.apply_symm_apply] using this

/-- Under actual irreducible-subquotient detection, matrix irreducibility
forces irreducibility of the whole representation. -/
theorem isIrreducible_of_fixedMatrix [Nontrivial A]
    (hdet : ∀ D : SmoothRep.{0, uG, uV} ℂ G,
      D.IsIrreducible → SmoothRep.IsSubquotient D A →
        ∃ v : D, v ∈ fixedVectors D.representation K.toSubgroup ∧ v ≠ 0)
    (hirr : UnitarizabilityContinuation.IsIrreducibleFamily (fixedMatrix A K hK e)) :
    A.IsIrreducible := by
  classical
  have hall := SmoothRep.fixedVector_of_irreducible_subquotient_detection A K hK hdet
  have hgen := SmoothRep.fixedVectors_generate_subquotients_of_detection A K hK hall
  have hAA : SmoothRep.IsSubquotient A A :=
    SmoothRep.IsQuotient.isSubquotient ⟨𝟙 A, fun v => ⟨v, rfl⟩⟩
  refine { exists_pair_ne := ⟨⊥, ⊤, fun he => ?_⟩, eq_bot_or_eq_top := fun S => ?_ }
  · obtain ⟨v, hv⟩ := exists_ne (0 : A)
    apply hv
    have hmem : v ∈ (⊤ : Subrepresentation A.representation) := trivial
    rw [← he] at hmem
    exact hmem
  · by_cases hS : S = ⊥
    · exact Or.inl hS
    right
    let U : Submodule ℂ (n → ℂ) := S.toSubmodule.comap
      ((fixedVectors A.representation K.toSubgroup).subtype ∘ₗ e.equivFun.symm.toLinearMap)
    have hU : ∀ g v, v ∈ U → (fixedMatrix A K hK e g).mulVec v ∈ U := by
      intro g v hv
      change (e.equivFun.symm ((fixedMatrix A K hK e g).mulVec v) : A) ∈ S
      rw [← fixedMatrix_mulVec, LinearEquiv.symm_apply_apply]
      exact averageMap_mem A K hK S (S.apply_mem_toSubmodule g hv)
    rcases hirr U hU with h | h
    · exfalso
      have hSmod : S.toSubmodule ≠ ⊥ := fun h => hS (Subrepresentation.toSubmodule_injective h)
      obtain ⟨s, hs, hs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hSmod
      let C := SmoothRep.subrepresentation A S
      have hC : Nontrivial C := ⟨⟨⟨s, hs⟩, 0, fun hz => hs0 (congrArg Subtype.val hz)⟩⟩
      have hCA : SmoothRep.IsSubquotient C A :=
        (SmoothRep.subrepresentation_isSubrepresentation (A := A) S).isSubquotient
      obtain ⟨w, hw, hw0⟩ := hall C hCA hC
      let i := SmoothRep.hom (SmoothRep.subtype A S)
      let v : fixedVectors A.representation K.toSubgroup := ⟨i w, map_mem_fixedVectors i hw⟩
      have hv : e.equivFun v ∈ U := by
        change (e.equivFun.symm (e.equivFun v) : A) ∈ S
        rw [LinearEquiv.symm_apply_apply]
        exact w.property
      have hv0 : e.equivFun v = 0 := by simpa only [h, Submodule.mem_bot] using hv
      have hv0' : v = 0 := e.equivFun.injective (hv0.trans (map_zero e.equivFun).symm)
      apply hw0
      apply Subtype.ext
      exact congrArg
        (fun z : fixedVectors A.representation K.toSubgroup => (z : A)) hv0'
    · apply hgen A hAA S
      intro v hv
      have hvU : e.equivFun ⟨v, hv⟩ ∈ U := h ▸ Submodule.mem_top
      change (e.equivFun.symm (e.equivFun ⟨v, hv⟩) : A) ∈ S at hvU
      change v ∈ S
      rw [LinearEquiv.symm_apply_apply] at hvU
      exact hvU

/-- The exact comparison needed for determinant arguments. Detection remains
an explicit premise of this internal lemma. -/
theorem isIrreducible_iff_fixedMatrix [Nontrivial A]
    (hdet : ∀ D : SmoothRep.{0, uG, uV} ℂ G,
      D.IsIrreducible → SmoothRep.IsSubquotient D A →
        ∃ v : D, v ∈ fixedVectors D.representation K.toSubgroup ∧ v ≠ 0) :
    A.IsIrreducible ↔
      UnitarizabilityContinuation.IsIrreducibleFamily (fixedMatrix A K hK e) :=
  ⟨fixedMatrix_isIrreducible A K hK e, isIrreducible_of_fixedMatrix A K hK e hdet⟩

end Langlands.Renard.AlgebraicFamily.CompactCompressionMatrices
