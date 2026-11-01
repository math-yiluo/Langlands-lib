import Langlands.Representation.IntegerLattice.GeneralizedWeightSupportStatement
import Langlands.Representation.Exponents.DualEigenfunctionalExistence

/-! # Actual generalized-weight support and common eigenvectors -/

set_option autoImplicit false

namespace Langlands

universe u

open IntegerLattice

/-- The actual generalized-weight block is nonzero exactly when its label
is realized by a common nonzero eigenvector of the original tuple. -/
theorem commutingTupleGeneralizedWeightSupport :
    CommutingTupleGeneralizedWeightSupportStatement.{u} := by
  intro d V _ _ _ A c
  constructor
  · intro hW
    let W := generalizedWeightBlock A c
    let f : Fin d → Module.End ℂ V := fun i => (A.1 i : Module.End ℂ V)
    have : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW
    have hc : ∀ i j, Commute (f i) (f j) := by
      intro i j
      rcases eq_or_ne i j with rfl | hij
      · exact Commute.refl _
      · exact (A.2 hij).map (Units.coeHom _)
    have hstab : ∀ i, Set.MapsTo (f i) W W := by
      intro i
      simpa only [tupleRepresentationEquiv_generator] using
        mapsTo_generalizedWeightBlock A c (generator d i)
    have hNmaps : ∀ i,
        Set.MapsTo (f i - algebraMap ℂ (Module.End ℂ V) (c i : ℂ)) W W := by
      intro i w hw
      rw [LinearMap.sub_apply, Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply,
        Module.End.one_apply]
      exact W.sub_mem (hstab i hw) (W.smul_mem _ hw)
    let N : Fin d → Module.End ℂ W := fun i =>
      (f i - algebraMap ℂ (Module.End ℂ V) (c i : ℂ)).restrict (hNmaps i)
    have hNc : ∀ i j, Commute (N i) (N j) := by
      intro i j
      have h : Commute (f i - algebraMap ℂ (Module.End ℂ V) (c i : ℂ))
          (f j - algebraMap ℂ (Module.End ℂ V) (c j : ℂ)) :=
        ((hc i j).sub_right (Algebra.commute_algebraMap_right _ _)).sub_left
          (Algebra.commute_algebraMap_left _ _)
      refine LinearMap.ext fun w => Subtype.ext ?_
      exact LinearMap.congr_fun h.eq (w : V)
    have hNn : ∀ i, IsNilpotent (N i) := by
      intro i
      have hle : W ≤ (f i).maxGenEigenspace (c i : ℂ) :=
        fun w hw => mem_generalizedWeightBlock.mp hw i
      exact Module.End.isNilpotent_restrict_of_le hle
        (Module.End.isNilpotent_restrict_maxGenEigenspace_sub_algebraMap (f i) (c i : ℂ))
    obtain ⟨w, hw0, hw⟩ :=
      DualEigenfunctional.exists_ne_zero_forall_apply_eq_zero N hNc hNn
    refine ⟨(w : V), fun h => hw0 (Subtype.ext h), fun i => ?_⟩
    have h := congrArg Subtype.val (hw i)
    have hzero : f i (w : V) - (c i : ℂ) • (w : V) = 0 := by
      simpa [N, Algebra.algebraMap_eq_smul_one] using h
    exact sub_eq_zero.mp hzero
  · rintro ⟨v, hv0, hv⟩
    apply (Submodule.ne_bot_iff _).mpr
    refine ⟨v, mem_generalizedWeightBlock.mpr (fun i => ?_), hv0⟩
    exact Module.End.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.mpr (hv i))

end Langlands
