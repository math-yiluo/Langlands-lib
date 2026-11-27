import Langlands.TraceFormula.IsotypicTrace.OccurrenceClosure
import Langlands.Representation.Unitary.AdmissibleSemisimplicityProof
import Langlands.Representation.Category.FiniteIndexRestriction
import Langlands.Representation.Smooth.SmoothPart.BasicProof
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-! # Local occurrence from a compact operator on each fixed space -/

noncomputable section

universe uG uE

namespace Langlands.TraceFormula.IsotypicTrace

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
  {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

variable (π : G →* (E →L[ℂ] E))

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
  [TotallyDisconnectedSpace G] [CompleteSpace E] in
private theorem isClosed_fixedSpace
    (K : OpenSubgroup G) :
    IsClosed (fixedVectors (toRepresentation π) K.toSubgroup : Set E) := by
  change IsClosed {x : E | ∀ k : K, π k x = x}
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun k => isClosed_eq (π k).continuous continuous_id

/-- A symmetric operator commuting with the local action and compact on every compact open
fixed space supplies an admissible irreducible subrepresentation when it acts nontrivially on
one such space. -/
theorem exists_irreducible_of_compactOnFixedSpaces
    (hπ : ∀ g x y, inner ℂ (π g x) (π g y) = inner ℂ x y)
    (B : E →L[ℂ] E) (hBs : B.IsSymmetric)
    (hBcomm : ∀ g x, B (π g x) = π g (B x))
    (hBc : ∀ K : OpenSubgroup G, IsCompact (K : Set G) →
      IsCompactOperator (B.comp (fixedVectors (toRepresentation π) K.toSubgroup).subtypeL))
    (K₀ : OpenSubgroup G) (hK₀ : IsCompact (K₀ : Set G))
    (x : fixedVectors (toRepresentation π) K₀.toSubgroup) (hx : B x ≠ 0) :
    ∃ (V : Type uE) (_ : AddCommGroup V) (_ : Module ℂ V)
      (ρ : Representation ℂ G V), IsAdmissible ρ ∧ ρ.IsIrreducible ∧
        ∃ j : ρ.IntertwiningMap (toRepresentation π), Function.Injective j := by
  let ρ := toRepresentation π
  let F (K : OpenSubgroup G) := fixedVectors ρ K.toSubgroup
  have hF (K : OpenSubgroup G) (z : E) (hz : z ∈ F K) : B z ∈ F K := by
    intro k
    change π k (B z) = B z
    rw [← hBcomm, show π k z = z from hz k]
  let Bfix (K : OpenSubgroup G) : F K →L[ℂ] F K := B.restrict (hF K)
  have hcompact (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) :
      IsCompactOperator (Bfix K) := by
    exact (hBc K hK).codRestrict (fun z => hF K z z.property) (isClosed_fixedSpace π K)
  have hs : (Bfix K₀).IsSymmetric := hBs.restrict_invariant (hF K₀)
  have hb0 : Bfix K₀ ≠ 0 := by
    intro heq
    apply hx
    exact congrArg (fun A : F K₀ →L[ℂ] F K₀ => (A x : E)) heq
  let : CompleteSpace (F K₀) := (isClosed_fixedSpace π K₀).completeSpace_coe
  obtain ⟨c, hc, hc0⟩ : ∃ c : ℂ, Module.End.HasEigenvalue (Bfix K₀).toLinearMap c ∧ c ≠ 0 := by
    by_contra! h
    exact hb0 ((ContinuousLinearMap.eq_zero_of_forall_hasEigenvalue_eq_zero
      (hcompact K₀ hK₀) hs).mp h)
  obtain ⟨y, hy⟩ := hc.exists_hasEigenvector
  have hyB : B (y : E) = c • (y : E) :=
    congrArg (fun z : F K₀ => (z : E)) hy.apply_eq_smul
  let M : Subrepresentation ρ :=
    { toSubmodule := smoothVectors ρ ⊓ Module.End.eigenspace B.toLinearMap c
      apply_mem_toSubmodule := by
        intro g z hz
        refine ⟨isSmoothVector_apply g hz.1, Module.End.mem_eigenspace_iff.mpr ?_⟩
        change B (π g z) = c • π g z
        rw [hBcomm, show B z = c • z from Module.End.mem_eigenspace_iff.mp hz.2, map_smul] }
  let yM : M.toSubmodule := ⟨y, ⟨⟨K₀, y.property⟩, Module.End.mem_eigenspace_iff.mpr hyB⟩⟩
  have hyM : yM ≠ 0 := fun hz => hy.2 (Subtype.ext (congrArg (fun w : M.toSubmodule => (w : E)) hz))
  have hcofinal := exists_isCompact_openSubgroup_le (Gv := G)
  have hMadm : IsAdmissible M.toRepresentation := by
    refine ⟨?_, ?_⟩
    · intro z
      obtain ⟨K, hK⟩ := z.property.1
      exact ⟨K, fun k => Subtype.ext (hK k)⟩
    · intro K
      obtain ⟨L, hLc, hLK⟩ := hcofinal K
      let U := Module.End.eigenspace (Bfix L).toLinearMap c
      let : CompleteSpace (F L) := (isClosed_fixedSpace π L).completeSpace_coe
      have : FiniteDimensional ℂ U :=
        ContinuousLinearMap.finite_dimensional_eigenspace (hcompact L hLc) c hc0
      let j : fixedVectors M.toRepresentation K.toSubgroup →ₗ[ℂ] U :=
        { toFun := fun z =>
            have hzL : ((z : M.toSubmodule) : E) ∈ F L := fun k =>
              congrArg (fun w : M.toSubmodule => (w : E)) (z.property ⟨k, hLK k.property⟩)
            ⟨⟨z, hzL⟩, Module.End.mem_eigenspace_iff.mpr
              (Subtype.ext (Module.End.mem_eigenspace_iff.mp (z : M.toSubmodule).property.2))⟩
          map_add' := fun _ _ => Subtype.ext (Subtype.ext rfl)
          map_smul' := fun _ _ => Subtype.ext (Subtype.ext rfl) }
      exact Module.Finite.of_injective j fun _ _ heq =>
        Subtype.ext (Subtype.ext (congrArg (fun w : U => ((w : F L) : E)) heq))
  have hMu : IsUnitarizable M.toRepresentation := by
    exact ⟨{ toInnerProductCore := InnerProductSpace.toCore
             invariant := fun g z w => hπ g z w }⟩
  have hss := admissibleUnitarySemisimplicity G hcofinal M.toSubmodule M.toRepresentation hMadm hMu
  let : IsSemisimpleModule (MonoidAlgebra ℂ G) M.toRepresentation.asModule :=
    (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule _).mp hss
  have hnt : (⊥ : Subrepresentation M.toRepresentation) ≠ ⊤ := by
    intro h
    have hmem : yM ∈ (⊤ : Subrepresentation M.toRepresentation).toSubmodule := Submodule.mem_top
    rw [← h] at hmem
    exact hyM (Submodule.mem_bot ℂ |>.mp hmem)
  let e := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := M.toRepresentation)
  have he : (⊤ : Submodule (MonoidAlgebra ℂ G) M.toRepresentation.asModule) ≠ ⊥ := by
    intro h
    apply hnt.symm
    apply e.injective
    simpa only [OrderIso.map_top, OrderIso.map_bot] using h
  obtain ⟨A', hA', _⟩ := (eq_bot_or_exists_atom_le _).resolve_left he
  let A := e.symm A'
  have hA : IsAtom A := (e.symm.isAtom_iff A').mpr hA'
  let ι : M.toRepresentation.IntertwiningMap ρ := ⟨M.toSubmodule.subtype, fun _ => rfl⟩
  let ιA : A.toRepresentation.IntertwiningMap M.toRepresentation :=
    ⟨A.toSubmodule.subtype, fun _ => rfl⟩
  let j := ι.comp ιA
  have hinj : Function.Injective j := Subtype.val_injective.comp Subtype.val_injective
  have hAirr := FiniteIndexRestriction.isIrreducible_toRepresentation_of_isAtom A hA
  have hAadm := isAdmissible_of_injective ιA Subtype.val_injective hMadm
  exact ⟨A.toSubmodule, inferInstance, inferInstance, A.toRepresentation, hAadm, hAirr, j, hinj⟩

end Langlands.TraceFormula.IsotypicTrace
