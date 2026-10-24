import Langlands.Representation.CuspidalSupport.ConstituentInduction
import Langlands.Representation.Smooth.FixedVectors.FiniteTypes

noncomputable section

namespace Langlands.CuspidalSupport

open SmoothRep

universe uG uV uI

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [NonarchimedeanGroup G] [WeaklyLocallyCompactSpace G]

/-- The finite-type choice supplies all the fixed-vector hypotheses for the
constituent induction, while retaining a nonzero vector of the constituent. -/
theorem constituent_of_finite_types
    (H : OpenSubgroup G) [H.toSubgroup.Normal]
    [(H.toSubgroup ⊔ Subgroup.center G).FiniteIndex]
    (A D : SmoothRep.{0, uG, uV} ℂ G)
    (hAa : A.IsAdmissible)
    (hA : Representation.IsSemisimpleRepresentation
      (A.representation.comp H.toSubgroup.subtype))
    (hDa : D.IsAdmissible) (hDi : D.IsIrreducible)
    {ι : Type uI} [Finite ι]
    (T : ι → Subrepresentation (D.representation.comp H.toSubgroup.subtype))
    (hT : ∀ i, T i ≠ ⊥)
    (htypes : ∀ S : Subrepresentation (A.representation.comp H.toSubgroup.subtype),
      IsAtom S → ∃ i, Nonempty ((T i).toRepresentation.Equiv S.toRepresentation))
    (hDA : IsSubquotient D A) :
    IsSubrepresentation D A ∧ IsQuotient D A := by
  let := hDi
  let : Nontrivial D :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) D.representation.asModule
  obtain ⟨v, hv⟩ := exists_ne (0 : D)
  obtain ⟨L, hvL⟩ := D.isSmooth v
  obtain ⟨K, hK, hKL, hKH, hTK⟩ :=
    exists_compactOpen_fixed_finite_types D.representation D.isSmooth H T hT
      (L : Set G) L.mem_nhds_one
  have hvK : v ∈ fixedVectors D.representation K.toSubgroup :=
    fixedVectors_antitone D.representation
      (show K.toSubgroup ≤ L.toSubgroup from hKL) hvL
  have hDfix : Nontrivial (fixedVectors D.representation K.toSubgroup) :=
    ⟨⟨⟨v, hvK⟩, 0, fun heq => hv (congrArg Subtype.val heq)⟩⟩
  have hatoms := fixedVectors_meet_atoms_of_types D.representation A.representation
    H.toSubgroup K.toSubgroup hKH T hTK htypes
  have hgen : ∀ S : Subrepresentation (A.representation.comp H.toSubgroup.subtype),
      fixedVectors A.representation K.toSubgroup ≤ S.toSubmodule → S = ⊤ := by
    let := hA
    intro S hS
    refine eq_top_of_fixedVectors_le_of_semisimple
      (A.representation.comp H.toSubgroup.subtype)
      (K.toSubgroup.comap H.toSubgroup.subtype) ?_ S ?_
    · intro W hW
      obtain ⟨w, hwW, hwK, hw⟩ := hatoms W hW
      refine ⟨w, hwW, ?_, hw⟩
      rwa [fixedVectors_comp_subtype A.representation H.toSubgroup K.toSubgroup hKH]
    · rwa [fixedVectors_comp_subtype A.representation H.toSubgroup K.toSubgroup hKH]
  exact fixedVectorConstituentInduction G H.toSubgroup K hK hKH A D
    hA hgen (hAa.2 K) hDa hDi hDfix hDA

end Langlands.CuspidalSupport
