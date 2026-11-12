import Langlands.Representation.Plancherel.CompactInductionGeneration
import Langlands.Representation.Plancherel.CompactIntertwiningCompression
import Langlands.Representation.Jacquet.FixedVectorGeneratedCategory

/-! # Prescribed-level generation from actual compact-picture expansions -/

noncomputable section

open CategoryTheory
open scoped NNReal

namespace Langlands.Plancherel

open Aubert.General

universe uG uI uV

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P M U : Subgroup G}
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (hδ : IsUnimodularModulus U hU)
  (K : OpenSubgroup G) (hP : IsClosed (P : Set G)) (hK : IsCompact (K : Set G))
  (hPK : ∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G))
  {I : Type uI} (ν : I → (M →* ℝ≥0ˣ)) (hν : ∀ i, Continuous (ν i))
  (hr : Continuous h.projection)
  (A : SmoothRep.{0, uG, uV} ℂ M)

include hδ hP hK hPK hν hr in
/-- A top regular translate span at a specified level implies actual
fixed-vector generation at each unramified parameter at that same level. -/
theorem fixedVectorGenerated_unramifiedInduction_of_regularSpan
    (L : OpenSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hspan : regularTranslateSpan h hU hδ K hP hK hPK ν hν hr A
      (fixedGenerators h K A L) = ⊤) (χ : unramifiedCharacters ν) :
    Jacquet.fixedVectorGenerated L.toSubgroup (UnramifiedLeviInduction h hU ν χ A) := by
  let e := unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK ν hν hr χ A
  intro S hS
  apply top_unique
  intro f _
  have hf : e f ∈ regularTranslateSpan h hU hδ K hP hK hPK ν hν hr A
      (fixedGenerators h K A L) := by
    rw [hspan]
    exact Submodule.mem_top
  obtain ⟨n, c, gs, j, hfe⟩ := hf
  have he : f = ∑ i, (c i).val χ •
      (UnramifiedLeviInduction h hU ν χ A).representation (gs i) (e.symm (j i).val) := by
    apply e.injective
    rw [map_sum, hfe χ]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul]
    rfl
  rw [he]
  apply S.toSubmodule.sum_mem
  intro i _
  apply S.toSubmodule.smul_mem
  apply S.apply_mem_toSubmodule
  exact hS (compactFixedEquiv h hU hδ K hP hK hPK ν hν hr A
    χ L hLK (j i)).property

include hδ hP hK hPK hν hr in
/-- The regular-span criterion also generates the actual full-parabolic
normalized induction of every unramified twist. -/
theorem fixedVectorGenerated_normalizedTwistedInduction_of_regularSpan
    (L : OpenSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hspan : regularTranslateSpan h hU hδ K hP hK hPK ν hν hr A
      (fixedGenerators h K A L) = ⊤) (χ : unramifiedCharacters ν) :
    Jacquet.fixedVectorGenerated L.toSubgroup
      ((normalizedInductionFunctor h hU).obj
        (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ))) :=
  (Jacquet.fixedVectorGenerated L.toSubgroup).prop_of_iso
    (SmoothRep.mkIso (normalizedInductionLeviEquiv h hU hδ
      (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)))).symm
    (fixedVectorGenerated_unramifiedInduction_of_regularSpan h hU hδ K hP hK hPK ν hν hr A
      L hLK hspan χ)

include hδ hP hK hPK hν hr in
/-- Specialization at the trivial parameter gives generation of actual
untwisted normalized induction at the prescribed level. -/
theorem fixedVectorGenerated_normalizedInduction_of_regularSpan
    (L : OpenSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hspan : regularTranslateSpan h hU hδ K hP hK hPK ν hν hr A
      (fixedGenerators h K A L) = ⊤) :
    Jacquet.fixedVectorGenerated L.toSubgroup ((normalizedInductionFunctor h hU).obj A) := by
  have hgen := fixedVectorGenerated_normalizedTwistedInduction_of_regularSpan
    h hU hδ K hP hK hPK ν hν hr A L hLK hspan 1
  exact (Jacquet.fixedVectorGenerated L.toSubgroup).prop_of_iso
    ((normalizedInductionFunctor h hU).mapIso (SmoothRep.twistOneIso _ A)) hgen

include hδ hP hK hPK hr in
/-- Actual prescribed-level normalized induction generation from an Iwahori
contraction, a cofinal factorized basis, and coefficient orbit generators
fixed by the prescribed coefficient intersection. -/
theorem fixedVectorGenerated_normalizedInduction_of_contraction
    [T2Space G] {Ubar : Subgroup G}
    (hMUbar : M ≤ Subgroup.normalizer (Ubar : Set G))
    (hPUbar : ∀ x : G, x ∈ P → x ∈ Ubar → x = 1)
    (L : OpenSubgroup G) (hL : IsCompact (L : Set G))
    (hLK : L.toSubgroup ≤ K.toSubgroup) (hfL : IsCellFactorized U M Ubar L.toSubgroup)
    (g : G) (hg : Jacquet.IsIwahoriContraction L U M Ubar g)
    {J : Type*} (v : J → A)
    (hgen : ∀ u : A, u ∈ Submodule.span ℂ
      (Set.range fun x : M × J => A.representation x.1 (v x.2)))
    (hv : ∀ j, ∀ p : P, (p : G) ∈ L → A.representation (h.projection p) (v j) = v j)
    (hbasis : ∀ O : Set G, IsOpen O → (1 : G) ∈ O →
      ∃ L' : OpenSubgroup G, IsCompact (L' : Set G) ∧ (L' : Set G) ⊆ O ∧
        IsCellFactorized U M Ubar L'.toSubgroup) :
    Jacquet.fixedVectorGenerated L.toSubgroup ((normalizedInductionFunctor h hU).obj A) := by
  let ν₀ : Empty → (M →* ℝ≥0ˣ) := Empty.elim
  have hν₀ : ∀ i, Continuous (ν₀ i) := fun i => nomatch i
  exact fixedVectorGenerated_normalizedInduction_of_regularSpan h hU hδ K hP hK hPK
    ν₀ hν₀ hr A L hLK
    (regularTranslateSpan_eq_top h hU hδ K hP hK hPK ν₀ hν₀ hr A hMUbar hPUbar
      L hL hLK hfL g hg v hgen hv hbasis)

end Langlands.Plancherel
