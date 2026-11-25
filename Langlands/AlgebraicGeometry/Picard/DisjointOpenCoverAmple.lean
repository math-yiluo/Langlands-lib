import Langlands.AlgebraicGeometry.Picard.FiniteCoproductAmple
import Langlands.AlgebraicGeometry.Modules.FiniteFrameRankLoci

/-! # Ampleness assembled over a disjoint open cover -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace Langlands.AlgebraicGeometry.Picard

variable {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    (hU : (⨆ i, U i) = ⊤) (hd : Pairwise (fun i j => Disjoint (U i) (U j)))

/-- The actual scheme coproduct of a disjoint open cover is the original scheme. -/
def disjointOpenCoverIso : (∐ fun i => (U i).toScheme) ≅ X := by
  let f : ∀ i, (U i).toScheme ⟶ X := fun i => (U i).ι
  have hcov : (⨆ i, (f i).opensRange) = ⊤ := by
    simpa only [f, Scheme.Opens.opensRange_ι] using hU
  have hdis : Pairwise (fun i j => Disjoint (f i).opensRange (f j).opensRange) := by
    simpa only [f, Scheme.Opens.opensRange_ι] using hd
  have hc := nonempty_isColimit_cofanMk_of f hcov hdis
  have : IsIso (Sigma.desc f) :=
    (Cofan.nonempty_isColimit_iff_isIso_sigmaDesc (Cofan.mk X f)).mp hc
  exact asIso (Sigma.desc f)

theorem disjointOpenCoverIso_ι (i : ι) :
    Sigma.ι (fun i => (U i).toScheme) i ≫ (disjointOpenCoverIso U hU hd).hom = (U i).ι := by
  exact Sigma.ι_comp_desc _ _

namespace LineBundle

variable [CompactSpace X] [QuasiSeparatedSpace X] (L : LineBundle X)

include hU hd in
theorem isAmple_of_finite_disjoint_openCover [Finite ι]
    (hL : ∀ i, ((pullback (U i).ι).obj L).IsAmple) : L.IsAmple := by
  let E := disjointOpenCoverIso U hU hd
  let H := TopCat.homeoOfIso (Scheme.forgetToTop.mapIso E)
  let : CompactSpace (∐ fun i => (U i).toScheme : Scheme.{u}) := H.symm.compactSpace
  let : QuasiSeparatedSpace (∐ fun i => (U i).toScheme : Scheme.{u}) :=
    H.isOpenEmbedding.quasiSeparatedSpace
  let K := (pullback E.hom).obj L
  have hK : K.IsAmple := by
    apply isAmple_of_finite_coproduct (fun i => (U i).toScheme) K
    intro i
    let A : ((pullback (Sigma.ι (fun i => (U i).toScheme) i)).obj K).obj ≅
        ((pullback (U i).ι).obj L).obj :=
      (Scheme.Modules.pullbackComp (Sigma.ι (fun i => (U i).toScheme) i) E.hom).app L.obj ≪≫
        (Scheme.Modules.pullbackCongr (disjointOpenCoverIso_ι U hU hd i)).app L.obj
    exact (hL i).of_iso A.symm
  exact (hK.pullback_of_isAffineHom E.inv).of_iso
    ((Scheme.Modules.pullbackComp E.inv E.hom).app L.obj ≪≫
      (Scheme.Modules.pullbackCongr E.inv_hom_id).app L.obj ≪≫
        (Scheme.Modules.pullbackId X).app L.obj)

include hU hd in
/-- On a compact quasi-separated scheme, ampleness of the actual line
restrictions to all members of any disjoint open cover gives ampleness. -/
theorem isAmple_of_disjoint_openCover
    (hL : ∀ i, ((pullback (U i).ι).obj L).IsAmple) : L.IsAmple := by
  classical
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun i => (U i : Set X)) (fun i => (U i).isOpen) (by
      intro x _
      have hx : x ∈ ⨆ i, U i := by rw [hU]; trivial
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
      exact Set.mem_iUnion.mpr ⟨i, hi⟩)
  let J := {i : ι // i ∈ s}
  have hcov : (⨆ j : J, U j.val) = ⊤ := by
    apply top_le_iff.mp
    intro x _
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨i, hi⟩, hxi⟩
  have hdis : Pairwise (fun i j : J => Disjoint (U i.val) (U j.val)) :=
    fun i j hij => hd (fun he => hij (Subtype.ext he))
  exact isAmple_of_finite_disjoint_openCover (fun j : J => U j.val) hcov hdis L
    (fun j => hL j.val)

end LineBundle

namespace FiniteLocalFrames

variable {M : X.Modules} (a : FiniteLocalFrames M)
    [CompactSpace X] [QuasiSeparatedSpace X] (L : LineBundle X)

/-- Actual ampleness on every clopen rank locus assembles without a global
constant-rank assumption. -/
theorem isAmple_of_rankOpen
    (hL : ∀ n, ((LineBundle.pullback (a.rankOpen n).ι).obj L).IsAmple) : L.IsAmple := by
  apply LineBundle.isAmple_of_disjoint_openCover (fun n : ULift.{u} ℕ => a.rankOpen n.down)
    _ _ L (fun n => hL n.down)
  · apply top_le_iff.mp
    intro x _
    have hx : x ∈ ⨆ n, a.rankOpen n := by rw [a.iSup_rankOpen]; trivial
    obtain ⟨n, hn⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨n⟩, hn⟩
  · intro i j hij
    exact a.rankOpen_disjoint (fun he => hij (ULift.ext he))

end FiniteLocalFrames

end Langlands.AlgebraicGeometry.Picard
