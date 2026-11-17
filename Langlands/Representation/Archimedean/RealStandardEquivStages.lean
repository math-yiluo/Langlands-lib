import Langlands.Representation.Archimedean.RealInjectiveIntertwinerStages

/-! # Induction in stages of actual real standard equivalences -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.InductionStages

open Langlands.LocalFactor.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

section Surjectivity

variable {n a r : ℕ} {pre ds es post : List RealBlock}
  (h : a + r ≤ n) (ha : realRank pre = a) (hr : realRank es = r)
  (hr' : realRank ds = r) (hn : realRank (pre ++ es ++ post) = n)
  {T : KFin r ds →ₗ[ℂ] KFin r es}
  (hT : ∀ k f, T (kRep r ds k f) = kRep r es k (T f))

/-- A surjective compact-equivariant middle map induces a surjective ambient map. -/
theorem surjective_ind (hs : Function.Surjective T) :
    Function.Surjective (ind h ha hr hr' hn T hT) := by
  intro G
  obtain ⟨G', hG', hG⟩ := exists_sub_mem_range_ind h ha hr hn hr' T hT ⊥ ⊤
    (fun k v hv => by rw [Submodule.mem_bot] at hv ⊢; rw [hv, map_zero])
    (fun _ _ _ => Submodule.mem_top)
    (fun v _ => by obtain ⟨u, hu⟩ := hs v; exact ⟨u, by rw [hu, sub_self]; exact Submodule.zero_mem _⟩)
    G (fun _ => Submodule.mem_top)
  have hz : G' = 0 := eq_zero_of_sliceK h ha hr G' fun k =>
    (Submodule.mem_bot ℂ).mp (hG' k)
  rw [hz, sub_zero] at hG
  exact hG

/-- Bijectivity is preserved by the actual induced standard intertwiner. -/
theorem standardInd_bijective
    (hI : IsRealStandardIntertwiner r (realStandardRep r es) (realStandardLie r es) ds T)
    (hb : Function.Bijective T) :
    Function.Bijective (standardInd h ha hr hr' hn hI) :=
  ⟨standardInd_injective h ha hr hr' hn hI hb.1,
    surjective_ind h ha hr hr' hn (isRealStandardIntertwiner_iff.mp hI).1 hb.2⟩

end Surjectivity

section Equivalence

variable {n a r : ℕ} {pre ds es post : List RealBlock}
  (h : a + r ≤ n) (ha : realRank pre = a) (hr : realRank es = r)
  (hr' : realRank ds = r) (hn : realRank (pre ++ es ++ post) = n)
  (E : KFin r ds ≃ₗ[ℂ] KFin r es)
  (hE : IsRealStandardIntertwiner r (realStandardRep r es) (realStandardLie r es)
    ds E.toLinearMap)

/-- An actual middle equivalence, extended through arbitrary surrounding blocks. -/
def standardEquivInd :
    KFin n (pre ++ ds ++ post) ≃ₗ[ℂ] KFin n (pre ++ es ++ post) :=
  LinearEquiv.ofBijective (standardInd h ha hr hr' hn hE)
    (standardInd_bijective h ha hr hr' hn hE E.bijective)

theorem standardEquivInd_intertwiner :
    IsRealStandardIntertwiner n (realStandardRep n (pre ++ es ++ post))
      (realStandardLie n (pre ++ es ++ post)) (pre ++ ds ++ post)
      (standardEquivInd h ha hr hr' hn E hE).toLinearMap :=
  standardInd_intertwiner h ha hr hr' hn hE

/-- Its inverse commutes with the compact action and Lie derivatives as well. -/
theorem standardEquivInd_symm_intertwiner :
    IsRealStandardIntertwiner n (realStandardRep n (pre ++ ds ++ post))
      (realStandardLie n (pre ++ ds ++ post)) (pre ++ es ++ post)
      (standardEquivInd h ha hr hr' hn E hE).symm.toLinearMap := by
  let I := standardEquivInd h ha hr hr' hn E hE
  have hI := isRealStandardIntertwiner_iff.mp
    (standardEquivInd_intertwiner h ha hr hr' hn E hE)
  change (∀ k f, I (kRep n (pre ++ ds ++ post) k f) =
      kRep n (pre ++ es ++ post) k (I f)) ∧
    (∀ X f, I (lie n (pre ++ ds ++ post) X f) =
      lie n (pre ++ es ++ post) X (I f)) at hI
  apply isRealStandardIntertwiner_iff.mpr
  constructor
  · intro k f
    apply I.injective
    change I (I.symm (kRep n (pre ++ es ++ post) k f)) =
      I (kRep n (pre ++ ds ++ post) k (I.symm f))
    rw [I.apply_symm_apply, hI.1, I.apply_symm_apply]
  · intro X f
    apply I.injective
    change I (I.symm (lie n (pre ++ es ++ post) X f)) =
      I (lie n (pre ++ ds ++ post) X (I.symm f))
    rw [I.apply_symm_apply, hI.2, I.apply_symm_apply]

/-- The induced equivalence retains the defining actual compact-slice identity. -/
theorem sliceK_standardEquivInd (k : unitaryCompact ℝ n)
    (F : KFin n (pre ++ ds ++ post)) :
    sliceK h ha hr k (standardEquivInd h ha hr hr' hn E hE F) =
      E (sliceK h ha hr' k F) :=
  sliceK_ind h ha hr hr' hn (isRealStandardIntertwiner_iff.mp hE).1 k F

/-- The inverse is also characterized on every actual compact slice. -/
theorem sliceK_standardEquivInd_symm (k : unitaryCompact ℝ n)
    (F : KFin n (pre ++ es ++ post)) :
    sliceK h ha hr' k ((standardEquivInd h ha hr hr' hn E hE).symm F) =
      E.symm (sliceK h ha hr k F) := by
  apply E.injective
  rw [E.apply_symm_apply, ← sliceK_standardEquivInd h ha hr hr' hn E hE,
    LinearEquiv.apply_symm_apply]

end Equivalence

end Langlands.Archimedean.InductionStages

namespace Langlands.Archimedean

open InductionStages Langlands.LocalFactor.Archimedean

/-- Actual standard equivalences extend in stages, with both exact intertwining
directions and both compact-slice identities. -/
def RealStandardEquivStagesStatement : Prop :=
  ∀ {n a r : ℕ} {pre ds es post : List RealBlock}
    (h : a + r ≤ n) (ha : realRank pre = a) (hr : realRank es = r)
    (hr' : realRank ds = r) (_hn : realRank (pre ++ es ++ post) = n)
    (E : KFin r ds ≃ₗ[ℂ] KFin r es)
    (_hE : IsRealStandardIntertwiner r (realStandardRep r es) (realStandardLie r es)
      ds E.toLinearMap),
    ∃ I : KFin n (pre ++ ds ++ post) ≃ₗ[ℂ] KFin n (pre ++ es ++ post),
      IsRealStandardIntertwiner n (realStandardRep n (pre ++ es ++ post))
        (realStandardLie n (pre ++ es ++ post)) (pre ++ ds ++ post) I.toLinearMap ∧
      IsRealStandardIntertwiner n (realStandardRep n (pre ++ ds ++ post))
        (realStandardLie n (pre ++ ds ++ post)) (pre ++ es ++ post)
        I.symm.toLinearMap ∧
      (∀ k F, sliceK h ha hr k (I F) = E (sliceK h ha hr' k F)) ∧
      (∀ k F, sliceK h ha hr' k (I.symm F) = E.symm (sliceK h ha hr k F))

theorem realStandardEquivStages : RealStandardEquivStagesStatement := by
  intro n a r pre ds es post h ha hr hr' hn E hE
  exact ⟨standardEquivInd h ha hr hr' hn E hE,
    standardEquivInd_intertwiner h ha hr hr' hn E hE,
    standardEquivInd_symm_intertwiner h ha hr hr' hn E hE,
    sliceK_standardEquivInd h ha hr hr' hn E hE,
    sliceK_standardEquivInd_symm h ha hr hr' hn E hE⟩

end Langlands.Archimedean
