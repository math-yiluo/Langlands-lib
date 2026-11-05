import Langlands.GroupScheme.Nilpotent.TorusDescent

/-! # Reflection of nilpotence under field base change -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

variable {k K : Type u} [Field k] [Field K]
    {G : GroupScheme (Spec (CommRingCat.of k))}

/-- A uniform all-test lower central bound descends along a flat surjective
field base change, with the same index. -/
theorem HasUniformNilpotentPoints.of_baseChange
    (b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k))
    [Flat b] [Surjective b] {d : ℕ}
    (hd : HasUniformNilpotentPoints ((GroupScheme.baseChange b).obj G) d) :
    HasUniformNilpotentPoints G d := by
  apply IteratedCommutator.hasUniformNilpotentPoints_of_word_eq_one (G := G) (d := d)
  let X : Over (Spec (CommRingCat.of k)) := IteratedCommutator.source G d
  let X' : Over (Spec (CommRingCat.of K)) := (Over.pullback b).obj X
  let p : (Over.map b).obj X' ⟶ X :=
    Over.homMk (pullback.fst X.hom b) (by
      change pullback.fst X.hom b ≫ X.hom = pullback.snd X.hom b ≫ b
      exact pullback.condition)
  let : Epi p.left := by
    change Epi (pullback.fst X.hom b)
    exact Flat.epi_of_flat_of_surjective _
  have ep : Epi p := Over.epi_of_epi_left p
  let e := baseChangePointsEquiv b G X'
  have hbound :
      (⊤ : Subgroup ((Over.map b).obj X' ⟶ G.X)).lowerCentralSeries d = ⊥ := by
    have h := congrArg (Subgroup.map e.toMonoidHom) (hd X')
    simpa only [Subgroup.map_lowerCentralSeries,
      Subgroup.map_top_of_surjective e.toMonoidHom e.surjective,
      Subgroup.map_bot] using h
  have hp := IteratedCommutator.word_mem_lowerCentralSeries G d p
  rw [hbound, Subgroup.mem_bot] at hp
  have he : p ≫ IteratedCommutator.word G d =
      p ≫ (1 : IteratedCommutator.source G d ⟶ G.X) := by
    simpa only [MonObj.comp_one] using hp
  exact @Epi.left_cancellation (Over (Spec (CommRingCat.of k))) _
    ((Over.map b).obj X') X p ep G.X (IteratedCommutator.word G d)
    (1 : IteratedCommutator.source G d ⟶ G.X) he

/-- The same uniform bound holds before and after flat surjective field
base change, without smoothness or reducedness assumptions. -/
theorem hasUniformNilpotentPoints_baseChange_iff
    (b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k))
    [Flat b] [Surjective b] (d : ℕ) :
    HasUniformNilpotentPoints ((GroupScheme.baseChange b).obj G) d ↔
      HasUniformNilpotentPoints G d :=
  ⟨HasUniformNilpotentPoints.of_baseChange b,
    fun h => h.baseChange b⟩

variable [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]

/-- The pullback's chosen uniform bound, retained as a bound on the original
group along flat surjective field base change. -/
def IsNilpotentGroupScheme.descendedUniformNilpotenceBound
    (b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k))
    [Flat b] [Surjective b]
    (hG : IsNilpotentGroupScheme ((GroupScheme.baseChange b).obj G)) :
    ℕ := by
  have : Smooth ((GroupScheme.baseChange b).obj G).X.hom := by
    change Smooth (pullback.snd G.X.hom b)
    infer_instance
  have : IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom := by
    change IsAffineHom (pullback.snd G.X.hom b)
    infer_instance
  have : ConnectedSpace ((GroupScheme.baseChange b).obj G).X.left :=
    G.connectedSpace_baseChange_of_smooth_affine b
  exact hG.uniformNilpotenceBound

/-- The descended bound applies on every relative scheme test of the original
group, including nonreduced tests. -/
theorem IsNilpotentGroupScheme.descendedUniformNilpotenceBound_spec
    (b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k))
    [Flat b] [Surjective b]
    (hG : IsNilpotentGroupScheme ((GroupScheme.baseChange b).obj G)) :
    HasUniformNilpotentPoints G (hG.descendedUniformNilpotenceBound b) := by
  have : Smooth ((GroupScheme.baseChange b).obj G).X.hom := by
    change Smooth (pullback.snd G.X.hom b)
    infer_instance
  have : IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom := by
    change IsAffineHom (pullback.snd G.X.hom b)
    infer_instance
  have : ConnectedSpace ((GroupScheme.baseChange b).obj G).X.left :=
    G.connectedSpace_baseChange_of_smooth_affine b
  exact hG.uniformNilpotenceBound_spec.of_baseChange b

/-- Nilpotence of geometric points descends along flat surjective field
base change for smooth connected affine group schemes. -/
theorem IsNilpotentGroupScheme.of_baseChange
    (b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k))
    [Flat b] [Surjective b]
    (hG : IsNilpotentGroupScheme ((GroupScheme.baseChange b).obj G)) :
    IsNilpotentGroupScheme G :=
  (hG.descendedUniformNilpotenceBound_spec b).isNilpotentGroupScheme

/-- Geometric nilpotence is equivalent before and after flat surjective
field base change for smooth connected affine group schemes. -/
theorem isNilpotentGroupScheme_baseChange_iff
    (b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k))
    [Flat b] [Surjective b] :
    IsNilpotentGroupScheme ((GroupScheme.baseChange b).obj G) ↔
      IsNilpotentGroupScheme G :=
  ⟨IsNilpotentGroupScheme.of_baseChange b, fun h => h.baseChange b⟩

end Langlands.GroupScheme
