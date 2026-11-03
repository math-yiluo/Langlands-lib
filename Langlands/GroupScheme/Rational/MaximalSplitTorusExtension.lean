import Langlands.GroupScheme.Rational.SplitTorusFiniteRank
import Langlands.GroupScheme.Rational.SplitTorusMonomorphism
import Mathlib.Data.Nat.Find

/-! # Maximal extensions of actual split subtori -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable {k : Type u} [Field k]
local notation "S" => Spec (CommRingCat.of k)
variable (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
variable {T : CommGroupScheme (Spec (CommRingCat.of k))} (i : T.toGrp ⟶ G)

/-- Every actual split subtorus of an affine locally finite-type group over a
field factors through an actual maximal split torus. -/
theorem exists_maximalSplitTorus_extension (hi : IsSplitSubtorus i) :
    ∃ (M : CommGroupScheme S) (j : M.toGrp ⟶ G), IsMaximalSplitTorus j ∧
      ∃ f : T.toGrp ⟶ M.toGrp, f ≫ j = i := by
  classical
  let := Lie.finiteDimensional_lieKernel k G
  let N := Module.finrank k (Additive (lieKernel G k))
  let p : ℕ → Prop := fun n => ∃ (I : Type u) (_ : Finite I)
    (j : splitTorus S I ⟶ G), IsClosedSubgroup j ∧
      ∃ f : T.toGrp ⟶ splitTorus S I, f ≫ j = i ∧ Nat.card I = n
  have hbound (n : ℕ) (hn : p n) : n ≤ N := by
    obtain ⟨I, hI, j, hj, f, hfi, rfl⟩ := hn
    exact splitTorus.card_le_finrank_lieKernel I j hj
  obtain ⟨I₀, hI₀, ⟨e₀⟩⟩ := hi.1
  have hp₀ : p (Nat.card I₀) := by
    refine ⟨I₀, hI₀, e₀.inv ≫ i, hi.2.iso_comp e₀.symm, e₀.hom, ?_, rfl⟩
    simp
  have hp := Nat.findGreatest_spec (hbound _ hp₀) hp₀
  obtain ⟨I, hI, j, hj, f, hfi, hcard⟩ := hp
  refine ⟨splitTorus.commGroupScheme S I, j, ⟨⟨isSplitTorus_splitTorus I, hj⟩, ?_⟩,
    f, hfi⟩
  intro M j' hj' a ha
  obtain ⟨J, hJ, ⟨e⟩⟩ := hj'.1
  let d : splitTorus S I ⟶ splitTorus S J := a ≫ e.hom
  let j'' : splitTorus S J ⟶ G := e.inv ≫ j'
  have hj'' : IsClosedSubgroup j'' := hj'.2.iso_comp e.symm
  have hfac : d ≫ j'' = j := by
    dsimp only [d, j'']
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using ha
  have hpJ : p (Nat.card J) := by
    refine ⟨J, hJ, j'', hj'', f ≫ d, ?_, rfl⟩
    rw [Category.assoc, hfac, hfi]
  have hle : Nat.card J ≤ Nat.card I := by
    rw [hcard]
    exact Nat.le_findGreatest (hbound _ hpJ) hpJ
  let : IsClosedImmersion j.hom.hom.left := hj
  let : Mono j.hom.hom := Over.mono_of_mono_left _
  let : Mono d.hom.hom := mono_of_mono_fac
    (congrArg (fun b => b.hom.hom) hfac)
  have hge : Nat.card I ≤ Nat.card J := splitTorus.card_le_card_of_mono I J d
  let : IsIso d := splitTorus.isIso_of_mono_of_card_eq I J d (le_antisymm hge hle)
  exact (isIso_comp_right_iff a e.hom).mp (show IsIso (a ≫ e.hom) from inferInstance)

/-- A choice of an actual maximal split torus through which the given split
subtorus factors, with its maximality and factorization proofs. -/
def maximalSplitExtension (hi : IsSplitSubtorus i) :
    Σ M : CommGroupScheme S, {j : M.toGrp ⟶ G // IsMaximalSplitTorus j ∧
      ∃ f : T.toGrp ⟶ M.toGrp, f ≫ j = i} :=
  let h := exists_maximalSplitTorus_extension G i hi
  ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec⟩

end Langlands.GroupScheme
