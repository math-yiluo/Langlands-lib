import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Noetherian.Defs

/-! # Finite support for sums of ideals on a Noetherian scheme -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

universe u v

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.NoetherianIdealSheaf

private lemma ideal_finset_sup {X : Scheme.{u}} {ι : Type v}
    (s : Finset ι) (I : ι → X.IdealSheafData) (U : X.affineOpens) :
    (s.sup I).ideal U = s.sup (fun i => (I i).ideal U) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert i s hi hs =>
    simp only [Finset.sup_insert, Scheme.IdealSheafData.ideal_sup, Pi.sup_apply, hs]

variable {X : Scheme.{u}} [IsNoetherian X]

/-- A sum of quasi-coherent ideal sheaves on a Noetherian scheme already equals
one finite subsum. -/
theorem exists_finite_sup {ι : Type v} (I : ι → X.IdealSheafData) :
    ∃ s : Finset ι, (⨆ i, I i) = s.sup I := by
  classical
  let 𝒰 := X.affineCover.finiteSubcover
  have haf (i : 𝒰.I₀) : IsAffine (𝒰.X i) := by
    change IsAffine (X.affineCover.X _)
    infer_instance
  let V : 𝒰.I₀ → X.affineOpens := fun i =>
    ⟨(𝒰.f i).opensRange, by
      have := haf i
      exact isAffineOpen_opensRange (𝒰.f i)⟩
  have hV : ⨆ i, (V i).1 = ⊤ := 𝒰.iSup_opensRange
  have hlocal (i : 𝒰.I₀) :
      ∃ s : Finset ι, (⨆ j, I j).ideal (V i) ≤ s.sup (fun j => (I j).ideal (V i)) := by
    have : IsNoetherianRing Γ(X, V i) :=
      IsLocallyNoetherian.component_noetherian (V i)
    have hcompact : IsCompactElement ((⨆ j, I j).ideal (V i)) :=
      (Submodule.fg_iff_compact _).mp (IsNoetherian.noetherian _)
    obtain ⟨s, hs⟩ := hcompact.exists_finset_of_le_iSup
      (fun j => (I j).ideal (V i)) (by
        simp only [Scheme.IdealSheafData.ideal_iSup, iSup_apply]
        exact le_rfl)
    exact ⟨s, by simpa only [Finset.sup_eq_iSup] using hs⟩
  choose t ht using hlocal
  let s := Finset.univ.biUnion t
  refine ⟨s, le_antisymm ?_ ?_⟩
  · apply Scheme.IdealSheafData.le_of_iSup_eq_top V hV
    intro i
    have hts : t i ⊆ s := by
      intro j hj
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hj⟩
    rw [ideal_finset_sup]
    exact (ht i).trans (Finset.sup_mono hts)
  · exact Finset.sup_le fun i _ => le_iSup I i

/-- A chosen finite set of indices supporting the full sum of ideal sheaves. -/
def finiteSupSupport {ι : Type v} (I : ι → X.IdealSheafData) : Finset ι :=
  (exists_finite_sup I).choose

/-- The chosen finite support gives the original full sum. -/
theorem finiteSupSupport_spec {ι : Type v} (I : ι → X.IdealSheafData) :
    (⨆ i, I i) = (finiteSupSupport I).sup I :=
  (exists_finite_sup I).choose_spec

end Langlands.AlgebraicGeometry.NoetherianIdealSheaf
