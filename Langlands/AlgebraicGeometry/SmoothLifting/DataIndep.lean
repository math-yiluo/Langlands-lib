import Langlands.AlgebraicGeometry.SmoothLifting.DataChange

/-! # Independence of global affine combinations from the lifting data

Two lifting data over the same ring `C` that share a global lift have interchangeable charts, and
global affine combinations of common lifts do not depend on which data is used.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Limits

namespace Langlands.AlgebraicGeometry.SmoothLifting

variable {X S : Scheme.{u}} {f : X ⟶ S} {C : CommRingCat.{u}} {I : Ideal C}
  {x₀ : Spec (CommRingCat.of (C ⧸ I)) ⟶ X} {s : Spec C ⟶ S}

section Indep

variable {I₂ : Ideal C} {x₀₂ : Spec (CommRingCat.of (C ⧸ I₂)) ⟶ X} {s₂ : Spec C ⟶ S}

/-- A global lift lands in the open of a chart on the basic open of its element. -/
theorem IsGlobalLift.mem_chart (hI : SqZero I) {y : Spec C ⟶ X} (hy : IsGlobalLift f I x₀ s y)
    (ch : Chart f I x₀ s) (q : Spec C) (hq : ch.g ∉ q.asIdeal) : y q ∈ ch.U := by
  obtain ⟨p, rfl⟩ := specMap_surjective (CommRingCat.ofHom (Ideal.Quotient.mk I))
    Ideal.Quotient.mk_surjective
    (by rw [CommRingCat.hom_ofHom, Ideal.mk_ker]; exact hI.le_nilradical) q
  rw [← Scheme.Hom.comp_apply, hy.1]
  exact ch.hx p hq

/-- Transfer of a chart to other data sharing a global lift. -/
def Chart.transfer (hI : SqZero I) (ch : Chart f I x₀ s) {y : Spec C ⟶ X}
    (hy : IsGlobalLift f I x₀ s y) (hy₂ : IsGlobalLift f I₂ x₀₂ s₂ y) :
    Chart f I₂ x₀₂ s₂ where
  V := ch.V
  hV := ch.hV
  U := ch.U
  hU := ch.hU
  hUV := ch.hUV
  g := ch.g
  hs p hp := by
    rw [← hy₂.2, hy.2]
    exact ch.hs p hp
  hx p hp := by
    rw [← hy₂.1, Scheme.Hom.comp_apply]
    exact hy.mem_chart hI ch _ hp

/-- Chart representatives do not depend on the data. -/
theorem Chart.rep_transfer (hI : SqZero I) (hI₂ : SqZero I₂) (ch : Chart f I x₀ s)
    {y : Spec C ⟶ X} (hy : IsGlobalLift f I x₀ s y) (hy₂ : IsGlobalLift f I₂ x₀₂ s₂ y)
    {T : Type u} [CommRing T] [Algebra C T] (hg : IsUnit (algebraMap C T ch.g))
    {z : Spec (CommRingCat.of T) ⟶ X} (hz : IsLift f I x₀ s T z)
    (hz₂ : IsLift f I₂ x₀₂ s₂ T z) :
    (ch.transfer hI hy hy₂).rep T hI₂ hg z hz₂ = ch.rep T hI hg z hz :=
  chartRep_eq _ _ _ (ch.rep_spec T hI hg z hz)

theorem affComb_congr' {B R : Type*} [CommRing B] [CommRing R] {ι : Type*} [Fintype ι]
    (J₁ J₂ : Ideal R) (hJ₁ : SqZero J₁) (hJ₂ : SqZero J₂) {φ₀ φ₀' : B →+* R} (e₀ : φ₀ = φ₀')
    {φ φ' : ι → B →+* R} (e : φ = φ') (h₁ : ∀ k b, φ k b - φ₀ b ∈ J₁)
    (h₂ : ∀ k b, φ' k b - φ₀' b ∈ J₂) (c : ι → R) :
    affComb J₁ hJ₁ φ₀ φ h₁ c = affComb J₂ hJ₂ φ₀' φ' h₂ c := by
  subst e₀ e
  exact RingHom.ext fun _ => rfl

/-- Chart combinations do not depend on the data. -/
theorem Chart.comb_transfer {ι : Type} [Fintype ι] (hI : SqZero I) (hI₂ : SqZero I₂)
    (ch : Chart f I x₀ s) {y : Spec C ⟶ X} (hy : IsGlobalLift f I x₀ s y)
    (hy₂ : IsGlobalLift f I₂ x₀₂ s₂ y) {T : Type u} [CommRing T] [Algebra C T]
    (hg : IsUnit (algebraMap C T ch.g)) (z₀ : Spec (CommRingCat.of T) ⟶ X)
    (hz₀ : IsLift f I x₀ s T z₀) (hz₀₂ : IsLift f I₂ x₀₂ s₂ T z₀)
    (z : ι → (Spec (CommRingCat.of T) ⟶ X)) (hz : ∀ k, IsLift f I x₀ s T (z k))
    (hz₂ : ∀ k, IsLift f I₂ x₀₂ s₂ T (z k)) (c : ι → T) :
    ch.comb T hI hg z₀ hz₀ z hz c =
      (ch.transfer hI hy hy₂).comb T hI₂ hg z₀ hz₀₂ z hz₂ c := by
  unfold Chart.comb
  rw [affComb_congr' _ _ _ (hI₂.map _)
    (congrArg CommRingCat.Hom.hom (ch.rep_transfer hI hI₂ hy hy₂ hg hz₀ hz₀₂).symm)
    (funext fun k => congrArg CommRingCat.Hom.hom
      (ch.rep_transfer hI hI₂ hy hy₂ hg (hz k) (hz₂ k)).symm)]
  rfl

/-- **Global affine combinations do not depend on the data**, only on the lifts. -/
theorem gcomb_data_indep {ι : Type} [Fintype ι] (hI : SqZero I) (hI₂ : SqZero I₂)
    {y₀ : Spec C ⟶ X} (hy₀ : IsGlobalLift f I x₀ s y₀) (hy₀₂ : IsGlobalLift f I₂ x₀₂ s₂ y₀)
    {y : ι → (Spec C ⟶ X)} (hy : ∀ k, IsGlobalLift f I x₀ s (y k))
    (hy₂ : ∀ k, IsGlobalLift f I₂ x₀₂ s₂ (y k)) (c : ι → C) :
    gcomb hI hy₀ hy c = gcomb hI₂ hy₀₂ hy₂ c := by
  classical
  obtain ⟨n, chs, hspan⟩ := exists_charts hI hy₀.h₀
  refine IsGlobalLift.ext_of_charts (fun i => (chs i).transfer hI hy₀ hy₀₂) hspan fun i => ?_
  have hg : IsUnit (algebraMap C (Loc (chs i).g) (chs i).g) := isUnit_loc _
  have h1 := gcomb_restr hI hy₀ hy c (chs i) (Loc (chs i).g) hg
  have h2 := gcomb_restr hI₂ hy₀₂ hy₂ c ((chs i).transfer hI hy₀ hy₀₂) (Loc (chs i).g) hg
  have h3 := (chs i).comb_transfer hI hI₂ hy₀ hy₀₂ hg _ (hy₀.isLift _) (hy₀₂.isLift _) _
    (fun k => (hy k).isLift _) (fun k => (hy₂ k).isLift _) (fun k => algebraMap C _ (c k))
  exact h1.trans (h3.trans h2.symm)

end Indep

end Langlands.AlgebraicGeometry.SmoothLifting
