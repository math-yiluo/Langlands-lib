import Langlands.Cohomology.Tate.OrdinaryTateComparison
import Langlands.Cohomology.Tate.OrdinaryTateBoundaryStatement
import Langlands.Cohomology.Tate.SpliceRepresentatives
import Langlands.Cohomology.Tate.DoubleBoundary
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Tate

set_option backward.isDefEq.respectTransparency false

variable {R G : Type u} [CommRing R] [Group G] [Fintype G]

/-- An ordinary cocycle is the same cochain viewed in the actual Tate complex. -/
def ordinaryTateCycles (A : Rep.{u} R G) (n : ℕ) :
    groupCohomology.cocycles A n ⟶ (tateComplex A).cycles n :=
  (tateComplex A).liftCycles (groupCohomology.iCocycles A n) (n + 1) (by simp)
    (by exact (groupCohomology.inhomogeneousCochains A).iCycles_d n (n + 1))

@[reassoc (attr := simp)]
lemma ordinaryTateCycles_iCycles (A : Rep.{u} R G) (n : ℕ) :
    ordinaryTateCycles A n ≫ (tateComplex A).iCycles n =
      groupCohomology.iCocycles A n := by
  simp [ordinaryTateCycles]

lemma ordinaryToTate_pos_π (A : Rep.{u} R G) (n : ℕ) [NeZero n] :
    groupCohomology.π A n ≫ ordinaryToTate A n =
      ordinaryTateCycles A n ≫ (tateComplex A).homologyπ n := by
  rw [ordinaryToTate_pos]
  change groupCohomology.π A n ≫
    ((tateComplexConnectData A).homologyIsoPos n n rfl).inv = _
  simp only [CochainComplex.ConnectData.homologyIsoPos, Iso.trans_inv, Iso.symm_inv, HomologicalComplex.homologyMapIso_inv,
    groupCohomology.π, groupCohomology]
  rw [← Category.assoc, HomologicalComplex.homologyπ_naturality,
    Category.assoc, HomologicalComplex.homologyπ_restrictionHomologyIso_hom,
    ← Category.assoc]
  congr 1
  apply (cancel_mono ((tateComplex A).iCycles n)).mp
  simp [ordinaryTateCycles, CochainComplex.ConnectData.restrictionGEIso,
    HomologicalComplex.restrictionXIso]

lemma ordinaryToTate_zero_π (A : Rep.{u} R G) :
    groupCohomology.π A 0 ≫ ordinaryToTate A 0 =
      ordinaryTateCycles A 0 ≫ (tateComplex A).homologyπ 0 := by
  rw [ordinaryToTate_zero, ← Category.assoc, groupCohomology.π_comp_H0Iso_hom]
  apply (cancel_epi (groupCohomology.cocyclesIso₀ A).inv).mp
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  ext a
  rw [ModuleCat.ofHom_apply, zeroClass_eq_cycleClass]
  apply congrArg ((tateComplex A).homologyπ 0)
  apply (ModuleCat.mono_iff_injective ((tateComplex A).iCycles 0)).mp inferInstance
  calc
    _ = (groupCohomology.cochainsIso₀ A).inv a :=
      (tateComplex A).i_cyclesMk _ _ _ _
    _ = _ := by
      have hi : ((groupCohomology.cocyclesIso₀ A).inv ≫ ordinaryTateCycles A 0) ≫
          (tateComplex A).iCycles 0 =
          (groupCohomology.shortComplexH0 A).f ≫ (groupCohomology.cochainsIso₀ A).inv := by
        exact (Category.assoc _ _ _).trans
          ((congrArg (fun f => (groupCohomology.cocyclesIso₀ A).inv ≫ f)
            (ordinaryTateCycles_iCycles A 0)).trans
              (groupCohomology.cocyclesIso₀_inv_comp_iCocycles A))
      exact (ConcreteCategory.congr_hom hi a).symm

lemma ordinaryToTate_π (A : Rep.{u} R G) (n : ℕ) :
    groupCohomology.π A n ≫ ordinaryToTate A n =
      ordinaryTateCycles A n ≫ (tateComplex A).homologyπ n := by
  cases n with
  | zero => exact ordinaryToTate_zero_π A
  | succ n => exact ordinaryToTate_pos_π A (n + 1)

lemma ordinaryToTate_cyclesMk (A : Rep.{u} R G) (n : ℕ)
    (z : (groupCohomology.inhomogeneousCochains A).X n)
    (hz : (groupCohomology.inhomogeneousCochains A).d n (n + 1) z = 0) :
    ordinaryToTate A n ((groupCohomology.inhomogeneousCochains A).homologyπ n
      ((groupCohomology.inhomogeneousCochains A).cyclesMk z (n + 1) (by simp) hz)) =
      cycleClass (tateComplex A) n z hz := by
  refine (ConcreteCategory.congr_hom (ordinaryToTate_π A n) _).trans ?_
  apply congrArg ((tateComplex A).homologyπ n)
  apply (ModuleCat.mono_iff_injective ((tateComplex A).iCycles n)).mp inferInstance
  calc
    _ = groupCohomology.iCocycles A n
        ((groupCohomology.inhomogeneousCochains A).cyclesMk z (n + 1) (by simp) hz) :=
      ConcreteCategory.congr_hom (ordinaryTateCycles_iCycles A n) _
    _ = z := (groupCohomology.inhomogeneousCochains A).i_cyclesMk _ _ _ _
    _ = _ := ((tateComplex A).i_cyclesMk (i := (n : ℤ)) z (n + 1) (by simp) (by exact hz)).symm

lemma ordinaryToTate_delta {S : ShortComplex (Rep.{u} R G)} (hS : S.ShortExact)
    (n : ℕ) :
    groupCohomology.δ hS n (n + 1) rfl ≫ ordinaryToTate S.X₁ (n + 1) =
      ordinaryToTate S.X₃ n ≫ TateCohomology.δ hS n := by
  let T := S.map (tateComplexFunctor R G)
  have hT : T.ShortExact := TateCohomology.map_tateComplexFunctor_shortExact hS
  let C := S.map (groupCohomology.cochainsFunctor R G)
  have hC : C.ShortExact := groupCohomology.map_cochainsFunctor_shortExact hS
  ext c
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective (groupCohomology.π S.X₃ n)).mp
    inferInstance c
  let z₀ := groupCohomology.iCocycles S.X₃ n z
  have hz₀ : C.X₃.d n (n + 1) z₀ = 0 :=
    ConcreteCategory.congr_hom (C.X₃.iCycles_d n (n + 1)) z
  have hzrep : C.X₃.cyclesMk z₀ (n + 1) (by simp) hz₀ = z := by
    apply (ModuleCat.mono_iff_injective (C.X₃.iCycles n)).mp inferInstance
    exact C.X₃.i_cyclesMk _ _ _ _
  obtain ⟨y, hy⟩ := complexExact_surjective hT n z₀
  have hy₀ : T.g.f (n + 1) (T.X₂.d n (n + 1) y) = 0 := by
    rw [complexMap_d_apply, hy]
    exact hz₀
  obtain ⟨x, hx⟩ := complexExact_preimage hT (n + 1) _ hy₀
  have hx₀ : C.f.f (n + 1) x = C.X₂.d n (n + 1) y := hx
  have hdx : C.X₁.d (n + 1) (n + 1 + 1) x = 0 :=
    hC.d_eq_zero_of_f_eq_d_apply n (n + 1) y x hx₀ (n + 1 + 1)
  have hd : groupCohomology.δ hS n (n + 1) rfl (groupCohomology.π S.X₃ n z) =
      C.X₁.homologyπ (n + 1) (C.X₁.cyclesMk x (n + 1 + 1) (by simp) hdx) := by
    rw [← hzrep]
    exact hC.δ_apply n (n + 1) rfl z₀ hz₀ y hy x hx₀ (n + 1 + 1) (by simp)
  have hzclass : ordinaryToTate S.X₃ n (groupCohomology.π S.X₃ n z) =
      cycleClass T.X₃ n z₀ hz₀ := by
    rw [← hzrep]
    exact ordinaryToTate_cyclesMk S.X₃ n z₀ hz₀
  change ordinaryToTate S.X₁ (n + 1) (groupCohomology.δ hS n (n + 1) rfl
      (groupCohomology.π S.X₃ n z)) =
    TateCohomology.δ hS n (ordinaryToTate S.X₃ n (groupCohomology.π S.X₃ n z))
  calc
    _ = ordinaryToTate S.X₁ (n + 1)
        (C.X₁.homologyπ (n + 1) (C.X₁.cyclesMk x (n + 1 + 1) (by simp) hdx)) :=
      congrArg (ordinaryToTate S.X₁ (n + 1)) hd
    _ = cycleClass T.X₁ (n + 1) x hdx := ordinaryToTate_cyclesMk S.X₁ (n + 1) x hdx
    _ = TateCohomology.δ hS n (cycleClass T.X₃ n z₀ hz₀) :=
      (delta_cycleClass hT n z₀ hz₀ y hy x hx).symm
    _ = _ := congrArg (TateCohomology.δ hS n) hzclass.symm

theorem ordinaryTateBoundaryLaws : OrdinaryTateBoundaryLaws.{u} := by
  intro R G _ _ _
  exact ⟨ordinaryToTate_cyclesMk, fun S hS n => ordinaryToTate_delta hS n⟩

end Langlands.Tate
