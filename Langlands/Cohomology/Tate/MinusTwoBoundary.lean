import Langlands.Cohomology.Tate.SpliceRepresentatives
import Langlands.Cohomology.Tate.LowDegree

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Tate

set_option backward.isDefEq.respectTransparency false

variable {R G : Type u} [CommRing R] [Group G] [Fintype G]

/-- Ordinary first-homology cycles mapped to the cycles of the actual Tate
complex in degree minus two. -/
def homologyOneTateCycles (A : Rep.{u} R G) :
    (groupHomology.inhomogeneousChains A).cycles 1 ⟶ (tateComplex A).cycles (-2) :=
  HomologicalComplex.cyclesMap (tateComplexConnectData A).restrictionLEIso.inv 1 ≫
    ((tateComplex A).restrictionCyclesIso (ComplexShape.embeddingUpIntLE (-1))
      1 0 (by simp) (show _ = (-2 : ℤ) by rfl) (show _ = (-1 : ℤ) by rfl)
      (by simp)).hom

lemma homologyOneToTate_π (A : Rep.{u} R G) :
    groupHomology.π A 1 ≫
        ((TateCohomology.isoGroupHomology (-2) 1 (by norm_num)).app A).inv =
      homologyOneTateCycles A ≫ (tateComplex A).homologyπ (-2) := by
  change groupHomology.π A 1 ≫
    ((tateComplexConnectData A).homologyIsoNeg 1 (-2) (by norm_num)).inv = _
  simp only [CochainComplex.ConnectData.homologyIsoNeg, Iso.trans_inv, Iso.symm_inv,
    HomologicalComplex.homologyMapIso_inv, groupHomology.π, groupHomology]
  rw [← Category.assoc, HomologicalComplex.homologyπ_naturality,
    Category.assoc, HomologicalComplex.homologyπ_restrictionHomologyIso_hom]
  rfl

lemma homologyOneTateCycles_iCycles (A : Rep.{u} R G) :
    homologyOneTateCycles A ≫ (tateComplex A).iCycles (-2) =
      (groupHomology.inhomogeneousChains A).iCycles 1 := by
  simp [homologyOneTateCycles, CochainComplex.ConnectData.restrictionLEIso,
    HomologicalComplex.restrictionXIso]
  exact Category.comp_id _

/-- A single one-chain is a cycle in the actual Tate complex when coefficients
are trivial. -/
lemma single_tate_cycle (A : Rep.{u} R G) [A.IsTrivial] (g : G) (a : A) :
    (tateComplex A).d (-2) (-1)
      ((groupHomology.chainsIso₁ A).inv (Finsupp.single g a)) = 0 := by
  change (groupHomology.inhomogeneousChains A).d 1 0
    ((groupHomology.chainsIso₁ A).inv (Finsupp.single g a)) = 0
  have h := ConcreteCategory.congr_hom (groupHomology.eq_d₁₀_comp_inv A)
    (Finsupp.single g a)
  change _ = (groupHomology.chainsIso₀ A).inv
    (groupHomology.d₁₀ A (Finsupp.single g a)) at h
  exact h.trans (by simp)

/-- The published degree-minus-two generator is the class of its actual
single-chain representative. -/
lemma minusTwoClass_eq_cycleClass (A : Rep.{u} R G) [A.IsTrivial] (g : G) (a : A) :
    minusTwoClass A g a =
      cycleClass (tateComplex A) (-2)
        ((groupHomology.chainsIso₁ A).inv (Finsupp.single g a))
        (single_tate_cycle A g a) := by
  let z := (groupHomology.isoCycles₁ A).inv
    ((groupHomology.cycles₁IsoOfIsTrivial A).inv (Finsupp.single g a))
  have hπ := ConcreteCategory.congr_hom (homologyOneToTate_π A) z
  change minusTwoClass A g a =
    (tateComplex A).homologyπ (-2) (homologyOneTateCycles A z) at hπ
  refine hπ.trans ?_
  apply congrArg ((tateComplex A).homologyπ (-2))
  apply (ModuleCat.mono_iff_injective ((tateComplex A).iCycles (-2))).mp inferInstance
  calc
    _ = (groupHomology.inhomogeneousChains A).iCycles 1 z :=
      ConcreteCategory.congr_hom (homologyOneTateCycles_iCycles A) z
    _ = (groupHomology.chainsIso₁ A).inv (Finsupp.single g a) :=
      groupHomology.isoCycles₁_inv_comp_iCycles_apply A _
    _ = _ := by
      symm
      exact (tateComplex A).i_cyclesMk (i := (-2 : ℤ))
        ((groupHomology.chainsIso₁ A).inv (Finsupp.single g a))
        (-2 + 1) (by simp) (by simpa using single_tate_cycle A g a)

/-- The actual degree-minus-two connecting map takes a lifted single chain to
the inverse-action difference of its coefficient lift. -/
lemma delta_minusTwoClass {S : ShortComplex (Rep.{u} R G)} (hS : S.ShortExact)
    [S.X₃.IsTrivial] (g : G) (a : S.X₃) (b : S.X₂) (hb : S.g.hom b = a)
    (c : S.X₁) (hc0 : S.X₁.ρ.norm c = 0)
    (hc : S.f.hom c = S.X₂.ρ g⁻¹ b - b) :
    TateCohomology.δ hS (-2) (minusTwoClass S.X₃ g a) =
      minusOneClass S.X₁ c hc0 := by
  have hy : (tateComplex.map S.g).f (-2)
      ((groupHomology.chainsIso₁ S.X₂).inv (Finsupp.single g b)) =
      (groupHomology.chainsIso₁ S.X₃).inv (Finsupp.single g a) := by
    apply (groupHomology.chainsIso₁ S.X₃).toLinearEquiv.injective
    change (groupHomology.chainsIso₁ S.X₃).hom
      ((groupHomology.chainsMap (MonoidHom.id G) S.g).f 1
        ((groupHomology.chainsIso₁ S.X₂).inv (Finsupp.single g b))) =
      (groupHomology.chainsIso₁ S.X₃).hom
        ((groupHomology.chainsIso₁ S.X₃).inv (Finsupp.single g a))
    rw [Iso.inv_hom_id_apply]
    have hh := ConcreteCategory.congr_hom
      (groupHomology.chainsMap_f_1_comp_chainsIso₁ (MonoidHom.id G) S.g)
      ((groupHomology.chainsIso₁ S.X₂).inv (Finsupp.single g b))
    simp only [ConcreteCategory.comp_apply, Iso.inv_hom_id_apply] at hh
    exact hh.trans (by simp [groupHomology.chainsMap₁, hb])
  have hx : (tateComplex.map S.f).f (-1)
      ((groupHomology.chainsIso₀ S.X₁).inv c) =
      (tateComplex S.X₂).d (-2) (-1)
        ((groupHomology.chainsIso₁ S.X₂).inv (Finsupp.single g b)) := by
    apply (groupHomology.chainsIso₀ S.X₂).toLinearEquiv.injective
    change (groupHomology.chainsIso₀ S.X₂).hom
      ((groupHomology.chainsMap (MonoidHom.id G) S.f).f 0
        ((groupHomology.chainsIso₀ S.X₁).inv c)) =
      (groupHomology.chainsIso₀ S.X₂).hom
        ((groupHomology.inhomogeneousChains S.X₂).d 1 0
          ((groupHomology.chainsIso₁ S.X₂).inv (Finsupp.single g b)))
    have hh := ConcreteCategory.congr_hom
      (groupHomology.chainsMap_f_0_comp_chainsIso₀ (MonoidHom.id G) S.f)
      ((groupHomology.chainsIso₀ S.X₁).inv c)
    simp only [ConcreteCategory.comp_apply, Iso.inv_hom_id_apply] at hh
    have hd := ConcreteCategory.congr_hom (groupHomology.eq_d₁₀_comp_inv S.X₂)
      (Finsupp.single g b)
    change (groupHomology.inhomogeneousChains S.X₂).d 1 0
      ((groupHomology.chainsIso₁ S.X₂).inv (Finsupp.single g b)) =
      (groupHomology.chainsIso₀ S.X₂).inv
      (groupHomology.d₁₀ S.X₂ (Finsupp.single g b)) at hd
    rw [hd, Iso.inv_hom_id_apply]
    refine hh.trans ?_
    change S.f.hom c = groupHomology.d₁₀ S.X₂ (Finsupp.single g b)
    rw [groupHomology.d₁₀_single]
    exact hc
  rw [minusTwoClass_eq_cycleClass]
  exact delta_cycleClass (TateCohomology.map_tateComplexFunctor_shortExact hS)
    (-2) ((groupHomology.chainsIso₁ S.X₃).inv (Finsupp.single g a))
    (by
      change (tateComplex S.X₃).d (-2) (-1)
        ((groupHomology.chainsIso₁ S.X₃).inv (Finsupp.single g a)) = 0
      exact single_tate_cycle S.X₃ g a)
    ((groupHomology.chainsIso₁ S.X₂).inv (Finsupp.single g b)) hy
    ((groupHomology.chainsIso₀ S.X₁).inv c) hx

end Langlands.Tate
