import Langlands.Cohomology.Tate.Coinduced
import Langlands.Cohomology.Tate.BoundaryDiagrams

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Tate

set_option backward.isDefEq.respectTransparency false

variable {R G : Type u} [CommRing R] [Group G] [Fintype G]

/-- An invariant vector is a cycle at the actual Tate splice. -/
lemma invariant_tate_cycle (A : Rep.{u} R G) (a : A.ρ.invariants) :
    (tateComplex A).d 0 1 ((groupCohomology.cochainsIso₀ A).inv a) = 0 := by
  have h := ConcreteCategory.congr_hom (groupCohomology.eq_d₀₁_comp_inv A) (a : A)
  have hz := ConcreteCategory.congr_hom (groupCohomology.subtype_comp_d₀₁ A) a
  change groupCohomology.d₀₁ A a = 0 at hz
  exact h.trans (by
    change (groupCohomology.cochainsIso₁ A).inv (groupCohomology.d₀₁ A a) = 0
    rw [hz, map_zero])

/-- The invariant-to-quotient class is the class of the actual degree-zero cochain. -/
lemma zeroClass_eq_cycleClass (A : Rep.{u} R G) (a : A.ρ.invariants) :
    zeroClass A a =
      cycleClass (tateComplex A) 0 ((groupCohomology.cochainsIso₀ A).inv a)
        (invariant_tate_cycle A a) := by
  let z : ModuleCat.of R A.ρ.invariants ⟶ (tateComplex A).cycles 0 :=
    (zeroHomologyData A).cyclesIso.inv ≫
      (ShortComplex.cyclesMapIso (zeroShortComplexIso A)).inv
  have hπ : ModuleCat.ofHom (zeroClass A) = z ≫ (tateComplex A).homologyπ 0 := by
    change (zeroHomologyData A).π ≫ (zeroHomologyData A).homologyIso.inv ≫
      ShortComplex.homologyMap (zeroShortComplexIso A).inv = _
    rw [← Category.assoc, (zeroHomologyData A).π_comp_homologyIso_inv,
      Category.assoc, ShortComplex.homologyπ_naturality]
    rfl
  have hi : z ≫ (tateComplex A).iCycles 0 =
      ModuleCat.ofHom A.ρ.invariants.subtype ≫ (groupCohomology.cochainsIso₀ A).inv := by
    change ((zeroHomologyData A).cyclesIso.inv ≫
      ShortComplex.cyclesMap (zeroShortComplexIso A).inv) ≫
      ((tateComplex A).sc 0).iCycles = _
    calc
      _ = (zeroHomologyData A).cyclesIso.inv ≫
          (zeroShortComplex A).iCycles ≫ (zeroShortComplexIso A).inv.τ₂ := by
        rw [Category.assoc, ShortComplex.cyclesMap_i]
      _ = _ := by
        rw [(zeroHomologyData A).cyclesIso_inv_comp_iCycles_assoc]
        rfl
  refine (ConcreteCategory.congr_hom hπ a).trans ?_
  apply congrArg ((tateComplex A).homologyπ 0)
  apply (ModuleCat.mono_iff_injective ((tateComplex A).iCycles 0)).mp inferInstance
  calc
    _ = (groupCohomology.cochainsIso₀ A).inv a := ConcreteCategory.congr_hom hi a
    _ = _ := by
      symm
      exact (tateComplex A).i_cyclesMk (i := 0)
        ((groupCohomology.cochainsIso₀ A).inv a) 1 (by simp) (invariant_tate_cycle A a)

/-- A norm-zero vector is a cycle in degree minus one of the actual Tate complex. -/
lemma normZero_tate_cycle (A : Rep.{u} R G) (a : A) (ha : A.ρ.norm a = 0) :
    (tateComplex A).d (-1) 0 ((groupHomology.chainsIso₀ A).inv a) = 0 := by
  change A.tateNorm ((groupHomology.chainsIso₀ A).inv a) = 0
  simp [Rep.tateNorm, ha]

/-- The actual Tate class of a norm-zero coefficient vector in degree minus one. -/
def minusOneClass (A : Rep.{u} R G) (a : A) (ha : A.ρ.norm a = 0) :
    tateCohomology A (-1) :=
  cycleClass (tateComplex A) (-1) ((groupHomology.chainsIso₀ A).inv a)
    (normZero_tate_cycle A a ha)

/-- Every degree-minus-one class has an actual norm-kernel representative. -/
lemma minusOneClass_surjective (A : Rep.{u} R G) (x : tateCohomology A (-1)) :
    ∃ (a : A) (ha : A.ρ.norm a = 0), minusOneClass A a ha = x := by
  obtain ⟨z, hz, rfl⟩ := cycleClass_surjective (tateComplex A) (-1) x
  let a := (groupHomology.chainsIso₀ A).hom z
  have ha : A.ρ.norm a = 0 := by
    change A.tateNorm z = 0 at hz
    have hh := congrArg (groupCohomology.cochainsIso₀ A).hom hz
    simp only [Rep.tateNorm, ConcreteCategory.comp_apply, Iso.inv_hom_id_apply, map_zero] at hh
    exact hh
  refine ⟨a, ha, ?_⟩
  have hrep : (groupHomology.chainsIso₀ A).inv a = z :=
    (groupHomology.chainsIso₀ A).hom_inv_id_apply z
  dsimp only [minusOneClass]
  congr 1

/-- At the splice, the actual connecting map takes a lifted vector to the norm of its lift. -/
lemma delta_minusOneClass {S : ShortComplex (Rep.{u} R G)} (hS : S.ShortExact)
    (a : S.X₃) (ha : S.X₃.ρ.norm a = 0) (b : S.X₂) (hb : S.g.hom b = a)
    (c : S.X₁.ρ.invariants) (hc : S.f.hom c = S.X₂.ρ.norm b) :
    TateCohomology.δ hS (-1) (minusOneClass S.X₃ a ha) =
      zeroClass S.X₁ c := by
  have hy : (tateComplex.map S.g).f (-1) ((groupHomology.chainsIso₀ S.X₂).inv b) =
      (groupHomology.chainsIso₀ S.X₃).inv a := by
    apply (groupHomology.chainsIso₀ S.X₃).toLinearEquiv.injective
    change (groupHomology.chainsIso₀ S.X₃).hom
      ((groupHomology.chainsMap (MonoidHom.id G) S.g).f 0
        ((groupHomology.chainsIso₀ S.X₂).inv b)) =
      (groupHomology.chainsIso₀ S.X₃).hom ((groupHomology.chainsIso₀ S.X₃).inv a)
    rw [Iso.inv_hom_id_apply]
    have hh := ConcreteCategory.congr_hom
      (groupHomology.chainsMap_f_0_comp_chainsIso₀ (MonoidHom.id G) S.g)
      ((groupHomology.chainsIso₀ S.X₂).inv b)
    simp only [ConcreteCategory.comp_apply, Iso.inv_hom_id_apply] at hh
    exact hh.trans hb
  have hx : (tateComplex.map S.f).f 0 ((groupCohomology.cochainsIso₀ S.X₁).inv c) =
      (tateComplex S.X₂).d (-1) 0 ((groupHomology.chainsIso₀ S.X₂).inv b) := by
    apply (groupCohomology.cochainsIso₀ S.X₂).toLinearEquiv.injective
    change (groupCohomology.cochainsIso₀ S.X₂).hom
      ((groupCohomology.cochainsMap (MonoidHom.id G) S.f).f 0
        ((groupCohomology.cochainsIso₀ S.X₁).inv c)) =
      (groupCohomology.cochainsIso₀ S.X₂).hom
        (S.X₂.tateNorm ((groupHomology.chainsIso₀ S.X₂).inv b))
    simp only [Rep.tateNorm, ConcreteCategory.comp_apply, Iso.inv_hom_id_apply]
    have hh := ConcreteCategory.congr_hom
      (groupCohomology.cochainsMap_f_0_comp_cochainsIso₀ (MonoidHom.id G) S.f)
      ((groupCohomology.cochainsIso₀ S.X₁).inv c)
    simp only [ConcreteCategory.comp_apply, Iso.inv_hom_id_apply] at hh
    exact hh.trans hc
  exact (delta_cycleClass (TateCohomology.map_tateComplexFunctor_shortExact hS)
    (-1) ((groupHomology.chainsIso₀ S.X₃).inv a) (normZero_tate_cycle S.X₃ a ha)
    ((groupHomology.chainsIso₀ S.X₂).inv b) hy
    ((groupCohomology.cochainsIso₀ S.X₁).inv c) hx).trans
      (zeroClass_eq_cycleClass S.X₁ c).symm

end Langlands.Tate
