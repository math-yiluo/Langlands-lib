import Langlands.GroupScheme.Rational.StandardParabolic
import Mathlib.Data.Set.Finite.Lattice

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace Dynamic

variable {S : Scheme.{u}} {T : CommGroupScheme S} {G : GroupScheme S}

/-- Cocharacters through `T` whose images centralize a fixed point form an
integer submodule. Membership uses the dynamic centralizer on the full test scheme. -/
def centralizingCocharacters (i : T.toGrp ⟶ G) {U : Over S} (g : U ⟶ G.X) :
    Submodule ℤ (cocharacterLattice T) where
  carrier := {zeta | g ∈ (centralizer (CommGroupScheme.groupHom zeta ≫ i)).carrier U}
  zero_mem' := by
    simp only [Set.mem_ofPred_eq]
    rw [← torusCentralizer_gm_eq_dynamicCentralizer]
    intro V a t
    rw [Grp.comp_hom_hom, ← Category.assoc, comp_groupHom_zero, MonObj.one_comp]
    exact Commute.one_right _
  add_mem' := by
    intro zeta eta hzeta heta
    simp only [Set.mem_ofPred_eq] at hzeta heta ⊢
    rw [← torusCentralizer_gm_eq_dynamicCentralizer] at hzeta heta ⊢
    intro V a t
    rw [Grp.comp_hom_hom, ← Category.assoc, comp_groupHom_add, MonObj.mul_comp]
    exact (hzeta V a t).mul_right (heta V a t)
  smul_mem' := by
    intro m zeta hzeta
    simp only [Set.mem_ofPred_eq] at hzeta ⊢
    rw [← torusCentralizer_gm_eq_dynamicCentralizer] at hzeta ⊢
    intro V a t
    rw [Grp.comp_hom_hom, ← Category.assoc, comp_groupHom_zsmul, GrpObj.zpow_comp]
    exact (hzeta V a t).zpow_right m

@[simp] theorem mem_centralizingCocharacters (i : T.toGrp ⟶ G)
    {U : Over S} (g : U ⟶ G.X) (zeta : cocharacterLattice T) :
    zeta ∈ centralizingCocharacters i g ↔
      g ∈ (centralizer (CommGroupScheme.groupHom zeta ≫ i)).carrier U :=
  Iff.rfl

end Dynamic

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}

/-- The subgroup functor centralizing every cocharacter annihilated by the
character subset `J`. Its definition uses no chosen positivity chamber. -/
def cocharacterAnnihilatorCentralizer (i : T.toGrp ⟶ G)
    (J : Set (characterLattice T)) : SubgroupFunctor G where
  carrier U := ⨅ (zeta : cocharacterLattice T)
    (_ : ∀ α ∈ J, latticePairing T α zeta = 0),
    (Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ i)).carrier U
  comp_mem a _ hx := by
    simp only [Subgroup.mem_iInf] at hx ⊢
    intro zeta hzeta
    exact (Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ i)).comp_mem a
      (hx zeta hzeta)

theorem mem_cocharacterAnnihilatorCentralizer (i : T.toGrp ⟶ G)
    (J : Set (characterLattice T)) {U : Over (Spec (CommRingCat.of k))}
    {g : U ⟶ G.X} :
    g ∈ (cocharacterAnnihilatorCentralizer i J).carrier U ↔
      ∀ zeta, (∀ α ∈ J, latticePairing T α zeta = 0) →
        g ∈ (Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ i)).carrier U := by
  simp only [cocharacterAnnihilatorCentralizer, Subgroup.mem_iInf]

section Standard

variable [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

/-- Given finitely many simple roots and one standard cocharacter, a sufficiently
large positive multiple of it moves every annihilating cocharacter into the
same standard face. -/
theorem IsStandardCocharacter.exists_add_zsmul
    (hfinite : (simpleRelativeRoots i ν).Finite)
    {J : Set (characterLattice T)} {zeta₀ : cocharacterLattice T}
    (hzeta₀ : IsStandardCocharacter i ν J zeta₀)
    (zeta : cocharacterLattice T) (hzeta : ∀ α ∈ J, latticePairing T α zeta = 0) :
    ∃ m : ℤ, IsStandardCocharacter i ν J (zeta + m • zeta₀) := by
  obtain ⟨b, hb⟩ := (hfinite.image (fun α => -latticePairing T α zeta)).bddAbove
  let m : ℤ := max b 0 + 1
  have hm : 0 ≤ m := by dsimp [m]; omega
  refine ⟨m, hzeta₀.1, ?_, ?_⟩
  · intro α hα
    simp only [map_add, map_smul, hzeta α hα, hzeta₀.2.1 α hα, smul_zero, add_zero]
  · intro α hα hαJ
    have hbound : -latticePairing T α zeta ≤ b := hb ⟨α, hα, rfl⟩
    have hpos : 0 < latticePairing T α zeta₀ := hzeta₀.2.2 α hα hαJ
    have hmul : m ≤ m * latticePairing T α zeta₀ := by
      have hle : (1 : ℤ) ≤ latticePairing T α zeta₀ := by omega
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hle hm
    simp only [map_add, map_smul, smul_eq_mul]
    dsimp [m] at hmul ⊢
    omega

/-- With finite simple roots and existence of a standard cocharacter, the
choice-free standard Levi is the centralizer of the full cocharacter
annihilator of its character subset. -/
theorem standardLevi_eq_cocharacterAnnihilatorCentralizer
    (hfinite : (simpleRelativeRoots i ν).Finite)
    (J : Set (characterLattice T))
    (hexists : ∃ zeta, IsStandardCocharacter i ν J zeta) :
    standardLevi i ν J = cocharacterAnnihilatorCentralizer i J := by
  obtain ⟨zeta₀, hzeta₀⟩ := hexists
  apply le_antisymm
  · intro U g hg
    rw [mem_standardLevi] at hg
    rw [mem_cocharacterAnnihilatorCentralizer]
    intro zeta hzeta
    obtain ⟨m, hm⟩ := hzeta₀.exists_add_zsmul i ν hfinite zeta hzeta
    have hzero : zeta₀ ∈ Dynamic.centralizingCocharacters i g :=
      hg zeta₀ hzeta₀
    have hsum : zeta + m • zeta₀ ∈ Dynamic.centralizingCocharacters i g :=
      hg _ hm
    have hsub := (Dynamic.centralizingCocharacters i g).sub_mem hsum
      ((Dynamic.centralizingCocharacters i g).smul_mem m hzero)
    simpa only [add_sub_cancel_right, Dynamic.mem_centralizingCocharacters] using hsub
  · intro U g hg
    rw [mem_cocharacterAnnihilatorCentralizer] at hg
    rw [mem_standardLevi]
    intro zeta hzeta
    exact hg zeta hzeta.2.1

end Standard

end Langlands.GroupScheme
