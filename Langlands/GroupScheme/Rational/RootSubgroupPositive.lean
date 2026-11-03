import Langlands.GroupScheme.Rational.RootSubgroup
import Langlands.GroupScheme.Rational.StandardParabolic

/-! # Positive relative root subgroups lie in dynamic unipotent subgroups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace AffineLine

variable (B : Scheme.{u})

/-- The monomial endomorphism `t ↦ t^m` of the actual affine line. -/
def powerMap (m : ℕ) : scheme B ⟶ scheme B :=
  (homEquiv (scheme B)).symm (coord B ^ m)

theorem homEquiv_comp_powerMap {U : Over B} (x : U ⟶ scheme B) (m : ℕ) :
    homEquiv U (x ≫ powerMap B m) = homEquiv U x ^ m := by
  rw [homEquiv_comp, powerMap, Equiv.apply_symm_apply, map_pow]
  rfl

/-- On the unit locus the affine monomial is the corresponding power map of Gm. -/
theorem unitInclusion_comp_powerMap (m : ℕ) :
    unitInclusion B ≫ powerMap B m =
      (CommGroupScheme.groupHom (Gm.powerHom B (m : ℤ))).hom.hom ≫ unitInclusion B := by
  have hp : (CommGroupScheme.groupHom (Gm.powerHom B (m : ℤ))).hom.hom =
      (𝟙 (Gm B).X) ^ (m : ℤ) := by
    simpa only [Category.id_comp, Gm.powerHom_apply] using
      Gm.comp_zsmul_id (𝟙 (Gm B).X) (m : ℤ)
  apply hom_ext
  rw [homEquiv_comp_powerMap, homEquiv_comp_unitInclusion, hp, map_zpow,
    zpow_natCast, Units.val_pow_eq_pow_val]
  rw [unitInclusion, Equiv.apply_symm_apply]

/-- A positive affine monomial fixes the zero section. -/
theorem zeroSection_comp_powerMap {m : ℕ} (hm : 0 < m) :
    zeroSection B ≫ powerMap B m = zeroSection B := by
  apply hom_ext
  rw [homEquiv_comp_powerMap, zeroSection, Equiv.apply_symm_apply,
    zero_pow (Nat.ne_of_gt hm)]

/-- Pullback along a positive affine monomial leaves the zero value unchanged. -/
theorem evalZero_whiskerLeft_powerMap {m : ℕ} (hm : 0 < m) {U Y : Over B}
    (e : U ⊗ scheme B ⟶ Y) :
    Dynamic.evalZero (U ◁ powerMap B m ≫ e) = Dynamic.evalZero e := by
  unfold Dynamic.evalZero
  rw [← Category.assoc]
  congr 1
  ext <;> simp [Category.assoc, zeroSection_comp_powerMap B hm]

end AffineLine

namespace RelativeRoot

variable {B : Scheme.{u}} {S : CommGroupScheme B} {G : GroupScheme B}
  (i : S.toGrp ⟶ G) (a : characterLattice S)

/-- Pulling the full torus orbit back along a cocharacter gives its dynamic orbit. -/
theorem orbit_comp_cocharacter (ν : (Gm B).toGrp ⟶ S.toGrp) {U : Over B}
    (g : U ⟶ G.X) :
    U ◁ ν.hom.hom ≫ orbit i g = Dynamic.orbit (ν ≫ i) g := by
  simp only [orbit, AutomorphicAction.conjugation_act, MonObj.comp_mul,
    GrpObj.comp_inv, whiskerLeft_snd_assoc, whiskerLeft_fst_assoc,
    Dynamic.orbit, Grp.comp_hom_hom]

/-- A positive power character along a cocharacter contracts the actual root subgroup. -/
theorem subgroup_le_dynamicUnipotent_of_power
    (ν : Gm B ⟶ S) {m : ℕ} (hm : 0 < m)
    (hcomp : ν ≫ a = Gm.powerHom B (m : ℤ)) :
    subgroup i a ≤ Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i) := by
  intro U g hg
  obtain ⟨e, he, he0⟩ := hg
  refine ⟨U ◁ AffineLine.powerMap B m ≫ e, ?_, ?_⟩
  · rw [Dynamic.IsOrbitExtension]
    calc
      U ◁ AffineLine.unitInclusion B ≫ (U ◁ AffineLine.powerMap B m ≫ e) =
          U ◁ (AffineLine.unitInclusion B ≫ AffineLine.powerMap B m) ≫ e := by
            rw [whiskerLeft_comp, Category.assoc]
      _ = U ◁ ((CommGroupScheme.groupHom (ν ≫ a)).hom.hom ≫
          AffineLine.unitInclusion B) ≫ e := by
            rw [hcomp, AffineLine.unitInclusion_comp_powerMap]
      _ = U ◁ (CommGroupScheme.groupHom ν).hom.hom ≫
          (U ◁ ((CommGroupScheme.groupHom a).hom.hom ≫
            AffineLine.unitInclusion B) ≫ e) := by
              rw [← Category.assoc, ← whiskerLeft_comp]
              rfl
      _ = U ◁ (CommGroupScheme.groupHom ν).hom.hom ≫ orbit i g :=
        congrArg (U ◁ (CommGroupScheme.groupHom ν).hom.hom ≫ ·) he
      _ = Dynamic.orbit (CommGroupScheme.groupHom ν ≫ i) g :=
        orbit_comp_cocharacter i _ g
  · rw [AffineLine.evalZero_whiskerLeft_powerMap B hm, he0]

end RelativeRoot

section Field

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) {a : characterLattice T} (ν : cocharacterLattice T)

/-- A positive lattice pairing makes the actual relative root subgroup lie in
the dynamic unipotent subgroup, on all test schemes. -/
theorem RelativeRoot.subgroup_le_dynamicUnipotent
    (ha : 0 < latticePairing T a ν) :
    RelativeRoot.subgroup i a ≤
      Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i) := by
  apply RelativeRoot.subgroup_le_dynamicUnipotent_of_power i a ν
    (show 0 < (latticePairing T a ν).toNat by omega)
  change ν ≫ a = ((latticePairing T a ν).toNat : ℤ) • 𝟙 (Gm _)
  rw [Int.toNat_of_nonneg ha.le]
  exact eq_gmEndEquiv_zsmul k (ν ≫ a)

variable [IsAffineHom G.X.hom]

/-- The subgroup of each simple positive root lies in the actual minimal
standard unipotent subgroup. -/
theorem RelativeRoot.subgroup_le_standardUnipotent_empty
    (ha : a ∈ simpleRelativeRoots i ν) :
    RelativeRoot.subgroup i a ≤ standardUnipotent i ν ∅ := by
  intro U g hg
  rw [mem_standardUnipotent]
  intro ζ hζ
  exact RelativeRoot.subgroup_le_dynamicUnipotent i ζ
    (hζ.2.2 a ha (Set.notMem_empty a)) U hg

/-- In particular each simple positive root subgroup lies in the actual minimal
standard parabolic. -/
theorem RelativeRoot.subgroup_le_standardParabolic_empty
    (ha : a ∈ simpleRelativeRoots i ν) :
    RelativeRoot.subgroup i a ≤ standardParabolic i ν ∅ :=
  (RelativeRoot.subgroup_le_standardUnipotent_empty i ν ha).trans
    (standardUnipotent_le_standardParabolic i ν ∅)

end Field

end Langlands.GroupScheme
