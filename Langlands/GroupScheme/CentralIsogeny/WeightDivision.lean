import Langlands.GroupScheme.Torus.ZeroDifferential
import Langlands.GroupScheme.Rational.SplitTorusImageDominant
import Langlands.GroupScheme.Torus.WeightRestriction
import Langlands.GroupScheme.CentralIsogeny.NonzeroWeightEquivalence

/-! # Dividing split-torus actions and roots by the characteristic -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G H : GroupScheme (Spec (CommRingCat.of k))}

namespace SplitTorusImage

/-- A closed image inclusion reflects vanishing of the differential of the
factor map. -/
theorem DominantFactorization.zero_differential_factor
    {f : T.toGrp ⟶ G} (D : DominantFactorization f)
    (hf : ∀ X : lieKernel T.toGrp k, Lie.targetMap f k X = 1) :
    ∀ X : lieKernel T.toGrp k, Lie.targetMap D.factor k X = 1 := by
  have : IsClosedImmersion D.inclusion.hom.hom.left := D.isSplitSubtorus.2
  have : Mono D.inclusion.hom.hom := Over.mono_of_mono_left _
  intro X
  apply lieKernelTarget_injective D.inclusion k inferInstance
  rw [map_one]
  apply Subtype.ext
  change (X.val ≫ D.factor.hom.hom) ≫ D.inclusion.hom.hom = 1
  rw [Category.assoc, ← Grp.comp_hom_hom, D.factor_comp]
  exact congrArg Subtype.val (hf X)

end SplitTorusImage

/-- A zero-differential homomorphism from a split torus to any affine group
factors through multiplication by the nonzero characteristic on its source. -/
theorem IsSplitTorus.exists_factor_characteristic_of_zero_differential_to_group
    [IsAffineHom G.X.hom]
    (hT : IsSplitTorus T.toGrp) (p : ℕ) [CharP k p] (hp : p ≠ 0)
    (f : T.toGrp ⟶ G)
    (hf : ∀ X : lieKernel T.toGrp k, Lie.targetMap f k X = 1) :
    ∃ g : T.toGrp ⟶ G,
      f = CommGroupScheme.groupHom ((p : ℤ) • 𝟙 T) ≫ g := by
  let D := hT.dominantFactorization f
  obtain ⟨g, hg⟩ := hT.exists_factor_characteristic_of_zero_differential
    D.isSplitSubtorus.1 p hp (Additive.ofMul D.factor) (D.zero_differential_factor hf)
  refine ⟨CommGroupScheme.groupHom g ≫ D.inclusion, ?_⟩
  have hg' := congrArg CommGroupScheme.groupHom hg
  change D.factor =
    CommGroupScheme.groupHom ((p : ℤ) • 𝟙 T) ≫ CommGroupScheme.groupHom g at hg'
  calc
    f = D.factor ≫ D.inclusion := D.factor_comp.symm
    _ = (CommGroupScheme.groupHom ((p : ℤ) • 𝟙 T) ≫
        CommGroupScheme.groupHom g) ≫ D.inclusion := by rw [hg']
    _ = _ := Category.assoc _ _ _

/-- In characteristic zero, a homomorphism from a split torus to any affine
group with vanishing differential is the trivial homomorphism. -/
theorem IsSplitTorus.hom_eq_zero_of_zero_differential_to_group
    [CharZero k] [IsAffineHom G.X.hom]
    (hT : IsSplitTorus T.toGrp) (f : T.toGrp ⟶ G)
    (hf : ∀ X : lieKernel T.toGrp k, Lie.targetMap f k X = 1) : f = 0 := by
  let D := hT.dominantFactorization f
  have hz := hT.hom_eq_zero_of_zero_differential D.isSplitSubtorus.1
    (Additive.ofMul D.factor) (D.zero_differential_factor hf)
  have hz' := congrArg CommGroupScheme.groupHom hz
  change D.factor = 0 at hz'
  calc
    f = D.factor ≫ D.inclusion := D.factor_comp.symm
    _ = 0 ≫ D.inclusion := by rw [hz']
    _ = 0 := Limits.zero_comp

/-- If a central isogeny kills the tangent of a split-torus action, every
root of that action is the characteristic times a root of a divided action
on the target. -/
theorem IsCentralIsogeny.exists_divided_root
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
    [LocallyOfFiniteType G.X.hom] [LocallyOfFiniteType H.X.hom]
    (q : G ⟶ H) (hq : IsCentralIsogeny q)
    (hT : IsSplitTorus T.toGrp) (p : ℕ) [CharP k p] (hp : p ≠ 0)
    (i : T.toGrp ⟶ G)
    (hi : ∀ X : lieKernel T.toGrp k, Lie.targetMap (i ≫ q) k X = 1)
    {χ : characterLattice T} (hχ : χ ∈ roots i) :
    ∃ (j : T.toGrp ⟶ H) (ψ : characterLattice T),
      ψ ∈ roots j ∧ χ = (p : ℤ) • ψ ∧
        i ≫ q = CommGroupScheme.groupHom ((p : ℤ) • 𝟙 T) ≫ j := by
  obtain ⟨j, hj⟩ :=
    hT.exists_factor_characteristic_of_zero_differential_to_group p hp (i ≫ q) hi
  have hχ' : χ ∈ roots (i ≫ q) := by
    rw [roots_comp_eq_of_centralIsogeny q hq i hT]
    exact hχ
  rw [hj] at hχ'
  obtain ⟨_, ψ, hψ, hψχ⟩ :=
    (mem_roots_comp_iff hT hT ((p : ℤ) • 𝟙 T) j χ).mp hχ'
  simp only [Preadditive.zsmul_comp, Category.id_comp] at hψχ
  exact ⟨j, ψ, hψ, hψχ.symm, hj⟩

/-- The universe-general split-source division interface for arbitrary affine
targets, together with characteristic-zero vanishing. -/
def SplitTorusActionDivisionStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (_ : IsSplitTorus T.toGrp)
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    (f : T.toGrp ⟶ G),
    (∀ X : lieKernel T.toGrp k, Lie.targetMap f k X = 1) →
      (∀ (p : ℕ) [CharP k p], p ≠ 0 →
        ∃ g : T.toGrp ⟶ G,
          f = CommGroupScheme.groupHom ((p : ℤ) • 𝟙 T) ≫ g) ∧
      (CharZero k → f = 0)

theorem splitTorusActionDivision : SplitTorusActionDivisionStatement.{u} := by
  intro k _ T hT G _ f hf
  constructor
  · intro p _ hp
    exact hT.exists_factor_characteristic_of_zero_differential_to_group p hp f hf
  · intro hzero
    let := hzero
    exact hT.hom_eq_zero_of_zero_differential_to_group f hf

end Langlands.GroupScheme
