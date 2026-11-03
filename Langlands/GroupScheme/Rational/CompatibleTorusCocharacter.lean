import Langlands.GroupScheme.Rational.GenericTorusCocharacter
import Langlands.GroupScheme.Rational.StandardLeviAnnihilator
import Langlands.GroupScheme.Rational.LeviFactorization
import Langlands.GroupScheme.Dynamic.DominantCombinationInclusions

/-! # A whole-torus centralizing cocharacter compatible with a given cocharacter -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
    {B : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

/-- A cocharacter of a split torus can retain the whole-torus centralizer while
refining the dynamic parabolic and enlarging the dynamic unipotent of a given
cocharacter of the same torus. -/
theorem IsSplitTorus.exists_compatible_cocharacter (hB : IsSplitTorus B.toGrp)
    (b : B.toGrp ⟶ G) (ν : cocharacterLattice B) :
    ∃ zeta : cocharacterLattice B,
      Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ b) = torusCentralizer b ∧
        Dynamic.parabolic (CommGroupScheme.groupHom zeta ≫ b) ≤
          Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ b) ∧
        Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ b) ≤
          Dynamic.unipotent (CommGroupScheme.groupHom zeta ≫ b) := by
  let τ := centralizingCocharacter hB b
  let χ := CommGroupScheme.groupHom ν ≫ b
  let θ := CommGroupScheme.groupHom τ ≫ b
  have hθ : SubgroupFunctor.range θ ≤ Dynamic.centralizer χ := by
    intro T g hg
    apply torusCentralizer_le_dynamicCentralizer b (CommGroupScheme.groupHom ν) T
    apply range_le_torusCentralizer b T
    obtain ⟨t, rfl⟩ := SubgroupFunctor.mem_range.mp hg
    exact SubgroupFunctor.mem_range.mpr
      ⟨t ≫ (CommGroupScheme.groupHom τ).hom.hom, by
        simp only [θ, Grp.comp_hom_hom, Category.assoc]⟩
  obtain ⟨N, hN⟩ := Dynamic.exists_dominant_inclusions χ θ hθ
  let zeta := (N : ℤ) • ν + τ
  let ψ := CommGroupScheme.groupHom zeta ≫ b
  have hψ : ∀ (T : Over (Spec (CommRingCat.of k)))
      (t : T ⟶ (Gm (Spec (CommRingCat.of k))).X),
      t ≫ ψ.hom.hom = ((t ^ (N : ℤ)) ≫ χ.hom.hom) * (t ≫ θ.hom.hom) := by
    intro T t
    simp only [ψ, χ, θ, zeta, Grp.comp_hom_hom, ← Category.assoc,
      comp_groupHom_add, comp_groupHom_zsmul, MonObj.mul_comp, GrpObj.zpow_comp]
  obtain ⟨hP, hU, hZ⟩ := hN (N : ℤ) le_rfl ψ hψ
  refine ⟨zeta, le_antisymm ?_ (torusCentralizer_le_dynamicCentralizer b _), hP, hU⟩
  intro T g hg
  have hsum : zeta ∈ Dynamic.centralizingCocharacters b g := hg
  have hν : ν ∈ Dynamic.centralizingCocharacters b g := hZ T hg
  have hτ : τ ∈ Dynamic.centralizingCocharacters b g := by
    have hsub := (Dynamic.centralizingCocharacters b g).sub_mem hsum
      ((Dynamic.centralizingCocharacters b g).smul_mem (N : ℤ) hν)
    simpa only [zeta, add_sub_cancel_left] using hsub
  change g ∈ (Dynamic.centralizer θ).carrier T at hτ
  rw [centralizingCocharacter_spec hB b] at hτ
  exact hτ

/-- A chosen whole-torus centralizing cocharacter compatible with `ν`. -/
def compatibleCentralizingCocharacter (hB : IsSplitTorus B.toGrp)
    (b : B.toGrp ⟶ G) (ν : cocharacterLattice B) : cocharacterLattice B :=
  (hB.exists_compatible_cocharacter b ν).choose

/-- The chosen cocharacter preserves the full centralizer and the two dynamic
inclusions on every test scheme. -/
theorem compatibleCentralizingCocharacter_spec (hB : IsSplitTorus B.toGrp)
    (b : B.toGrp ⟶ G) (ν : cocharacterLattice B) :
    let zeta := compatibleCentralizingCocharacter hB b ν
    Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ b) = torusCentralizer b ∧
      Dynamic.parabolic (CommGroupScheme.groupHom zeta ≫ b) ≤
        Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ b) ∧
      Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ b) ≤
        Dynamic.unipotent (CommGroupScheme.groupHom zeta ≫ b) :=
  (hB.exists_compatible_cocharacter b ν).choose_spec

end Langlands.GroupScheme
