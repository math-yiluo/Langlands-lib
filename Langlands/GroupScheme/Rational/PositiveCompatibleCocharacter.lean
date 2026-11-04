import Langlands.GroupScheme.Rational.CompatibleTorusCocharacter
import Langlands.GroupScheme.Absolute.RegularPerturbation

/-! # Compatible whole-torus centralizers preserving finite positivity -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
    {B : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    {I : Type v}

/-- A cocharacter retaining the whole-torus centralizer and the two dynamic
inclusions can also preserve every positive form in a supplied finite family. -/
theorem IsSplitTorus.exists_compatible_cocharacter_on_finite
    (hB : IsSplitTorus B.toGrp) (b : B.toGrp ⟶ G) (ν : cocharacterLattice B)
    (q : I → cocharacterLattice B →+ ℤ) (s : Finset I) :
    ∃ zeta : cocharacterLattice B,
      Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ b) = torusCentralizer b ∧
        Dynamic.parabolic (CommGroupScheme.groupHom zeta ≫ b) ≤
          Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ b) ∧
        Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ b) ≤
          Dynamic.unipotent (CommGroupScheme.groupHom zeta ≫ b) ∧
        ∀ a ∈ s, 0 < q a ν → 0 < q a zeta := by
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
  obtain ⟨N₀, hN₀⟩ := Dynamic.exists_dominant_inclusions χ θ hθ
  let N := max N₀ (IntegralPerturbation.bound q s τ)
  let zeta := N • ν + τ
  let ψ := CommGroupScheme.groupHom zeta ≫ b
  have hψ : ∀ (T : Over (Spec (CommRingCat.of k)))
      (t : T ⟶ (Gm (Spec (CommRingCat.of k))).X),
      t ≫ ψ.hom.hom = ((t ^ (N : ℤ)) ≫ χ.hom.hom) * (t ≫ θ.hom.hom) := by
    intro T t
    simp only [ψ, χ, θ, zeta, ← natCast_zsmul, Grp.comp_hom_hom,
      ← Category.assoc, comp_groupHom_add, comp_groupHom_zsmul, MonObj.mul_comp,
      GrpObj.zpow_comp]
  obtain ⟨hP, hU, hZ⟩ := hN₀ (N : ℤ) (by exact_mod_cast le_max_left N₀ _) ψ hψ
  refine ⟨zeta, le_antisymm ?_ (torusCentralizer_le_dynamicCentralizer b _),
    hP, hU, ?_⟩
  · intro T g hg
    have hsum : zeta ∈ Dynamic.centralizingCocharacters b g := hg
    have hν : ν ∈ Dynamic.centralizingCocharacters b g := hZ T hg
    have hτ : τ ∈ Dynamic.centralizingCocharacters b g := by
      have hsub := (Dynamic.centralizingCocharacters b g).sub_mem hsum
        ((Dynamic.centralizingCocharacters b g).smul_mem (N : ℤ) hν)
      simpa only [zeta, natCast_zsmul, add_sub_cancel_left] using hsub
    change g ∈ (Dynamic.centralizer θ).carrier T at hτ
    rw [centralizingCocharacter_spec hB b] at hτ
    exact hτ
  · intro a ha hpos
    exact (IntegralPerturbation.signs q s ν τ (le_max_right N₀ _) ha).1.mpr
      (Or.inl hpos)

/-- A chosen compatible cocharacter preserving a supplied finite family of
strictly positive integral additive forms. -/
def compatibleCentralizingCocharacterOnFinite
    (hB : IsSplitTorus B.toGrp) (b : B.toGrp ⟶ G) (ν : cocharacterLattice B)
    (q : I → cocharacterLattice B →+ ℤ) (s : Finset I) : cocharacterLattice B :=
  (hB.exists_compatible_cocharacter_on_finite b ν q s).choose

/-- The chosen finite-family refinement has the whole-torus centralizer,
the two dynamic inclusions, and preserves each originally positive form. -/
theorem compatibleCentralizingCocharacterOnFinite_spec
    (hB : IsSplitTorus B.toGrp) (b : B.toGrp ⟶ G) (ν : cocharacterLattice B)
    (q : I → cocharacterLattice B →+ ℤ) (s : Finset I) :
    let zeta := compatibleCentralizingCocharacterOnFinite hB b ν q s
    Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ b) = torusCentralizer b ∧
      Dynamic.parabolic (CommGroupScheme.groupHom zeta ≫ b) ≤
        Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ b) ∧
      Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ b) ≤
        Dynamic.unipotent (CommGroupScheme.groupHom zeta ≫ b) ∧
      ∀ a ∈ s, 0 < q a ν → 0 < q a zeta :=
  (hB.exists_compatible_cocharacter_on_finite b ν q s).choose_spec

end Langlands.GroupScheme
