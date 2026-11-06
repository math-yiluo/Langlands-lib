import Langlands.GroupScheme.Rational.CentralizerRootSupport
import Langlands.GroupScheme.Rational.CompatibleTorusCocharacter
import Langlands.GroupScheme.Dynamic.CommonTorusIntersectionDeterminants

/-! # Opposite-radical intersections inside a dominant dynamic radical -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}

section Admissible

variable [IsAffineHom G.X.hom]

/-- A cocharacter `mu` is admissible for the pair `(zeta, eta)` when it pairs
nonnegatively with every actual relative root that is negative on `zeta` and
positive on `eta`, that is, with every root of `U(-zeta) ∩ U(eta)`. -/
def IsOppositeIntersectionAdmissible (i : T.toGrp ⟶ G)
    (zeta eta mu : cocharacterLattice T) : Prop :=
  ∀ α ∈ relativeRoots i, latticePairing T α zeta < 0 →
    0 < latticePairing T α eta → 0 ≤ latticePairing T α mu

end Admissible

section ZeroRoots

variable [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

/-- If the centralizer of `eta` lies in the centralizer of `zeta`, every actual
relative root orthogonal to `eta` is orthogonal to `zeta`. -/
theorem relativeRoot_pairing_eq_zero_of_centralizer_le
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G) (zeta eta : cocharacterLattice T)
    (hle : Dynamic.centralizer (CommGroupScheme.groupHom eta ≫ i) ≤
      Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ i))
    {α : characterLattice T} (hα : α ∈ relativeRoots i)
    (h0 : latticePairing T α eta = 0) :
    latticePairing T α zeta = 0 := by
  by_contra hne
  have h1 := weightSpace_inf_tangentSubmodule_centralizer hT i eta α
  have h2 := weightSpace_inf_tangentSubmodule_centralizer hT i zeta α
  simp only [h0, ↓reduceIte] at h1
  simp only [hne, ↓reduceIte] at h2
  have hsub : weightSpace i α ≤ weightSpace i α ⊓ RelativeRoot.tangentSubmodule
      (Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ i)) := by
    conv_lhs => rw [← h1]
    exact inf_le_inf_left _ (RelativeRoot.tangentSubmodule_mono hle)
  rw [h2] at hsub
  exact (mem_relativeRoots.1 hα).2 (le_bot_iff.1 hsub)

end ZeroRoots

section Inclusions

variable [IsAffineHom G.X.hom] [Smooth G.X.hom]

/-- Root-sign criterion for an opposite-radical intersection. Suppose the
centralizer of `eta` lies in that of `zeta`, and `theta` is positive on every
actual root that is negative on `zeta` and positive on `eta`. Then
`U(-zeta) ∩ U(eta) ≤ U(theta)` on every test scheme. The proof applies the
smooth root-sign radical criterion inside the dynamic parabolic `P(eta)`. -/
theorem unipotent_neg_inf_unipotent_le
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G)
    (zeta eta theta : cocharacterLattice T)
    (hle : Dynamic.centralizer (CommGroupScheme.groupHom eta ≫ i) ≤
      Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ i))
    (hroot : ∀ α ∈ relativeRoots i, latticePairing T α zeta < 0 →
      0 < latticePairing T α eta → 0 < latticePairing T α theta) :
    Dynamic.unipotent (CommGroupScheme.groupHom (-zeta) ≫ i) ⊓
        Dynamic.unipotent (CommGroupScheme.groupHom eta ≫ i) ≤
      Dynamic.unipotent (CommGroupScheme.groupHom theta ≫ i) := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let H := Dynamic.Affine.parabolicScheme (CommGroupScheme.groupHom eta ≫ i)
  let j : H ⟶ G := Dynamic.Affine.parabolicHom (CommGroupScheme.groupHom eta ≫ i)
  have hj : (Dynamic.parabolic (CommGroupScheme.groupHom eta ≫ i)).IsRepresentedBy j :=
    Dynamic.Affine.isRepresentedBy_parabolicHom _
  have hjc : IsClosedSubgroup j := Dynamic.Affine.isClosedSubgroup_parabolicHom _
  have : IsClosedImmersion j.hom.hom.left := hjc
  have : Mono j.hom.hom := hj.1
  have : Smooth H.X.hom := (dynamicSmooth k G _ H j).1 hj
  have : IsAffineHom H.X.hom := by
    rw [← Over.w j.hom.hom]
    infer_instance
  have ht : SubgroupFunctor.range i ≤
      Dynamic.parabolic (CommGroupScheme.groupHom eta ≫ i) :=
    (range_le_centralizer_groupHom_comp i eta).trans (Dynamic.centralizer_le_parabolic _)
  let iH : T.toGrp ⟶ H := hj.factorHom i ht
  have hcomp : iH ≫ j = i := hj.factorHom_comp i ht
  have hrestrict (c : cocharacterLattice T) :
      Dynamic.unipotent (CommGroupScheme.groupHom c ≫ iH) =
        (Dynamic.unipotent (CommGroupScheme.groupHom c ≫ i)).comap j := by
    rw [Dynamic.unipotent_eq_comap_of_isClosedSubgroup _ j hjc, Category.assoc, hcomp]
  have htop : Dynamic.parabolic (CommGroupScheme.groupHom eta ≫ iH) = ⊤ := by
    rw [Dynamic.parabolic_eq_comap_of_isClosedSubgroup _ j hjc, Category.assoc, hcomp]
    exact SubgroupFunctor.range_le_iff_comap_eq_top.1 hj.2.le
  have hnonneg : ∀ α ∈ relativeRoots iH, 0 ≤ latticePairing T α eta := by
    intro α hα
    refine RelativeRoot.nonnegative_rootSupport_of_parabolic_le hT iH 0 eta ?_ α hα ?_
    · intro U g _
      rw [htop]
      exact Subgroup.mem_top _
    · rw [map_zero]
  have hH : Dynamic.unipotent (CommGroupScheme.groupHom (-zeta) ≫ iH) ≤
      Dynamic.unipotent (CommGroupScheme.groupHom theta ≫ iH) := by
    refine (rootSignUnipotentInclusions k H T hT iH (-zeta) theta).2 ?_
    intro α hα hpos
    have hαG := relativeRoots_subset_of_factor hj iH hcomp hα
    have hneg : latticePairing T α zeta < 0 := by
      rw [map_neg] at hpos
      omega
    have heta : 0 < latticePairing T α eta := by
      refine (hnonneg α hα).lt_of_ne fun h0 => ?_
      have := relativeRoot_pairing_eq_zero_of_centralizer_le hT i zeta eta hle hαG h0.symm
      omega
    exact hroot α hαG hneg heta
  intro U g hg
  have hgP : g ∈ (Dynamic.parabolic (CommGroupScheme.groupHom eta ≫ i)).carrier U :=
    Dynamic.unipotent_le_parabolic _ U hg.2
  rw [← hj.2] at hgP
  obtain ⟨x, rfl⟩ := SubgroupFunctor.mem_range.1 hgP
  have hx : x ∈ (Dynamic.unipotent (CommGroupScheme.groupHom (-zeta) ≫ iH)).carrier U := by
    rw [hrestrict, SubgroupFunctor.mem_comap]
    exact hg.1
  have hx' := hH U hx
  rw [hrestrict, SubgroupFunctor.mem_comap] at hx'
  exact hx'

end Inclusions

section Dominance

variable [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

/-- Dominance of large multiples: for large `n`, the dynamic subgroups of
`n • mu - zeta` compare with those of `mu` as `P(n • mu - zeta) ≤ P(mu)`,
`U(mu) ≤ U(n • mu - zeta)` and `Z(n • mu - zeta) ≤ Z(mu)`. -/
theorem exists_dominant_nsmul_sub (i : T.toGrp ⟶ G) (zeta mu : cocharacterLattice T) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Dynamic.parabolic (CommGroupScheme.groupHom ((n : ℤ) • mu - zeta) ≫ i) ≤
          Dynamic.parabolic (CommGroupScheme.groupHom mu ≫ i) ∧
        Dynamic.unipotent (CommGroupScheme.groupHom mu ≫ i) ≤
          Dynamic.unipotent (CommGroupScheme.groupHom ((n : ℤ) • mu - zeta) ≫ i) ∧
        Dynamic.centralizer (CommGroupScheme.groupHom ((n : ℤ) • mu - zeta) ≫ i) ≤
          Dynamic.centralizer (CommGroupScheme.groupHom mu ≫ i) := by
  let χ := CommGroupScheme.groupHom mu ≫ i
  let θ := CommGroupScheme.groupHom (-zeta) ≫ i
  have hθ : SubgroupFunctor.range θ ≤ Dynamic.centralizer χ :=
    (SubgroupFunctor.range_comp_le _ i).trans (range_le_centralizer_groupHom_comp i mu)
  obtain ⟨N, hN⟩ := Dynamic.exists_dominant_inclusions χ θ hθ
  refine ⟨N, fun n hn => hN (n : ℤ) (by exact_mod_cast hn) _ fun U t => ?_⟩
  simp only [χ, θ, Grp.comp_hom_hom, ← Category.assoc, sub_eq_add_neg,
    comp_groupHom_add, comp_groupHom_zsmul, MonObj.mul_comp, GrpObj.zpow_comp]

end Dominance

section Combined

variable [IsAffineHom G.X.hom] [Smooth G.X.hom]

/-- For an admissible `mu`, every large multiple gives a single dynamic radical
`U(n • mu - zeta)` containing `U(-zeta) ∩ U(eta)` whose parabolic lies in
`P(mu)`; the centralizer hypothesis compares `Z(eta)` with `Z(zeta)`. -/
theorem exists_unipotent_inf_le_and_parabolic_le
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G) (zeta eta mu : cocharacterLattice T)
    (hle : Dynamic.centralizer (CommGroupScheme.groupHom eta ≫ i) ≤
      Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ i))
    (hadm : IsOppositeIntersectionAdmissible i zeta eta mu) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Dynamic.unipotent (CommGroupScheme.groupHom (-zeta) ≫ i) ⊓
          Dynamic.unipotent (CommGroupScheme.groupHom eta ≫ i) ≤
        Dynamic.unipotent (CommGroupScheme.groupHom ((n : ℤ) • mu - zeta) ≫ i) ∧
      Dynamic.parabolic (CommGroupScheme.groupHom ((n : ℤ) • mu - zeta) ≫ i) ≤
          Dynamic.parabolic (CommGroupScheme.groupHom mu ≫ i) ∧
        Dynamic.unipotent (CommGroupScheme.groupHom mu ≫ i) ≤
          Dynamic.unipotent (CommGroupScheme.groupHom ((n : ℤ) • mu - zeta) ≫ i) ∧
        Dynamic.centralizer (CommGroupScheme.groupHom ((n : ℤ) • mu - zeta) ≫ i) ≤
          Dynamic.centralizer (CommGroupScheme.groupHom mu ≫ i) := by
  obtain ⟨N, hN⟩ := exists_dominant_nsmul_sub i zeta mu
  refine ⟨N, fun n hn => ⟨?_, hN n hn⟩⟩
  refine unipotent_neg_inf_unipotent_le hT i zeta eta _ hle fun α hα hneg hpos => ?_
  have hmu := hadm α hα hneg hpos
  rw [map_sub, map_zsmul, smul_eq_mul]
  linarith [mul_nonneg (Int.natCast_nonneg n) hmu]

end Combined

end Langlands.GroupScheme
