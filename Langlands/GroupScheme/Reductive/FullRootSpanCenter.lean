import Langlands.GroupScheme.Reductive.SplitSemisimplicity

/-! # Trivial full centre from integral generation by roots -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- If actual roots of a split maximal torus generate its full integral
character lattice, the full scheme-theoretic centre is trivial. -/
theorem center_eq_bot_of_full_rootSpan {K : Type u} [Field K]
    {G : GroupScheme (Spec (CommRingCat.of K))} (hG : IsConnectedReductive G)
    {T : CommGroupScheme (Spec (CommRingCat.of K))} (hT : IsSplitTorus T.toGrp)
    (i : T.toGrp ⟶ G) (hi : IsMaximalTorus i)
    {J : Type u} (P : RootDatum J (characterLattice T) (cocharacterLattice T))
    (hP : letI := hG.isAffineHom; IsRootDatumOf i P) (hspan : P.rootSpan ℤ = ⊤) :
    center G = ⊥ := by
  have := hG.isAffineHom
  have := hG.smooth
  obtain ⟨Z, z, hz⟩ := schemeTheoreticCenterExistence K G hG
  have hself := maximalTorusCentralizer K G hG T i hi
  have : IsClosedImmersion i.hom.hom.left := hi.2.1
  have hri : (SubgroupFunctor.range i).IsRepresentedBy i := ⟨Over.mono_of_mono_left _, rfl⟩
  have hle : SubgroupFunctor.range z ≤ SubgroupFunctor.range i := by
    rw [← hself, hz.2]
    intro U g hg V a t
    exact hg V a (t ≫ i.hom.hom)
  let w := hri.liftOfLE z hle
  have hw : w ≫ i = z := hri.liftOfLE_comp z hle
  have hc : IsCentral (w ≫ i) := by
    rw [hw]
    exact hz.isCentral
  have : IsClosedImmersion z.hom.hom.left := hz.1
  have : IsAffineHom Z.X.hom := by
    rw [← Over.w z.hom.hom]
    infer_instance
  have : IsAffine Z.X.left := isAffine_of_isAffineHom Z.X.hom
  let φ := characterLattice.pointCharacters T Z.X w.hom.hom
  have hroot : ∀ j, φ (.ofAdd (P.root j)) = 1 := by
    intro j
    have hα : P.root j ∈ roots i := hP.2.1 ▸ ⟨j, rfl⟩
    have h := pointCharacters_root_eq_one_of_isCentral i w hc Z.X (𝟙 _) hα
    rwa [Category.id_comp] at h
  let f : characterLattice T →ₗ[ℤ] Additive (Γ(Z.X.left, ⊤))ˣ :=
    (MonoidHom.toAdditiveRight φ).toIntLinearMap
  have hker : P.rootSpan ℤ ≤ LinearMap.ker f := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    change Additive.ofMul (φ (.ofAdd (P.root j))) = 0
    rw [hroot j]
    rfl
  rw [hspan] at hker
  have hf : f = 0 := LinearMap.ker_eq_top.mp (top_unique hker)
  have hwone : w.hom.hom = 1 := by
    apply (characterLattice.pointCharactersEquiv T hT Z.X).injective
    rw [_root_.map_one]
    apply MonoidHom.ext
    intro χ
    have h := LinearMap.congr_fun hf χ.toAdd
    exact h
  have hz1 : z.hom.hom = 1 := by
    rw [← hw, Grp.comp_hom_hom, hwone, MonObj.one_comp]
  apply SubgroupFunctor.ext
  intro U
  apply bot_unique
  intro x hx
  rw [← hz.2] at hx
  obtain ⟨a, rfl⟩ := hx
  change a ≫ z.hom.hom = 1
  rw [hz1, MonObj.comp_one]

end Langlands.GroupScheme
