import Langlands.GroupScheme.Rational.CocharacterCentralizers
import Langlands.GroupScheme.Rational.GenericLieWeights
import Langlands.GroupScheme.Rational.Statement
import Langlands.GroupScheme.RepresentedSubgroup
import Langlands.GroupScheme.Rational.LeviFactorization
import Langlands.GroupScheme.Dynamic.ParabolicLieCriterion
import Langlands.GroupScheme.Dynamic.AffineRepresentability
import Langlands.GroupScheme.Dynamic.SmoothConnectedStatement
import Langlands.GroupScheme.Dynamic.LieStatement
import Langlands.GroupScheme.Lie.SubgroupEqualityStatement

/-! # Generic centralizers from the structure of dynamic centralizers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section Lie

variable {R : CommRingCat.{u}} {H G : GroupScheme (Spec R)} {A : Type u} [CommRing A]
  [Algebra R A]

/-- A homomorphism carries the actual Lie algebra into the actual Lie algebra. -/
theorem comp_mem_lieKernel (f : H ⟶ G) (X : lieKernel H A) :
    X.val ≫ f.hom.hom ∈ lieKernel G A := by
  change Lie.reduction G _ = 1
  have hX : Lie.reduction H X.val = 1 := X.property
  rw [Lie.reduction, Lie.affineMap_apply] at hX ⊢
  rw [← Category.assoc, hX, MonObj.one_comp]

/-- Along a monomorphism, a dual-number point whose image lies in the actual Lie algebra lies in
the actual Lie algebra. -/
theorem mem_lieKernel_of_comp_mem (f : H ⟶ G) [Mono f.hom.hom]
    {Y : Lie.AffinePoints H (DualNumber A)} (hY : Y ≫ f.hom.hom ∈ lieKernel G A) :
    Y ∈ lieKernel H A := by
  change Lie.reduction H Y = 1
  have h : Lie.reduction G (Y ≫ f.hom.hom) = 1 := hY
  rw [Lie.reduction, Lie.affineMap_apply] at h ⊢
  apply (cancel_mono f.hom.hom).mp
  rw [Category.assoc, h, MonObj.one_comp]

end Lie

namespace SubgroupFunctor

variable {S : Scheme.{u}} {K H G : GroupScheme S}

/-- A homomorphism whose points lie in a represented subgroup functor factors through the
representing group scheme. -/
theorem IsRepresentedBy.exists_comp_eq {F : SubgroupFunctor G} {j : H ⟶ G}
    (hj : F.IsRepresentedBy j) (f : K ⟶ G) (hf : range f ≤ F) : ∃ f' : K ⟶ H, f' ≫ j = f :=
  ⟨hj.factorHom f hf, hj.factorHom_comp f hf⟩

end SubgroupFunctor

section Field

variable {k : Type u} [Field k]

/-- Let `G` be a smooth connected affine group over a field and `χ`, `ψ` cocharacters of `G`
such that `ψ` lands in the dynamic centralizer of `χ`. If the weight-zero part of the actual Lie
algebra for `χ` lies in the weight-zero part for `ψ`, then the dynamic centralizer of `χ` lies in
that of `ψ`. This is conditional on the four structural statements. -/
theorem dynamicCentralizer_le_of_weightSpace_zero_le
    (hS : DynamicSmoothStatement.{u}) (hC : DynamicConnectedStatement.{u})
    (hL : DynamicLieStatement.{u}) (hE : LieSubgroupEqualityStatement.{u})
    {G : GroupScheme (Spec (CommRingCat.of k))} [Smooth G.X.hom] [IsAffineHom G.X.hom]
    [ConnectedSpace G.X.left] (χ ψ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (hψ : SubgroupFunctor.range ψ ≤ Dynamic.centralizer χ)
    (hw : weightSpace χ (Gm.powerHom _ 0) ≤ weightSpace ψ (Gm.powerHom _ 0)) :
    Dynamic.centralizer χ ≤ Dynamic.centralizer ψ := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  -- `H` represents `Z_G(χ)`.
  let H := Dynamic.Affine.centralizerScheme χ
  let j : H ⟶ G := Dynamic.Affine.centralizerHom χ
  have hj : (Dynamic.centralizer χ).IsRepresentedBy j :=
    Dynamic.Affine.isRepresentedBy_centralizerHom χ
  have : Mono j.hom.hom := hj.1
  have : IsClosedImmersion j.hom.hom.left := Dynamic.Affine.isClosedSubgroup_centralizerHom χ
  have : IsAffine H.X.left := isAffine_of_isAffineHom j.hom.hom.left
  have : Smooth H.X.hom := (hS k G χ H j).2.1 hj
  have : ConnectedSpace H.X.left := ((hC k G χ H j).2 inferInstance).2 hj
  -- `ψ` factors through `H`; `K` represents `Z_H(ψ')`.
  obtain ⟨ψ', hψ'⟩ := hj.exists_comp_eq ψ (hj.2 ▸ hψ)
  let K := Dynamic.Affine.centralizerScheme ψ'
  let jK : K ⟶ H := Dynamic.Affine.centralizerHom ψ'
  have hjK : (Dynamic.centralizer ψ').IsRepresentedBy jK :=
    Dynamic.Affine.isRepresentedBy_centralizerHom ψ'
  have : Mono jK.hom.hom := hjK.1
  have : Smooth K.X.hom := (hS k H ψ' K jK).2.1 hjK
  have htop : SubgroupFunctor.range jK = ⊤ := by
    refine hE k H K jK (Dynamic.Affine.isClosedSubgroup_centralizerHom ψ') fun X => ?_
    let XG : lieKernel G k := ⟨X.val ≫ j.hom.hom, comp_mem_lieKernel j X⟩
    have h₁ : XG.val ∈ (Dynamic.centralizer χ).carrier _ := by
      rw [← hj.2]
      exact SubgroupFunctor.mem_range.mpr ⟨X.val, rfl⟩
    have h₂ : XG.val ∈ (Dynamic.centralizer ψ).carrier _ :=
      (hL k G ψ XG).1.mpr (hw ((hL k G χ XG).1.mp h₁))
    have h₃ : X.val ∈ (Dynamic.centralizer ψ').carrier _ := by
      rw [Dynamic.centralizer_eq_comap_of_mono ψ' j, SubgroupFunctor.mem_comap, hψ']
      exact h₂
    rw [← hjK.2] at h₃
    obtain ⟨Y, hY⟩ := SubgroupFunctor.mem_range.mp h₃
    refine ⟨⟨Y, mem_lieKernel_of_comp_mem jK ?_⟩, hY⟩
    rw [hY]
    exact X.property
  intro U g hg
  rw [← hj.2] at hg
  obtain ⟨h, rfl⟩ := SubgroupFunctor.mem_range.mp hg
  have hh : h ∈ (Dynamic.centralizer ψ').carrier U := by
    rw [← hjK.2, htop]
    exact Subgroup.mem_top _
  have h' := Dynamic.centralizer_le_comap ψ' j U hh
  have h'' := SubgroupFunctor.mem_comap.mp h'
  rwa [hψ'] at h''

/-- **Generic centralizers**, conditional on the four structural statements on dynamic
subgroups and Lie algebras. -/
theorem genericCentralizerStatement_of
    (hS : DynamicSmoothStatement.{u}) (hC : DynamicConnectedStatement.{u})
    (hL : DynamicLieStatement.{u}) (hE : LieSubgroupEqualityStatement.{u}) :
    GenericCentralizerStatement.{u} := by
  intro k _ G hG T i hi ν hν
  have := hG.smooth
  have := hG.isAffineHom
  have := hG.connectedSpace
  have hT : IsSplitTorus T.toGrp := hi.isSplitSubtorus.1
  refine le_antisymm ?_ (torusCentralizer_le_dynamicCentralizer i _)
  refine le_torusCentralizer_of_le_dynamicCentralizer hT i fun c => ?_
  refine dynamicCentralizer_le_of_weightSpace_zero_le hS hC hL hE _ _ ?_ ?_
  · exact (SubgroupFunctor.range_comp_le _ i).trans
      ((range_le_torusCentralizer i).trans (torusCentralizer_le_dynamicCentralizer i _))
  · rw [map_zero, weightSpace_zero_genericCocharacter hT i ν hν]
    simpa only [Limits.comp_zero] using weightSpace_le_comp c i 0

end Field

end Langlands.GroupScheme
