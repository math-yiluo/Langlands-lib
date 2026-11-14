import Langlands.GroupScheme.ZExtensionExistenceStatement
import Langlands.GroupScheme.ZExtensionPushout
import Langlands.GroupScheme.Torus.InducedEmbedding
import Langlands.GroupScheme.SimplyConnected.CommutatorCoverImage
import Langlands.GroupScheme.SimplyConnected.DerivedCoverProof
import Langlands.GroupScheme.Absolute.MaximalTorusCentralizerProof
import Langlands.GroupScheme.Torus.ExistenceProof

/-! # Existence of z-extensions over every field: proof -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

open ZExtensionPushout CommutatorCoverImage in
/-- **Existence of z-extensions** (KP Construction 11.4.1). Every connected reductive group
over a field has a z-extension: a central extension by an induced torus whose source is
connected reductive with simply connected derived group. -/
theorem zExtensionExistence : ZExtensionExistenceStatement.{u} := by
  intro k _ G hG
  classical
  -- the derived subgroup, its simply connected cover, and a central torus
  obtain ⟨D, C, d, π, h⟩ := simplyConnectedDerivedCoverExistence k G hG
  obtain ⟨R, i, hRaff, hRlft, hRt, -, hi, hsurj⟩ :=
    reductiveCentralTorusSurjectivity k G D d hG h.isDerivedSubgroup
  have hC : IsSimplyConnected C := h.isSimplyConnectedCover.isSimplyConnected
  have hCr : IsConnectedReductive C := hC.isSemisimple.isConnectedReductive
  have hRr : IsConnectedReductive R.toGrp := hRt.isConnectedReductive_of_fieldSplitting
  -- the cover `m : R × C ⟶ G`, `(r, c) ↦ i(r) · d(π(c))`
  let m := coverMultiplication (d := d) (π := π) i hi
  have hmd : m.hom.hom = (R.toGrp.X ◁ π.hom.hom) ≫ subgroupProductMap i d := by
    change subgroupMultiplication i (π ≫ d) = _
    rw [subgroupMultiplication, subgroupProductMap, MonObj.comp_mul, whiskerLeft_fst_assoc,
      whiskerLeft_snd_assoc]
    rfl
  have : Surjective π.hom.hom.left := h.isSimplyConnectedCover.isCentralIsogeny.surjective
  have : MorphismProperty.IsStableUnderComposition @Surjective.{u} :=
    (inferInstance : MorphismProperty.IsMultiplicative @Surjective.{u}).toIsStableUnderComposition
  have hwsurj : Surjective (R.toGrp.X ◁ π.hom.hom).left :=
    MorphismProperty.pullbackMap (P := @Surjective.{u}) (inferInstance : Surjective (𝟙 _))
      (inferInstance : Surjective π.hom.hom.left) (by simp) (Over.w π.hom.hom).symm
  have : Surjective m.hom.hom.left := by
    have : Surjective (subgroupProductMap i d).left := ⟨hsurj⟩
    rw [hmd, Over.comp_left]
    infer_instance
  have : IsAffineHom R.toGrp.X.hom := hRaff
  have : LocallyOfFiniteType R.toGrp.X.hom := hRlft
  have : IsAffineHom C.X.hom := hCr.isAffineHom
  have : Smooth C.X.hom := hCr.smooth
  have : Smooth G.X.hom := hG.smooth
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : Flat m.hom.hom.left :=
    subgroupMultiplication_flat_of_surjective i (π ≫ d) (commute_of_isCentral i hi)
      (by assumption)
  have hm : IsCentral (kernelι m) := isCentral_kernel_coverMultiplication h i hi
  -- the source `R × C` is connected reductive
  have hA₀ : IsConnectedReductive (R.toGrp ⊗ C) :=
    (directProductReductive k R.toGrp C).2.1 hRr hCr
  have : Smooth (R.toGrp ⊗ C).X.hom := hA₀.smooth
  have : IsAffineHom (R.toGrp ⊗ C).X.hom := hA₀.isAffineHom
  -- `C` contains every commutator of `R × C`
  have hc₀ : ∀ (T : Over (Spec (CommRingCat.of k))) (x y : T ⟶ (R.toGrp ⊗ C).X),
      ∃ w : T ⟶ C.X, w ≫ (prodInr R.toGrp C).hom.hom = x * y * x⁻¹ * y⁻¹ := by
    intro T x y
    refine ⟨(x ≫ snd R.X C.X) * (y ≫ snd R.X C.X) * (x ≫ snd R.X C.X)⁻¹ *
      (y ≫ snd R.X C.X)⁻¹, ?_⟩
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, prodInr_hom_fst, MonObj.comp_one]
      simp only [MonObj.mul_comp, GrpObj.inv_comp]
      rw [eq_comm, mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
      exact mul_comm _ _
    · rw [Category.assoc, prodInr_hom_snd, Category.comp_id]
      simp only [MonObj.mul_comp, GrpObj.inv_comp]
  -- the central kernel of `m` lies in a maximal torus of `R × C`
  obtain ⟨T, jT, hjT⟩ := maximalTorusExistence k (R.toGrp ⊗ C)
  have : IsClosedImmersion jT.hom.hom.left := hjT.2.1
  have : Mono jT.hom.hom := Over.mono_of_mono_left _
  have hrep : (torusCentralizer jT).IsRepresentedBy jT := by
    rw [maximalTorusCentralizer k _ hA₀ T jT hjT]
    exact ⟨inferInstance, rfl⟩
  have hle : SubgroupFunctor.range (kernelι m) ≤ torusCentralizer jT := by
    intro U x hx
    have hx' : x ∈ (center (R.toGrp ⊗ C)).carrier U :=
      (isCentral_iff_range_le_center _).mp hm U hx
    intro V a t
    exact hx' V a (t ≫ jT.hom.hom)
  let κ : kernel m ⟶ T.toGrp := hrep.liftOfLE (kernelι m) hle
  have hκ : κ.hom.hom ≫ jT.hom.hom = (kernelι m).hom.hom := by
    rw [← Grp.comp_hom_hom, SubgroupFunctor.IsRepresentedBy.liftOfLE_comp]
  have : Mono κ.hom.hom := mono_of_mono_fac hκ
  -- the maximal torus embeds into an induced torus
  obtain ⟨S, φ, hS, hφ⟩ := IsTorus.exists_mono_inducedTorus T hjT.1
  let j : kernel m ⟶ S.toGrp := κ ≫ CommGroupScheme.groupHom φ
  have : Mono j.hom.hom := by
    change Mono (κ.hom.hom ≫ (CommGroupScheme.groupHom φ).hom.hom)
    infer_instance
  exact exists_zExtension_of_centralCover hG hA₀ m hm (prodInr R.toGrp C) hc₀ hC hS j

end Langlands.GroupScheme
