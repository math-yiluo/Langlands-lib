import Langlands.GroupScheme.CentralIsogeny.CommutatorDescent
import Langlands.GroupScheme.Reductive.CommutingMultiplication
import Langlands.GroupScheme.Reductive.CentralTorusSurjectivityProof
import Langlands.GroupScheme.Reductive.CentralDerivedProductProof
import Langlands.GroupScheme.Adjoint.SecondCenterReductive
import Langlands.GroupScheme.SimplyConnected.DerivedCover

/-! # Commutators lift to the simply connected cover of the derived subgroup -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k] {G D C : GroupScheme (Spec (CommRingCat.of k))}
  {R : CommGroupScheme (Spec (CommRingCat.of k))}
  {d : D ⟶ G} {π : C ⟶ D}

namespace CommutatorCoverImage

/-- A central factor commutes with the image of the cover. -/
theorem commute_of_isCentral (i : R.toGrp ⟶ G) (hi : IsCentral i)
    (T : Over (Spec (CommRingCat.of k))) (r : T ⟶ R.toGrp.X) (c : T ⟶ C.X) :
    Commute (r ≫ i.hom.hom) (c ≫ (π ≫ d).hom.hom) :=
  commute_of_mem_center (hi T r) _

/-- The multiplication homomorphism `R × C → G`, `(r, c) ↦ i(r) · d(π(c))`. -/
abbrev coverMultiplication (i : R.toGrp ⟶ G) (hi : IsCentral i) : R.toGrp ⊗ C ⟶ G :=
  commutingSubgroupMultiplicationHom i (π ≫ d) (commute_of_isCentral i hi)

/-- The kernel of `R × C → G` is central: its `C`-component maps into the centre of `G`, so
all its commutators lie in the central kernel of `π`, and `C` has trivial second centre. -/
theorem isCentral_kernel_coverMultiplication (h : IsSimplyConnectedDerivedCover d π)
    (i : R.toGrp ⟶ G) (hi : IsCentral i) :
    IsCentral (kernelι (coverMultiplication (d := d) (π := π) i hi)) := by
  apply (isCentral_kernelι_iff _).mpr
  intro T x hx
  have hx' : ((x ≫ fst R.toGrp.X C.X) ≫ i.hom.hom) *
      ((x ≫ snd R.toGrp.X C.X) ≫ (π ≫ d).hom.hom) = 1 := by
    rw [← comp_subgroupMultiplication, lift_comp_fst_snd]
    exact hx
  have hcd : (x ≫ snd R.toGrp.X C.X) ≫ (π ≫ d).hom.hom =
      ((x ≫ fst R.toGrp.X C.X) ≫ i.hom.hom)⁻¹ :=
    eq_inv_of_mul_eq_one_right hx'
  have hC : IsConnectedReductive C :=
    h.isSimplyConnectedCover.isSimplyConnected.isSemisimple.isConnectedReductive
  have hcC : x ≫ snd R.toGrp.X C.X ∈ (center C).carrier T := by
    apply SecondCenter.secondCenterTrivial_of_centralDerivedProduct
      reductiveCentralDerivedProduct k C hC
    intro T' a c'
    apply h.isSimplyConnectedCover.isCentralIsogeny.mem_center_of_comp_eq_one
    rw [← h.comp_eq_one_iff]
    have hz : (a ≫ x ≫ snd R.toGrp.X C.X) ≫ (π ≫ d).hom.hom =
        ((a ≫ x ≫ fst R.toGrp.X C.X) ≫ i.hom.hom)⁻¹ := by
      rw [Category.assoc, hcd, GrpObj.comp_inv, ← Category.assoc, ← Category.assoc,
        Category.assoc a]
    have hcomm : Commute ((a ≫ x ≫ fst R.toGrp.X C.X) ≫ i.hom.hom)
        (c' ≫ (π ≫ d).hom.hom) :=
      commute_of_isCentral i hi T' _ c'
    simp only [MonObj.mul_comp, GrpObj.inv_comp, hz, inv_inv]
    rw [hcomm.inv_left.eq]
    group
  rw [mem_center]
  intro T' a y
  have hfst : Commute ((a ≫ x) ≫ fst R.toGrp.X C.X) (y ≫ fst R.toGrp.X C.X) := by
    change _ * _ = _ * _
    exact mul_comm _ _
  have hsnd : Commute ((a ≫ x) ≫ snd R.toGrp.X C.X) (y ≫ snd R.toGrp.X C.X) := by
    rw [Category.assoc]
    exact hcC T' a _
  change _ * _ = _ * _
  apply CartesianMonoidalCategory.hom_ext
  · rw [MonObj.mul_comp, MonObj.mul_comp]
    exact hfst.eq
  · rw [MonObj.mul_comp, MonObj.mul_comp]
    exact hsnd.eq

end CommutatorCoverImage

open CommutatorCoverImage in
/-- **Commutators lift to the simply connected cover.** For a connected reductive group `G`
over a field, with derived subgroup `d : D → G` and simply connected cover `π : C → D`, the
commutator of any two `T`-points of `G` is the image of a `T`-point of `C`. -/
theorem IsSimplyConnectedDerivedCover.exists_comp_eq_commutator
    (h : IsSimplyConnectedDerivedCover d π) {T : Over (Spec (CommRingCat.of k))}
    (x y : T ⟶ G.X) :
    ∃ c : T ⟶ C.X, c ≫ (π ≫ d).hom.hom = x * y * x⁻¹ * y⁻¹ := by
  obtain ⟨R, i, hRaff, hRlft, -, -, hi, hsurj⟩ :=
    reductiveCentralTorusSurjectivity k G D d h.isConnectedReductive h.isDerivedSubgroup
  have hG := h.isConnectedReductive
  have hC : IsConnectedReductive C :=
    h.isSimplyConnectedCover.isSimplyConnected.isSemisimple.isConnectedReductive
  let q := CommutatorCoverImage.coverMultiplication (d := d) (π := π) i hi
  have hqd : q.hom.hom = (R.toGrp.X ◁ π.hom.hom) ≫ subgroupProductMap i d := by
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
  have : Surjective q.hom.hom.left := by
    have : Surjective (subgroupProductMap i d).left := ⟨hsurj⟩
    rw [hqd, Over.comp_left]
    infer_instance
  have : IsAffineHom R.toGrp.X.hom := hRaff
  have : LocallyOfFiniteType R.toGrp.X.hom := hRlft
  have : IsAffineHom C.X.hom := hC.isAffineHom
  have : Smooth C.X.hom := hC.smooth
  have : Smooth G.X.hom := hG.smooth
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : Flat q.hom.hom.left :=
    subgroupMultiplication_flat_of_surjective i (π ≫ d) (commute_of_isCentral i hi)
      (by assumption)
  have : IsAffineHom (R.toGrp.X ⊗ C.X).hom := SecondCenter.isAffineHom_tensor _ _
  have : IsAffine (R.toGrp.X ⊗ C.X).left := isAffine_of_isAffineHom (R.toGrp.X ⊗ C.X).hom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : QuasiCompact q.hom.hom.left := inferInstance
  have hq := isCentral_kernel_coverMultiplication h i hi
  let φ := CommutatorDescent.hom q hq
  have hφfst : φ ≫ fst R.toGrp.X C.X = 1 := by
    have := CommutatorDescent.epi_tensorHom q
    apply (cancel_epi (q.hom.hom ⊗ₘ q.hom.hom)).mp
    rw [CommutatorDescent.fac_assoc, MonObj.comp_one,
      ← Category.id_comp (commutatorMap (𝟙 (R.toGrp ⊗ C)) (𝟙 (R.toGrp ⊗ C))),
      commutatorMap_points]
    simp only [Grp.id_hom_hom, Category.comp_id, Category.id_comp, MonObj.mul_comp,
      GrpObj.inv_comp]
    rw [mul_assoc, mul_mul_mul_comm, mul_inv_cancel, mul_inv_cancel, one_mul]
  refine ⟨lift x y ≫ φ ≫ snd R.toGrp.X C.X, ?_⟩
  have hcomm := CommutatorDescent.hom_comp q hq
  have h1 := congrArg (fun f => lift x y ≫ f) hcomm
  simp only [commutatorMap_lift, Grp.id_hom_hom, Category.comp_id] at h1
  rw [← h1]
  change _ = lift x y ≫ φ ≫ subgroupMultiplication i (π ≫ d)
  simp only [subgroupMultiplication, MonObj.comp_mul]
  rw [← Category.assoc φ, hφfst, MonObj.one_comp, MonObj.comp_one, one_mul]
  simp only [Category.assoc]

end Langlands.GroupScheme
