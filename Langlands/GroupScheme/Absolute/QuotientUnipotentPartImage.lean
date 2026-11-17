import Langlands.GroupScheme.Absolute.UnipotentPart
import Langlands.GroupScheme.Absolute.SolvableUnipotentFactorizationProof
import Langlands.GroupScheme.Absolute.RationalSubgroupContainment
import Langlands.GroupScheme.Reductive.UnipotentQuotient
import Langlands.GroupScheme.Torus.HeightExistence
import Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof
import Langlands.GroupScheme.Torus.FiniteImage
import Langlands.GroupScheme.Torus.WeylGroupSchemeQuotientPoints

/-! # Images of unipotent parts of solvable groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {B C U J : GroupScheme (Spec (CommRingCat.of k))}

/-- A homomorphism carries greatest unipotent subgroups onto supplied smooth
closed subgroup images. -/
def PreservesUnipotentParts (q : B ⟶ C) : Prop :=
  ∀ (U J : GroupScheme (Spec (CommRingCat.of k))) (i : U ⟶ B) (j : J ⟶ C) (f : U ⟶ J),
    IsUnipotentPart i → IsClosedSubgroup j → Smooth J.X.hom →
      Surjective f.hom.hom.left → i ≫ q = f ≫ j → IsUnipotentPart j

namespace QuotientUnipotentPartImage

variable [IsAlgClosed k]
  [Smooth B.X.hom] [IsAffineHom B.X.hom] [ConnectedSpace B.X.left]
  [Smooth C.X.hom] [IsAffineHom C.X.hom] [ConnectedSpace C.X.left]

/-- Surjective homomorphisms between smooth connected solvable affine groups
over an algebraically closed field preserve unipotent parts. -/
theorem preservesUnipotentParts (hB : IsSolvableGroupScheme B)
    (hC : IsSolvableGroupScheme C) (q : B ⟶ C) (hq : Surjective q.hom.hom.left) :
    PreservesUnipotentParts q := by
  intro U J i j f hi hj hJsm hf hcomm
  have : Smooth U.X.hom := hi.smooth
  have : ConnectedSpace U.X.left := hi.connectedSpace
  have : IsAffineHom U.X.hom := hi.isClosedSubgroup.isAffineHom
  have : Smooth J.X.hom := hJsm
  have : IsAffineHom J.X.hom := hj.isAffineHom
  have : Surjective f.hom.hom.left := hf
  have : ConnectedSpace J.X.left :=
    f.hom.hom.left.surjective.connectedSpace f.hom.hom.left.continuous
  have : IsLocallyNoetherian J.X.left := LocallyOfFiniteType.isLocallyNoetherian J.X.hom
  have : IsReduced J.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field k _ J.X.hom
  have : LocallyOfFiniteType (f.hom.hom.left ≫ J.X.hom) := by
    rw [Over.w f.hom.hom]
    infer_instance
  have : LocallyOfFiniteType f.hom.hom.left :=
    locallyOfFiniteType_of_comp _ J.X.hom
  have : Flat f.hom.hom.left := DominantHomFlat.flat_of_isDominant f
  have hJU : IsUnipotent J := hi.isUnipotent.of_flat_surjective f
  obtain ⟨V, v, hv⟩ := exists_isUnipotentPart C hC
  have : Smooth V.X.hom := hv.smooth
  have : IsAffineHom V.X.hom := hv.isClosedSubgroup.isAffineHom
  have : IsReduced V.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field k _ V.X.hom
  have hjv := hv.greatest J j hj hJU
  obtain ⟨T, t, ht⟩ := exists_isMaximalTorus B
  have hT := ht.1.isSplitTorus_of_finiteGaloisSplitting torusFiniteGaloisSplitting
  have : IsAffineHom T.X.hom := hT.isAffineHom
  let φ := t ≫ q
  have hS := hT.isSplitTorus_schematicImage φ
  let S : CommGroupScheme (Spec (CommRingCat.of k)) :=
    { SchematicImage.image φ with comm := hS.isCommMonObj }
  let s : S.toGrp ⟶ C := SchematicImage.inclusion φ
  let ft : T.toGrp ⟶ S.toGrp := SchematicImage.projection φ
  have hs : IsClosedSubgroup s := HomImage.isClosedSubgroup_inclusion φ
  have hft : ft ≫ s = t ≫ q := SchematicImage.projection_inclusion φ
  have hinter := range_inf_eq_bot_of_isSplitTorus_of_isUnipotent
    unipotentClosedSubgroup s hs hS v hv.isUnipotent
  have hvj : SubgroupFunctor.range v ≤ SubgroupFunctor.range j := by
    apply SubgroupFunctor.range_le_of_algClosed_points hj
    rintro x ⟨z, rfl⟩
    change rationalPoints V at z
    change z ≫ v.hom.hom ∈ (SubgroupFunctor.range j).carrier _
    obtain ⟨b, hb⟩ := rationalPoints.map_surjective_of_surjective q hq
      (z ≫ v.hom.hom)
    obtain ⟨W, a, ha, _, _, hW, _, hfac⟩ :=
      solvableUnipotentFactorization k B hB T t ht
    obtain ⟨w, y, hwy⟩ := hfac b
    obtain ⟨u, hu⟩ := (hi.greatest W a ha hW) _ ⟨w, rfl⟩
    change rationalPoints U at u
    change u ≫ i.hom.hom = w ≫ a.hom.hom at hu
    let p := w ≫ a.hom.hom ≫ q.hom.hom
    let r := y ≫ t.hom.hom ≫ q.hom.hom
    have hpj : p ∈ (SubgroupFunctor.range j).carrier
        (Over.mk (𝟙 (Spec (CommRingCat.of k)))) := by
      refine ⟨u ≫ f.hom.hom, ?_⟩
      change (u ≫ f.hom.hom) ≫ j.hom.hom = p
      rw [Category.assoc, ← Grp.comp_hom_hom, ← hcomm]
      change u ≫ i.hom.hom ≫ q.hom.hom = p
      rw [← Category.assoc, hu]
      rfl
    have hprod : p * r = z ≫ v.hom.hom := by
      have he := congrArg (fun b => b ≫ q.hom.hom) hwy
      simp only [MonObj.mul_comp, Category.assoc] at he
      exact he.trans hb
    have hpv := hjv _ hpj
    have hzv : z ≫ v.hom.hom ∈ (SubgroupFunctor.range v).carrier
        (Over.mk (𝟙 (Spec (CommRingCat.of k)))) := ⟨z, rfl⟩
    have hrv : r ∈ (SubgroupFunctor.range v).carrier
        (Over.mk (𝟙 (Spec (CommRingCat.of k)))) := by
      have h := ((SubgroupFunctor.range v).carrier _).mul_mem
        (((SubgroupFunctor.range v).carrier _).inv_mem hpv) hzv
      simpa only [← hprod, inv_mul_cancel_left] using h
    have hrs : r ∈ (SubgroupFunctor.range s).carrier
        (Over.mk (𝟙 (Spec (CommRingCat.of k)))) := by
      refine ⟨y ≫ ft.hom.hom, ?_⟩
      change (y ≫ ft.hom.hom) ≫ s.hom.hom = r
      rw [Category.assoc, ← Grp.comp_hom_hom, hft]
      rfl
    have hrone : r = 1 := by
      apply Subgroup.mem_bot.mp
      change r ∈ (⊥ : SubgroupFunctor C).carrier _
      rw [← hinter]
      exact ⟨hrs, hrv⟩
    rw [← hprod, hrone, mul_one]
    exact hpj
  refine ⟨hj, hJsm, inferInstance, hJU, ?_⟩
  intro W w hw hWu
  exact (hv.greatest W w hw hWu).trans hvj

end QuotientUnipotentPartImage

end Langlands.GroupScheme
