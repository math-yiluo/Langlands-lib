import Langlands.Geometry.Building.UnramifiedCoverNormalizerComparison
import Langlands.Geometry.Building.UnramifiedSplitBoundedPoints
import Langlands.GroupScheme.Rational.MaximalSplitTorusCentralizer

/-! # The zero-subgroup normalizer action over the maximal unramified field -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.Geometry.Building.UnramifiedZeroDatum

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))} [IsAffineHom G.X.hom]
    (E : UnramifiedZeroDatum F G) (B : MaximalUnramified.BuildingData F G)

omit [IsAffineHom G.X.hom] in
/-- The actual torus norm subgroup has unit character values for the normalized
integer valuation of the maximal unramified field. -/
theorem torusIwahori_le_integerCharacterValuationKernel :
    E.torusIwahori ≤ characterValuationKernel (MaximalUnramified.valuation F) E.T.toGrp := by
  have ht : E.torusIwahori ≤
      characterValuationKernel (LocalGalois.Separable.fixedFieldValuation F) E.T.toGrp :=
    torusNormIwahori_le_characterValuationKernel
      (LocalGalois.Separable.fixedFieldValuation F) (intermediateValuation F E.L)
      (intermediateValuation_conjugate F E.L) E.T
  intro t ht'
  have hchar := ht ht'
  rw [mem_characterValuationKernel] at hchar ⊢
  intro χ
  exact (MaximalUnramified.valuation_isEquiv F).eq_one_iff_eq_one.mpr (hchar χ)

/-- Conjugating the chosen maximal torus aligns its maximal split part with
the apartment torus. Its norm subgroup then lies in the kernel of the original
normalizer action, and normality preserves the zero subgroup. -/
theorem exists_zeroPoints_eq_simplyConnectedImage_sup_trivialNormalizer :
    ∃ Q : Subgroup (normalizerPoints B.i),
      Q ≤ B.apartment.normalizerAffineEquiv.ker ∧
      E.zeroPoints =
        E.simplyConnectedImage ⊔ Q.map (normalizerPoints B.i).subtype := by
  obtain ⟨A, a, f, ha, hf⟩ := E.isMaximallySplitMaximalTorus.2
  obtain ⟨g, e, he⟩ := (maximalSplitTorusConjugacy (UnramifiedClosure F) G
    B.isConnectedReductive).1 A B.S a B.i ha B.isMaximalSplitTorus
  let j := E.i ≫ (G.innerIso g).hom
  let b := e.inv ≫ f
  have hb : b ≫ j = B.i := by
    dsimp [b, j]
    calc
      (e.inv ≫ f) ≫ (E.i ≫ (G.innerIso g).hom) =
          e.inv ≫ ((f ≫ E.i) ≫ (G.innerIso g).hom) := by
            simp only [Category.assoc]
      _ = e.inv ≫ (e.hom ≫ B.i) := by rw [hf, he]
      _ = B.i := e.inv_hom_id_assoc B.i
  have hcentral := range_le_torusCentralizer_of_factor B.i j b hb
  let c := B.centralizer.isRepresentedBy.factorHom j hcentral
  have hc : c ≫ B.centralizer.j = j :=
    B.centralizer.isRepresentedBy.factorHom_comp j hcentral
  let τ : rationalPoints E.T.toGrp →* normalizerPoints B.i :=
    B.centralizer.toNormalizer.comp (rationalPoints.map c)
  have hτ (t : rationalPoints E.T.toGrp) :
      (τ t : rationalPoints G) = rationalPoints.map j t := by
    change rationalPoints.map B.centralizer.j (rationalPoints.map c t) =
      rationalPoints.map j t
    simpa only [rationalPoints.map_apply, Grp.comp_hom_hom, Category.assoc] using
      congrArg (fun q => rationalPoints.map q t) hc
  let Q := E.torusIwahori.map τ
  have hQ : Q.map (normalizerPoints B.i).subtype =
      E.torusIwahori.map (rationalPoints.map j) := by
    rw [Subgroup.map_map]
    congr 1
    exact MonoidHom.ext hτ
  refine ⟨Q, ?_, ?_⟩
  · rintro _ ⟨t, ht, rfl⟩
    apply AffineEquiv.ext
    intro x
    have hz : rationalPoints.map c t ∈
        characterValuationKernel (MaximalUnramified.valuation F) B.centralizer.Z :=
      map_characterValuationKernel_le _ c
        ⟨t, E.torusIwahori_le_integerCharacterValuationKernel ht, rfl⟩
    exact B.isOmegaCompatible.smul_eq_self hz x
  · have : E.zeroPoints.Normal := E.normal_zeroPoints
    have : E.simplyConnectedImage.Normal :=
      normal_of_simplyConnectedImage_le E.isSimplyConnectedDerivedCover le_rfl
    have hj : rationalPoints.map j =
        (MulAut.conj g).toMonoidHom.comp (rationalPoints.map E.i) := by
      apply MonoidHom.ext
      intro t
      change rationalPoints.map (E.i ≫ (G.innerIso g).hom) t = _
      simpa only [rationalPoints.map_apply, Grp.comp_hom_hom, Category.assoc,
        MonoidHom.comp_apply] using
        DFunLike.congr_fun (rationalPoints_map_innerIso g) (rationalPoints.map E.i t)
    have hconj := Subgroup.Normal.map_conj_eq E.zeroPoints g
    change (E.simplyConnectedImage ⊔
      E.torusIwahori.map (rationalPoints.map E.i)).map
        (MulAut.conj g).toMonoidHom = _ at hconj
    rw [Subgroup.map_sup, MulEquiv.toMonoidHom_eq_coe,
      Subgroup.Normal.map_conj_eq E.simplyConnectedImage g] at hconj
    rw [hQ, hj, ← Subgroup.map_map]
    simpa only [MulEquiv.toMonoidHom_eq_coe] using hconj.symm

/-- Every zero-normalizer element has affine Weyl action, conditional only on
the explicit simply connected normalizer assertion over the same field. -/
theorem normalizer_mem_affineWeylGroup_of_mem_zeroPoints
    (hsc : MaximalUnramified.SimplyConnectedNormalizerAffineWeylStatement.{u})
    (n : normalizerPoints B.i) (hn : (n : rationalPoints G) ∈ E.zeroPoints) :
    B.apartment.normalizerAffineEquiv n ∈
      AffineRootSystem.affineWeylGroup B.affineRoots := by
  obtain ⟨Q, hQ, hzero⟩ :=
    E.exists_zeroPoints_eq_simplyConnectedImage_sup_trivialNormalizer B
  have : E.simplyConnectedImage.Normal :=
    normal_of_simplyConnectedImage_le E.isSimplyConnectedDerivedCover le_rfl
  rw [hzero] at hn
  obtain ⟨c, hc, t, ht, hct⟩ := Subgroup.mem_sup_of_normal_left.mp hn
  obtain ⟨m, hm, rfl⟩ := ht
  change c * (m : rationalPoints G) = (n : rationalPoints G) at hct
  let k : normalizerPoints B.i := n * m⁻¹
  have hk : (k : rationalPoints G) = c := by
    change (n : rationalPoints G) * (m : rationalPoints G)⁻¹ = c
    rw [← hct]
    group
  have hw := E.normalizer_mem_affineWeylGroup_of_mem_simplyConnectedImage
    B hsc k (hk.symm ▸ hc)
  have hmker : B.apartment.normalizerAffineEquiv m = 1 := hQ hm
  have hkn : B.apartment.normalizerAffineEquiv k =
      B.apartment.normalizerAffineEquiv n := by
    dsimp [k]
    rw [map_mul, map_inv, hmker, inv_one, mul_one]
  rwa [hkn] at hw

/-- The affine Weyl upper inclusion for the actual zero-normalizer intersection. -/
theorem zeroNormalizer_map_le_affineWeylGroup_of_statement
    (hsc : MaximalUnramified.SimplyConnectedNormalizerAffineWeylStatement.{u}) :
    (E.zeroPoints.subgroupOf (normalizerPoints B.i)).map
        B.apartment.normalizerAffineEquiv ≤
      AffineRootSystem.affineWeylGroup B.affineRoots := by
  rintro _ ⟨n, hn, rfl⟩
  exact E.normalizer_mem_affineWeylGroup_of_mem_zeroPoints B hsc n hn

/-- Restrict the original zero-normalizer action to the affine Weyl subgroup,
with the simply connected assertion retained as an explicit argument. -/
def zeroNormalizerWeylActionOfStatement
    (hsc : MaximalUnramified.SimplyConnectedNormalizerAffineWeylStatement.{u}) :
    E.zeroPoints.subgroupOf (normalizerPoints B.i) →*
      AffineRootSystem.affineWeylGroup B.affineRoots :=
  (B.apartment.normalizerAffineEquiv.comp
    (E.zeroPoints.subgroupOf (normalizerPoints B.i)).subtype).codRestrict _
      (fun n => E.normalizer_mem_affineWeylGroup_of_mem_zeroPoints
        B hsc n n.property)

@[simp]
theorem zeroNormalizerWeylActionOfStatement_coe
    (hsc : MaximalUnramified.SimplyConnectedNormalizerAffineWeylStatement.{u})
    (n : E.zeroPoints.subgroupOf (normalizerPoints B.i)) :
    (E.zeroNormalizerWeylActionOfStatement B hsc n :
      B.Apartment ≃ᵃ[ℝ] B.Apartment) = B.apartment.normalizerAffineEquiv n :=
  rfl

end Langlands.Geometry.Building.UnramifiedZeroDatum
