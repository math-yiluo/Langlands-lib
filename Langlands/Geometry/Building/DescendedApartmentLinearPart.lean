import Langlands.Geometry.Building.AffineFacetIncidenceTransfer
import Langlands.Geometry.Building.IntegerAffineRootFibreInfinitude
import Langlands.Geometry.Building.IntegerValuationLocalComparison
import Langlands.Geometry.Building.SplitTorusTranslationBaseChange
import Langlands.Geometry.Building.CentralIsogenyTranslation
import Langlands.Geometry.Building.MaximalUnramifiedBuildingData
import Langlands.GroupScheme.Rational.ScalarExtensionNaturality
import Langlands.Geometry.Building.MaximalUnramifiedApartmentInjective

/-! # The linear part of a descended apartment map -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.GroupScheme.GaloisPointComparison Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building

section Points

variable (F K : Type u) [Field F] [Field K] [Algebra F K]

/-- Scalar extension of the rational point of `𝔾_m` with coordinate `t`, read in
`𝔾_{m,K}` through the base-change isomorphism, has coordinate the image of `t`. -/
theorem Gm.affinePointsEquiv_rationalExtend (t : Fˣ) :
    Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of K)))
        (rationalExtend F K (Gm (Spec (CommRingCat.of F))).toGrp
            ((Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of F)))).symm t) ≫
          (Gm.baseChangeIso (baseMap F K)).hom.hom.hom) =
      Units.map (algebraMap F K).toMonoidHom t := by
  apply Units.ext
  set u := (Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of F)))).symm t with hu
  let a : (Over.map (baseMap F K)).obj (Over.mk (𝟙 (Spec (CommRingCat.of K)))) ⟶
      Over.mk (𝟙 (Spec (CommRingCat.of F))) :=
    Over.homMk (baseMap F K) (by simp)
  have hpt : baseChangePointsEquiv (baseMap F K) (Gm (Spec (CommRingCat.of F))).toGrp _
      (rationalExtend F K (Gm (Spec (CommRingCat.of F))).toGrp u) = a ≫ u := by
    apply Over.OverMorphism.ext
    rw [baseChangePointsEquiv_left, Over.comp_left]
    exact rationalExtend_fst F K _ u
  rw [Gm.affinePointsEquiv_val, Gm.pointsEquiv_baseChangeIso_hom,
    Gm.baseChangeUnitsEquiv_apply, hpt, Gm.pointsEquiv_naturality]
  have ht : (t : F) = (Scheme.ΓSpecIso (CommRingCat.of F)).hom
      (Gm.pointsEquiv _ (Over.mk (𝟙 (Spec (CommRingCat.of F)))) u).val := by
    rw [← Gm.affinePointsEquiv_val, hu, MulEquiv.apply_symm_apply]
  simp only [Units.coe_map]
  rw [ht]
  change ((baseMap F K).appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom) _ = _
  rw [Scheme.ΓSpecIso_naturality]
  rfl

/-- Scalar extension of the point `c(t)` of a cocharacter `c` is the point `c_K(t)` of the
base-changed cocharacter at the image of `t`. -/
theorem rationalExtend_cocharacterPoints (S : CommGroupScheme (Spec (CommRingCat.of F)))
    (c : cocharacterLattice S) (t : Fˣ) :
    rationalExtend F K S.toGrp (CocharacterUniformizer.cocharacterPoints F S c t) =
      CocharacterUniformizer.cocharacterPoints K
        ((CommGroupScheme.baseChange (algebraBaseMap F K)).obj S)
        (cocharacterLattice.baseChange (algebraBaseMap F K) S c)
        (Units.map (algebraMap F K).toMonoidHom t) := by
  set u := (Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of F)))).symm t
  have hu : rationalExtend F K (Gm (Spec (CommRingCat.of F))).toGrp u ≫
      (Gm.baseChangeIso (baseMap F K)).hom.hom.hom =
      (Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of K)))).symm
        (Units.map (algebraMap F K).toMonoidHom t) := by
    rw [MulEquiv.eq_symm_apply]
    exact Gm.affinePointsEquiv_rationalExtend F K t
  have hinv : rationalExtend F K (Gm (Spec (CommRingCat.of F))).toGrp u =
      (Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of K)))).symm
          (Units.map (algebraMap F K).toMonoidHom t) ≫
        (Gm.baseChangeIso (baseMap F K)).inv.hom.hom := by
    rw [← hu, Category.assoc, ← Grp.comp_hom_hom, Iso.hom_inv_id, Grp.id_hom_hom,
      Category.comp_id]
  change rationalExtend F K S.toGrp (rationalPoints.map (CommGroupScheme.groupHom c) u) =
    rationalPoints.map (CommGroupScheme.groupHom
      (cocharacterLattice.baseChange (algebraBaseMap F K) S c))
      ((Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of K)))).symm
        (Units.map (algebraMap F K).toMonoidHom t))
  rw [rationalExtend_map, cocharacterLattice.groupHom_baseChange, hinv]
  rfl

end Points

section LinearPart

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (B : ValuationBuildingData G)
  (C : MaximalUnramified.BuildingData F (baseChanged F (inertiaFixedField F) G))
  (f : baseChanged F (inertiaFixedField F) B.S.toGrp ⟶ C.S.toGrp)

/-- The factorization `f : S_K → C.S`, as a map of commutative group schemes out of the
base change of the commutative group scheme `S = B.S`. -/
abbrev descendedTorusHom :
    (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj B.S ⟶ C.S :=
  Additive.ofMul f

/-- The map of real cocharacter spaces induced by a factorization `f : S_K → C.S` of the
base change of the torus inclusion of `B`: base change of cocharacters of the split torus
`S = B.S`, followed by composition with `f`. -/
def descendedCocharacterMap : V B.S →ₗ[ℝ] V C.S :=
  cocharacterMapReal (descendedTorusHom B C f) ∘ₗ
    (splitCocharacterBaseChange (K := inertiaFixedField F) B.S
      B.isMaximalSplitTorus.1.1).toLinearMap

theorem descendedCocharacterMap_tmul (r : ℝ) (c : cocharacterLattice B.S) :
    descendedCocharacterMap B C f (r ⊗ₜ[ℤ] c) =
      r ⊗ₜ[ℤ] (cocharacterLattice.baseChange (algebraBaseMap F (inertiaFixedField F)) B.S c ≫
        descendedTorusHom B C f) :=
  rfl

/-- Real evaluation of a character of `C.S` on the image of `v` is the evaluation on `v` of
any character of `S` whose base change is its restriction along `f`. -/
theorem eval_descendedCocharacterMap (χ : characterLattice C.S) (ψ : characterLattice B.S)
    (hψ : characterLattice.baseChange (algebraBaseMap F (inertiaFixedField F)) B.S ψ =
      descendedTorusHom B C f ≫ χ)
    (v : V B.S) :
    RealTorusSpace.eval C.S χ (descendedCocharacterMap B C f v) =
      RealTorusSpace.eval B.S ψ v := by
  rw [descendedCocharacterMap, LinearMap.comp_apply, eval_cocharacterMapReal, ← hψ]
  exact eval_splitCocharacterBaseChange B.S B.isMaximalSplitTorus.1.1 ψ v

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem rationalPoints_map_comp_apply' {k : Type u} [Field k]
    {H₁ H₂ H₃ : GroupScheme (Spec (CommRingCat.of k))} (p : H₁ ⟶ H₂) (q : H₂ ⟶ H₃)
    (y : rationalPoints H₁) :
    rationalPoints.map (p ≫ q) y = rationalPoints.map q (rationalPoints.map p y) := by
  rw [rationalPoints.map_apply, rationalPoints.map_apply, rationalPoints.map_apply,
    Grp.comp_hom_hom, Category.assoc]

/-- The image under `f` of the scalar extension of the point `c(t)` is the point of the
cocharacter `c_K ≫ f` of `C.S` at the image of `t`. -/
theorem map_rationalExtend_cocharacterPoints (c : cocharacterLattice B.S) (t : Fˣ) :
    rationalPoints.map f (rationalExtend F (inertiaFixedField F) B.S.toGrp
        (CocharacterUniformizer.cocharacterPoints F B.S c t)) =
      CocharacterUniformizer.cocharacterPoints (inertiaFixedField F) C.S
        (cocharacterLattice.baseChange (algebraBaseMap F (inertiaFixedField F)) B.S c ≫
          descendedTorusHom B C f)
        (Units.map (algebraMap F (inertiaFixedField F)).toMonoidHom t) := by
  rw [rationalExtend_cocharacterPoints]
  exact (rationalPoints_map_comp_apply' _ _ _).symm

/-- The order of the chosen uniformizer is `1`. -/
private theorem localFieldOrder_uniformizerUnit' :
    localFieldOrder F (SplitTorusValuation.uniformizerUnit F) = 1 := by
  simp [localFieldOrder, SplitTorusValuation.fieldOrderUnits_uniformizerUnit]

private theorem translation_cocharacterPoints_uniformizer (c : cocharacterLattice B.S) :
    (B.translation (rationalPoints.map B.centralizer.s
        (CocharacterUniformizer.cocharacterPoints F B.S c
          (SplitTorusValuation.uniformizerUnit F)))).toAdd = (-1 : ℝ) ⊗ₜ[ℤ] c := by
  have h := (IntegerValuationBuildingData.ofLocal B).translation_cocharacterCentralizerPoint
    c (SplitTorusValuation.uniformizerUnit F)
  rw [IntegerValuationBuildingData.ofLocal_translation, IntegerValuation.order_normalized,
    localFieldOrder_uniformizerUnit'] at h
  exact h

private theorem translation_descendedCocharacterPoint (c : cocharacterLattice B.S) :
    (C.translation (C.cocharacterCentralizerPoint
        (cocharacterLattice.baseChange (algebraBaseMap F (inertiaFixedField F)) B.S c ≫
          descendedTorusHom B C f)
        (Units.map (algebraMap F (inertiaFixedField F)).toMonoidHom
          (SplitTorusValuation.uniformizerUnit F)))).toAdd =
      descendedCocharacterMap B C f ((-1 : ℝ) ⊗ₜ[ℤ] c) := by
  rw [C.translation_cocharacterCentralizerPoint,
    MaximalUnramified.order_base_eq_localFieldOrder, localFieldOrder_uniformizerUnit',
    descendedCocharacterMap_tmul]

variable {B C f}

private theorem rationalExtend_centralizerPoint
    (hf : f ≫ C.i = (GroupScheme.baseChange (baseMap F (inertiaFixedField F))).map B.i)
    (c : cocharacterLattice B.S) :
    rationalExtend F (inertiaFixedField F) G
        (rationalPoints.map B.centralizer.j (rationalPoints.map B.centralizer.s
          (CocharacterUniformizer.cocharacterPoints F B.S c
            (SplitTorusValuation.uniformizerUnit F)))) =
      rationalPoints.map C.centralizer.j (C.cocharacterCentralizerPoint
        (cocharacterLattice.baseChange (algebraBaseMap F (inertiaFixedField F)) B.S c ≫
          descendedTorusHom B C f)
        (Units.map (algebraMap F (inertiaFixedField F)).toMonoidHom
          (SplitTorusValuation.uniformizerUnit F))) := by
  rw [← rationalPoints_map_comp_apply', B.centralizer.comp_eq, rationalExtend_map, ← hf,
    rationalPoints_map_comp_apply', map_rationalExtend_cocharacterPoints,
    IntegerValuationBuildingData.cocharacterCentralizerPoint,
    ← rationalPoints_map_comp_apply', C.centralizer.comp_eq]

/-- The descended apartment map on translations by `(-1) ⊗ c`, for integral cocharacters
`c`: these are the translations by the points `c(ϖ)` of the centralizer. -/
theorem descendedApartment_map_neg_one_tmul_vadd
    (e : B.ReducedBuilding → C.ReducedBuilding) (a : B.Apartment →ᵃ[ℝ] C.Apartment)
    (he : ∀ (g : rationalPoints G) (z : B.ReducedBuilding),
      e (g • z) = rationalExtend F (inertiaFixedField F) G g • e z)
    (ha : ∀ w : B.Apartment, e (B.apartmentMap w) = C.apartmentMap (a w))
    (hf : f ≫ C.i = (GroupScheme.baseChange (baseMap F (inertiaFixedField F))).map B.i)
    (c : cocharacterLattice B.S) (w : B.Apartment) :
    a ((Submodule.Quotient.mk ((-1 : ℝ) ⊗ₜ[ℤ] c) : TranslationSpace B.i) +ᵥ w) =
      (Submodule.Quotient.mk (descendedCocharacterMap B C f ((-1 : ℝ) ⊗ₜ[ℤ] c)) :
        TranslationSpace C.i) +ᵥ a w := by
  apply maximalUnramifiedApartmentInjective F _ C
  conv_lhs => rw [← ha, ← translation_cocharacterPoints_uniformizer B c,
    ← B.centralizer_smul_apartmentMap, he, rationalExtend_centralizerPoint hf, ha,
    C.centralizer_smul_apartmentMap, translation_descendedCocharacterPoint]

/-- **The linear part of a descended apartment map.** Let `e` embed the reduced building of
`B` into that of `C`, equivariantly for scalar extension of rational points, and let the
affine map `a` describe `e` on apartments. If `f : S_K → C.S` factors the base change of the
torus inclusion of `B` through that of `C`, then `a` carries the translation by the class of
`v ∈ V(S)` to the translation by the class of its image `f_*(v_K) ∈ V(C.S)`. -/
theorem descendedApartment_map_vadd
    (e : B.ReducedBuilding → C.ReducedBuilding) (a : B.Apartment →ᵃ[ℝ] C.Apartment)
    (he : ∀ (g : rationalPoints G) (z : B.ReducedBuilding),
      e (g • z) = rationalExtend F (inertiaFixedField F) G g • e z)
    (ha : ∀ w : B.Apartment, e (B.apartmentMap w) = C.apartmentMap (a w))
    (hf : f ≫ C.i = (GroupScheme.baseChange (baseMap F (inertiaFixedField F))).map B.i)
    (v : V B.S) (w : B.Apartment) :
    a ((Submodule.Quotient.mk v : TranslationSpace B.i) +ᵥ w) =
      (Submodule.Quotient.mk (descendedCocharacterMap B C f v) : TranslationSpace C.i) +ᵥ
        a w := by
  have hgen : ∀ c : cocharacterLattice B.S,
      (a.linear ∘ₗ (rootAnnihilator B.i).mkQ) ((-1 : ℝ) ⊗ₜ[ℤ] c) =
        ((rootAnnihilator C.i).mkQ ∘ₗ descendedCocharacterMap B C f) ((-1 : ℝ) ⊗ₜ[ℤ] c) := by
    intro c
    have h1 := descendedApartment_map_neg_one_tmul_vadd e a he ha hf c w
    rw [AffineMap.map_vadd] at h1
    exact vadd_right_cancel (a w) h1
  have hL : ∀ v : V B.S, (a.linear ∘ₗ (rootAnnihilator B.i).mkQ) v =
      ((rootAnnihilator C.i).mkQ ∘ₗ descendedCocharacterMap B C f) v := by
    intro v
    induction v using TensorProduct.inductionOn with
    | tmul r c =>
      have hr : r ⊗ₜ[ℤ] c = (-r) • ((-1 : ℝ) ⊗ₜ[ℤ] c) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, neg_mul_neg, mul_one]
      rw [hr, map_smul, map_smul, hgen c]
    | add v₁ v₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂]
  rw [AffineMap.map_vadd]
  exact congrArg (· +ᵥ a w) (hL v)

end LinearPart

end Langlands.Geometry.Building
