import Langlands.Geometry.Building.UnramifiedSplitTranslationFixerStatement
import Langlands.Geometry.Building.IntegerCentralizer
import Langlands.Geometry.Building.CocharacterUniformizerEvaluation
import Langlands.Geometry.Building.ApartmentFacetClosureFixing
import Langlands.Geometry.Building.MaximalUnramifiedUniformizer
import Langlands.GroupScheme.Reductive.AlgebraicExtensionAscent

/-! # Split-centralizing fixers fix all split translations -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.GroupScheme.GaloisPointComparison Langlands.LocalGalois.Separable
open Langlands.BruhatTits

namespace Langlands.Geometry.Building

private theorem centralizerTranslation_cocharacter
    {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {Z : GroupScheme (Spec (CommRingCat.of k))}
    (v : Valuation k (WithZero (Multiplicative ℤ))) (s : T.toGrp ⟶ Z)
    (hs : Function.Bijective (Cartan.restrictionEvaluation s))
    (ν : cocharacterLattice T) (t : kˣ) :
    (IntegerValuation.centralizerTranslation v s hs
      (rationalPoints.map s (CocharacterUniformizer.cocharacterPoints k T ν t))).toAdd =
        -(IntegerValuation.order v t ⊗ₜ[ℤ] ν) := by
  apply hs.injective
  apply AddMonoidHom.ext
  intro χ
  change eval T (Cartan.characterRestriction s χ)
    (IntegerValuation.centralizerTranslation v s hs
      (rationalPoints.map s (CocharacterUniformizer.cocharacterPoints k T ν t))).toAdd =
    eval T (Cartan.characterRestriction s χ) (-(IntegerValuation.order v t ⊗ₜ[ℤ] ν))
  rw [IntegerValuation.eval_centralizerTranslation,
    ← rationalCharacterEval_characterRestrict]
  have he : characterRestrict s χ =
      (rationalCharacters.equivCharacterLattice T).symm
        (Cartan.characterRestriction s χ) := by
    simp [Cartan.characterRestriction]
  rw [he, CocharacterUniformizer.rationalCharacterEval_cocharacterPoints,
    map_neg, eval_tmul]
  simp [IntegerValuation.order, map_zpow, toAdd_zpow, mul_comm]

private theorem convex_contains_real_line
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {s : Set E} (hs : Convex ℝ s) (w : E)
    (hw : ∀ n : ℤ, (n : ℝ) • w ∈ s) (r : ℝ) : r • w ∈ s := by
  let n : ℤ := ⌊r⌋
  have hn : (n : ℝ) ≤ r := Int.floor_le r
  have hn' : r < (n : ℝ) + 1 := Int.lt_floor_add_one r
  have h := hs (hw n) (hw (n + 1))
    (a := 1 - (r - (n : ℝ))) (b := r - (n : ℝ))
    (by linarith) (by linarith) (by ring)
  convert h using 1
  rw [Int.cast_add, Int.cast_one]
  module

private theorem convex_contains_tensor_image
    {M E : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
    (L : (ℝ ⊗[ℤ] M) →ₗ[ℝ] E) {s : Set E} (hs : Convex ℝ s)
    (hM : ∀ ν : M, L ((1 : ℝ) ⊗ₜ[ℤ] ν) ∈ s)
    (w : ℝ ⊗[ℤ] M) : L w ∈ s := by
  have hline (ν : M) (r : ℝ) : L (r ⊗ₜ[ℤ] ν) ∈ s := by
    have hi (n : ℤ) : (n : ℝ) • L ((1 : ℝ) ⊗ₜ[ℤ] ν) ∈ s := by
      rw [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      have h := hM (n • ν)
      simpa only [TensorProduct.tmul_smul, TensorProduct.smul_tmul',
        zsmul_eq_mul, mul_one, map_smul] using h
    have h := convex_contains_real_line hs (L ((1 : ℝ) ⊗ₜ[ℤ] ν)) hi r
    simpa only [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one] using h
  have hall : ∀ z : ℝ ⊗[ℤ] M, ∀ r : ℝ, L (r • z) ∈ s := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul a ν =>
      intro r
      simpa only [TensorProduct.smul_tmul', smul_eq_mul] using hline ν (r * a)
    | add z z' hz hz' =>
      intro r
      have h := hs (hz (2 * r)) (hz' (2 * r))
        (a := (1 / 2 : ℝ)) (b := (1 / 2 : ℝ))
        (by norm_num) (by norm_num) (by norm_num)
      convert h using 1
      rw [← map_smul, ← map_smul, ← map_add]
      congr 1
      module
  simpa only [one_smul] using hall w 1

private theorem split_translation_fixer_of_order_one
    {k : Type u} [Field k]
    {A T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {i : T.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (v : Valuation k (WithZero (Multiplicative ℤ))) (t : kˣ)
    (ht : IntegerValuation.order v t = 1)
    (D : KPApartmentData i (IntegerValuation.order v)) (C : CentralizerDatum i)
    (hD : IntegerValuation.IsOmegaCompatible v D C) (f : A ⟶ T)
    (g : rationalPoints G)
    (hcomm : ∀ a : rationalPoints A.toGrp,
      Commute g (rationalPoints.map (CommGroupScheme.groupHom f ≫ i) a))
    (x : D.Apartment) (hx : g • D.apartmentMap x = D.apartmentMap x)
    (w : V A) :
    g • D.apartmentMap
      ((rootAnnihilator i).mkQ (cocharacterMapReal f w) +ᵥ x) =
    D.apartmentMap ((rootAnnihilator i).mkQ (cocharacterMapReal f w) +ᵥ x) := by
  let L : V A →ₗ[ℝ] TranslationSpace i :=
    (rootAnnihilator i).mkQ ∘ₗ cocharacterMapReal f
  change L w ∈ D.fixedApartmentCoordinates g x
  apply convex_contains_tensor_image L (D.convex_fixedApartmentCoordinates hG hi g x)
  intro ν
  let a := CocharacterUniformizer.cocharacterPoints k A (-ν) t
  let b := CocharacterUniformizer.cocharacterPoints k T ((-ν) ≫ f) t
  let z := rationalPoints.map C.s b
  have hb : rationalPoints.map (CommGroupScheme.groupHom f) a = b := by
    dsimp [a, b, CocharacterUniformizer.cocharacterPoints, rationalPoints.map]
    simp only [Category.assoc]
    rfl
  have hcomp (y : rationalPoints T.toGrp) :
      rationalPoints.map C.j (rationalPoints.map C.s y) = rationalPoints.map i y := by
    change (y ≫ C.s.hom.hom) ≫ C.j.hom.hom = y ≫ i.hom.hom
    rw [Category.assoc]
    exact congrArg (fun e => y ≫ e.hom.hom) C.comp_eq
  have hn : (C.toNormalizer z : rationalPoints G) = rationalPoints.map i b := hcomp b
  have htrans : (IntegerValuation.centralizerTranslation v C.s C.bijective z).toAdd =
      cocharacterMapReal f ((1 : ℝ) ⊗ₜ[ℤ] ν) := by
    dsimp [z, b]
    rw [centralizerTranslation_cocharacter, ht]
    have hneg : (-ν) ≫ f = -(ν ≫ f) := (cocharacterMapInt f).map_neg ν
    rw [hneg, TensorProduct.tmul_neg, neg_neg]
  have horbit : rationalPoints.map i b • D.apartmentMap x =
      D.apartmentMap (L ((1 : ℝ) ⊗ₜ[ℤ] ν) +ᵥ x) := by
    rw [← hn, ← D.apartmentMap_smul, hD.smul_eq_vadd, htrans]
    rfl
  have hgb : Commute g (rationalPoints.map i b) := by
    have hc := hcomm a
    have he : rationalPoints.map (CommGroupScheme.groupHom f ≫ i) a =
        rationalPoints.map i b := by
      rw [← hb]
      change a ≫ (CommGroupScheme.groupHom f ≫ i).hom.hom =
        (a ≫ (CommGroupScheme.groupHom f).hom.hom) ≫ i.hom.hom
      simp only [Category.assoc]
      rfl
    rwa [he] at hc
  change g • D.apartmentMap (L ((1 : ℝ) ⊗ₜ[ℤ] ν) +ᵥ x) = _
  rw [← horbit, ← mul_smul, hgb.eq, mul_smul, hx]

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in
/-- The corrected KP independence assertion over the maximal unramified field,
with its exact published statement and no characteristic restriction. -/
theorem unramifiedSplitTranslationFixer : UnramifiedSplitTranslationFixerStatement.{u} := by
  intro F _ _ _ _ G hG S iS _hiS T iT f hf
  let : IsAffineHom G.X.hom := hG.isAffineHom
  intro hiT
  let : Mono ((GroupScheme.baseChange
      (algebraBaseMap F (inertiaFixedField F))).map iT).hom.hom.left :=
    mono_of_isMaximalSplitTorus hiT
  have hGK : IsConnectedReductive
      ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj G) :=
    hG.baseChange_of_algebraicExtension (K := inertiaFixedField F)
  let : IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := hGK.isAffineHom
  intro D C hD g hcomm x hx v hv
  rw [splitTranslationDirections, Submodule.mem_map] at hv
  obtain ⟨y, hy, rfl⟩ := hv
  obtain ⟨w, rfl⟩ := hy
  apply split_translation_fixer_of_order_one hGK hiT
    (MaximalUnramified.valuation F) (MaximalUnramified.baseUniformizerUnit F)
    (MaximalUnramified.order_baseUniformizerUnit F) D C hD
    ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map f)
    g ?_ x hx w
  intro a
  have hfK : CommGroupScheme.groupHom
        ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map f) ≫
      (GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT =
      (GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iS := by
    rw [← hf, Functor.map_comp]
    rfl
  rw [hfK]
  exact hcomm a

end Langlands.Geometry.Building
