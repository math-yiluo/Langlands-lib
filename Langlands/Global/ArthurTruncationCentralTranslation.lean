import Langlands.Global.ArthurTruncation
import Langlands.GroupScheme.Rational.CentralRootRestriction

/-! # Central translations commute with Arthur truncation

The minimal-parabolic height of a split central adelic point is annihilated by the simple roots.
The cutoffs are unchanged by that height shift and the constant terms commute with right
translation. This is the pointwise identity used to separate the central coordinate in §8 of
Lapid 2011.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory TensorProduct
open scoped CategoryTheory.MonObj

namespace Langlands.Global.ArthurTruncation

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace AdelicGroupPoints ArthurParabolicSpaces

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {T A : CommGroupScheme (Spec (CommRingCat.of F))}
  {i : T.toGrp ⟶ G} [Mono i.hom.hom.left] {ν : cocharacterLattice T}
  (hi : IsMaximalSplitTorus i) {K : Subgroup (AdelicGroupPoints F G)}
  (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K)
  (hρ : Function.Bijective (restrictToTorus F i ν ∅))

private theorem map_comp_point {P Q R : GroupScheme (Spec (CommRingCat.of F))}
    (f : P ⟶ Q) (g : Q ⟶ R) (x : AdelicGroupPoints F P) :
    map F P R (f ≫ g) x = map F Q R g (map F P Q f x) := by
  simp only [map_apply, GroupScheme.affinePointsTarget_apply, Grp.comp_hom_hom, Category.assoc]

omit [NumberField F] in
private theorem realParameterPairing_dualMap {P Q : GroupScheme (Spec (CommRingCat.of F))}
    (f : P ⟶ Q) (m : RealCharacterParameter F Q) (H : RealCharacterDual F P) :
    realParameterPairing F Q m (realCharacterDualMap F P Q f H) =
      realParameterPairing F P (rationalCharacterRestrictReal f m) H := by
  induction m using TensorProduct.inductionOn with
  | tmul t χ =>
    rw [rationalCharacterRestrictReal_tmul, realParameterPairing_tmul, realParameterPairing_tmul]
    rfl
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]

omit [NumberField F] [LocallyOfFiniteType G.X.hom] [Mono i.hom.hom.left] in
private theorem toA0_add (hT : IsSplitTorus T.toGrp)
    (a b : RealCharacterDual F (Standard.parabolicScheme i ν ∅)) :
    toA0 hT hρ (a + b) = toA0 hT hρ a + toA0 hT hρ b := by
  apply (isPerfPair_of_isSplitTorus hT).bijective_right.injective
  apply LinearMap.ext
  intro m
  obtain ⟨m, rfl⟩ := hρ.surjective m
  change pair T (restrictToTorus F i ν ∅ m) (toA0 hT hρ (a + b)) =
    pair T (restrictToTorus F i ν ∅ m) (toA0 hT hρ a + toA0 hT hρ b)
  rw [map_add, pair_toA0, pair_toA0, pair_toA0, map_add]

omit [LocallyOfFiniteType G.X.hom] [Mono i.hom.hom.left] in
/-- On the maximal split torus, evaluating the Iwasawa height gives the logarithm of the
corresponding character norm. -/
theorem eval_height_torus (α : characterLattice T) (a : AdelicGroupPoints F T.toGrp) :
    eval T α (height hi hK hρ (map F T.toGrp G i a)) =
      realParameterPairing F T.toGrp ((1 : ℝ) ⊗ₜ[ℤ] α) (characterLog F T.toGrp a) := by
  let f := torusToParabolic F i ν ∅
  let p := Standard.parabolicHom i ν ∅
  have hp : map F (Standard.parabolicScheme i ν ∅) G p
      (map F T.toGrp (Standard.parabolicScheme i ν ∅) f a) = map F T.toGrp G i a := by
    rw [← map_comp_point, torusToParabolic_comp]
  obtain ⟨m, hm⟩ := hρ.surjective ((1 : ℝ) ⊗ₜ[ℤ] α)
  rw [← hp, height, hK.height_map, characterLog_map, eval_eq_pair, ← hm, pair_toA0,
    realParameterPairing_dualMap]
  rfl

omit [Mono i.hom.hom.left] in
/-- Evaluations of the simple roots on the height of an adelic point from a central split torus
are zero. The torus is supplied inside the maximal split torus used for the height. -/
theorem height_splitCentral_mem_rootAnnihilator (f : A ⟶ T) (hA : IsSplitTorus A.toGrp)
    (hc : IsCentral (CommGroupScheme.groupHom f ≫ i)) (a : AdelicGroupPoints F A.toGrp) :
    height hi hK hρ (map F A.toGrp G (CommGroupScheme.groupHom f ≫ i) a) ∈
      rootAnnihilator T (simpleRelativeRoots i ν) := by
  apply (mem_rootAnnihilator _ _).mpr
  intro α hα
  rw [map_comp_point, eval_height_torus, characterLog_map, realParameterPairing_dualMap]
  have hroot : ((1 : ℝ) ⊗ₜ[ℤ] α : Vstar T) ∈ relativeRootSpanReal i :=
    Submodule.subset_span ⟨α, simpleRelativeRoots_subset_relativeRoots i ν hα, rfl⟩
  have hzero := LinearMap.mem_ker.mp (relativeRootSpanReal_le_centralRestrictionKer i f hA hc hroot)
  rw [hzero, map_zero, LinearMap.zero_apply]

/-- On the full adelic group, `Λᵀ(R(z) φ) = R(z)(Λᵀ φ)` for points `z` of a central split torus
inside the maximal split torus. No convergence or smoothness premise is needed for this identity
of the pointwise operators. -/
theorem truncation_rightTranslate_splitCentral (hG : IsConnectedReductive G)
    (D : RelativeRootReflectionData i) (f : A ⟶ T) (hA : IsSplitTorus A.toGrp)
    (hc : IsCentral (CommGroupScheme.groupHom f ≫ i)) (a : AdelicGroupPoints F A.toGrp)
    (Tp : V T) (φ : AdelicGroupPoints F G → ℂ) (x : AdelicGroupPoints F G) :
    let z := map F A.toGrp G (CommGroupScheme.groupHom f ≫ i) a
    truncation hG hi D hK hρ Tp (fun g => φ (g * z)) x =
      truncation hG hi D hK hρ Tp φ (x * z) := by
  classical
  let z := map F A.toGrp G (CommGroupScheme.groupHom f ≫ i) a
  change truncation hG hi D hK hρ Tp (fun g => φ (g * z)) x =
    truncation hG hi D hK hρ Tp φ (x * z)
  let P₀ := Standard.parabolicScheme i ν ∅
  let p := Standard.parabolicHom i ν ∅
  let b := map F A.toGrp T.toGrp (CommGroupScheme.groupHom f) a
  let q := map F T.toGrp P₀ (torusToParabolic F i ν ∅) b
  have hq : map F P₀ G p q = z := by
    rw [show map F P₀ G p q = map F T.toGrp G i b by
      rw [← map_comp_point, torusToParabolic_comp]]
    exact (map_comp_point _ _ _).symm
  have hcomm (g : AdelicGroupPoints F G) : Commute z g := commute_of_mem_center (hc _ a) g
  have hheight (g : AdelicGroupPoints F G) :
      height hi hK hρ (g * z) = height hi hK hρ z + height hi hK hρ g := by
    rw [← (hcomm g).eq, ← hq]
    simp only [height, p, P₀, hK.height_map_mul, hK.height_map, toA0_add]
  have hann : height hi hK hρ z ∈ rootAnnihilator T (simpleRelativeRoots i ν) :=
    height_splitCentral_mem_rootAnnihilator hi hK hρ f hA hc a
  let Δ := simpleRelativeRoots i ν
  have hcut (J : Set (characterLattice T)) (g : AdelicGroupPoints F G) :
      ArthurRelative.tauHat hG hi ν D J Δ (height hi hK hρ (g * z) - Tp) =
      ArthurRelative.tauHat hG hi ν D J Δ (height hi hK hρ g - Tp) := by
    simp only [ArthurRelative.tauHat_eq hG hi D (ν := ν) J (J₂ := Δ) Set.Subset.rfl]
    have hval (β : characterLattice T) (hβ : β ∈ Δ) :
        ArthurRelative.weight hG hi ν D Δ β (height hi hK hρ (g * z) - Tp) =
        ArthurRelative.weight hG hi ν D Δ β (height hi hK hρ g - Tp) := by
      rw [hheight, map_sub, map_add, ArthurRelative.weight_eq_zero_of_mem_rootAnnihilator
        hG hi ν D Δ β hann, zero_add, map_sub]
    refine if_congr ?_ rfl rfl
    exact forall_congr' fun β => forall_congr' fun hβ => by rw [hval β hβ.1]
  have hterm (J : Set (characterLattice T)) (g : AdelicGroupPoints F G) :
      constantTerm F i ν J (fun y => φ (y * z)) g = constantTerm F i ν J φ (g * z) := by
    unfold constantTerm subgroupConstantTerm
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [mul_assoc]
  unfold truncation
  refine Finset.sum_congr rfl fun S _ => congrArg (_ * ·) ?_
  refine tsum_congr fun c => ?_
  rw [← mul_assoc ((c.out : rationalSubgroup F G) : AdelicGroupPoints F G) x z, hcut, hterm]

/-- Pointwise commutation with central translations, as used for the full-to-norm-one separation. -/
def TruncationCentralTranslationStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (T A : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]
    (ν : cocharacterLattice T) (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (D : RelativeRootReflectionData i) (K : Subgroup (AdelicGroupPoints F G))
    (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K)
    (hρ : Function.Bijective (restrictToTorus F i ν ∅))
    (f : A ⟶ T), IsSplitTorus A.toGrp → IsCentral (CommGroupScheme.groupHom f ≫ i) →
    ∀ (a : AdelicGroupPoints F A.toGrp) (Tp : V T) (φ : AdelicGroupPoints F G → ℂ) (x : AdelicGroupPoints F G),
      let z := map F A.toGrp G (CommGroupScheme.groupHom f ≫ i) a
      truncation hG hi D hK hρ Tp (fun g => φ (g * z)) x =
        truncation hG hi D hK hρ Tp φ (x * z)

theorem truncationCentralTranslation : TruncationCentralTranslationStatement.{u} := by
  intro F _ _ G _ _ T A i _ ν hG hi D K hK hρ f hA hc a Tp φ x
  exact truncation_rightTranslate_splitCentral hi hK hρ hG D f hA hc a Tp φ x

end Langlands.Global.ArthurTruncation
