import Langlands.Geometry.Building.IntegerValuationBuildingData
import Langlands.Geometry.Building.ReflectionRealizationUniqueness
import Langlands.GroupScheme.Rational.RelativeRootsCharacterSpan

/-! # Centralizer points fixing an apartment point

For integer-valued building data over any field, a point `z` of the actual centralizer
`Z = Z_G(S)` whose image lies in `G(k)^1` and which fixes one point of the apartment lies in
`Z(k)^1`. Joint spanning by relative roots and restricted rational characters makes the
character valuation of `z` vanish.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.LinearAlgebra.RationalSpan Langlands.BruhatTits

namespace Langlands.Geometry.Building

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}

/-- Evaluation at a real cocharacter as an integral linear form on the characters. -/
def evalAtLinear (T : CommGroupScheme (Spec (CommRingCat.of k))) (w : V T) :
    characterLattice T →ₗ[ℤ] ℝ where
  toFun χ := eval T χ w
  map_add' χ ψ := by
    simp only [eval_eq_pair, TensorProduct.tmul_add, map_add, LinearMap.add_apply]
  map_smul' n χ := by
    rw [eval_zsmul_apply, RingHom.id_apply, zsmul_eq_mul]

@[simp] theorem evalAtLinear_apply (w : V T) (χ : characterLattice T) :
    evalAtLinear T w χ = eval T χ w :=
  rfl

/-- In a connected reductive group, a real cocharacter of a maximal split torus annihilated
by every relative root and by every restricted rational character of `G` is zero. -/
theorem eq_zero_of_eval_relativeRoots_of_eval_torusCharacterRestrict
    (hG : IsConnectedReductive G) (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i) {w : V T}
    (hroot : haveI := hG.isAffineHom; ∀ a ∈ relativeRoots i, eval T a w = 0)
    (hchar : ∀ χ : rationalCharacters G, eval T (torusCharacterRestrict i χ) w = 0) :
    w = 0 := by
  let := hG.isAffineHom
  let L := (evalAtLinear T w).liftBaseChange ℚ
  have hL : L = 0 := by
    apply LinearMap.ext_on (relativeRootsRestrictedCharactersSpan k G hG T i hi)
    rintro _ ⟨β, hβ, rfl⟩
    rw [LinearMap.zero_apply, toRat_apply, LinearMap.liftBaseChange_one_tmul,
      evalAtLinear_apply]
    rcases hβ with hβ | ⟨χ, rfl⟩
    · exact hroot β hβ
    · exact hchar χ
  apply eq_zero_of_forall_eval_eq_zero hi.isSplitSubtorus.1
  intro χ
  have h := LinearMap.congr_fun hL (toRat χ)
  rwa [LinearMap.zero_apply, toRat_apply, LinearMap.liftBaseChange_one_tmul,
    evalAtLinear_apply] at h

namespace IntegerValuationBuildingData

variable {v : Valuation k (WithZero (Multiplicative ℤ))} [IsAffineHom G.X.hom]
  (B : IntegerValuationBuildingData v G)

/-- Restricting a rational character of `G` to `S` through the centralizer agrees with
restricting it directly. -/
theorem characterRestriction_characterRestrict (χ : rationalCharacters G) :
    Cartan.characterRestriction B.centralizer.s (characterRestrict B.centralizer.j χ) =
      torusCharacterRestrict B.i χ := by
  have h : characterRestrict B.centralizer.s (characterRestrict B.centralizer.j χ) =
      characterRestrict B.i χ := by
    rw [← AddMonoidHom.comp_apply, ← characterRestrict_comp, B.centralizer.comp_eq]
  simp only [Cartan.characterRestriction, torusCharacterRestrict, AddMonoidHom.comp_apply, h]

/-- A centralizer point in `G(k)^1` fixing one apartment point lies in `Z(k)^1`. -/
theorem mem_characterValuationKernel_of_smul_eq {z : rationalPoints B.centralizer.Z}
    (hz : rationalPoints.map B.centralizer.j z ∈ characterValuationKernel v G)
    {x : B.Apartment} (hx : B.centralizer.toNormalizer z • x = x) :
    z ∈ characterValuationKernel v B.centralizer.Z := by
  rw [← IntegerValuation.centralizerValuation_ker v B.centralizer.s B.centralizer.bijective,
    MonoidHom.mem_ker]
  set w := (IntegerValuation.centralizerValuation v B.centralizer.s
    B.centralizer.bijective z).toAdd with hw
  suffices hw0 : w = 0 by
    rw [← ofAdd_toAdd (IntegerValuation.centralizerValuation v B.centralizer.s
      B.centralizer.bijective z), ← hw, hw0, ofAdd_zero]
  apply eq_zero_of_eval_relativeRoots_of_eval_torusCharacterRestrict
    B.isConnectedReductive B.i B.isMaximalSplitTorus
  · intro a ha
    have h1 := B.isOmegaCompatible.smul_eq_vadd z x
    rw [hx] at h1
    have h2 : (Submodule.Quotient.mk (IntegerValuation.centralizerTranslation v
        B.centralizer.s B.centralizer.bijective z).toAdd : TranslationSpace B.i) = 0 :=
      vadd_right_cancel x (h1.symm.trans (zero_vadd _ x).symm)
    have h4 := mem_rootAnnihilator.1 ((Submodule.Quotient.mk_eq_zero _).1 h2) a ha
    rwa [IntegerValuation.centralizerTranslation_toAdd, map_neg, neg_eq_zero] at h4
  · intro χ
    rw [← B.characterRestriction_characterRestrict χ, hw,
      IntegerValuation.centralizerValuation_spec, rationalCharacterEval_characterRestrict]
    have h := (mem_characterValuationKernel.mp hz) χ
    have h' : IntegerValuation.orderUnits v
        (rationalCharacterEval χ (rationalPoints.map B.centralizer.j z)) = 1 :=
      (IntegerValuation.orderUnits_eq_one_iff v _).2 h
    simp only [IntegerValuation.order, h', toAdd_one, Int.cast_zero]

/-- On one apartment point, `Z(k)^1` is exactly the set of centralizer points whose image
lies in `G(k)^1` and which fix that point. -/
theorem mem_characterValuationKernel_iff_smul_eq (z : rationalPoints B.centralizer.Z)
    (x : B.Apartment) :
    z ∈ characterValuationKernel v B.centralizer.Z ↔
      rationalPoints.map B.centralizer.j z ∈ characterValuationKernel v G ∧
        B.centralizer.toNormalizer z • x = x :=
  ⟨fun hz => ⟨IntegerValuation.map_mem_characterValuationKernel v B.centralizer.j hz,
      B.isOmegaCompatible.smul_eq_self hz x⟩,
    fun h => B.mem_characterValuationKernel_of_smul_eq h.1 h.2⟩

/-- If the apartment embeds in the reduced building, a centralizer point whose image lies in
`K_x` lies in `Z(k)^1`. -/
theorem mem_characterValuationKernel_of_mem_oneStabilizer
    (hinj : Function.Injective B.apartmentMap) {z : rationalPoints B.centralizer.Z}
    {x : B.Apartment}
    (hz : rationalPoints.map B.centralizer.j z ∈ B.oneStabilizer (B.apartmentMap x)) :
    z ∈ characterValuationKernel v B.centralizer.Z := by
  obtain ⟨hz1, hzx⟩ := B.mem_oneStabilizer.mp hz
  apply B.mem_characterValuationKernel_of_smul_eq hz1 (x := x)
  apply hinj
  rw [← B.normalizer_smul_apartmentMap, CentralizerDatum.toNormalizer,
    coe_centralizerToNormalizer]
  exact hzx

/-- If the apartment embeds in the reduced building, the centralizer points with image in
`K_x` are exactly `Z(k)^1`. -/
theorem comap_oneStabilizer_eq_characterValuationKernel
    (hinj : Function.Injective B.apartmentMap) (x : B.Apartment) :
    (B.oneStabilizer (B.apartmentMap x)).comap (rationalPoints.map B.centralizer.j) =
      characterValuationKernel v B.centralizer.Z := by
  ext z
  exact ⟨fun hz => B.mem_characterValuationKernel_of_mem_oneStabilizer hinj hz,
    fun hz => B.map_mem_oneStabilizer hz x⟩

end IntegerValuationBuildingData

end Langlands.Geometry.Building
