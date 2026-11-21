import Langlands.Global.AdelicSplitCenterHaar
import Langlands.Global.AdelicSplitCenterQuotient

/-! # The full rational adelic quotient as a product

The positive/norm-one decomposition of the ambient group descends to a homeomorphism on
rational quotients and preserves the chosen quotient measures with normalized positive Haar.
This is the measure transport used before Fourier analysis in Lapid 2011, §8.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Set
open scoped CategoryTheory.MonObj Topology

namespace Langlands.Global.PositiveRealTorus

open Langlands.GroupScheme AdelicGroupPoints

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
  (hi : Function.Injective (characterRestrict i)) [(characterRestrict i).range.FiniteIndex]
  (I : Type u) [Fintype I] (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I)
  (hc : IsCentral i)

omit [IsAffine G.X.left] in
private theorem positiveFactor_principal (γ : rationalSubgroup F G) :
    positiveFactor F G T i hi I e γ = 1 :=
  positiveFactor_normOne F G T i hi I e
    ⟨γ, rationalSubgroup_le_normOneSubgroup F G γ.property⟩

private def principalProjection (γ : rationalSubgroup F G) : rationalNormOneSubgroup F G :=
  ⟨normOneProjection F G T i hi I e hc γ, by
    obtain ⟨q, hq⟩ := γ.property
    rw [← hq, normOneProjection_rational]
    exact ⟨q, rfl⟩⟩

private theorem principalProjection_val (γ : rationalSubgroup F G) :
    (principalProjection F G T i hi I e hc γ).val.val = γ.val :=
  congrArg Subtype.val (normOneProjection_normOne F G T i hi I e hc
    ⟨γ, rationalSubgroup_le_normOneSubgroup F G γ.property⟩)

private theorem principalProjection_inclusion (γ : rationalNormOneSubgroup F G) :
    principalProjection F G T i hi I e hc (rationalNormOneSubgroupInclusion F G γ) = γ :=
  Subtype.ext (normOneProjection_normOne F G T i hi I e hc γ.val)

private theorem fullQuotientCoordinates_invariant (γ : rationalSubgroup F G)
    (x : AdelicGroupPoints F G) :
    (positiveFactor F G T i hi I e ((γ : AdelicGroupPoints F G) * x),
      LeftCosetSpace.mk (rationalNormOneSubgroup F G)
        (normOneProjection F G T i hi I e hc ((γ : AdelicGroupPoints F G) * x))) =
    (positiveFactor F G T i hi I e x,
      LeftCosetSpace.mk (rationalNormOneSubgroup F G) (normOneProjection F G T i hi I e hc x)) := by
  apply Prod.ext
  · rw [map_mul, positiveFactor_principal, one_mul]
  · let π := normOneProjection F G T i hi I e hc
    let δ := principalProjection F G T i hi I e hc γ
    change LeftCosetSpace.mk (rationalNormOneSubgroup F G) (π (γ.val * x)) =
      LeftCosetSpace.mk (rationalNormOneSubgroup F G) (π x)
    rw [map_mul]
    change LeftCosetSpace.mk (rationalNormOneSubgroup F G) (δ.val * π x) = _
    exact LeftCosetSpace.mk_subgroup_mul (rationalNormOneSubgroup F G) δ (π x)

/-- Actual multiplication of a positive central point and a norm-one class identifies the full
rational quotient with the positive points times the norm-one rational quotient. -/
def rationalQuotientDecomposition :
    intrinsicSubgroup F T × NormOneRationalQuotient F G ≃ₜ RationalQuotient F G where
  toFun p := LeftCosetSpace.rightTranslate (rationalSubgroup F G)
    (positivePointMap F G T i p.1) (normOneQuotientInclusion F G p.2)
  invFun := LeftCosetSpace.lift (rationalSubgroup F G) (fun x =>
    (positiveFactor F G T i hi I e x, LeftCosetSpace.mk (rationalNormOneSubgroup F G)
      (normOneProjection F G T i hi I e hc x)))
    (fullQuotientCoordinates_invariant F G T i hi I e hc)
  left_inv := by
    rintro ⟨a, q⟩
    obtain ⟨n, rfl⟩ := LeftCosetSpace.mk_surjective (rationalNormOneSubgroup F G) q
    change (positiveFactor F G T i hi I e ((n : AdelicGroupPoints F G) * positivePointMap F G T i a),
      LeftCosetSpace.mk (rationalNormOneSubgroup F G)
        (normOneProjection F G T i hi I e hc ((n : AdelicGroupPoints F G) *
          positivePointMap F G T i a))) = (a, LeftCosetSpace.mk (rationalNormOneSubgroup F G) n)
    rw [(positivePointMap_commute F G T i hc a (n : AdelicGroupPoints F G)).eq.symm,
      positiveFactor_mul_normOne, map_mul, normOneProjection_positivePointMap,
      normOneProjection_normOne, one_mul]
  right_inv := by
    intro q
    obtain ⟨x, rfl⟩ := LeftCosetSpace.mk_surjective (rationalSubgroup F G) q
    change LeftCosetSpace.mk (rationalSubgroup F G)
      ((normOneProjection F G T i hi I e hc x : AdelicGroupPoints F G) *
        positivePointMap F G T i (positiveFactor F G T i hi I e x)) =
      LeftCosetSpace.mk (rationalSubgroup F G) x
    rw [(positivePointMap_commute F G T i hc _ _).eq.symm, normOneProjection_apply,
      positivePointMap_mul_normOneFactor]
  continuous_toFun := by
    rw [← (IsOpenQuotientMap.id.prodMap
      (LeftCosetSpace.isOpenQuotientMap_mk (rationalNormOneSubgroup F G))).continuous_comp_iff]
    exact (LeftCosetSpace.continuous_mk (rationalSubgroup F G)).comp
      ((continuous_subtype_val.comp continuous_snd).mul
        ((positivePointMap F G T i).continuous.comp continuous_fst))
  continuous_invFun := by
    apply LeftCosetSpace.continuous_lift
    exact (positiveFactor F G T i hi I e).continuous.prodMk
      ((LeftCosetSpace.continuous_mk (rationalNormOneSubgroup F G)).comp
        (normOneProjection F G T i hi I e hc).continuous)

@[simp] theorem rationalQuotientDecomposition_mk (a : intrinsicSubgroup F T)
    (n : normOneSubgroup F G) :
    rationalQuotientDecomposition F G T i hi I e hc
      (a, LeftCosetSpace.mk (rationalNormOneSubgroup F G) n) =
    LeftCosetSpace.mk (rationalSubgroup F G) (positivePointMap F G T i a * n) := by
  change LeftCosetSpace.mk (rationalSubgroup F G)
    ((n : AdelicGroupPoints F G) * positivePointMap F G T i a) = _
  rw [(positivePointMap_commute F G T i hc a (n : AdelicGroupPoints F G)).eq]

@[simp] theorem rationalQuotientDecomposition_symm_mk (x : AdelicGroupPoints F G) :
    (rationalQuotientDecomposition F G T i hi I e hc).symm
      (LeftCosetSpace.mk (rationalSubgroup F G) x) =
    (positiveFactor F G T i hi I e x, LeftCosetSpace.mk (rationalNormOneSubgroup F G)
      (normOneProjection F G T i hi I e hc x)) := rfl

variable [LocallyOfFiniteType G.X.hom]

/-- Pulling a measurable norm-one transversal back under the norm-one projection gives a
measurable transversal for the full principal action. -/
private theorem isFundamentalDomain_preimage_normOneProjection (s : Set (normOneSubgroup F G))
    (hs : MeasurableSet s)
    (huniq : ∀ n : normOneSubgroup F G, ∃! γ : rationalNormOneSubgroup F G, γ.val * n ∈ s) :
    IsFundamentalDomain (rationalSubgroup F G) (normOneProjection F G T i hi I e hc ⁻¹' s)
      (Measure.haar : Measure (AdelicGroupPoints F G)) := by
  let π := normOneProjection F G T i hi I e hc
  let pr := principalProjection F G T i hi I e hc
  refine IsFundamentalDomain.mk' (π.continuous.measurable hs).nullMeasurableSet (fun x => ?_)
  obtain ⟨γ, hγ, hγu⟩ := huniq (π x)
  have hm (δ : rationalSubgroup F G) : δ.val * x ∈ π ⁻¹' s ↔ (pr δ).val * π x ∈ s := by
    change π (δ.val * x) ∈ s ↔ (pr δ).val * π x ∈ s
    rw [map_mul]
    rfl
  let γG := rationalNormOneSubgroupInclusion F G γ
  refine ⟨γG, (hm γG).mpr ?_, fun δ hδ => ?_⟩
  · change (principalProjection F G T i hi I e hc
      (rationalNormOneSubgroupInclusion F G γ)).val * π x ∈ s
    rwa [principalProjection_inclusion F G T i hi I e hc γ]
  · apply Subtype.ext
    calc δ.val = (pr δ).val.val := (principalProjection_val F G T i hi I e hc δ).symm
      _ = γG.val := congrArg (fun t : rationalNormOneSubgroup F G => t.val.val)
        (hγu _ ((hm δ).mp hδ))

/-- The full quotient Haar measure is the pushforward of the product of normalized positive
Haar and the existing norm-one quotient Haar. There is no additional unknown measure scalar. -/
theorem measurePreserving_rationalQuotientDecomposition :
    MeasurePreserving (rationalQuotientDecomposition F G T i hi I e hc)
      ((normalizedPositiveHaarMeasure F G T i hi I e hc).prod
        (normOneRationalQuotientHaarMeasure F G)) (rationalQuotientHaarMeasure F G) := by
  let E := normOneDecomposition F G T i hi I e
  let Q := rationalQuotientDecomposition F G T i hi I e hc
  let π := normOneProjection F G T i hi I e hc
  let μA := normalizedPositiveHaarMeasure F G T i hi I e hc
  let μN : Measure (normOneSubgroup F G) := Measure.haar
  let μG : Measure (AdelicGroupPoints F G) := Measure.haar
  let : SigmaFinite μA := normalizedPositiveHaarMeasure_sigmaFinite F G T i hi I e hc
  obtain ⟨s, hs, huniq⟩ := LeftCosetSpace.exists_measurable_fundamentalDomain
    (rationalNormOneSubgroup F G) (isDiscrete_rationalNormOneSubgroup F G)
  have hfdN : IsFundamentalDomain (rationalNormOneSubgroup F G) s μN :=
    IsFundamentalDomain.mk' hs.nullMeasurableSet huniq
  have hfdG := isFundamentalDomain_preimage_normOneProjection F G T i hi I e hc s hs huniq
  have hpre : E ⁻¹' (π ⁻¹' s) = (univ : Set (intrinsicSubgroup F T)) ×ˢ s := by
    ext p
    change π (positivePointMap F G T i p.1 * p.2) ∈ s ↔ p ∈ _
    simp only [map_mul, π, normOneProjection_positivePointMap, normOneProjection_normOne,
      one_mul, mem_prod, mem_univ, true_and]
  have hamb : Measure.map E (μA.prod μN) = μG :=
    (measurePreserving_normOneDecomposition F G T i hi I e hc).map_eq
  have hS : MeasurableSet (π ⁻¹' s) := π.continuous.measurable hs
  have hres : μG.restrict (π ⁻¹' s) = Measure.map E (μA.prod (μN.restrict s)) := by
    rw [← hamb, Measure.restrict_map E.continuous.measurable hS, hpre]
    congr 1
    simpa only [Measure.restrict_univ] using
      (Measure.prod_restrict («μ» := μA) (ν := μN) univ s).symm
  let qN := LeftCosetSpace.mk (rationalNormOneSubgroup F G)
  let qG := LeftCosetSpace.mk (rationalSubgroup F G)
  let m := Prod.map (id : intrinsicSubgroup F T → _) qN
  have hm := (MeasurePreserving.id μA).prod
    (LeftCosetSpace.measurePreserving_mk (rationalNormOneSubgroup F G) μN s)
  refine ⟨Q.continuous.measurable, ?_⟩
  rw [normOneRationalQuotientHaarMeasure_eq F G hfdN, rationalQuotientHaarMeasure_eq F G hfdG]
  change Measure.map Q (μA.prod (LeftCosetSpace.quotientMeasure _ μN s)) =
    Measure.map qG (μG.restrict (π ⁻¹' s))
  rw [← hm.map_eq, hres, Measure.map_map Q.continuous.measurable hm.measurable,
    Measure.map_map (LeftCosetSpace.measurable_mk (rationalSubgroup F G)) E.continuous.measurable]
  have heq : (Q ∘ m) = (qG ∘ E) := by
    funext p
    exact rationalQuotientDecomposition_mk F G T i hi I e hc p.1 p.2
  exact congrArg (fun f => Measure.map f (μA.prod (μN.restrict s))) heq

end Langlands.Global.PositiveRealTorus
