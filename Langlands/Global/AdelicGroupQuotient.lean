import Langlands.Global.AdelicGroupRationalTopology
import Langlands.Global.LeftCosetSpace

/-! # Actual rational and norm-one adelic homogeneous quotients -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain Topology
open scoped CategoryTheory.MonObj

namespace Langlands.Global.AdelicGroupPoints

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))

/-- The actual left quotient by the principal rational subgroup. -/
abbrev RationalQuotient := LeftCosetSpace (rationalSubgroup F G)

/-- The actual rational quotient of the norm-one adelic subgroup. -/
abbrev NormOneRationalQuotient := LeftCosetSpace (rationalNormOneSubgroup F G)

/-- The natural map from the norm-one rational quotient to the full rational quotient. -/
def normOneQuotientInclusion : NormOneRationalQuotient F G → RationalQuotient F G :=
  Quotient.map' (fun x : normOneSubgroup F G => (x : AdelicGroupPoints F G))
    fun x y h => by
      apply QuotientGroup.rightRel_apply.mpr
      rcases QuotientGroup.rightRel_apply.mp h with ⟨q, hq⟩
      exact ⟨q, congrArg (fun z : normOneSubgroup F G =>
        (z : AdelicGroupPoints F G)) hq⟩

@[simp]
theorem normOneQuotientInclusion_mk (x : normOneSubgroup F G) :
    normOneQuotientInclusion F G (LeftCosetSpace.mk (rationalNormOneSubgroup F G) x) =
      LeftCosetSpace.mk (rationalSubgroup F G) (x : AdelicGroupPoints F G) := rfl

/-- Rational equivalence of two norm-one points is already equivalence inside that subgroup. -/
theorem normOneQuotientInclusion_injective :
    Function.Injective (normOneQuotientInclusion F G) := by
  intro q r
  refine Quotient.inductionOn₂ q r ?_
  intro x y h
  apply (LeftCosetSpace.mk_eq_mk_iff (rationalNormOneSubgroup F G) x y).mpr
  change LeftCosetSpace.mk (rationalSubgroup F G) (x : AdelicGroupPoints F G) =
    LeftCosetSpace.mk (rationalSubgroup F G) (y : AdelicGroupPoints F G) at h
  rcases (LeftCosetSpace.mk_eq_mk_iff (rationalSubgroup F G) _ _).mp h with ⟨z, hz⟩
  refine ⟨z, ?_⟩
  apply Subtype.ext
  exact hz

/-- The actual quotient inclusion is continuous by the quotient universal property. -/
theorem continuous_normOneQuotientInclusion :
    Continuous (normOneQuotientInclusion F G) := by
  apply (LeftCosetSpace.continuous_iff (rationalNormOneSubgroup F G)).mpr
  exact (LeftCosetSpace.continuous_mk (rationalSubgroup F G)).comp continuous_subtype_val

/-- A full rational class comes from norm-one points exactly when its representatives are norm one. -/
theorem preimage_range_normOneQuotientInclusion :
    LeftCosetSpace.mk (rationalSubgroup F G) ⁻¹'
      Set.range (normOneQuotientInclusion F G) =
        (normOneSubgroup F G : Set (AdelicGroupPoints F G)) := by
  ext x
  constructor
  · rintro ⟨q, hq⟩
    obtain ⟨y, rfl⟩ := LeftCosetSpace.mk_surjective (rationalNormOneSubgroup F G) q
    have h := (LeftCosetSpace.mk_eq_mk_iff (rationalSubgroup F G) _ _).mp hq
    have hm := (normOneSubgroup F G).mul_mem
      (rationalSubgroup_le_normOneSubgroup F G h) y.property
    change x ∈ normOneSubgroup F G
    simpa only [inv_mul_cancel_right] using hm
  · intro hx
    exact ⟨LeftCosetSpace.mk (rationalNormOneSubgroup F G) ⟨x, hx⟩, rfl⟩

/-- Saturated inverse images of quotient subsets are exactly their subgroup inclusions. -/
theorem preimage_normOneQuotientInclusion_image (s : Set (NormOneRationalQuotient F G)) :
    LeftCosetSpace.mk (rationalSubgroup F G) ⁻¹' (normOneQuotientInclusion F G '' s) =
      (fun x : normOneSubgroup F G => (x : AdelicGroupPoints F G)) ''
        (LeftCosetSpace.mk (rationalNormOneSubgroup F G) ⁻¹' s) := by
  ext x
  constructor
  · rintro ⟨q, hq, hqx⟩
    have hx : x ∈ normOneSubgroup F G := by
      change x ∈ (normOneSubgroup F G : Set (AdelicGroupPoints F G))
      rw [← preimage_range_normOneQuotientInclusion F G]
      exact ⟨q, hqx⟩
    refine ⟨⟨x, hx⟩, ?_, rfl⟩
    have he : LeftCosetSpace.mk (rationalNormOneSubgroup F G) ⟨x, hx⟩ = q := by
      apply normOneQuotientInclusion_injective F G
      exact hqx.symm
    change LeftCosetSpace.mk (rationalNormOneSubgroup F G) ⟨x, hx⟩ ∈ s
    rw [he]
    exact hq
  · rintro ⟨y, hy, rfl⟩
    exact ⟨LeftCosetSpace.mk (rationalNormOneSubgroup F G) y, hy, rfl⟩

/-- The actual norm-one rational quotient is a closed subspace of the full rational quotient. -/
theorem isClosedEmbedding_normOneQuotientInclusion :
    IsClosedEmbedding (normOneQuotientInclusion F G) := by
  apply IsClosedEmbedding.of_continuous_injective_isClosedMap
    (continuous_normOneQuotientInclusion F G) (normOneQuotientInclusion_injective F G)
  intro s hs
  apply (LeftCosetSpace.isQuotientMap_mk (rationalSubgroup F G)).isCoinducing.isClosed_preimage.mp
  rw [preimage_normOneQuotientInclusion_image]
  exact (isClosed_normOneSubgroup F G).isClosedMap_subtype_val _
    (hs.preimage (LeftCosetSpace.continuous_mk (rationalNormOneSubgroup F G)))

/-- The quotient inclusion intertwines positive right translation by norm-one elements. -/
theorem normOneQuotientInclusion_rightTranslate (g : normOneSubgroup F G)
    (q : NormOneRationalQuotient F G) :
    normOneQuotientInclusion F G
      (LeftCosetSpace.rightTranslate (rationalNormOneSubgroup F G) g q) =
        LeftCosetSpace.rightTranslate (rationalSubgroup F G) (g : AdelicGroupPoints F G)
          (normOneQuotientInclusion F G q) := by
  induction q using Quotient.inductionOn with
  | _ x => rfl

/-- Functions on the full rational quotient are exactly rational-left-invariant functions. -/
def rationalQuotientFunctionEquiv (E : Type v) :
    (RationalQuotient F G → E) ≃
      {f : AdelicGroupPoints F G → E // ∀ (q : RationalGroupPoints F G) (x),
        f (rational F G q * x) = f x} where
  toFun f := ⟨fun x => f (LeftCosetSpace.mk (rationalSubgroup F G) x), by
    intro q x
    exact congrArg f (LeftCosetSpace.mk_subgroup_mul (rationalSubgroup F G)
      ⟨rational F G q, ⟨q, rfl⟩⟩ x)⟩
  invFun f := LeftCosetSpace.lift (rationalSubgroup F G) f.val (by
    rintro ⟨_, q, rfl⟩ x
    exact f.property q x)
  left_inv f := by
    funext q
    induction q using Quotient.inductionOn with
    | _ x => rfl
  right_inv f := by
    apply Subtype.ext
    rfl

@[simp]
theorem rationalQuotientFunctionEquiv_apply (E : Type v) (f : RationalQuotient F G → E)
    (x : AdelicGroupPoints F G) :
    (rationalQuotientFunctionEquiv F G E f).val x =
      f (LeftCosetSpace.mk (rationalSubgroup F G) x) := rfl

/-- Pullback gives precisely the positive right action on rational-invariant functions. -/
theorem rationalQuotientFunctionEquiv_rightTranslate (E : Type v)
    (f : RationalQuotient F G → E) (g x : AdelicGroupPoints F G) :
    (rationalQuotientFunctionEquiv F G E
      (fun q => f (LeftCosetSpace.rightTranslate (rationalSubgroup F G) g q))).val x =
        (rationalQuotientFunctionEquiv F G E f).val (x * g) := rfl

variable [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

/-- The actual full rational homogeneous quotient is Hausdorff. -/
instance rationalQuotientT2Space : T2Space (RationalQuotient F G) := by
  let : IsClosed (rationalSubgroup F G : Set (AdelicGroupPoints F G)) :=
    rationalSubgroup_isClosed F G
  infer_instance

/-- The actual norm-one rational quotient is Hausdorff. -/
instance normOneRationalQuotientT2Space : T2Space (NormOneRationalQuotient F G) := by
  let : IsClosed (rationalNormOneSubgroup F G : Set (normOneSubgroup F G)) :=
    rationalNormOneSubgroup_isClosed F G
  infer_instance

/-- Local compactness descends through the open full rational quotient map. -/
instance rationalQuotientLocallyCompactSpace : LocallyCompactSpace (RationalQuotient F G) :=
  inferInstance

/-- Local compactness descends through the open norm-one rational quotient map. -/
instance normOneRationalQuotientLocallyCompactSpace :
    LocallyCompactSpace (NormOneRationalQuotient F G) := inferInstance

end Langlands.Global.AdelicGroupPoints
