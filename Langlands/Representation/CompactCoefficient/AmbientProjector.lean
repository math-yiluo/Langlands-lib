import Langlands.Representation.CompactCoefficient.IsotypicTransport
import Langlands.Representation.CompactCoefficient.TotalProjector

/-!
# Ambient equivariance of total compact-isotypic projectors

Conjugation in an ambient group permutes the compact-coefficient classes of
a normal subgroup. Intrinsic component covariance therefore makes their
pointwise finite sum equivariant for the ambient action.
-/

noncomputable section

namespace Langlands

universe uG uH uC uV uW

namespace CompactCoefficientClass

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {H : Type uH} [Group H] [TopologicalSpace H]

/-- Covariance of all intrinsic components implies covariance of their total,
with the class indices transported through the actual group equivalence. -/
theorem pointwiseFiniteSum_isotypic_covariant
    (e : H ≃ₜ* G)
    {A : SmoothRep.{0, uG, uV} ℂ G} {B : SmoothRep.{0, uH, uW} ℂ H}
    (P : CompactCoefficientClass.{uG, uC} G →
      A.representation.IntertwiningMap A.representation)
    (Q : CompactCoefficientClass.{uH, uC} H →
      B.representation.IntertwiningMap B.representation)
    (hfiniteP : ∀ v : A, Function.HasFiniteSupport (fun c => P c v))
    (hfiniteQ : ∀ v : B, Function.HasFiniteSupport (fun c => Q c v))
    (hidP : ∀ c, IsIdempotentElem (P c).toLinearMap)
    (hidQ : ∀ c, IsIdempotentElem (Q c).toLinearMap)
    (hrP : ∀ c, (P c).range = isotypicSubrepresentation c A)
    (hkP : ∀ c, (P c).ker = annihilatorSubrepresentation c A)
    (hrQ : ∀ c, (Q c).range = isotypicSubrepresentation c B)
    (hkQ : ∀ c, (Q c).ker = annihilatorSubrepresentation c B)
    (f : (SmoothRep.pullback e A).representation.IntertwiningMap B.representation)
    (v : A) :
    pointwiseFiniteSum Q hfiniteQ (f v) = f (pointwiseFiniteSum P hfiniteP v) :=
  pointwiseFiniteSum_covariant (fun c => SmoothRep.pullbackMap e (P c))
    hfiniteP Q hfiniteQ f.toLinearMap (pullbackEquiv e)
    (fun c w => (isotypicProjectors_covariant e c (P c) (Q (pullbackEquiv e c))
      (hidP c) (hidQ _) (hrP c) (hkP c) (hrQ _) (hkQ _) f w).symm) v

end CompactCoefficientClass

namespace SmoothRep

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- Restriction to an actual subgroup, retaining the ambient carrier. -/
def restrictSubgroup (N : Subgroup G) (A : SmoothRep.{0, uG, uV} ℂ G) :
    SmoothRep.{0, uG, uV} ℂ N :=
  of (A.representation.comp N.subtype)
    (isSmooth_comp N.subtype continuous_subtype_val A.isSmooth)

/-- Restriction of an actual intertwiner retains its linear map. -/
def restrictSubgroupMap (N : Subgroup G)
    {A : SmoothRep.{0, uG, uV} ℂ G} {B : SmoothRep.{0, uG, uW} ℂ G}
    (f : A.representation.IntertwiningMap B.representation) :
    (restrictSubgroup N A).representation.IntertwiningMap
      (restrictSubgroup N B).representation where
  toLinearMap := f.toLinearMap
  isIntertwining' n := f.isIntertwining' n.val

variable [IsTopologicalGroup G] (N : Subgroup G) [N.Normal]

/-- Inverse conjugation on a normal subgroup, with its actual subspace topology. -/
def normalSubgroupInverseConjugation (g : G) : N ≃ₜ* N where
  toFun n := ⟨g⁻¹ * n.val * g, Subgroup.Normal.conj_mem' inferInstance _ n.property g⟩
  invFun n := ⟨g * n.val * g⁻¹, Subgroup.Normal.conj_mem inferInstance _ n.property g⟩
  left_inv n := by ext; simp [mul_assoc]
  right_inv n := by ext; simp [mul_assoc]
  map_mul' n m := by ext; simp [mul_assoc]
  continuous_toFun := (continuous_const.mul continuous_subtype_val |>.mul
    continuous_const).subtype_mk _
  continuous_invFun := (continuous_const.mul continuous_subtype_val |>.mul
    continuous_const).subtype_mk _

/-- The action of `g` intertwines the restriction pulled back by inverse
conjugation with the original restriction. -/
def restrictionConjugationMap (A : SmoothRep.{0, uG, uV} ℂ G) (g : G) :
    Representation.IntertwiningMap
      (pullback (normalSubgroupInverseConjugation N g) (restrictSubgroup N A)).representation
      (restrictSubgroup N A).representation where
  toLinearMap := A.representation g
  isIntertwining' n := by
    change (A.representation g).comp (A.representation (g⁻¹ * n.val * g)) =
      (A.representation n.val).comp (A.representation g)
    change A.representation g * A.representation (g⁻¹ * n.val * g) =
      A.representation n.val * A.representation g
    rw [← map_mul, ← map_mul]
    simp [mul_assoc]

end SmoothRep

namespace CompactCoefficientClass

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (N : Subgroup G) [N.Normal]
  {A : SmoothRep.{0, uG, uV} ℂ G}
  (P : CompactCoefficientClass.{uG, uC} N →
    (SmoothRep.restrictSubgroup N A).representation.IntertwiningMap
      (SmoothRep.restrictSubgroup N A).representation)
  (hfinite : ∀ v : A, Function.HasFiniteSupport (fun c => P c v))
  (hid : ∀ c, IsIdempotentElem (P c).toLinearMap)
  (hr : ∀ c, (P c).range = isotypicSubrepresentation c (SmoothRep.restrictSubgroup N A))
  (hk : ∀ c, (P c).ker = annihilatorSubrepresentation c (SmoothRep.restrictSubgroup N A))

include hid hr hk

/-- The total of intrinsic projectors on a normal subgroup commutes with
the whole ambient group action. -/
theorem pointwiseFiniteSum_commutes_ambient (g : G) (v : A) :
    pointwiseFiniteSum P hfinite (A.representation g v) =
      A.representation g (pointwiseFiniteSum P hfinite v) :=
  pointwiseFiniteSum_isotypic_covariant (SmoothRep.normalSubgroupInverseConjugation N g)
    P P hfinite hfinite hid hid hr hk hr hk (SmoothRep.restrictionConjugationMap N A g) v

/-- Upgrade the normal-subgroup total to an actual ambient intertwiner. -/
def ambientTotalProjector : A.representation.IntertwiningMap A.representation where
  toLinearMap := (pointwiseFiniteSum P hfinite).toLinearMap
  isIntertwining' g := by
    ext v
    exact pointwiseFiniteSum_commutes_ambient N P hfinite hid hr hk g v

@[simp]
theorem ambientTotalProjector_apply (v : A) :
    ambientTotalProjector N P hfinite hid hr hk v = pointwiseFiniteSum P hfinite v := rfl

/-- The ambient total has the same underlying range as the subgroup total. -/
theorem ambientTotalProjector_range
    (horth : ∀ c d, c ≠ d → ∀ v, P c (P d v) = 0) :
    (ambientTotalProjector N P hfinite hid hr hk).range.toSubmodule =
      (totalIsotypicSubrepresentation.{uG, uC} (SmoothRep.restrictSubgroup N A)).toSubmodule := by
  change (pointwiseFiniteSum P hfinite).range.toSubmodule = _
  rw [pointwiseFiniteSum_range P hfinite (fun c v => DFunLike.congr_fun (hid c) v) horth]
  congr 1
  exact iSup_congr hr

/-- The ambient total has the same underlying kernel as the subgroup total. -/
theorem ambientTotalProjector_ker
    (horth : ∀ c d, c ≠ d → ∀ v, P c (P d v) = 0) :
    (ambientTotalProjector N P hfinite hid hr hk).ker.toSubmodule =
      (totalAnnihilatorSubrepresentation.{uG, uC} (SmoothRep.restrictSubgroup N A)).toSubmodule := by
  change (pointwiseFiniteSum P hfinite).ker.toSubmodule = _
  rw [pointwiseFiniteSum_ker P hfinite (fun c v => DFunLike.congr_fun (hid c) v) horth]
  congr 1
  exact iInf_congr hk

theorem ambientTotalProjector_idempotent
    (horth : ∀ c d, c ≠ d → ∀ v, P c (P d v) = 0) (v : A) :
    ambientTotalProjector N P hfinite hid hr hk
      (ambientTotalProjector N P hfinite hid hr hk v) =
      ambientTotalProjector N P hfinite hid hr hk v :=
  pointwiseFiniteSum_idempotent P hfinite (fun c w => DFunLike.congr_fun (hid c) w) horth v

/-- The ambient totals are natural for actual ambient intertwiners, including
between independent carrier universes. -/
theorem ambientTotalProjectors_natural
    {B : SmoothRep.{0, uG, uW} ℂ G}
    (Q : CompactCoefficientClass.{uG, uC} N →
      (SmoothRep.restrictSubgroup N B).representation.IntertwiningMap
        (SmoothRep.restrictSubgroup N B).representation)
    (hfiniteQ : ∀ v : B, Function.HasFiniteSupport (fun c => Q c v))
    (hidQ : ∀ c, IsIdempotentElem (Q c).toLinearMap)
    (hrQ : ∀ c, (Q c).range = isotypicSubrepresentation c (SmoothRep.restrictSubgroup N B))
    (hkQ : ∀ c, (Q c).ker = annihilatorSubrepresentation c (SmoothRep.restrictSubgroup N B))
    (f : A.representation.IntertwiningMap B.representation) (v : A) :
    ambientTotalProjector N Q hfiniteQ hidQ hrQ hkQ (f v) =
      f (ambientTotalProjector N P hfinite hid hr hk v) :=
  pointwiseFiniteSum_covariant P hfinite Q hfiniteQ f.toLinearMap (Equiv.refl _)
    (fun c w => (isotypicProjectors_natural c (P c) (Q c) (hid c) (hidQ c)
      (hr c) (hk c) (hrQ c) (hkQ c) (SmoothRep.restrictSubgroupMap N f) w).symm) v

end CompactCoefficientClass
end Langlands
