import Langlands.TraceFormula.TwistedOrbital
import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Homeomorph.Lemmas

/-! Closed twisted orbits and the topology on their centralizer quotients. -/

noncomputable section

namespace Langlands.TraceFormula

open Function Langlands.QuotientIntegration Topology

universe u v

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SigmaCompactSpace G]
variable {S : Type v} [FunLike S G G] [MonoidHomClass S G G]
  (θ : S) (hθ : Continuous θ) (δ : G)

include hθ in
/-- The map from actual left cosets to a closed twisted orbit is a closed embedding
in the ambient group. -/
theorem isClosedEmbedding_twistedOrbitFunction_id
    (hClosed : IsClosed (Set.range fun x : G => twistedConj θ x δ)) :
    IsClosedEmbedding (twistedOrbitFunction θ δ id) := by
  let H := twistedCentralizer θ δ
  let O := Set.range fun x : G => twistedConj θ x δ
  have hq := leftQuotient_isOpenQuotientMap H
  let f₀ : LeftQuotient H → G := twistedOrbitFunction θ δ id
  have hf₀ (x : G) : f₀ (leftQuotientMap H x) = twistedConj θ x δ := rfl
  have hf₀O (q : LeftQuotient H) : f₀ q ∈ O := by
    obtain ⟨x, rfl⟩ := hq.surjective q
    exact ⟨x, (hf₀ x).symm⟩
  let f (q : LeftQuotient H) : O := ⟨f₀ q, hf₀O q⟩
  have hInj : Injective f := by
    intro q r hqr
    obtain ⟨x, rfl⟩ := hq.surjective q
    obtain ⟨y, rfl⟩ := hq.surjective r
    have he : twistedConj θ x δ = twistedConj θ y δ := congrArg Subtype.val hqr
    apply Quotient.sound
    change QuotientGroup.rightRel H x y
    rw [QuotientGroup.rightRel_apply]
    change twistedConj θ (y * x⁻¹) δ = δ
    rw [← twistedConj_mul, ← he, twistedConj_mul, mul_inv_cancel, twistedConj_one]
  have hSurj : Surjective f := by
    rintro ⟨g, ⟨x, rfl⟩⟩
    exact ⟨leftQuotientMap H x, Subtype.ext (hf₀ x)⟩
  let : LocallyCompactSpace O := hClosed.locallyCompactSpace
  let : MulAction G O :=
    { smul := fun a y => ⟨twistedConj θ a⁻¹ y.val, by
        obtain ⟨x, hx⟩ := y.property
        refine ⟨x * a⁻¹, ?_⟩
        change twistedConj θ x δ = y.val at hx
        change twistedConj θ (x * a⁻¹) δ = twistedConj θ a⁻¹ y.val
        rw [← twistedConj_mul, hx]⟩
      one_smul := fun y => Subtype.ext (by
        change twistedConj θ (1 : G)⁻¹ y.val = y.val
        rw [inv_one, twistedConj_one])
      mul_smul := fun a b y => Subtype.ext (by
        change twistedConj θ (a * b)⁻¹ y.val = twistedConj θ a⁻¹ (twistedConj θ b⁻¹ y.val)
        rw [mul_inv_rev, ← twistedConj_mul]) }
  let : ContinuousSMul G O := ⟨by
    apply Continuous.subtype_mk
    simp only [twistedConj_apply, inv_inv]
    exact (continuous_fst.mul (continuous_subtype_val.comp continuous_snd)).mul
      (hθ.comp continuous_fst.inv)⟩
  let : MulAction.IsPretransitive G O := ⟨by
    rintro ⟨u, ⟨x, rfl⟩⟩ ⟨v, ⟨y, rfl⟩⟩
    refine ⟨y⁻¹ * x, Subtype.ext ?_⟩
    change twistedConj θ (y⁻¹ * x)⁻¹ (twistedConj θ x δ) = twistedConj θ y δ
    rw [twistedConj_mul, mul_inv_rev, inv_inv, ← mul_assoc, mul_inv_cancel, one_mul]⟩
  let δ₀ : O := ⟨δ, ⟨1, twistedConj_one θ δ⟩⟩
  have hCompose : f ∘ leftQuotientMap H = fun x : G => x⁻¹ • δ₀ := by
    funext x
    apply Subtype.ext
    change twistedConj θ x δ = twistedConj θ x⁻¹⁻¹ δ
    rw [inv_inv]
  let e := (Equiv.ofBijective f ⟨hInj, hSurj⟩).toHomeomorphOfContinuousOpen
    (hq.isQuotientMap.continuous_iff.mpr
      (((continuous_id.inv.mul continuous_const).mul hθ).subtype_mk _))
    (hq.isOpenMap_iff.mpr (by
      change IsOpenMap (f ∘ leftQuotientMap H)
      rw [hCompose]
      exact (isOpenMap_smul_of_sigmaCompact δ₀).comp (isOpenMap_inv G)))
  exact hClosed.isClosedEmbedding_subtypeVal.comp e.isClosedEmbedding

end Langlands.TraceFormula
