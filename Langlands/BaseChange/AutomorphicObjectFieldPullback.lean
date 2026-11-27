import Langlands.BaseChange.ConcordanceRingEquiv
import Langlands.BaseChange.TwistedCharacter
import Langlands.BaseChange.TwistedLocalGroupTransport
import Langlands.Correspondence.AutomorphicRelations
import Langlands.Group.GL.LocalFieldTopology
import Langlands.HarmonicAnalysis.FieldTransport
import Langlands.Representation.CompactCoefficient.GroupTransport
import Langlands.Representation.CuspidalSupport.GroupTransport
import Langlands.Representation.RankinSelberg.FieldTransport.Group
import Langlands.Representation.Smooth.Transfer.PullbackProof
import Langlands.Representation.Unramified.HeckeOperators
import Langlands.Representation.Whittaker.GeneralLinear

/-! # Irreducible admissible representations along a field isomorphism -/

noncomputable section

set_option autoImplicit false

namespace Langlands.BaseChange

open Correspondence HarmonicAnalysis Unramified

universe uF uD uV

attribute [local instance] heckeFieldTopology heckeFieldValuativeRel heckeFieldLocalField
  heckeGeneralLinearTopology heckeGeneralLinearTopologicalGroup heckeGeneralLinearT2
  heckeGeneralLinearMeasurable heckeGeneralLinearBorel

private local instance {p : ℕ} [Fact p.Prime] (F : PadicField p) (n : ℕ) :
    LocallyCompactSpace (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearLocallyCompactSpace n

private local instance {p : ℕ} [Fact p.Prime] (F : PadicField p) (n : ℕ) :
    TotallyDisconnectedSpace (GeneralLinear n F.Carrier) :=
  LocalFieldTopology.generalLinear_totallyDisconnectedSpace F.Carrier n

section Intertwiner

variable {F₀ : Type*} {E₀ : Type*} {F₁ : Type*} {E₁ : Type*}
  [CommRing F₀] [CommRing E₀] [Algebra F₀ E₀] [CommRing F₁] [CommRing E₁] [Algebra F₁ E₁]
  {σ₀ : E₀ ≃ₐ[F₀] E₀} {σ₁ : E₁ ≃ₐ[F₁] E₁} {n : ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]

/-- A sigma-intertwiner is carried along a ring isomorphism that intertwines the two
automorphisms, when the new representation is the entrywise pullback of the old one.
The underlying linear map is unchanged. -/
def SigmaIntertwiner.ringPullback (c : E₁ ≃+* E₀) (hc : ∀ x, c (σ₁ x) = σ₀ (c x))
    {τ : Representation ℂ (GeneralLinear n E₀) W} {ρ : Representation ℂ (GeneralLinear n E₁) W}
    (hρ : ∀ g, ρ g = τ (Matrix.GeneralLinearGroup.map c.toRingHom g))
    (A : SigmaIntertwiner σ₀ n τ) : SigmaIntertwiner σ₁ n ρ :=
  Representation.Equiv.mk A.toLinearEquiv (fun g => by
    have hmap : Matrix.GeneralLinearGroup.map c.toRingHom (entrywiseAut σ₁ n g) =
        entrywiseAut σ₀ n (Matrix.GeneralLinearGroup.map c.toRingHom g) := by
      apply Units.ext
      ext i j
      exact hc (g i j)
    change A.toLinearMap ∘ₗ ρ g = ρ (entrywiseAut σ₁ n g) ∘ₗ A.toLinearMap
    rw [hρ, hρ, hmap]
    exact A.comp_apply_eq _)

@[simp]
theorem SigmaIntertwiner.ringPullback_toLinearMap (c : E₁ ≃+* E₀)
    (hc : ∀ x, c (σ₁ x) = σ₀ (c x))
    {τ : Representation ℂ (GeneralLinear n E₀) W} {ρ : Representation ℂ (GeneralLinear n E₁) W}
    (hρ : ∀ g, ρ g = τ (Matrix.GeneralLinearGroup.map c.toRingHom g))
    (A : SigmaIntertwiner σ₀ n τ) :
    (A.ringPullback c hc hρ).toLinearMap = A.toLinearMap := rfl

end Intertwiner

section Pullback

variable {p q : ℕ} [Fact p.Prime] [Fact q.Prime] {F : PadicField.{uF} p} {D : PadicField.{uD} q}
  (a : F.Carrier ≃+* D.Carrier) (ha : Continuous a) (ha' : Continuous a.symm)

/-- Pull an irreducible admissible representation of `GL_n(D)` back to `GL_n(F)`
through the entrywise map of a bicontinuous field isomorphism. -/
def fieldPullbackObject {n : ℕ+} (A : AutomorphicObject.{uD, uV} D n) :
    AutomorphicObject.{uF, uV} F n :=
  let κ := generalLinearRingEquiv (n := (n : ℕ)) a ha ha'
  ⟨SmoothRep.of (A.obj.representation.comp κ.toMonoidHom)
      (isSmooth_comp κ.toMonoidHom κ.continuous A.obj.isSmooth),
    (isIrreducible_comp_continuousMulEquiv_iff A.obj.representation κ).mpr A.property.1,
    isAdmissible_comp_continuousMulEquiv A.obj.representation κ A.property.2⟩

@[simp]
theorem fieldPullbackObject_representation {n : ℕ+}
    (A : AutomorphicObject.{uD, uV} D n) (g : GeneralLinear (n : ℕ) F.Carrier) :
    (fieldPullbackObject a ha ha' A).obj.representation g =
      A.obj.representation (generalLinearRingEquiv a ha ha' g) := rfl

private theorem fieldPullback_mem_upperUnipotent_iff (r : ℕ)
    (g : GeneralLinear (r + 1) F.Carrier) :
    generalLinearRingEquiv a ha ha' g ∈ GeneralLinear.upperUnipotent (r + 1) D.Carrier ↔
      g ∈ GeneralLinear.upperUnipotent (r + 1) F.Carrier := by
  change ((generalLinearRingEquiv a ha ha' g).val.IsUpperTriangular ∧
      ∀ i, generalLinearRingEquiv a ha ha' g i i = 1) ↔
    (g.val.IsUpperTriangular ∧ ∀ i, g i i = 1)
  simp only [generalLinearRingEquiv_apply_apply]
  constructor
  · rintro ⟨hT, hD⟩
    refine ⟨fun i j hij => a.injective ?_, fun i => a.injective ?_⟩
    · simpa using hT hij
    · simpa using hD i
  · rintro ⟨hT, hD⟩
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · change a (g i j) = 0
      rw [show g i j = 0 from hT hij, map_zero]
    · rw [hD i, map_one]

/-- Genericity is preserved by pullback, for the pulled-back additive character. -/
theorem fieldPullbackObject_isGeneric {r : ℕ}
    (A : AutomorphicObject.{uD, uV} D r.succPNat) (ψ : NontrivialAdditiveCharacter D)
    (hA : Whittaker.IsGeneric ψ r A.obj.representation) :
    Whittaker.IsGeneric (FieldTransport.additiveCharacter a.symm ha ψ) r
      (fieldPullbackObject a ha ha' A).obj.representation := by
  refine ⟨(fieldPullbackObject a ha ha' A).property.1, (fieldPullbackObject a ha ha' A).property.2, ?_⟩
  obtain ⟨ℓ, hℓ⟩ := hA.2.2
  let κ := generalLinearRingEquiv (n := r + 1) a ha ha'
  have hN := fieldPullback_mem_upperUnipotent_iff a ha ha' r
  have hθ (u : GeneralLinear.upperUnipotent (r + 1) F.Carrier) :
      Whittaker.standardCharacter ψ r ⟨κ u, (hN u).2 u.2⟩ =
        Whittaker.standardCharacter (FieldTransport.additiveCharacter a.symm ha ψ) r u := by
    apply Units.ext
    have h1 : (∑ i : Fin r, (κ u.val) i.castSucc i.succ) =
        a (∑ i : Fin r, u.val i.castSucc i.succ) := by
      rw [map_sum]
      rfl
    exact congrArg (fun x : D.Carrier => ((ψ x : Circle) : ℂ)) h1
  have hfun := Whittaker.functionals_comp κ.toMulEquiv hN hθ A.obj.representation
  have hmem : ℓ.val ∈ Whittaker.functionals (GeneralLinear.upperUnipotent (r + 1) F.Carrier)
      (Whittaker.standardCharacter (FieldTransport.additiveCharacter a.symm ha ψ) r)
      (A.obj.representation.comp κ.toMulEquiv.toMonoidHom) :=
    (congrArg (fun S => ℓ.val ∈ S) hfun).mpr ℓ.property
  exact ⟨⟨ℓ.val, hmem⟩, hℓ⟩

/-- The twisted distribution of the pullback is the original twisted distribution, for the
pushed-forward Haar measure and the transported test function. -/
theorem fieldPullbackObject_twistedDistribution {n : ℕ+}
    (A : AutomorphicObject.{uD, uV} D n) (μ : MeasureTheory.Measure (GeneralLinear (n : ℕ) F.Carrier))
    [μ.IsHaarMeasure] (B : Module.End ℂ A.obj) (f : SchwartzBruhat (GeneralLinear (n : ℕ) F.Carrier)) :
    letI := (generalLinearRingEquiv (n := (n : ℕ)) a ha ha').isHaarMeasure_map μ
    twistedDistribution μ (fieldPullbackObject a ha ha' A).obj.representation
        (fieldPullbackObject a ha ha' A).property.2 B f =
      twistedDistribution (μ.map (generalLinearRingEquiv (n := (n : ℕ)) a ha ha'))
        A.obj.representation A.property.2 B
        (Hecke.TestFunction.pullback
          (generalLinearRingEquiv (n := (n : ℕ)) a ha ha').symm.toHomeomorph f) :=
  twistedDistribution_comp_equiv (generalLinearRingEquiv a ha ha') μ A.obj.representation
    A.property.2 (fieldPullbackObject a ha ha' A).property.2 B f

/-- The same change of variables for the ordinary distribution character. -/
theorem fieldPullbackObject_distribution {n : ℕ+}
    (A : AutomorphicObject.{uD, uV} D n) (μ : MeasureTheory.Measure (GeneralLinear (n : ℕ) F.Carrier))
    [μ.IsHaarMeasure] (f : SchwartzBruhat (GeneralLinear (n : ℕ) F.Carrier)) :
    letI := (generalLinearRingEquiv (n := (n : ℕ)) a ha ha').isHaarMeasure_map μ
    Character.distribution μ (fieldPullbackObject a ha ha' A).obj.representation
        (fieldPullbackObject a ha ha' A).property.2 f =
      Character.distribution (μ.map (generalLinearRingEquiv (n := (n : ℕ)) a ha ha'))
        A.obj.representation A.property.2
        (Hecke.TestFunction.pullback
          (generalLinearRingEquiv (n := (n : ℕ)) a ha ha').symm.toHomeomorph f) :=
  distribution_comp_equiv (generalLinearRingEquiv a ha ha') μ A.obj.representation
    A.property.2 (fieldPullbackObject a ha ha' A).property.2 f

end Pullback

/-- Pullback along a bicontinuous field isomorphism preserves genericity for the
pulled-back additive character. Its twisted distributions are the original ones
for the pushed-forward Haar measure and the transported test function. -/
def AutomorphicObjectFieldPullbackStatement : Prop :=
  ∀ (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (F : PadicField.{uF} p) (D : PadicField.{uD} q)
    (a : F.Carrier ≃+* D.Carrier) (ha : Continuous a) (ha' : Continuous a.symm)
    (r : ℕ) (A : AutomorphicObject.{uD, uV} D r.succPNat),
    (∀ ψ : NontrivialAdditiveCharacter D, Whittaker.IsGeneric ψ r A.obj.representation →
      Whittaker.IsGeneric (FieldTransport.additiveCharacter a.symm ha ψ) r
        (fieldPullbackObject a ha ha' A).obj.representation) ∧
    ∀ (μ : MeasureTheory.Measure (GeneralLinear (r.succPNat : ℕ) F.Carrier)) [μ.IsHaarMeasure]
      (B : Module.End ℂ A.obj) (f : SchwartzBruhat (GeneralLinear (r.succPNat : ℕ) F.Carrier)),
      letI := (generalLinearRingEquiv (n := (r.succPNat : ℕ)) a ha ha').isHaarMeasure_map μ
      twistedDistribution μ (fieldPullbackObject a ha ha' A).obj.representation
          (fieldPullbackObject a ha ha' A).property.2 B f =
        twistedDistribution (μ.map (generalLinearRingEquiv (n := (r.succPNat : ℕ)) a ha ha'))
          A.obj.representation A.property.2 B
          (Hecke.TestFunction.pullback
            (generalLinearRingEquiv (n := (r.succPNat : ℕ)) a ha ha').symm.toHomeomorph f)

theorem automorphicObjectFieldPullback :
    AutomorphicObjectFieldPullbackStatement.{uF, uD, uV} := by
  intro p q _ _ F D a ha ha' r A
  exact ⟨fun ψ hψ => fieldPullbackObject_isGeneric a ha ha' A ψ hψ,
    fun μ _ B f => fieldPullbackObject_twistedDistribution a ha ha' A μ B f⟩

end Langlands.BaseChange
