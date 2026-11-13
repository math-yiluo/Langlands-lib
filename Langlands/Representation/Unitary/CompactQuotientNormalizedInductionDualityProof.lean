import Langlands.Representation.Unitary.CompactQuotientNormalizedInductionDualityStatement
import Langlands.Representation.Unitary.RelativeQuotientMeasure
import Langlands.Representation.Unitary.CompactInductionIntegralDuality

/-! # Normalized induction from a compact quotient commutes with duality -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory MeasureTheory
open scoped NNReal

namespace Langlands.Induction

universe uG v w

variable {G : Type uG} [Group G] [TopologicalSpace G] [NonarchimedeanGroup G]
  [LocallyCompactSpace G]

omit [LocallyCompactSpace G] in
set_option maxHeartbeats 1600000 in
/-- Integral-characterized compact induction dualities are natural on all smooth objects. -/
theorem exists_naturalCompactIntegralDuality (P : Subgroup G) (χ : SmoothCharacter ℂ P)
    (K : Subgroup G) [MeasurableSpace K] (μ : Measure K)
    (hdual : ∀ A : Langlands.SmoothRep.{0, uG, v} ℂ P,
      ∃ E : Representation.Equiv
          (smoothContragredient (compactInduced P (twist χ.toMonoidHom A.representation)))
          (compactInduced P (twist χ.toMonoidHom (smoothContragredient A.representation))),
        ∀ (ℓ : SmoothDual (compactInduced P (twist χ.toMonoidHom A.representation)))
          (f : CompactFunctions P (twist χ.toMonoidHom A.representation)),
          smoothDualPairing _ ℓ f =
            ∫ k : K, smoothDualPairing A.representation (eval P _ (E ℓ).val k)
              (eval P _ f.val k) ∂μ) :
    let i : Langlands.SmoothRep.{0, uG, v} ℂ P ⥤
        Langlands.SmoothRep.{0, uG, max uG v} ℂ G :=
      Langlands.SmoothRep.toRep ⋙ normalizedCompactInductionFunctor P χ
    Nonempty (i.op ⋙ Langlands.SmoothRep.contragredientFunctor ≅
      Langlands.SmoothRep.contragredientFunctor ⋙ i) := by
  let i : Langlands.SmoothRep.{0, uG, v} ℂ P ⥤
      Langlands.SmoothRep.{0, uG, max uG v} ℂ G :=
    Langlands.SmoothRep.toRep ⋙ normalizedCompactInductionFunctor P χ
  choose E hE using hdual
  refine ⟨NatIso.ofComponents (fun X => Langlands.SmoothRep.mkIso
    (A := (i.obj X.unop).contragredient)
    (B := i.obj X.unop.contragredient) (E X.unop)) ?_⟩
  intro X Y f
  apply ObjectProperty.hom_ext
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro (ℓ : SmoothDual (compactInduced P (twist χ.toMonoidHom X.unop.representation)))
  have hEY := hE Y.unop
  have hEX := hE X.unop
  change E Y.unop (contragredientMap
      (Langlands.SmoothRep.hom (i.map f.unop)) ℓ) =
    Langlands.SmoothRep.hom (i.map (Langlands.SmoothRep.contragredientHom f.unop))
      (E X.unop ℓ)
  rw [← (E Y.unop).apply_symm_apply
    (Langlands.SmoothRep.hom (i.map (Langlands.SmoothRep.contragredientHom f.unop))
      (E X.unop ℓ))]
  congr 1
  apply Subtype.ext
  apply LinearMap.ext
  intro (x : CompactFunctions P (twist χ.toMonoidHom Y.unop.representation))
  change smoothDualPairing (compactInduced P (twist χ.toMonoidHom X.unop.representation)) ℓ
      (Langlands.SmoothRep.hom (i.map f.unop) x) =
    smoothDualPairing (compactInduced P (twist χ.toMonoidHom Y.unop.representation))
      ((E Y.unop).symm (Langlands.SmoothRep.hom
        (i.map (Langlands.SmoothRep.contragredientHom f.unop)) (E X.unop ℓ))) x
  rw [hEY, (E Y.unop).apply_symm_apply, hEX]
  rfl

section Conjugate

variable (P : Subgroup G) {V : Type v} {W : Type w}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- Postcomposition by an equivariant antilinear coefficient map. -/
def postcomposeSmoothConjugate (σ : Representation ℂ P V) (τ : Representation ℂ P W)
    (e : V →ₗ⋆[ℂ] W) (he : ∀ (p : P) (x : V), e (σ p x) = τ p (e x))
    (f : SmoothFunctions P σ) : SmoothFunctions P τ :=
  smoothFunctionOf P τ (fun x => e (eval P σ f x))
    (fun p x => by
      change e (f.val.val ((p : G) * x)) = τ p (e (f.val.val x))
      exact (congrArg e (f.val.property p x)).trans (he p _))
    f.property.choose (fun k x => congrArg e
      (congrArg (fun F : EquivariantFunctions P σ => F.val x) (f.property.choose_spec k)))

/-- Antilinear coefficient equivalences give antilinear smooth induction equivalences. -/
def smoothInducedConjugateEquiv (σ : Representation ℂ P V) (τ : Representation ℂ P W)
    (e : V ≃ₗ⋆[ℂ] W) (he : ∀ (p : P) (x : V), e (σ p x) = τ p (e x)) :
    SmoothFunctions P σ ≃ₗ⋆[ℂ] SmoothFunctions P τ where
  toFun := postcomposeSmoothConjugate P σ τ e.toLinearMap he
  invFun := postcomposeSmoothConjugate P τ σ e.symm.toLinearMap (fun p y => by
    apply e.injective
    exact (e.apply_symm_apply _).trans
      ((congrArg (τ p) (e.apply_symm_apply y).symm).trans (he p _).symm))
  left_inv f := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    exact e.symm_apply_apply _
  right_inv f := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    exact e.apply_symm_apply _
  map_add' f g := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    exact map_add e _ _
  map_smul' c f := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    exact map_smulₛₗ e c _

/-- Antilinear coefficient equivalences give antilinear compact induction equivalences
when the quotient is compact. -/
def compactInducedConjugateEquiv [CompactSpace (LeftQuotient P)]
    (σ : Representation ℂ P V) (τ : Representation ℂ P W)
    (e : V ≃ₗ⋆[ℂ] W) (he : ∀ (p : P) (x : V), e (σ p x) = τ p (e x)) :
    CompactFunctions P σ ≃ₗ⋆[ℂ] CompactFunctions P τ :=
  (compactQuotientInductionEquiv P σ).toLinearEquiv.trans
    ((smoothInducedConjugateEquiv P σ τ e he).trans
      (compactQuotientInductionEquiv P τ).symm.toLinearEquiv)

omit [LocallyCompactSpace G] in
/-- Pointwise antilinear postcomposition commutes with right translation. -/
theorem compactInducedConjugateEquiv_equivariant [CompactSpace (LeftQuotient P)]
    (σ : Representation ℂ P V) (τ : Representation ℂ P W)
    (e : V ≃ₗ⋆[ℂ] W) (he : ∀ (p : P) (x : V), e (σ p x) = τ p (e x))
    (g : G) (f : CompactFunctions P σ) :
    compactInducedConjugateEquiv P σ τ e he (compactInduced P σ g f) =
      compactInduced P τ g (compactInducedConjugateEquiv P σ τ e he f) := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  rfl

end Conjugate

end Langlands.Induction

namespace Langlands.Renard.CompactRepresentation

open Langlands.Induction

universe uG v

set_option maxHeartbeats 1600000 in
/-- Renard IV.2.1: normalized induction from a closed cocompact subgroup commutes
with smooth contragredients naturally and with hermitian contragredients. -/
theorem compactQuotientNormalizedInductionDuality :
    CompactQuotientNormalizedInductionDualityStatement.{uG, v} := by
  intro G _ _ _ _ _ P hP _ _
  refine ⟨exists_relativeHalfModulus P, ?_⟩
  intro χ hχ
  borelize G
  obtain ⟨μ, hpos, hscalar⟩ := exists_compactQuotient_relativeMeasure P hP
  have hδ : ∀ q : P, (χ.toMonoidHom q : ℂ) * χ.toMonoidHom q =
      (((relativePositiveModulus P q : ℝ≥0) : ℝ) : ℂ) := by
    intro q
    have h := hχ.2 q
    rw [← complexCharacter_relativePositiveModulus P] at h
    simpa only [pow_two, Jacquet.complexCharacter_apply] using h
  have hdual := fun (A : Langlands.SmoothRep.{0, uG, v} ℂ P) =>
    exists_compactIntegralDualEquiv P hP χ.toMonoidHom χ.isOpen_ker
      (fun q => (relativePositiveModulus P q : ℝ≥0)) hδ (⊤ : Subgroup G) μ hpos hscalar
      A.representation A.isSmooth
  refine ⟨exists_naturalCompactIntegralDuality P χ (⊤ : Subgroup G) μ hdual, ?_⟩
  intro τ σ e he
  obtain ⟨F, _hF⟩ := hdual τ
  have heχ : ∀ (q : P) (x : σ),
      e (twist χ.toMonoidHom σ.representation q x) =
        twist χ.toMonoidHom (smoothContragredient τ.representation) q (e x) := by
    intro q x
    have hc : (starRingEnd ℂ) (χ.toMonoidHom q : ℂ) = (χ.toMonoidHom q : ℂ) := by
      obtain ⟨r, _hr, hreal⟩ := hχ.1 q
      rw [hreal]
      exact Complex.conj_ofReal r
    change e ((χ.toMonoidHom q : ℂ) • σ.representation q x) =
      (χ.toMonoidHom q : ℂ) • smoothContragredient τ.representation q (e x)
    rw [map_smulₛₗ, he, hc]
  let J := compactInducedConjugateEquiv P (twist χ.toMonoidHom σ.representation)
    (twist χ.toMonoidHom (smoothContragredient τ.representation)) e heχ
  refine ⟨J.trans F.symm.toLinearEquiv, ?_⟩
  intro g x
  change F.symm (J (compactInduced P (twist χ.toMonoidHom σ.representation) g x)) =
    smoothContragredient (compactInduced P (twist χ.toMonoidHom τ.representation)) g
      (F.symm (J x))
  rw [show J (compactInduced P (twist χ.toMonoidHom σ.representation) g x) =
    compactInduced P (twist χ.toMonoidHom (smoothContragredient τ.representation)) g
      (J x) from compactInducedConjugateEquiv_equivariant P _ _ e heχ g x]
  exact LinearMap.congr_fun (F.symm.isIntertwining' g) (J x)

end Langlands.Renard.CompactRepresentation
