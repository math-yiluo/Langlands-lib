import Langlands.AlgebraicGeometry.FibreDenseOpenPullback
import Langlands.AlgebraicGeometry.SmoothReducedBase
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! # Descent of morphisms from smooth covers using dense opens -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology

namespace Langlands.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

/-- A separated morphism to a separated base has separated source. -/
theorem separatedScheme_of_separated_over {X S : Scheme.{u}} [S.IsSeparated]
    (p : X ⟶ S) [IsSeparated p] : X.IsSeparated := by
  constructor
  rw [← terminal.comp_from p]
  infer_instance

/-- The inverse image of a dense open under an open map is dominant. -/
theorem isDominant_preimage_ι {X Y : Scheme.{u}} (q : X ⟶ Y) (hq : IsOpenMap q)
    (U : Y.Opens) (hU : Dense (U : Set Y)) : IsDominant (q ⁻¹ᵁ U).ι :=
  Opens.isDominant_ι (hU.preimage hq)

/-- Factor through an open immersion on the inverse image of its range. -/
def liftOpensRange {X Y U : Scheme.{u}} (q : X ⟶ Y) (i : U ⟶ Y) [IsOpenImmersion i] :
    (q ⁻¹ᵁ i.opensRange).toScheme ⟶ U :=
  (q ∣_ i.opensRange) ≫ i.isoOpensRange.inv

@[reassoc (attr := simp)]
theorem liftOpensRange_fac {X Y U : Scheme.{u}} (q : X ⟶ Y) (i : U ⟶ Y) [IsOpenImmersion i] :
    liftOpensRange q i ≫ i = (q ⁻¹ᵁ i.opensRange).ι ≫ q := by
  simp [liftOpensRange, morphismRestrict_ι]

/-- A morphism on a smooth surjective quasi-compact cover descends if it agrees with a
specified morphism on the pullback of a dense open in the base of the cover. -/
theorem exists_hom_of_agrees_over_dense_open {S P X U Y : Scheme.{u}} [IsReduced S]
    (f : X ⟶ S) [Smooth f] [Y.IsSeparated]
    (q : P ⟶ X) [Smooth q] [Surjective q] [QuasiCompact q]
    (i : U ⟶ X) [IsOpenImmersion i] [IsDominant i] (d : P ⟶ Y) (j : U ⟶ Y)
    (h : ∀ ⦃T : Scheme.{u}⦄ (v : T ⟶ P) (u : T ⟶ U), v ≫ q = u ≫ i → v ≫ d = u ≫ j) :
    ∃ b : X ⟶ Y, q ≫ b = d ∧ i ≫ b = j := by
  let p₁ := pullback.fst q q
  let p₂ := pullback.snd q q
  let v := p₁ ≫ q
  have : Smooth p₁ := inferInstanceAs (Smooth (pullback.fst q q))
  have : Smooth v := by dsimp [v]; infer_instance
  have : Smooth (v ≫ f) := inferInstance
  have : IsReduced (pullback q q) := SmoothReducedBase.isReduced_of_smooth_of_isReduced (v ≫ f)
  let O := v ⁻¹ᵁ i.opensRange
  have hO : IsDominant O.ι := isDominant_preimage_ι v v.isOpenMap _
    (by simpa only [Scheme.Hom.coe_opensRange, DenseRange] using IsDominant.denseRange (f := i))
  have hpair : p₁ ≫ d = p₂ ≫ d := by
    apply AlgebraicGeometry.ext_of_isDominant O.ι
    rw [← Category.assoc, ← Category.assoc]
    let u := liftOpensRange v i
    have hu : u ≫ i = O.ι ≫ v := liftOpensRange_fac _ _
    have h₁ : (O.ι ≫ p₁) ≫ q = u ≫ i := by rw [hu, Category.assoc]
    have h₂ : (O.ι ≫ p₂) ≫ q = u ≫ i := by
      rw [hu, Category.assoc]
      exact congrArg (fun g => O.ι ≫ g) (pullback.condition (f := q) (g := q)).symm
    exact (h _ _ h₁).trans (h _ _ h₂).symm
  obtain ⟨b, hb⟩ := IsRegularEpi.exists_of_isKernelPair q (IsPullback.of_hasPullback q q) d hpair
  have hb' : q ≫ b = d := hb
  refine ⟨b, hb', ?_⟩
  let v₁ := pullback.fst q i
  let v₂ := pullback.snd q i
  have : Surjective v₂ := inferInstanceAs (Surjective (pullback.snd q i))
  have : IsReduced U := SmoothReducedBase.isReduced_of_smooth_of_isReduced (i ≫ f)
  apply AlgebraicGeometry.ext_of_isDominant v₂
  rw [← Category.assoc, show v₂ ≫ i = v₁ ≫ q from pullback.condition.symm,
    Category.assoc, hb']
  exact h v₁ v₂ pullback.condition

/-- Two smooth surjective quasi-compact maps from a common scheme give isomorphic quotients
if their comparison agrees with a common dense open chart on the first quotient. -/
theorem exists_iso_of_agrees_over_dense_open {S P X U Y : Scheme.{u}} [IsReduced S]
    (f : X ⟶ S) (g : Y ⟶ S) [Smooth f] [Smooth g] [X.IsSeparated] [Y.IsSeparated]
    (q : P ⟶ X) [Smooth q] [Surjective q] [QuasiCompact q]
    (d : P ⟶ Y) [Smooth d] [Surjective d] [QuasiCompact d]
    (i : U ⟶ X) [IsOpenImmersion i] [IsDominant i] (j : U ⟶ Y) [Mono j]
    (h : ∀ ⦃T : Scheme.{u}⦄ (v : T ⟶ P) (u : T ⟶ U), v ≫ q = u ≫ i → v ≫ d = u ≫ j) :
    ∃ e : X ≅ Y, q ≫ e.hom = d ∧ i ≫ e.hom = j := by
  obtain ⟨α, hα, hαi⟩ := exists_hom_of_agrees_over_dense_open f q i d j h
  let p₁ := pullback.fst d d
  let p₂ := pullback.snd d d
  let v₁ := p₁ ≫ q
  let v₂ := p₂ ≫ q
  have : Smooth p₁ := inferInstanceAs (Smooth (pullback.fst d d))
  have : Smooth p₂ := inferInstanceAs (Smooth (pullback.snd d d))
  have : Smooth (p₁ ≫ d ≫ g) := inferInstance
  have : IsReduced (pullback d d) := SmoothReducedBase.isReduced_of_smooth_of_isReduced
    (p₁ ≫ d ≫ g)
  have hdi : Dense (i.opensRange : Set X) := by
    simpa only [Scheme.Hom.coe_opensRange, DenseRange] using IsDominant.denseRange (f := i)
  let O₁ := v₁ ⁻¹ᵁ i.opensRange
  let O₂ := v₂ ⁻¹ᵁ i.opensRange
  let O := O₁ ⊓ O₂
  have hO₁ : Dense (O₁ : Set ↑(pullback d d)) := hdi.preimage (p₁ ≫ q).isOpenMap
  have hO₂ : Dense (O₂ : Set ↑(pullback d d)) := hdi.preimage (p₂ ≫ q).isOpenMap
  have : IsDominant O.ι := Opens.isDominant_ι (hO₁.inter_of_isOpen_left hO₂ O₁.isOpen)
  have hpair : p₁ ≫ q = p₂ ≫ q := by
    apply AlgebraicGeometry.ext_of_isDominant O.ι
    let u₁ := (pullback d d).homOfLE (inf_le_left : O ≤ O₁) ≫ liftOpensRange v₁ i
    let u₂ := (pullback d d).homOfLE (inf_le_right : O ≤ O₂) ≫ liftOpensRange v₂ i
    have h₁ : u₁ ≫ i = O.ι ≫ p₁ ≫ q := by
      dsimp only [u₁]
      rw [Category.assoc, liftOpensRange_fac, Scheme.homOfLE_ι_assoc]
    have h₂ : u₂ ≫ i = O.ι ≫ p₂ ≫ q := by
      dsimp only [u₂]
      rw [Category.assoc, liftOpensRange_fac, Scheme.homOfLE_ι_assoc]
    have h₁' : (O.ι ≫ p₁) ≫ d = u₁ ≫ j := h _ _ (by rw [Category.assoc, h₁])
    have h₂' : (O.ι ≫ p₂) ≫ d = u₂ ≫ j := h _ _ (by rw [Category.assoc, h₂])
    have he : u₁ = u₂ := (cancel_mono j).mp (by
      rw [← h₁', ← h₂', Category.assoc, Category.assoc, pullback.condition])
    rw [← h₁, ← h₂, he]
  obtain ⟨β, hβ⟩ := IsRegularEpi.exists_of_isKernelPair d (IsPullback.of_hasPullback d d) q hpair
  refine ⟨⟨α, β, ?_, ?_⟩, hα, hαi⟩
  · apply (cancel_epi q).mp
    rw [← Category.assoc, hα, hβ, Category.comp_id]
  · apply (cancel_epi d).mp
    rw [← Category.assoc, hβ, hα, Category.comp_id]

end Langlands.AlgebraicGeometry
