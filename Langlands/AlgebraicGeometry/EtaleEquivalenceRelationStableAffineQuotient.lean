import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationStableSystem
import Langlands.AlgebraicGeometry.RingEtaleGroupoidQuotientLevel
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationNoetherianPushout

/-! # Affine quotients at all sufficiently large stable levels -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct Opposite

namespace Langlands.AlgebraicGeometry.EtaleEquivalenceRelation.IsCartesianHom

open RingEtaleGroupoid

variable {E E₀ : EtaleEquivalenceRelation.{u}} {f : E.U ⟶ E₀.U} {g : E.R ⟶ E₀.R}
  (h : IsCartesianHom E E₀ f g) [IsAffine E.U] [IsAffine E₀.U] [IsAffine E₀.R]

/-- An affine quotient of the original relation persists at every stable level
containing a suitable finite subset of its coordinate ring. -/
lemma exists_stable_affineQuotient_finite_set (hq : E.HasAffineQuotient) :
    ∃ s : Finset Γ(E.U, ⊤), ∀ i : h.stableIndex, (s : Set Γ(E.U, ⊤)) ⊆ i.1 →
      (h.stableDiagram.obj (op i)).HasAffineQuotient := by
  have : IsAffine E.R := h.isAffine_R
  let := E₀.s.appTop.hom.toAlgebra
  let := f.appTop.hom.toAlgebra
  obtain ⟨A₁, B₁, _, _, _, _, _, _, _, φ, F, hF, hFbij⟩ :=
    exists_fg_pushout_of_hasAffineQuotient E hq
  let : Algebra A₁ Γ(E.U, ⊤) := (φ.comp (algebraMap A₁ B₁)).toAlgebra
  have hE₀ := E₀.ringEtaleGroupoid
  have : Algebra.Etale Γ(E₀.U, ⊤) Γ(E₀.R, ⊤) :=
    RingHom.etale_algebraMap.mp hE₀.etale_algebraMap
  have : Algebra.FiniteType Γ(E₀.U, ⊤) Γ(E₀.R, ⊤) := inferInstance
  let L : B₁ ⊗[A₁] Γ(E.U, ⊤) →+*
      Γ(E₀.R, ⊤) ⊗[Γ(E₀.U, ⊤)] Γ(E.U, ⊤) :=
    h.relationIso.inv.hom.comp F
  have hinv : ∀ x, h.relationIso.inv (h.relationIso.hom x) = x := fun x => by
    change (h.relationIso.hom ≫ h.relationIso.inv).hom x = x
    rw [Iso.hom_inv_id]
    rfl
  have hL : ∀ b d, L (b ⊗ₜ d) =
      h.coaction.coaction (φ b) * ((1 : Γ(E₀.R, ⊤)) ⊗ₜ d) := by
    intro b d
    change h.relationIso.inv (F (b ⊗ₜ d)) =
      h.ringHom (φ b) * ((1 : Γ(E₀.R, ⊤)) ⊗ₜ d)
    rw [hF, map_mul, ← h.relationIso_hom_one_tmul d, hinv]
    rfl
  have hLbij : Function.Bijective L :=
    (ConcreteCategory.bijective_of_isIso h.relationIso.inv).comp hFbij
  obtain ⟨s, hs⟩ := hE₀.exists_bijective_level h.coaction h.coaction_isMultiplicative
    φ L hL hLbij
  refine ⟨s, ?_⟩
  intro i hi
  obtain ⟨φi, _, Fi, hFi, hFibij⟩ := hs i.1 i.2.2 hi
  let : Algebra A₁ i.1 := (φi.comp (algebraMap A₁ B₁)).toAlgebra
  let θi := hE₀.subalgebraCoaction h.coaction i.1 i.2.2
  have hθi : θi.IsMultiplicative :=
    hE₀.subalgebraCoaction_isMultiplicative h.coaction h.coaction_isMultiplicative i.1 i.2.2
  let : Algebra i.1 (Γ(E₀.R, ⊤) ⊗[Γ(E₀.U, ⊤)] i.1) :=
    Algebra.TensorProduct.rightAlgebra
  exact hasAffineQuotient_of_bijective (θi.toRingHom hθi)
    (hE₀.level θi hθi).toScheme (Iso.refl _) (Iso.refl _) (by simp) (by simp)
    { toRingHom := φi, commutes' := fun _ => rfl } Fi hFi hFibij

variable [IsNoetherianRing Γ(E₀.U, ⊤)]

/-- An affine quotient exists at every stable level above one fixed stable level. -/
lemma exists_stable_affineQuotient_threshold (hq : E.HasAffineQuotient) :
    ∃ i : h.stableIndex, ∀ j : h.stableIndex, i ≤ j →
      (h.stableDiagram.obj (op j)).HasAffineQuotient := by
  let := E₀.s.appTop.hom.toAlgebra
  let := f.appTop.hom.toAlgebra
  obtain ⟨s, hs⟩ := h.exists_stable_affineQuotient_finite_set hq
  obtain ⟨S, hS, hsS, hstable⟩ :=
    E₀.ringEtaleGroupoid.exists_fg_stableSubalgebra h.coaction h.coaction_isMultiplicative s
  refine ⟨⟨S, hS, hstable⟩, ?_⟩
  intro j hij
  exact hs j (fun x hx => hij (hsS hx))

/-- One can retain any prescribed stable level while descending an affine quotient. -/
lemma exists_stable_affineQuotient_above (hq : E.HasAffineQuotient) (i : h.stableIndex) :
    ∃ j : h.stableIndex, i ≤ j ∧ (h.stableDiagram.obj (op j)).HasAffineQuotient := by
  let := E₀.s.appTop.hom.toAlgebra
  let := f.appTop.hom.toAlgebra
  obtain ⟨k, hk⟩ := h.exists_stable_affineQuotient_threshold hq
  obtain ⟨j, hij, hkj⟩ :=
    (StableSystem.indexDirected E₀.ringEtaleGroupoid h.coaction
      h.coaction_isMultiplicative).directed i k
  exact ⟨j, hij, hk j hkj⟩

/-- Choose a threshold above which every stable level has an affine quotient. -/
noncomputable def affineQuotientThreshold (hq : E.HasAffineQuotient) : h.stableIndex :=
  (h.exists_stable_affineQuotient_threshold hq).choose

/-- Every stable level above the chosen threshold has an affine quotient. -/
lemma hasAffineQuotient_of_affineQuotientThreshold_le (hq : E.HasAffineQuotient)
    (i : h.stableIndex) (hi : h.affineQuotientThreshold hq ≤ i) :
    (h.stableDiagram.obj (op i)).HasAffineQuotient :=
  (h.exists_stable_affineQuotient_threshold hq).choose_spec i hi

end Langlands.AlgebraicGeometry.EtaleEquivalenceRelation.IsCartesianHom
