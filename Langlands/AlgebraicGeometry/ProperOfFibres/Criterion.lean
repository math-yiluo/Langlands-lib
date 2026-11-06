import Mathlib
import Langlands.AlgebraicGeometry.ProperOfFibres.ValuationCore

/-! # Properness of a smooth scheme embedded in a proper scheme, from its field fibres -/

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.ProperOfFibres

/-- The base change of a monomorphism over `S` along any `T ⟶ S` is a monomorphism. -/
theorem mono_pullbackMap {X Y S T : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (j : X ⟶ Y) [Mono j]
    (hfac : j ≫ g = f) (t : T ⟶ S) :
    Mono (pullback.map f t g t j (𝟙 _) (𝟙 _) (by rw [Category.comp_id, hfac])
      (by rw [Category.comp_id, Category.id_comp])) := by
  have e₁ : pullback.map f t g t j (𝟙 _) (𝟙 _) (by rw [Category.comp_id, hfac])
      (by rw [Category.comp_id, Category.id_comp]) ≫ pullback.fst g t = pullback.fst f t ≫ j :=
    pullback.lift_fst _ _ _
  have e₂ : pullback.map f t g t j (𝟙 _) (𝟙 _) (by rw [Category.comp_id, hfac])
      (by rw [Category.comp_id, Category.id_comp]) ≫ pullback.snd g t = pullback.snd f t :=
    (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  refine ⟨fun a b h => pullback.hom_ext ((cancel_mono j).1 ?_) ?_⟩
  · simpa only [Category.assoc, e₁] using congrArg (· ≫ pullback.fst g t) h
  · simpa only [Category.assoc, e₂] using congrArg (· ≫ pullback.snd g t) h

/-- The field fibre of a base change is a field fibre of the original morphism. -/
theorem isProper_pullback_snd_pullback_snd {X S T : Scheme.{u}} (f : X ⟶ S) (t : T ⟶ S)
    {k : Type u} [Field k] (φ : Spec (CommRingCat.of k) ⟶ T) [IsProper (pullback.snd f (φ ≫ t))] :
    IsProper (pullback.snd (pullback.snd f t) φ) := by
  rw [← pullbackLeftPullbackSndIso_hom_snd f t φ]
  infer_instance

variable {S X Y : Scheme.{u}}

/-- **Properness from the field fibres.** Let `f : X ⟶ S` be smooth, separated and
quasi-compact, and let `j : X ⟶ Y` be a monomorphism over `S` into a proper `S`-scheme of
finite presentation. If for every field `k` and every `Spec k ⟶ S` the fibre of `f` is proper
and connected, then `f` is proper. -/
theorem isProper_of_fibres (f : X ⟶ S) [Smooth f] [IsSeparated f] [QuasiCompact f]
    (g : Y ⟶ S) [IsProper g] [LocallyOfFinitePresentation g] (j : X ⟶ Y) [Mono j]
    (hfac : j ≫ g = f)
    (hfib : ∀ (k : Type u) [Field k] (φ : Spec (CommRingCat.of k) ⟶ S),
      IsProper (pullback.snd f φ) ∧ ConnectedSpace ↥(pullback f φ)) :
    IsProper f := by
  have : GeometricallyConnected f :=
    ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun k _ φ => (hfib k φ).2⟩
  have : UniversallyClosed f := by
    refine UniversallyClosed.of_valuativeCriterion f fun sq => ?_
    let R := sq.R
    let K := sq.K
    let t := sq.i₂
    let f' := pullback.snd f t
    let g' := pullback.snd g t
    let j' := pullback.map f t g t j (𝟙 _) (𝟙 _) (by rw [Category.comp_id, hfac])
      (by rw [Category.comp_id, Category.id_comp])
    have : Mono j' := mono_pullbackMap f g j hfac t
    have hfac' : j' ≫ g' = f' := (pullback.lift_snd _ _ _).trans (Category.comp_id _)
    have : IsIntegrallyClosed R := inferInstance
    let φK := Spec.map (CommRingCat.ofHom (algebraMap R K))
    let φκ := Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
    have : IsProper (pullback.snd f (φK ≫ t)) := (hfib K _).1
    have : IsProper (pullback.snd f (φκ ≫ t)) := (hfib (IsLocalRing.ResidueField R) _).1
    have : IsProper (pullback.snd f' φK) := isProper_pullback_snd_pullback_snd f t φK
    have : IsProper (pullback.snd f' φκ) := isProper_pullback_snd_pullback_snd f t φκ
    have : Nonempty ↥(pullback f' φκ) := by
      have := (hfib (IsLocalRing.ResidueField R) (φκ ≫ t)).2
      exact ⟨(pullbackLeftPullbackSndIso f t φκ).inv (Classical.arbitrary _)⟩
    have hf' : IsProper f' := isProper_of_isLocalRing K f' g' j' hfac'
    have hE : ValuativeCriterion.Existence f' := by
      have h : UniversallyClosed f' := inferInstance
      rw [UniversallyClosed.eq_valuativeCriterion] at h
      exact h.1
    let sq' : ValuativeCommSq f' :=
      ⟨R, K, pullback.lift sq.i₁ φK sq.commSq.w, 𝟙 _,
        ⟨(pullback.lift_snd _ _ _).trans (Category.comp_id _).symm⟩⟩
    obtain ⟨⟨l, hl₁, hl₂⟩⟩ := (hE sq').exists_lift
    refine ⟨⟨⟨l ≫ pullback.fst f t, ?_, ?_⟩⟩⟩
    · change φK ≫ l ≫ pullback.fst f t = sq.i₁
      rw [← Category.assoc]
      rw [show φK ≫ l = pullback.lift sq.i₁ φK sq.commSq.w from hl₁, pullback.lift_fst]
    · change (l ≫ pullback.fst f t) ≫ f = t
      rw [Category.assoc, pullback.condition, ← Category.assoc]
      change (l ≫ f') ≫ t = t
      rw [show l ≫ f' = 𝟙 _ from hl₂, Category.id_comp]
  exact { }

/-- `isProper_of_fibres` for schemes over `S` in `Over S`. -/
theorem isProper_hom_of_fibres {X Y : Over S} (j : X ⟶ Y) [Smooth X.hom] [IsSeparated X.hom]
    [QuasiCompact X.hom] [IsProper Y.hom] [LocallyOfFinitePresentation Y.hom] [Mono j.left]
    (hfib : ∀ (k : Type u) [Field k] (φ : Spec (CommRingCat.of k) ⟶ S),
      IsProper ((Over.pullback φ).obj X).hom ∧ ConnectedSpace ((Over.pullback φ).obj X).left) :
    IsProper X.hom :=
  isProper_of_fibres X.hom Y.hom j.left (Over.w j) hfib

/-- `isProper_hom_of_fibres` with all hypotheses as explicit implications, for every base. -/
theorem properAmbientCriterion :
    ∀ (S : Scheme.{u}) (X Y : Over S) (j : X ⟶ Y),
      Smooth X.hom → IsSeparated X.hom → QuasiCompact X.hom →
      IsProper Y.hom → LocallyOfFinitePresentation Y.hom → Mono j.left →
      (∀ (k : Type u) [Field k] (f : Spec (CommRingCat.of k) ⟶ S),
        IsProper ((Over.pullback f).obj X).hom ∧
          ConnectedSpace ((Over.pullback f).obj X).left) →
      IsProper X.hom :=
  fun _ _ _ j _ _ _ _ _ _ hfib => isProper_hom_of_fibres j hfib

end Langlands.AlgebraicGeometry.ProperOfFibres
