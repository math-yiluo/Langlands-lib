import Langlands.CategoryTheory.Renard.RepresentabilityUniversalStatements

/-!
# Representations and left universal properties

Proofs of the final remark and corollary of Renard A.III.2.
-/

universe w vA vB uA uB

open CategoryTheory Opposite

set_option backward.defeqAttrib.useBackward true

namespace Langlands.Renard.RepresentabilityUniversal

/-- Invertibility of the chosen transformation is equivalent to its universality. -/
theorem yonedaUniversalStatement :
    YonedaUniversalStatement.{w, vA, uA} := by
  classical
  intro C _ F X ω
  constructor
  · intro hω
    have := hω
    refine ⟨Limits.IsTerminal.ofUniqueHom
      (fun c => CostructuredArrow.homMk
        (uliftYoneda.{w}.preimage (c.hom ≫ inv ω)) (by simp)) ?_⟩
    intro c m
    apply CostructuredArrow.hom_ext
    apply uliftYoneda.{w}.map_injective
    apply (cancel_mono ω).1
    simpa using CostructuredArrow.w m
  · rintro ⟨h⟩
    have hbij (Y : C) : Function.Bijective (ω.app (op Y)) := by
      constructor
      · intro a b hab
        apply ULift.ext
        apply h.hom_ext
        apply uliftYonedaEquiv.{w}.injective
        simpa only [uliftYonedaEquiv_comp,
          uliftYonedaEquiv_uliftYoneda_map, ULift.up_down,
          CostructuredArrow.mk_hom_eq_self] using hab
      · intro b
        let θ : uliftYoneda.{w}.obj Y ⟶ F ⋙ uliftFunctor.{vA} :=
          uliftYonedaEquiv.{w}.symm b
        refine ⟨ULift.up (h.lift (CostructuredArrow.mk θ)), ?_⟩
        have hfac := congrArg uliftYonedaEquiv.{w}
          (h.fac (CostructuredArrow.mk θ))
        simpa only [uliftYonedaEquiv_comp,
          uliftYonedaEquiv_uliftYoneda_map, CostructuredArrow.mk_hom_eq_self,
          CostructuredArrow.mk_left,
          θ, Equiv.apply_symm_apply] using hfac
    have : ∀ Y : Cᵒᵖ, IsIso (ω.app Y) :=
      fun Y => (isIso_iff_bijective _).2 (hbij Y.unop)
    exact NatIso.isIso_of_isIso_app ω

/-- The natural Hom equivalence factors every arrow through its identity value. -/
theorem homPresheafUniversalStatement :
    HomPresheafUniversalStatement.{vA, vB, uA, uB} := by
  intro A _ B _ F Y X r
  refine ⟨Limits.IsTerminal.ofUniqueHom
    (fun c => CostructuredArrow.homMk (r.homEquiv.symm c.hom) ?_) ?_⟩
  · simpa using
      (r.homEquiv_eq (r.homEquiv.symm c.hom)).symm
  · intro c m
    apply CostructuredArrow.hom_ext
    apply r.homEquiv.injective
    change r.homEquiv m.left = r.homEquiv (r.homEquiv.symm c.hom)
    rw [Equiv.apply_symm_apply, r.homEquiv_eq]
    exact CostructuredArrow.w m

/-- Full faithfulness lifts the composite comparison and makes it unique. -/
theorem compatibleUniquenessStatement :
    CompatibleUniquenessStatement.{w, vA, uA} := by
  classical
  intro C _ F X X' ω ω'
  let e : X ≅ X' := uliftYoneda.{w}.preimageIso (ω ≪≫ ω'.symm)
  refine ⟨e, ?_, ?_⟩
  · simp [e]
  · intro e' he'
    apply Iso.ext
    apply uliftYoneda.{w}.map_injective
    apply (cancel_mono ω'.hom).1
    simpa [e] using he'

/-- Renard A.III.2: universality, the Hom-presheaf criterion, and compatible uniqueness. -/
theorem representabilityUniversalStatements :
    RepresentabilityUniversalStatements.{w, vA, vB, uA, uB} :=
  ⟨yonedaUniversalStatement, homPresheafUniversalStatement,
    compatibleUniquenessStatement⟩

end Langlands.Renard.RepresentabilityUniversal
