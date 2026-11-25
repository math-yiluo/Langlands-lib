/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.FourierTransform.Perverse
public import WeilConjectures.ConstructibleSheaf.LisseRankOne
public import WeilConjectures.AlgebraicGeometry.CondensedArtinSchreier
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.AdmissibleCondensedCoefficients
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
public import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
import WeilConjectures.AlgebraicGeometry.CondensedArtinSchreierProjectorFacts
import WeilConjectures.AlgebraicGeometry.CondensedArtinSchreierProjectorDescent

/-! # The Fourier kernel is lisse of rank one

Source: literature/blueprint/latest/blueprint/sec-fourier-transform/sk-thm-inversion/
prop-kernel-lisse.md (blueprint: lemma-artin-schreier-character-sheaf).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.Etale

open AlgebraicGeometry.Etale.DerivedCategory AlgebraicGeometry.ProEtale

private theorem rankOne_artinSchreierSheafOf
    {Λ : Type (u + 1)} [CommRing Λ]
    {k : Type u} [Field k] [Fintype k] [Invertible (Fintype.card k : Λ)]
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    (ψ : AddChar k Λ) (f : Γ(X, ⊤)) :
    Scheme.IsLisseRankOneSheaf (artinSchreierSheafOf X ψ f) := by
  let a := AffineSpace.artinSchreierMap PUnit (Spec (.of k)) (Fintype.card k)
  let b := AffineSpace.homOfVector (X ↘ Spec (.of k)) (fun _ : PUnit.{u + 1} ↦ f)
  have : Etale a := etale_artinSchreierMap (k := k)
  let U : Scheme.Cover.{u} Scheme.etalePrecoverage (AffineSpace PUnit (Spec (.of k))) :=
    .singleton a ((Scheme.singleton_mem_precoverage_iff (P := @Etale) _).2
      ⟨AffineSpace.surjective_artinSchreierMap k, inferInstance⟩)
  refine ⟨U.pullback₁ b, fun i ↦ ⟨?_⟩⟩
  change (upperStar (ModuleCat Λ) (pullback.fst b a)).obj
    ((upperStar (ModuleCat Λ) b).obj (artinSchreierSheaf ψ)) ≅ _
  exact (upperStarComp (ModuleCat Λ) (pullback.fst b a) b).symm.app _ ≪≫
    (upperStarComp (ModuleCat Λ) (pullback.snd b a) a _ pullback.condition).app _ ≪≫
    (upperStar (ModuleCat Λ) (pullback.snd b a)).mapIso
      (artinSchreierSheafUpperStarIso ψ) ≪≫
    (Functor.Monoidal.εIso (upperStar (ModuleCat Λ) (pullback.snd b a))).symm ≪≫
    Functor.Monoidal.εIso (presheafToSheaf _ (ModuleCat Λ))

-- Explicit monoidal module comparisons need additional elaboration heartbeats.
set_option linter.unusedVariables false in
-- Preserve the original statement's named, nondependent hypotheses verbatim.
/-- The Fourier kernel is lisse of rank one, of Tor amplitude `[0, 0]`, multiplicative in
the character, with tensor inverse the kernel of the inverse character. The four branches
are the finite small-etale kernel, the degree-`q` small-etale Artin--Schreier model, the
admissible condensed prime-field kernel and the degree-`q` condensed model.

Source: current blueprint, sec-fourier-transform/sk-thm-inversion/prop-kernel-lisse.md,
all clauses (blueprint: lemma-artin-schreier-character-sheaf).

Proof.
1. For finite coefficients use the proved character multiplication, inverse and Tor
   theorems of the source library. Pull back its counit trivialization of the degree-q
   Artin–Schreier sheaf along the function to obtain an explicit rank-one etale cover.
2. For condensed coefficients, split the self pullback of the Artin–Schreier cover into
   the translates of its diagonal. The canonical split-cover product map identifies
   pullback of the regular-module pushforward with a product indexed by the finite field.
   The deck-evaluation formula identifies translations with shifts of the coordinates.
3. Pullback is linear and preserves images. The finite character-projector calculation
   identifies the pulled-back image with the regular module by evaluation at zero,
   which is exactly the adjunction counit. Deck maps preserve multiplication and constants;
   therefore products of character images are fixed by the product-character projector.
4. Apply the monoidal-adjunction counit identity and conservativity of restriction to
   the Artin–Schreier cover to obtain the tensor-product and trivial-character unit
   isomorphisms. Pull them and the explicit trivializing cover back along the function.
   Taking the inverse character gives a tensor inverse, hence flatness and Tor amplitude
   [0,0]. Finally specialize the finite field to ULift (ZMod p), transporting the product
   and inverse characters by their defining equalities. No character is assumed nontrivial. -/
theorem prop_kernel_lisse :
    (∀ (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
      (p : ℕ) [Fact p.Prime] [Invertible (p : Λ)]
      {S V V' : Scheme.{u}} (π : V ⟶ S) (π' : V' ⟶ S)
      [CharP Γ(pullback π π', ⊤) p] (Ψ Ψ' : AddChar (ZMod p) Λ)
      (b : Γ(pullback π π', ⊤)),
      IsLisse ((_root_.DerivedCategory.singleFunctor _ 0).obj
        (fourierKernel Λ π π' Ψ b)) ∧
        Scheme.IsLisseRankOneSheaf (fourierKernel Λ π π' Ψ b) ∧
        Nonempty (fourierKernel Λ π π' Ψ b ⊗ fourierKernel Λ π π' Ψ' b ≅
          fourierKernel Λ π π' (Ψ * Ψ') b) ∧
        Nonempty (fourierKernel Λ π π' Ψ b ⊗ fourierKernel Λ π π' Ψ⁻¹ b ≅ 𝟙_ _) ∧
        DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) (pullback π π') 0 0
          ((_root_.DerivedCategory.singleFunctor _ 0).obj
            (fourierKernel Λ π π' Ψ b))) ∧
    (∀ (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
      (k : Type u) [Field k] [Fintype k]
      [Invertible (Fintype.card k : Λ)]
      (X : Scheme.{u}) [X.Over (Spec (.of k))]
      (ψ ψ' : AddChar k Λ) (f : Γ(X, ⊤)),
      Scheme.IsLocallyConstantSheaf (artinSchreierSheafOf X ψ f) ∧
        Nonempty (artinSchreierSheafOf X ψ f ⊗ artinSchreierSheafOf X ψ' f ≅
          artinSchreierSheafOf X (ψ * ψ') f) ∧
        Nonempty (artinSchreierSheafOf X ψ f ⊗ artinSchreierSheafOf X ψ⁻¹ f ≅ 𝟙_ _)) ∧
    (∀ (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
      [MonObj Λ] [IsCommMonObj Λ]
      (p : ℕ) [Fact p.Prime] (hp : IsUnit (p : MonObj.Γ Λ))
      (hΛ : ProEtale.CondensedRing.IsAdmissibleCoefficient Λ)
      (X : Scheme.{u}) [X.Over (Spec (.of (ULift.{u} (ZMod p))))]
      (Ψ Ψ' : AddChar (ZMod p) (MonObj.Γ Λ)) (b : Γ(X, ⊤)),
      IsLisseCoefficientModule Λ
          (condensedArtinSchreierSheafOf Λ (ULift.{u} (ZMod p)) X
            (Ψ.compAddMonoidHom AddEquiv.ulift.toAddMonoidHom) b) ∧
        (∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i : U.I₀,
          Nonempty ((ProEtale.CondensedRing.upperStar Λ (U.f i)).obj
            (condensedArtinSchreierSheafOf Λ (ULift.{u} (ZMod p)) X
              (Ψ.compAddMonoidHom AddEquiv.ulift.toAddMonoidHom) b) ≅
              Mod.regular (ProEtale.condensedRingObj Λ (U.X i)))) ∧
        Nonempty (
          condensedArtinSchreierSheafOf Λ (ULift.{u} (ZMod p)) X
              (Ψ.compAddMonoidHom AddEquiv.ulift.toAddMonoidHom) b ⊗
            condensedArtinSchreierSheafOf Λ (ULift.{u} (ZMod p)) X
              (Ψ'.compAddMonoidHom AddEquiv.ulift.toAddMonoidHom) b ≅
          condensedArtinSchreierSheafOf Λ (ULift.{u} (ZMod p)) X
            ((Ψ * Ψ').compAddMonoidHom AddEquiv.ulift.toAddMonoidHom) b) ∧
        Nonempty (
          condensedArtinSchreierSheafOf Λ (ULift.{u} (ZMod p)) X
              (Ψ.compAddMonoidHom AddEquiv.ulift.toAddMonoidHom) b ⊗
            condensedArtinSchreierSheafOf Λ (ULift.{u} (ZMod p)) X
              ((Ψ⁻¹).compAddMonoidHom AddEquiv.ulift.toAddMonoidHom) b ≅
          Mod.regular (ProEtale.condensedRingObj Λ X)) ∧
        _root_.DerivedCategory.torAmplitudeIn
          (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
            (ProEtale.condensedRingObj Λ X)) 0 0
          ((_root_.DerivedCategory.singleFunctor _ 0).obj
            (condensedArtinSchreierSheafOf Λ (ULift.{u} (ZMod p)) X
              (Ψ.compAddMonoidHom AddEquiv.ulift.toAddMonoidHom) b))) ∧
    (∀ (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
      [MonObj Λ] [IsCommMonObj Λ]
      (k : Type u) [Field k] [Fintype k]
      (hq : IsUnit (Fintype.card k : MonObj.Γ Λ))
      (hΛ : ProEtale.CondensedRing.IsAdmissibleCoefficient Λ)
      (X : Scheme.{u}) [X.Over (Spec (.of k))]
      (ψ ψ' : AddChar k (MonObj.Γ Λ)) (f : Γ(X, ⊤)),
      IsLisseCoefficientModule Λ (condensedArtinSchreierSheafOf Λ k X ψ f) ∧
        (∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i : U.I₀,
          Nonempty ((ProEtale.CondensedRing.upperStar Λ (U.f i)).obj
            (condensedArtinSchreierSheafOf Λ k X ψ f) ≅
              Mod.regular (ProEtale.condensedRingObj Λ (U.X i)))) ∧
        Nonempty (condensedArtinSchreierSheafOf Λ k X ψ f ⊗
            condensedArtinSchreierSheafOf Λ k X ψ' f ≅
          condensedArtinSchreierSheafOf Λ k X (ψ * ψ') f) ∧
        Nonempty (condensedArtinSchreierSheafOf Λ k X ψ f ⊗
            condensedArtinSchreierSheafOf Λ k X ψ⁻¹ f ≅
          Mod.regular (ProEtale.condensedRingObj Λ X)) ∧
        _root_.DerivedCategory.torAmplitudeIn
          (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
            (ProEtale.condensedRingObj Λ X)) 0 0
          ((_root_.DerivedCategory.singleFunctor _ 0).obj
            (condensedArtinSchreierSheafOf Λ k X ψ f))) := by
  suffices H : ∀ (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
      [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k] [Fintype k]
      (hq : IsUnit (Fintype.card k : MonObj.Γ Λ))
      (hΛ : ProEtale.CondensedRing.IsAdmissibleCoefficient Λ)
      (X : Scheme.{u}) [X.Over (Spec (.of k))]
      (ψ ψ' : AddChar k (MonObj.Γ Λ)) (f : Γ(X, ⊤)),
      IsLisseCoefficientModule Λ (condensedArtinSchreierSheafOf Λ k X ψ f) ∧
        (∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i : U.I₀,
          Nonempty ((ProEtale.CondensedRing.upperStar Λ (U.f i)).obj
            (condensedArtinSchreierSheafOf Λ k X ψ f) ≅
              Mod.regular (ProEtale.condensedRingObj Λ (U.X i)))) ∧
        Nonempty (condensedArtinSchreierSheafOf Λ k X ψ f ⊗
            condensedArtinSchreierSheafOf Λ k X ψ' f ≅
          condensedArtinSchreierSheafOf Λ k X (ψ * ψ') f) ∧
        Nonempty (condensedArtinSchreierSheafOf Λ k X ψ f ⊗
            condensedArtinSchreierSheafOf Λ k X ψ⁻¹ f ≅
          Mod.regular (ProEtale.condensedRingObj Λ X)) ∧
        _root_.DerivedCategory.torAmplitudeIn
          (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
            (ProEtale.condensedRingObj Λ X)) 0 0
          ((_root_.DerivedCategory.singleFunctor _ 0).obj
            (condensedArtinSchreierSheafOf Λ k X ψ f)) by
    refine ⟨?_, ?_, ?_, H⟩
    · intro Λ _ _ p _ _ S V V' π π' _ Ψ Ψ' b
      have ht := torAmplitudeIn_fourierKernel Λ π π' Ψ b
      refine ⟨?_, ?_, nonempty_iso_fourierKernel_mul Λ π π' Ψ Ψ' b,
        nonempty_iso_fourierKernel_inv Λ π π' Ψ b, ht⟩
      · exact ⟨isDualizable_fourierKernel Λ π π' Ψ b,
          ⟨DerivedCategory.boundedConstructible_singleFunctor_obj _ 0, 0, 0, ht⟩,
          ht, fourierKernel Λ π π' Ψ b, inferInstance, ⟨Iso.refl _⟩⟩
      · let := (pullback π π').overSpecZModOfCharP p
        unfold fourierKernel artinSchreierSheafZMod
        exact rankOne_artinSchreierSheafOf _ _ b
    · intro Λ _ _ k _ _ _ X _ ψ ψ' f
      exact ⟨inferInstance, nonempty_iso_artinSchreierSheafOf_mul X ψ ψ' f,
        nonempty_iso_artinSchreierSheafOf_inv X ψ f⟩
    · intro Λ _ _ p _ hp hΛ X _ Ψ Ψ' b
      have hq : IsUnit (Fintype.card (ULift.{u} (ZMod p)) : MonObj.Γ Λ) := by
        simpa only [Fintype.card_ulift, ZMod.card] using hp
      have hm : (Ψ * Ψ').compAddMonoidHom AddEquiv.ulift.toAddMonoidHom =
          Ψ.compAddMonoidHom AddEquiv.ulift.toAddMonoidHom *
            Ψ'.compAddMonoidHom AddEquiv.ulift.toAddMonoidHom := by ext; rfl
      have hi : (Ψ⁻¹).compAddMonoidHom AddEquiv.ulift.toAddMonoidHom =
          (Ψ.compAddMonoidHom AddEquiv.ulift.toAddMonoidHom)⁻¹ := by ext; rfl
      obtain ⟨h1, h2, ⟨em⟩, ⟨ei⟩, h5⟩ := H Λ (ULift.{u} (ZMod p)) hq hΛ X
        (Ψ.compAddMonoidHom AddEquiv.ulift.toAddMonoidHom)
        (Ψ'.compAddMonoidHom AddEquiv.ulift.toAddMonoidHom) b
      refine ⟨h1, h2, ⟨?_⟩, ⟨?_⟩, h5⟩
      · exact em ≪≫ eqToIso (congrArg
          (fun χ ↦ condensedArtinSchreierSheafOf Λ (ULift.{u} (ZMod p)) X χ b) hm.symm)
      · exact (tensorIso (Iso.refl _) (eqToIso (congrArg
          (fun χ ↦ condensedArtinSchreierSheafOf Λ (ULift.{u} (ZMod p)) X χ b) hi))) ≪≫ ei
  intro Λ _ _ k _ _ hq hΛ X _ ψ ψ' f
  let := hq.invertible
  exact condensedArtinSchreier_properties_of_projectors Λ k
    (condensedArtinSchreierProjector_evaluation Λ k)
    (fun χ χ' ↦ (condensedArtinSchreierProjector_products Λ k χ χ').1)
    (condensedArtinSchreierProjector_products Λ k ψ ψ').2 X ψ ψ' f

end AlgebraicGeometry.Etale
