/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.CategoryTheory.Functor.OfSequence
import WeilConjectures.AlgebraicGeometry.ClosedSupportedFormalAlgebraization
import WeilConjectures.AlgebraicGeometry.FormalSecondIdealQuotientAdic
import WeilConjectures.AlgebraicGeometry.FormalSecondIdealQuotientSupported
import WeilConjectures.AlgebraicGeometry.FormalSecondIdealAlgebraizationTransitions

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- Construction of the algebraized K-adic system, its comparison isomorphism and the map to the
`K`-adic completion of `H` induced by `α` through `θ`.
Source: Stacks Project, Tag 088A, construction of the systems G_e.
(blueprint: lem-weil-pbc-devissage-second-adic-system-lift-data)
The proof descends each quotient system to the closed subscheme V(K^(e+1)),
uses the assumed completion equivalence and pushes forward. This gives the terms `N_e` and the
comparisons `σ_e`. The `I`-adic system map `σ_e ≫ (α mod K^(e+1)) ≫ θ_e⁻¹` goes between
completions of coherent modules supported on V(K^(e+1)); full faithfulness of completion there
lifts it to `δ_e : N_e ⟶ H / K^(e+1) H`. Faithfulness on V(K^(e+2)), together with naturality
of `α mod K` and of `θ`, shows that the `δ_e` commute with the transitions. -/
theorem grothendieckDevissage_secondAdicSystem_lift_data
    {X : Scheme.{u}} [IsNoetherian X] (I K : X.IdealSheafData)
    (M : CoherentFormalModule X I)
    (hthick : ∀ (e : ℕ), 1 ≤ e →
      ∀ (hZ : IsNoetherian (K ^ e).subscheme),
        Functor.IsEquivalence
          (@completion ((K ^ e).subscheme) hZ (I.comap (K ^ e).subschemeι)))
    (H : CoherentModules X) (α : M ⟶ (completion X I).obj H)
    (θ : formalCompletionSystem K H.obj ⋙ formalCompletionFunctor I ≅
      (formalCompletionSystem I H.obj ⋙ formalCompletionFunctor K).flip) :
    ∃ (N : CoherentFormalModule X K) (δ : N ⟶ (completion X K).obj H)
      (σ : N.obj ⋙ formalCompletionFunctor I ≅
        (M.obj ⋙ formalCompletionFunctor K).flip),
      ∀ e n : ℕ,
        (σ.hom.app (op e)).app (op n) ≫
          formalModuleQuotientMap K (α.hom.app (op n)) (Nat.le_refl (e + 1)) =
        formalModuleQuotientMap I (δ.hom.app (op e)) (Nat.le_refl (n + 1)) ≫
          (θ.hom.app (op e)).app (op n) := by
  classical
  let B := (M.obj ⋙ formalCompletionFunctor K).flip
  have halg (e : ℕ) :
      ∃ (G : CoherentModules (K ^ (e + 1)).subscheme)
        (hG : RingedSpace.IsCoherent X.toRingedSpace
          ((Scheme.Modules.pushforward (K ^ (e + 1)).subschemeι).obj G.obj)),
        Nonempty (formalCompletionSystem I
          ((Scheme.Modules.pushforward (K ^ (e + 1)).subschemeι).obj G.obj) ≅ B.obj (op e)) := by
    have hQ := formalSecondIdealQuotient_coherent I K M e
    have hsupport := formalSecondIdealQuotient_supported I K M e
    let Q : CoherentFormalModule X I := ⟨B.obj (op e), hQ⟩
    obtain ⟨G, hG, ⟨β⟩⟩ := closedSupported_formal_algebraization
      (K ^ (e + 1)).subschemeι I
      (hthick (e + 1) (Nat.succ_le_succ (Nat.zero_le e)) _) Q hsupport
    exact ⟨G, hG, ⟨(ObjectProperty.ι (IsCoherentFormalModule I)).mapIso β⟩⟩
  choose G hG β using halg
  let b (e : ℕ) := (β e).some
  have ht := formalSecondIdealAlgebraization_transitions I K M hthick G b
  have hzero (e : ℕ) := (ht e).1
  choose t hq hb using fun e ↦ (ht e).2
  let F : ℕᵒᵖ ⥤ X.Modules := Functor.ofOpSequence
    (X := fun e ↦ (Scheme.Modules.pushforward (K ^ (e + 1)).subschemeι).obj (G e).obj) t
  have hstep (e : ℕ) : F.map (homOfLE (Nat.le_succ e)).op = t e :=
    Functor.ofOpSequence_map_homOfLE_succ
      (X := fun e ↦ (Scheme.Modules.pushforward (K ^ (e + 1)).subschemeι).obj (G e).obj) t e
  have hF : IsCoherentFormalModule K F := by
    refine ⟨hG, hzero, ?_⟩
    intro e
    obtain ⟨q, hq⟩ := hq e
    refine ⟨q, ?_⟩
    rw [hstep]
    exact hq
  let N : CoherentFormalModule X K := ⟨F, hF⟩
  let s : F ⋙ formalCompletionFunctor I ⟶ B :=
    NatTrans.ofOpSequence (fun e ↦ (b e).hom) (by
      intro e
      change formalCompletionMap I
        (F.map (homOfLE (Nat.le_succ e)).op) ≫ (b e).hom = _
      rw [hstep]
      exact hb e)
  have (a : ℕᵒᵖ) : IsIso (s.app a) := by
    change IsIso ((b a.unop).hom)
    infer_instance
  have : IsIso s := NatIso.isIso_of_isIso_app s
  let σ := asIso s
  -- The target quotients `H / K^(e+1) H`, supported on V(K^(e+1)).
  let Hq (e : ℕ) : CoherentModules X :=
    ⟨formalModuleQuotient K (e + 1) H.obj, (formalCompletionSystem_coherent K H).1 e⟩
  have hHq (e : ℕ) := (formalCompletionSystem_coherent K H).2.1 e
  let Fc (e : ℕ) : CoherentModules X := ⟨F.obj (op e), hG e⟩
  let γ := (flipFunctor _ _ _).map (Functor.whiskerRight α.hom (formalCompletionFunctor K))
  let a (e : ℕ) : formalCompletionSystem I (Fc e).obj ⟶ formalCompletionSystem I (Hq e).obj :=
    (b e).hom ≫ γ.app (op e) ≫ θ.inv.app (op e)
  have hlift (e : ℕ) : ∃ d : (Fc e).obj ⟶ (Hq e).obj, formalCompletionMap I d = a e := by
    let j := (K ^ (e + 1)).subschemeι
    obtain ⟨hf, _⟩ := supportedCompletion_fullyFaithful j I
      (hthick (e + 1) (by omega) (isNoetherian_of_locallyOfFiniteType j))
    let A : ObjectProperty.FullSubcategory
        (fun H : CoherentModules X ↦ CoherentModuleSupportedOn H j) :=
      ⟨Fc e, (coherentModuleSupportedOn_pow_subschemeι_iff K (e + 1) (by omega) _).mpr
        (hzero e)⟩
    let B : ObjectProperty.FullSubcategory
        (fun H : CoherentModules X ↦ CoherentModuleSupportedOn H j) :=
      ⟨Hq e, (coherentModuleSupportedOn_pow_subschemeι_iff K (e + 1) (by omega) _).mpr
        (hHq e)⟩
    exact ⟨((supportedCompletion j I).preimage (X := A) (Y := B) (a e)).hom.hom,
      (supportedCompletion j I).map_preimage (X := A) (Y := B) (a e)⟩
  choose d hd using hlift
  have hnat (e : ℕ) : F.map (homOfLE (Nat.le_succ e)).op ≫ d e =
      d (e + 1) ≫ (formalCompletionSystem K H.obj).map (homOfLE (Nat.le_succ e)).op := by
    let j := (K ^ (e + 2)).subschemeι
    obtain ⟨_, hf⟩ := supportedCompletion_fullyFaithful j I
      (hthick (e + 2) (by omega) (isNoetherian_of_locallyOfFiniteType j))
    let S₁ : ObjectProperty.FullSubcategory
        (fun H : CoherentModules X ↦ CoherentModuleSupportedOn H j) :=
      ⟨Fc (e + 1), (coherentModuleSupportedOn_pow_subschemeι_iff K (e + 2) (by omega) _).mpr
        (hzero (e + 1))⟩
    let S₂ : ObjectProperty.FullSubcategory
        (fun H : CoherentModules X ↦ CoherentModuleSupportedOn H j) :=
      ⟨Hq e, (coherentModuleSupportedOn_pow_subschemeι_iff K (e + 2) (by omega) _).mpr
        (isZero_idealModuleProduct_pow_succ K (e + 1) _ (hHq e))⟩
    let u : S₁ ⟶ S₂ := ObjectProperty.homMk (ObjectProperty.homMk
      (F.map (homOfLE (Nat.le_succ e)).op ≫ d e))
    let v : S₁ ⟶ S₂ := ObjectProperty.homMk (ObjectProperty.homMk
      (d (e + 1) ≫ (formalCompletionSystem K H.obj).map (homOfLE (Nat.le_succ e)).op))
    suffices huv : u = v from
      congrArg (fun w : S₁ ⟶ S₂ ↦ w.hom.hom) huv
    apply (supportedCompletion j I).map_injective
    change formalCompletionMap I (F.map (homOfLE (Nat.le_succ e)).op ≫ d e) =
      formalCompletionMap I
        (d (e + 1) ≫ (formalCompletionSystem K H.obj).map (homOfLE (Nat.le_succ e)).op)
    rw [(formalCompletionMap_laws I).2, (formalCompletionMap_laws I).2, hd, hd, hstep]
    have hγ := γ.naturality (homOfLE (Nat.le_succ e)).op
    have hθ' := θ.inv.naturality (homOfLE (Nat.le_succ e)).op
    have hbe : formalCompletionMap I (t e) ≫ (b e).hom = (b (e + 1)).hom ≫
        B.map (homOfLE (Nat.le_succ e)).op := hb e
    simp only [a, ← Category.assoc, hbe]
    simp only [Category.assoc]
    refine Eq.trans ?_ (congrArg (fun w ↦ (b (e + 1)).hom ≫ γ.app (op (e + 1)) ≫ w) hθ')
    have h1 := congrArg ((b (e + 1)).hom ≫ ·) (hγ =≫ θ.inv.app (op e))
    simp only [Category.assoc] at h1
    exact h1
  let δ : N ⟶ (completion X K).obj H :=
    ObjectProperty.homMk (NatTrans.ofOpSequence d hnat)
  refine ⟨N, δ, σ, fun e n ↦ ?_⟩
  have h := congrArg (fun w ↦ w.app (op n) ≫ (θ.hom.app (op e)).app (op n)) (hd e)
  simp only [a, NatTrans.comp_app, Category.assoc, ← NatTrans.comp_app (θ.inv.app (op e)),
    Iso.inv_hom_id_app, NatTrans.id_app] at h
  exact h.symm

end AlgebraicGeometry
