/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.CategoryTheory.Functor.OfSequence
import all WeilConjectures.AlgebraicGeometry.GrothendieckExistenceSupportedHom
import all WeilConjectures.AlgebraicGeometry.IdealPowerProductRestrictionZero

/-! # Lifting the comparison map of the second adic system

Source: Stacks Project, Tag 088A, construction of the maps G_e → H/K^e H.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- Full faithfulness of supported completion, transported through closed pushforward. -/
private theorem supported_completion_bijective
    {X Z : Scheme.{u}} [IsNoetherian X] (j : Z ⟶ X) [IsClosedImmersion j]
    (I : X.IdealSheafData)
    (he : (@completion Z (isNoetherian_of_locallyOfFiniteType j) (I.comap j)).IsEquivalence)
    (F G : CoherentModules X)
    (hF : CoherentModuleSupportedOn F j) (hG : CoherentModuleSupportedOn G j) :
    Function.Bijective (formalCompletionMap I : (F.obj ⟶ G.obj) → _) := by
  classical
  let : IsNoetherian Z := isNoetherian_of_locallyOfFiniteType j
  obtain ⟨E, ⟨β⟩⟩ := closedImmersion_coherent_equivalence j
  let Fs := (⟨F, hF⟩ : ObjectProperty.FullSubcategory
    (fun L : CoherentModules X ↦ CoherentModuleSupportedOn L j))
  let Gs := (⟨G, hG⟩ : ObjectProperty.FullSubcategory
    (fun L : CoherentModules X ↦ CoherentModuleSupportedOn L j))
  let FZ := E.inverse.obj Fs
  let GZ := E.inverse.obj Gs
  let A := ObjectProperty.ι (fun L : CoherentModules X ↦ CoherentModuleSupportedOn L j) ⋙
    ObjectProperty.ι (RingedSpace.IsCoherent X.toRingedSpace)
  let a : F.obj ≅ (Scheme.Modules.pushforward j).obj FZ.obj :=
    (A.mapIso (E.counitIso.app Fs)).symm ≪≫ β.app FZ
  let b : G.obj ≅ (Scheme.Modules.pushforward j).obj GZ.obj :=
    (A.mapIso (E.counitIso.app Gs)).symm ≪≫ β.app GZ
  let P := Scheme.Modules.pushforward j
  obtain ⟨hP⟩ := (Functor.FullyFaithful.nonempty_iff_map_bijective P).mpr
    ((closedImmersion_pushforward_fullyFaithful j).2)
  let C := completion Z (I.comap j)
  let := he
  let U := ObjectProperty.ι (RingedSpace.IsCoherent Z.toRingedSpace)
  have hC : C.FullyFaithful := Functor.FullyFaithful.ofFullyFaithful C
  have hCV := hC.comp (ObjectProperty.fullyFaithfulι (IsCoherentFormalModule (I.comap j)))
  obtain ⟨θ, _⟩ := (closedImmersion_coherentFormal_equivalence j I).2
  have hH : (U ⋙ P ⋙ formalCompletionFunctor I).FullyFaithful :=
    (hCV.comp (hP.whiskeringRight ℕᵒᵖ)).ofIso θ.symm
  have hcomposite := hH.map_bijective FZ GZ
  have hPcoh := ((ObjectProperty.fullyFaithfulι
    (RingedSpace.IsCoherent Z.toRingedSpace)).comp hP).map_bijective FZ GZ
  have hquot : Function.Bijective
      ((formalCompletionFunctor I).map : (P.obj FZ.obj ⟶ P.obj GZ.obj) → _) := by
    constructor
    · intro v w h
      obtain ⟨v', rfl⟩ := hPcoh.surjective v
      obtain ⟨w', rfl⟩ := hPcoh.surjective w
      exact congrArg (U ⋙ P).map (hcomposite.injective h)
    · intro v
      obtain ⟨w, hw⟩ := hcomposite.surjective v
      exact ⟨(U ⋙ P).map w, hw⟩
  exact map_bijective_of_isos (formalCompletionFunctor I) a b hquot

/-- Raising an annihilating power preserves annihilation. -/
private theorem annihilated_higher_power
    {X : Scheme.{u}} (K : X.IdealSheafData) (F : X.Modules)
    {a b : ℕ} (h : a ≤ b)
    (hz : IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι a).2 F)) :
    IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι b).2 F) := by
  obtain ⟨k, hk⟩ := formalModuleQuotient_factor K (𝟙 F) h
  have hi := hz.eq_zero_of_src
    (Scheme.idealModuleProductι (Scheme.idealSheafPower K.toModulesι a).2 F)
  have : Mono (Scheme.idealModuleProductι (Scheme.idealSheafPower K.toModulesι b).2 F) := by
    dsimp [Scheme.idealModuleProductι]
    infer_instance
  apply IsZero.of_mono_eq_zero
    (Scheme.idealModuleProductι (Scheme.idealSheafPower K.toModulesι b).2 F)
  simpa [hi] using hk

/-- Supported completion gives a Hom bijection for any two bounded K-torsion modules. -/
private theorem torsion_completion_bijective
    {X : Scheme.{u}} [IsNoetherian X] (I K : X.IdealSheafData)
    (hthick : ∀ (e : ℕ), 1 ≤ e →
      ∀ (hZ : IsNoetherian (K ^ e).subscheme),
        Functor.IsEquivalence
          (@completion ((K ^ e).subscheme) hZ (I.comap (K ^ e).subschemeι)))
    (F G : CoherentModules X) (a b : ℕ)
    (hF : IsZero (Scheme.idealModuleProduct
      (Scheme.idealSheafPower K.toModulesι (a + 1)).2 F.obj))
    (hG : IsZero (Scheme.idealModuleProduct
      (Scheme.idealSheafPower K.toModulesι (b + 1)).2 G.obj)) :
    Function.Bijective (formalCompletionMap I : (F.obj ⟶ G.obj) → _) := by
  let q := max (a + 1) (b + 1)
  have hq : 0 < q := lt_of_lt_of_le (Nat.succ_pos a) (le_max_left _ _)
  have hFs := annihilated_higher_power K F.obj (le_max_left (a + 1) (b + 1)) hF
  have hGs := annihilated_higher_power K G.obj (le_max_right (a + 1) (b + 1)) hG
  have hsupp (L : CoherentModules X)
      (hz : IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι q).2
        L.obj)) : CoherentModuleSupportedOn L (K ^ q).subschemeι := by
    change IsZero (Scheme.idealModuleProduct (K ^ q).subschemeι.ker.toModulesι L.obj)
    rw [Scheme.IdealSheafData.ker_subschemeι]
    have := Scheme.Modules.power_mono K q
    let p := Subobject.isoOfMkEqMk _ _ (Scheme.Modules.power_subobject K q)
    have hp : p.hom ≫ (K ^ q).toModulesι = (Scheme.idealSheafPower K.toModulesι q).2 := by
      simp [p]
    obtain ⟨d⟩ := Scheme.Modules.product_iso _ _ p hp L.obj
    exact d.isZero_iff.mp hz
  exact supported_completion_bijective (K ^ q).subschemeι I (hthick q hq _)
    F G (hsupp F hFs) (hsupp G hGs)

/-- Construct a comparison map for an already algebraized second-ideal system.
Source: Stacks Project, Tag 088A (lemma-existence-tricky), construction of
G_e → H/K^e H, using the closed-immersion equivalence of Tag 087T.
https://stacks.math.columbia.edu/tag/088A
(blueprint: lem-weil-pbc-devissage-second-adic-system-lift-compatibility).

Proof: Coherent modules killed by powers of K descend to a common closed thickening.
Closed pushforward is fully faithful and commutes naturally with I-completion.
The assumed completion equivalence on that thickening therefore gives a bijection
on Hom sets for the ambient I-completion. Form the doubly natural morphism τ by
composing σ, the K-reduction of α, and θ inverse. The terms N_e and H/K^(e+1)H
are coherent and annihilated by K^(e+1), so surjectivity lifts τ_e uniquely to d_e.
For adjacent indices, the two composites of d with the transitions have equal
I-completions by naturality of τ. Both endpoints are killed by a common higher
power of K, so injectivity makes the composites equal. Assemble these adjacent
compatible maps as a natural transformation δ. Its component lifting equations,
composed with θ, give precisely the displayed squares. The maps are uniquely
specified by their completions; no arbitrary witness or square hypothesis is used. -/
theorem grothendieckDevissage_secondAdicSystem_lift_compatibility
    {X : Scheme.{u}} [IsNoetherian X] (I K : X.IdealSheafData)
    (M : CoherentFormalModule X I)
    (hthick : ∀ (e : ℕ), 1 ≤ e →
      ∀ (hZ : IsNoetherian (K ^ e).subscheme),
        Functor.IsEquivalence
          (@completion ((K ^ e).subscheme) hZ (I.comap (K ^ e).subschemeι)))
    (H : CoherentModules X) (α : M ⟶ (completion X I).obj H)
    (θ : formalCompletionSystem K H.obj ⋙ formalCompletionFunctor I ≅
      (formalCompletionSystem I H.obj ⋙ formalCompletionFunctor K).flip)
    {N : CoherentFormalModule X K}
    (σ : N.obj ⋙ formalCompletionFunctor I ≅
      (M.obj ⋙ formalCompletionFunctor K).flip) :
    ∃ (δ : N ⟶ (completion X K).obj H), ∀ e n : ℕ,
      (σ.hom.app (op e)).app (op n) ≫
          formalModuleQuotientMap K (α.hom.app (op n)) (Nat.le_refl (e + 1)) =
        formalModuleQuotientMap I (δ.hom.app (op e)) (Nat.le_refl (n + 1)) ≫
          (θ.hom.app (op e)).app (op n) := by
  classical
  let Q := (completion X K).obj H
  let τ : N.obj ⋙ formalCompletionFunctor I ⟶ Q.obj ⋙ formalCompletionFunctor I :=
    σ.hom ≫ (flipFunctor ℕᵒᵖ ℕᵒᵖ X.Modules).map
      (Functor.whiskerRight α.hom (formalCompletionFunctor K)) ≫ θ.inv
  have hbij (e f : ℕ) : Function.Bijective
      (formalCompletionMap I : (N.obj.obj (op e) ⟶ Q.obj.obj (op f)) → _) :=
    torsion_completion_bijective I K hthick
      ⟨N.obj.obj (op e), N.property.1 e⟩ ⟨Q.obj.obj (op f), Q.property.1 f⟩
      e f (N.property.2.1 e) (Q.property.2.1 f)
  have hlift (e : ℕ) : ∃ d : N.obj.obj (op e) ⟶ Q.obj.obj (op e),
      formalCompletionMap I d = τ.app (op e) :=
    (hbij e e).surjective (τ.app (op e))
  choose d hd using hlift
  have hn (e : ℕ) : N.obj.map (homOfLE (Nat.le_succ e)).op ≫ d e =
      d (e + 1) ≫ Q.obj.map (homOfLE (Nat.le_succ e)).op := by
    apply (hbij (e + 1) e).injective
    change (formalCompletionFunctor I).map (_ ≫ _) =
      (formalCompletionFunctor I).map (_ ≫ _)
    rw [Functor.map_comp, Functor.map_comp]
    change formalCompletionMap I (N.obj.map (homOfLE (Nat.le_succ e)).op) ≫
        formalCompletionMap I (d e) = formalCompletionMap I (d (e + 1)) ≫
        formalCompletionMap I (Q.obj.map (homOfLE (Nat.le_succ e)).op)
    rw [hd, hd]
    exact τ.naturality (homOfLE (Nat.le_succ e)).op
  let δ : N ⟶ Q := ObjectProperty.homMk (NatTrans.ofOpSequence d hn)
  refine ⟨δ, ?_⟩
  intro e n
  have he := congrArg (fun f ↦ f.app (op n)) (hd e)
  change formalModuleQuotientMap I (d e) (Nat.le_refl (n + 1)) =
    (σ.hom.app (op e)).app (op n) ≫
      formalModuleQuotientMap K (α.hom.app (op n)) (Nat.le_refl (e + 1)) ≫
        (θ.inv.app (op e)).app (op n) at he
  change _ = formalModuleQuotientMap I (d e) (Nat.le_refl (n + 1)) ≫ _
  rw [he]
  simp only [Category.assoc, Iso.inv_hom_id_app_app]
  exact congrArg ((σ.hom.app (op e)).app (op n) ≫ ·) (Category.comp_id _).symm

end AlgebraicGeometry
