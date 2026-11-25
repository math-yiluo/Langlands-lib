/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
import all WeilConjectures.AlgebraicGeometry.CoherentFormalModule
import all WeilConjectures.AlgebraicGeometry.ThickeningSystemPushforwardAdic
import WeilConjectures.AlgebraicGeometry.ClosedImmersionCoherentEquivalence
import WeilConjectures.AlgebraicGeometry.ClosedImmersionPushforwardFullyFaithful
import WeilConjectures.AlgebraicGeometry.ClosedImmersionPushforwardAnnihilated
import WeilConjectures.AlgebraicGeometry.FinitePushforwardCoherent
import WeilConjectures.AlgebraicGeometry.GrothendieckDevissageSecondAdicSystemComparison

/-! # Adjacent maps between second-ideal algebraizations

Source: Stacks Project, Tag 088A, the maps G_(e+1) to G_e.
(blueprint: lem-weil-pbc-formal-second-ideal-algebraization-transitions).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- The `I`-adic completion `F ↦ (F / I^(n+1) F)_n` restricted to coherent modules supported
on the closed subscheme `Z`. -/
noncomputable abbrev supportedCompletion {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (I : X.IdealSheafData) :=
  ObjectProperty.ι (fun F : CoherentModules X ↦ CoherentModuleSupportedOn F i) ⋙
    ObjectProperty.ι (RingedSpace.IsCoherent X.toRingedSpace) ⋙ formalCompletionFunctor I

/-- If completion on the closed subscheme `Z` is an equivalence, then completion of coherent
modules supported on `Z` is fully faithful. Proof: transport full faithfulness across the closed
coherent equivalence and its natural completion comparison. -/
theorem supportedCompletion_fullyFaithful {X Z : Scheme.{u}}
    [IsNoetherian X] (i : Z ⟶ X) [IsClosedImmersion i] (I : X.IdealSheafData)
    (he : (@completion Z (isNoetherian_of_locallyOfFiniteType i)
      (I.comap i)).IsEquivalence) :
    (supportedCompletion i I).Full ∧ (supportedCompletion i I).Faithful := by
  classical
  let : IsNoetherian Z := isNoetherian_of_locallyOfFiniteType i
  let := he
  let P := Scheme.Modules.pushforward i
  have hbij := (closedImmersion_pushforward_fullyFaithful i).2
  let : P.Full := ⟨fun {G H} ↦ (hbij G H).2⟩
  let : P.Faithful := ⟨fun {G H} ↦ (hbij G H).1⟩
  obtain ⟨E, ⟨α⟩⟩ := closedImmersion_coherent_equivalence i
  obtain ⟨θ, _⟩ := (closedImmersion_coherentFormal_equivalence i I).2
  let D := ObjectProperty.ι (RingedSpace.IsCoherent Z.toRingedSpace) ⋙ P ⋙
    formalCompletionFunctor I
  let R := completion Z (I.comap i) ⋙ ObjectProperty.ι (IsCoherentFormalModule
    (I.comap i)) ⋙ (Functor.whiskeringRight ℕᵒᵖ Z.Modules X.Modules).obj P
  have hθ : D ≅ R := θ
  let : D.Full := Functor.Full.of_iso hθ.symm
  let : D.Faithful := Functor.Faithful.of_iso hθ.symm
  let C := supportedCompletion i I
  have hα : E.functor ⋙ C ≅ D := Functor.isoWhiskerRight α (formalCompletionFunctor I)
  let : (E.functor ⋙ C).Full := Functor.Full.of_iso hα.symm
  let : (E.functor ⋙ C).Faithful := Functor.Faithful.of_iso hα.symm
  have hε : E.inverse ⋙ (E.functor ⋙ C) ≅ C :=
    Functor.isoWhiskerRight E.counitIso C ≪≫ Functor.leftUnitor C
  exact ⟨Functor.Full.of_iso hε, Functor.Faithful.of_iso hε⟩

/-- Identify the recursive multiplication-image power with the subscheme ideal. -/
theorem coherentModuleSupportedOn_pow_subschemeι_iff {X : Scheme.{u}} (K : X.IdealSheafData)
    (r : ℕ) (hr : 0 < r) (F : CoherentModules X) :
    CoherentModuleSupportedOn F (K ^ r).subschemeι ↔
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι r).2 F.obj) := by
  obtain ⟨a, ha⟩ := power_inclusion_iso K r hr
  obtain ⟨d, _⟩ := product_inclusion_iso _ _ a ha F.obj
  change IsZero (Scheme.idealModuleProduct (K ^ r).subschemeι.ker.toModulesι F.obj) ↔ _
  rw [Scheme.IdealSheafData.ker_subschemeι]
  exact ⟨fun h ↦ h.of_iso d, fun h ↦ h.of_iso d.symm⟩

/-- A module killed by `K ^ r` is killed by `K ^ (r + 1)`: the product with the larger power
factors through the product with the smaller one. -/
theorem isZero_idealModuleProduct_pow_succ {X : Scheme.{u}} (K : X.IdealSheafData) (r : ℕ)
    (F : X.Modules)
    (h : IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι r).2 F)) :
    IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι (r + 1)).2 F) := by
  obtain ⟨k, hk⟩ := formalModuleQuotient_factor K (𝟙 F) (Nat.le_succ r)
  have hi : Scheme.idealModuleProductι (Scheme.idealSheafPower K.toModulesι r).2 F = 0 :=
    h.eq_zero_of_src _
  have hm := idealModuleProduct_mono (Scheme.idealSheafPower K.toModulesι (r + 1)).2 F
  apply IsZero.of_mono_eq_zero
    (Scheme.idealModuleProductι (Scheme.idealSheafPower K.toModulesι (r + 1)).2 _)
  simpa only [Category.comp_id, hi, comp_zero] using hk

/-- The closed ideal kills pushforward; compare the two ideal-power inclusions. -/
private theorem pushforward_power_zero {X : Scheme.{u}} [IsNoetherian X]
    (K : X.IdealSheafData) (e : ℕ) (G : CoherentModules (K ^ (e + 1)).subscheme) :
    IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι (e + 1)).2
      ((Scheme.Modules.pushforward (K ^ (e + 1)).subschemeι).obj G.obj)) := by
  let i := (K ^ (e + 1)).subschemeι
  let : IsNoetherian (K ^ (e + 1)).subscheme := isNoetherian_of_locallyOfFiniteType i
  have : G.obj.IsQuasicoherent :=
    ((Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType _ _).mp G.property).1
  obtain ⟨a, ha⟩ := power_inclusion_iso K (e + 1) (Nat.succ_pos e)
  obtain ⟨d, _⟩ := product_inclusion_iso _ _ a ha
    ((Scheme.Modules.pushforward i).obj G.obj)
  apply IsZero.of_iso _ d
  apply (product_zero_iff (K ^ (e + 1)) _).mpr
  intro V a ha s
  have hk : i.ker = K ^ (e + 1) := Scheme.IdealSheafData.ker_subschemeι _
  exact ((Scheme.Modules.closedImmersion_pushforward_annihilated i).1 G.obj).2
    V a (hk.symm ▸ ha) s

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Adjacent quotient transitions lift to maps inducing the smaller K-quotient.
Source: Stacks Project, Tag 088A, construction of the transitions of G_e.
(blueprint: lem-weil-pbc-formal-second-ideal-algebraization-transitions).

Proof: Write F_e for the pushforward of G_e from V(K^(e+1)). It is annihilated
by K^(e+1): on each affine open the action factors through the quotient ring, and
the section image of the recursively defined power is the corresponding ideal
power. Both F_(e+1) and F_e are annihilated by K^(e+2). Closed pushforward and
completion on V(K^(e+2)) therefore identify maps between them with maps between
their I-completions. Lift the adjacent transition of the double quotient system,
conjugated by the supplied comparison isomorphisms, to obtain t. Its completion
square is the displayed equation by construction. The map factors through the
K^(e+1)-quotient since the target is annihilated by that power. Completion of this
factor is an isomorphism: the iterated K-quotient equals the smaller K-quotient,
naturally in the I-level. Both modules in the factor lie on V(K^(e+1)), where
completion is an equivalence and reflects isomorphisms. Thus the factor is the
required q, and its composite with the quotient projection is t. -/
theorem formalSecondIdealAlgebraization_transitions
    {X : Scheme.{u}} [IsNoetherian X] (I K : X.IdealSheafData)
    (M : CoherentFormalModule X I)
    (hthick : ∀ (e : ℕ), 1 ≤ e →
      ∀ (hZ : IsNoetherian (K ^ e).subscheme),
        Functor.IsEquivalence
          (@completion ((K ^ e).subscheme) hZ (I.comap (K ^ e).subschemeι)))
    (G : ∀ e : ℕ, CoherentModules (K ^ (e + 1)).subscheme)
    (β : ∀ e : ℕ,
      formalCompletionSystem I
          ((Scheme.Modules.pushforward (K ^ (e + 1)).subschemeι).obj (G e).obj) ≅
        (M.obj ⋙ formalCompletionFunctor K).flip.obj (op e)) :
    ∀ e : ℕ,
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι (e + 1)).2
        ((Scheme.Modules.pushforward (K ^ (e + 1)).subschemeι).obj (G e).obj)) ∧
      ∃ t : (Scheme.Modules.pushforward (K ^ (e + 2)).subschemeι).obj (G (e + 1)).obj ⟶
          (Scheme.Modules.pushforward (K ^ (e + 1)).subschemeι).obj (G e).obj,
        (∃ q : formalModuleQuotient K (e + 1)
            ((Scheme.Modules.pushforward (K ^ (e + 2)).subschemeι).obj (G (e + 1)).obj) ≅
            (Scheme.Modules.pushforward (K ^ (e + 1)).subschemeι).obj (G e).obj,
          formalModuleQuotientπ K (e + 1) _ ≫ q.hom = t) ∧
        formalCompletionMap I t ≫ (β e).hom =
          (β (e + 1)).hom ≫
            (M.obj ⋙ formalCompletionFunctor K).flip.map (homOfLE (Nat.le_succ e)).op := by
  classical
  let F (e : ℕ) : CoherentModules X :=
    ⟨(Scheme.Modules.pushforward (K ^ (e + 1)).subschemeι).obj (G e).obj,
      (Scheme.Modules.isCoherent_pushforward_of_isFinite
        (K ^ (e + 1)).subschemeι (G e).obj (G e).property).1⟩
  have hz (e : ℕ) := pushforward_power_zero K e (G e)
  intro e
  refine ⟨hz e, ?_⟩
  let i := (K ^ (e + 2)).subschemeι
  have hsrc : CoherentModuleSupportedOn (F (e + 1)) i :=
    (coherentModuleSupportedOn_pow_subschemeι_iff K (e + 2) (by omega) _).mpr (hz (e + 1))
  have htgt : CoherentModuleSupportedOn (F e) i :=
    (coherentModuleSupportedOn_pow_subschemeι_iff K (e + 2) (by omega) _).mpr
      (isZero_idealModuleProduct_pow_succ K (e + 1) _ (hz e))
  let A : ObjectProperty.FullSubcategory
      (fun H : CoherentModules X ↦ CoherentModuleSupportedOn H i) := ⟨F (e + 1), hsrc⟩
  let B : ObjectProperty.FullSubcategory
      (fun H : CoherentModules X ↦ CoherentModuleSupportedOn H i) := ⟨F e, htgt⟩
  let C := supportedCompletion i I
  obtain ⟨hf, hg⟩ := supportedCompletion_fullyFaithful i I
    (hthick (e + 2) (by omega) (isNoetherian_of_locallyOfFiniteType i))
  let : C.Full := hf
  let : C.Faithful := hg
  let τ := (M.obj ⋙ formalCompletionFunctor K).flip.map (homOfLE (Nat.le_succ e)).op
  let a : C.obj A ⟶ C.obj B := (β (e + 1)).hom ≫ τ ≫ (β e).inv
  let t' : A ⟶ B := C.preimage a
  let t : (F (e + 1)).obj ⟶ (F e).obj := t'.hom.hom
  have ht : formalCompletionMap I t = a := C.map_preimage a
  have htβ : formalCompletionMap I t ≫ (β e).hom = (β (e + 1)).hom ≫ τ := by
    rw [ht]
    simp only [a, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hkill : Scheme.idealModuleProductι
      (Scheme.idealSheafPower K.toModulesι (e + 1)).2 (F (e + 1)).obj ≫ t = 0 := by
    obtain ⟨k, hk⟩ := formalModuleQuotient_factor K t (Nat.le_refl (e + 1))
    have hi : Scheme.idealModuleProductι
        (Scheme.idealSheafPower K.toModulesι (e + 1)).2 (F e).obj = 0 :=
      (hz e).eq_zero_of_src _
    rw [hk, hi, comp_zero]
  let s : formalModuleQuotient K (e + 1) (F (e + 1)).obj ⟶ (F e).obj :=
    cokernel.desc _ t hkill
  have hs : formalModuleQuotientπ K (e + 1) (F (e + 1)).obj ≫ s = t :=
    cokernel.π_desc _ _ _
  have hscomp : IsIso (formalCompletionMap I s) := by
    have happ (n : ℕᵒᵖ) : IsIso ((formalCompletionMap I s).app n) := by
      obtain ⟨θ, hθ⟩ := grothendieckDevissage_secondAdicSystem_comparison I K (F (e + 1)).obj
      let d := (θ.app (op e)).app n
      let b := ((formalCompletionFunctor K).mapIso ((β (e + 1)).app n)).app (op e)
      obtain ⟨c, hc⟩ := formalModuleQuotient_iterated K (M.obj.obj n) (Nat.le_succ (e + 1))
      have heq : (formalCompletionMap I s).app n ≫ ((β e).app n).hom =
          d.hom ≫ b.hom ≫ c.hom := by
        have hpI : Epi (formalModuleQuotientπ I (n.unop + 1)
            (formalModuleQuotient K (e + 1) (F (e + 1)).obj)) := by
          dsimp [formalModuleQuotientπ]; infer_instance
        have hpK : Epi (formalModuleQuotientπ K (e + 1) (F (e + 1)).obj) := by
          dsimp [formalModuleQuotientπ]; infer_instance
        apply (cancel_epi (formalModuleQuotientπ I (n.unop + 1)
          (formalModuleQuotient K (e + 1) (F (e + 1)).obj))).mp
        apply (cancel_epi (formalModuleQuotientπ K (e + 1) (F (e + 1)).obj)).mp
        have hθn : formalModuleQuotientπ K (e + 1) (F (e + 1)).obj ≫
            formalModuleQuotientπ I (n.unop + 1) _ ≫ d.hom =
            formalModuleQuotientπ I (n.unop + 1) (F (e + 1)).obj ≫
              formalModuleQuotientπ K (e + 1) _ := by
          simpa only [d, Iso.app_hom, op_unop] using hθ e n.unop
        change formalModuleQuotientπ K (e + 1) (F (e + 1)).obj ≫
            formalModuleQuotientπ I (n.unop + 1) _ ≫
            (formalCompletionMap I s).app n ≫ ((β e).app n).hom =
          formalModuleQuotientπ K (e + 1) (F (e + 1)).obj ≫
            formalModuleQuotientπ I (n.unop + 1) _ ≫ d.hom ≫ b.hom ≫ c.hom
        have hθn' := congrArg (fun f ↦ f ≫ b.hom ≫ c.hom) hθn
        simp only [Category.assoc] at hθn'
        rw [hθn']
        have hb : formalModuleQuotientπ K (e + 1)
            (formalModuleQuotient I (n.unop + 1) (F (e + 1)).obj) ≫ b.hom =
            ((β (e + 1)).app n).hom ≫ formalModuleQuotientπ K (e + 1) _ := by
          change formalModuleQuotientπ K (e + 1) _ ≫
            formalModuleQuotientMap K ((β (e + 1)).app n).hom (Nat.le_refl (e + 1)) = _
          exact cokernel.π_desc _ _ _
        have hb' := congrArg (fun f ↦
          formalModuleQuotientπ I (n.unop + 1) (F (e + 1)).obj ≫ f ≫ c.hom) hb
        simp only [Category.assoc] at hb'
        rw [hb']
        have hc' : formalModuleQuotientπ K (e + 1)
            (((M.obj ⋙ formalCompletionFunctor K).flip.obj (op (e + 1))).obj n) ≫
            c.hom = τ.app n := hc
        rw [hc']
        have htn := congrArg (fun f ↦ f.app n) htβ
        simp only [NatTrans.comp_app] at htn
        have hleft : formalModuleQuotientπ K (e + 1) (F (e + 1)).obj ≫
            formalModuleQuotientπ I (n.unop + 1) _ ≫
            (formalCompletionMap I s).app n =
            formalModuleQuotientπ I (n.unop + 1) (F (e + 1)).obj ≫
              (formalCompletionMap I t).app n := by
          simp only [formalCompletionMap, formalModuleQuotientMap, formalModuleQuotientπ,
            cokernel.π_desc]
          change (formalModuleQuotientπ K (e + 1) (F (e + 1)).obj ≫ s) ≫ _ = _
          rw [hs]
        have hleft' := congrArg (fun f ↦ f ≫ ((β e).app n).hom) hleft
        simp only [Category.assoc] at hleft'
        rw [hleft']
        exact congrArg (fun f ↦ formalModuleQuotientπ I (n.unop + 1)
          (F (e + 1)).obj ≫ f) htn
      have : IsIso ((formalCompletionMap I s).app n ≫ ((β e).app n).hom) := by
        rw [heq]
        infer_instance
      exact IsIso.of_isIso_comp_right ((formalCompletionMap I s).app n) ((β e).app n).hom
    let := happ
    exact NatIso.isIso_of_isIso_app _
  let j := (K ^ (e + 1)).subschemeι
  let Q : CoherentModules X := ⟨formalModuleQuotient K (e + 1) (F (e + 1)).obj,
    (formalCompletionSystem_coherent K (F (e + 1))).1 e⟩
  have hQ : CoherentModuleSupportedOn Q j :=
    (coherentModuleSupportedOn_pow_subschemeι_iff K (e + 1) (Nat.succ_pos e) Q).mpr
      ((formalCompletionSystem_coherent K (F (e + 1))).2.1 e)
  have hB : CoherentModuleSupportedOn (F e) j :=
    (coherentModuleSupportedOn_pow_subschemeι_iff K (e + 1) (Nat.succ_pos e) _).mpr (hz e)
  let A' : ObjectProperty.FullSubcategory
      (fun H : CoherentModules X ↦ CoherentModuleSupportedOn H j) := ⟨Q, hQ⟩
  let B' : ObjectProperty.FullSubcategory
      (fun H : CoherentModules X ↦ CoherentModuleSupportedOn H j) := ⟨F e, hB⟩
  let s' : A' ⟶ B' := ObjectProperty.homMk (ObjectProperty.homMk s)
  obtain ⟨hf', hg'⟩ := supportedCompletion_fullyFaithful j I
    (hthick (e + 1) (by omega) (isNoetherian_of_locallyOfFiniteType j))
  let : (supportedCompletion j I).Full := hf'
  let : (supportedCompletion j I).Faithful := hg'
  have : IsIso ((supportedCompletion j I).map s') := hscomp
  have : IsIso s' := isIso_of_reflects_iso s' (supportedCompletion j I)
  have hiso : IsIso s := inferInstanceAs (IsIso s'.hom.hom)
  exact ⟨t, ⟨⟨asIso s, hs⟩, htβ⟩⟩

end AlgebraicGeometry
