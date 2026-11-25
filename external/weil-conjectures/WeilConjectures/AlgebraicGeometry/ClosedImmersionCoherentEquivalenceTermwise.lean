/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.CategoryTheory.Whiskering
public import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
import WeilConjectures.AlgebraicGeometry.ClosedImmersionFormalPushforwardConditions
import WeilConjectures.AlgebraicGeometry.FormalSystemsPullback
import WeilConjectures.AlgebraicGeometry.ClosedImmersionPushforwardAnnihilated
import WeilConjectures.AlgebraicGeometry.ClosedImmersionPushforwardFullyFaithful
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry
open MonoidalCategory Scheme.Modules
/-- Termwise part of the closed immersion coherent formal equivalence.
Source: Stacks Project, Cohomology of Schemes, Tags 088A and 087T.
The proof constructs the restricted pushforward equivalence level by level, using
the annihilation, coherence, ideal-power, and full-faithfulness lemmas.
(blueprint: lem-weil-pbc-closed-immersion-coherent-formal-equivalence-termwise)
-/
theorem closedImmersion_coherentFormal_equivalence_termwise {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] [IsNoetherian X] (I : X.IdealSheafData) :
    ∃ E : @CoherentFormalModule Z (isNoetherian_of_locallyOfFiniteType i) (I.comap i) ≌
        ObjectProperty.FullSubcategory (fun M : CoherentFormalModule X I ↦
          SupportedOn I M i),
      Nonempty (E.functor ⋙
        ObjectProperty.ι (fun M : CoherentFormalModule X I ↦ SupportedOn I M i) ⋙
        ObjectProperty.ι (IsCoherentFormalModule I) ≅
        ObjectProperty.ι (IsCoherentFormalModule (I.comap i)) ⋙
          (Functor.whiskeringRight ℕᵒᵖ Z.Modules X.Modules).obj
            (Scheme.Modules.pushforward i)) := by
  classical
  set_option backward.isDefEq.respectTransparency false in
  have product_zero_iff : ∀ {X : Scheme.{u}} (J : X.IdealSheafData)
      (F : X.Modules),
      IsZero (Scheme.idealModuleProduct J.toModulesι F) ↔
        ∀ (V : X.Opens) (a : Γ(X, V)), a ∈ J.idealOfOpens V →
          ∀ s : Γ(F, V), a • s = 0 := by
    intro X J F
    let μ : J.toModules ⊗ F ⟶ F := J.toModulesι ▷ F ≫ (λ_ F).hom
    have hm : IsZero (image μ) ↔ μ = 0 := by
      constructor
      · intro h
        exact eq_zero_of_image_eq_zero (h.eq_of_src _ _)
      · intro h
        have hi : image.ι μ = 0 := by
          apply (cancel_epi (factorThruImage μ)).mp
          simp only [image.fac, comp_zero, h]
        exact IsZero.of_mono_eq_zero (image.ι μ) hi
    change IsZero (image μ) ↔ _
    rw [hm]
    constructor
    · intro h V a ha s
      have hr : a ∈ Set.range (J.toModulesι.app V) := by
        rw [J.range_toModulesι_app_eq_idealOfOpens V]
        exact ha
      obtain ⟨b, rfl⟩ := hr
      have he := congrArg (fun f : J.toModules ⊗ F ⟶ F ↦ f.app V (tmulSection b s)) h
      dsimp only [μ] at he
      rw [Hom.comp_app, ConcreteCategory.comp_apply, whiskerRight_app_tmulSection] at he
      erw [leftUnitor_hom_app_tmulSection'] at he
      exact he
    · intro h
      let adj := sheafificationAdjunction X
      apply (cancel_epi (SheafOfModules.tensorObjIsoSheafification J.toModules F).inv).mp
      apply (adj.homEquiv (J.toModules.val ⊗ F.val) F).injective
      rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
      apply PresheafOfModules.hom_ext
      intro U
      ext t
      change μ.val.app U
        ((SheafOfModules.tensorObjIsoSheafification J.toModules F).inv.val.app U
          (((adj.unit.app (J.toModules.val ⊗ F.val)).app U) t)) = _
      induction t using TensorProduct.inductionOn with
      | add t s ht hs => simp only [map_add, ht, hs]
      | tmul a s =>
        change μ.app U.unop (tmulSection a s) = 0
        dsimp only [μ]
        rw [Hom.comp_app, ConcreteCategory.comp_apply, whiskerRight_app_tmulSection]
        erw [leftUnitor_hom_app_tmulSection']
        exact h U.unop (J.toModulesι.app U.unop a)
          ((J.range_toModulesι_app_eq_idealOfOpens U.unop).subset ⟨a, rfl⟩) s
  
  
  have : IsNoetherian Z := isNoetherian_of_locallyOfFiniteType i
  let P := Scheme.Modules.pushforward i
  have hbij := (closedImmersion_pushforward_fullyFaithful i).2
  have : P.Full := ⟨fun {G H} ↦ (hbij G H).2⟩
  have : P.Faithful := ⟨fun {G H} ↦ (hbij G H).1⟩
  let C : @CoherentFormalModule Z (isNoetherian_of_locallyOfFiniteType i) (I.comap i) ⥤
      CoherentFormalModule X I :=
    ObjectProperty.lift (IsCoherentFormalModule I)
      (ObjectProperty.ι (IsCoherentFormalModule (I.comap i)) ⋙
        (Functor.whiskeringRight ℕᵒᵖ Z.Modules X.Modules).obj P)
      (fun G ↦ closedImmersion_formal_pushforward_conditions i I G.obj G.property)
  have hC (G : @CoherentFormalModule Z
      (isNoetherian_of_locallyOfFiniteType i) (I.comap i)) : SupportedOn I (C.obj G) i := by
    intro n
    have := ((isCoherent_iff_isQuasicoherent_and_isFiniteType Z
      (G.obj.obj (op n))).mp (G.property.1 n)).1
    exact (product_zero_iff i.ker (P.obj (G.obj.obj (op n)))).mpr
      ((closedImmersion_pushforward_annihilated i).1 (G.obj.obj (op n))).2
  let D := ObjectProperty.lift (fun M : CoherentFormalModule X I ↦ SupportedOn I M i) C hC
  obtain ⟨T, _, hT, _, _⟩ := (exists_formalSystemsPullback i I).1
  have hTobj (M : CoherentFormalModule X I) :
      IsCoherentFormalModule (I.comap i) (M.obj ⋙ tensorPullback i) := by
    have he := congrArg (fun F ↦ F.obj M) hT
    change (T.obj M).obj = M.obj ⋙ tensorPullback i at he
    rw [← he]
    exact (T.obj M).property
  have : D.EssSurj := ⟨fun M ↦ by
    let G : @CoherentFormalModule Z (isNoetherian_of_locallyOfFiniteType i) (I.comap i) :=
      ⟨M.obj.obj ⋙ tensorPullback i,
        hTobj M.obj⟩
    let adj := Classical.choose (exists_tensorPullbackAdjunction i)
    have hu (n : ℕᵒᵖ) : IsIso (adj.unit.app (M.obj.obj.obj n)) := by
      have := ((isCoherent_iff_isQuasicoherent_and_isFiniteType X
        (M.obj.obj.obj n)).mp (M.obj.property.1 n.unop)).1
      exact ((closedImmersion_pushforward_annihilated i).2 (M.obj.obj.obj n)
        ((product_zero_iff i.ker (M.obj.obj.obj n)).mp (M.property n.unop))).2.1
    let e : M.obj.obj ≅ (M.obj.obj ⋙ tensorPullback i) ⋙ P :=
      NatIso.ofComponents (fun n ↦ @asIso _ _ _ _ (adj.unit.app (M.obj.obj.obj n)) (hu n))
        (fun f ↦ adj.unit.naturality (M.obj.obj.map f))
    refine ⟨G, ⟨?_⟩⟩
    exact ObjectProperty.isoMk _ (ObjectProperty.isoMk _ e.symm)⟩
  have : D.IsEquivalence := {}
  exact ⟨D.asEquivalence, ⟨Iso.refl _⟩⟩

end AlgebraicGeometry
