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
import WeilConjectures.AlgebraicGeometry.ClosedImmersionPushforwardAnnihilated
import WeilConjectures.AlgebraicGeometry.ClosedImmersionPushforwardFullyFaithful
import WeilConjectures.AlgebraicGeometry.ClosedImmersionPushforwardIdealPowers
import WeilConjectures.AlgebraicGeometry.ClosedPushforwardStalks
import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBase
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.ClosedImmersionCoherentEquivalenceTermwise
import WeilConjectures.AlgebraicGeometry.ClosedImmersionCoherentEquivalenceCompletion
import WeilConjectures.AlgebraicGeometry.FinitePushforwardCoherent

/-! # Coherent modules and adic systems on a closed subscheme

Source: Stacks Project, Cohomology of Schemes, Tags 087T, 088A, 088C, and 088E
(blueprint: lem-weil-pbc-closed-immersion-coherent-equivalence).

## Main statements
* `closedImmersion_coherent_equivalence`: pushforward identifies coherent modules with
  coherent modules annihilated by the defining ideal.
* `closedImmersion_coherent_support`: support is the image of support.
* `closedImmersion_coherentFormal_equivalence`: the termwise equivalence and its natural
  compatibility with completion, including the canonical quotient projections.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

open MonoidalCategory Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
private theorem product_zero_iff {X : Scheme.{u}} (J : X.IdealSheafData)
    (F : X.Modules) :
    IsZero (Scheme.idealModuleProduct J.toModulesι F) ↔
      ∀ (V : X.Opens) (a : Γ(X, V)), a ∈ J.idealOfOpens V →
        ∀ s : Γ(F, V), a • s = 0 := by
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

/-- Pushforward induces the equivalence on coherent modules of Stacks Tag 087T.
(blueprint: lem-weil-pbc-closed-immersion-coherent-equivalence)
Proof (node steps 1--4): a closed immersion is finite
(lem-weil-pbc-closed-immersion-finite), so its pushforward preserves coherence
(lem-weil-pbc-finite-pushforward-coherent). Its defining ideal kills the pushforward
(lem-weil-pbc-closed-immersion-pushforward-annihilated). The pushforward is fully faithful
on all modules (lem-weil-pbc-closed-immersion-pushforward-fully-faithful), hence on these
full subcategories. A coherent module killed by the ideal is the pushforward of its
quasi-coherent finite type pullback (lem-weil-pbc-closed-immersion-pushforward-annihilated).
On the locally Noetherian source this pullback is coherent
(pqf-lem-coherent-ft-locnoeth). Thus the restricted pushforward is essentially surjective
and fully faithful, and yields the displayed equivalence and comparison with pushforward.
-/
theorem closedImmersion_coherent_equivalence {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] [IsLocallyNoetherian X] [IsLocallyNoetherian Z] :
    ∃ E : CoherentModules Z ≌
        ObjectProperty.FullSubcategory (fun F : CoherentModules X ↦
          CoherentModuleSupportedOn F i),
      Nonempty (E.functor ⋙
        ObjectProperty.ι (fun F : CoherentModules X ↦ CoherentModuleSupportedOn F i) ⋙
        ObjectProperty.ι (RingedSpace.IsCoherent X.toRingedSpace) ≅
        ObjectProperty.ι (RingedSpace.IsCoherent Z.toRingedSpace) ⋙
          Scheme.Modules.pushforward i) := by
  classical
  let P := Scheme.Modules.pushforward i
  have hbij := (closedImmersion_pushforward_fullyFaithful i).2
  have : P.Full := ⟨fun {G H} ↦ (hbij G H).2⟩
  have : P.Faithful := ⟨fun {G H} ↦ (hbij G H).1⟩
  let C : CoherentModules Z ⥤ CoherentModules X :=
    ObjectProperty.lift (RingedSpace.IsCoherent X.toRingedSpace)
      (ObjectProperty.ι (RingedSpace.IsCoherent Z.toRingedSpace) ⋙ P)
      (fun G ↦ (isCoherent_pushforward_of_isFinite i G.obj G.property).1)
  have hC (G : CoherentModules Z) : CoherentModuleSupportedOn (C.obj G) i := by
    have := ((isCoherent_iff_isQuasicoherent_and_isFiniteType Z G.obj).mp G.property).1
    exact (product_zero_iff i.ker (P.obj G.obj)).mpr
      ((closedImmersion_pushforward_annihilated i).1 G.obj).2
  let D := ObjectProperty.lift
    (fun F : CoherentModules X ↦ CoherentModuleSupportedOn F i) C hC
  have : D.EssSurj := ⟨fun F ↦ by
    have hF := (isCoherent_iff_isQuasicoherent_and_isFiniteType X F.obj.obj).mp
      F.obj.property
    have := hF.1
    obtain ⟨hq, hu, ht⟩ := (closedImmersion_pushforward_annihilated i).2 F.obj.obj
      ((product_zero_iff i.ker F.obj.obj).mp F.property)
    let G : CoherentModules Z := ⟨(tensorPullback i).obj F.obj.obj,
      (isCoherent_iff_isQuasicoherent_and_isFiniteType Z _).mpr ⟨hq, ht hF.2⟩⟩
    have := hu
    let adj := Classical.choose (exists_tensorPullbackAdjunction i)
    refine ⟨G, ⟨?_⟩⟩
    exact ObjectProperty.isoMk _
      (ObjectProperty.isoMk _ (asIso (adj.unit.app F.obj.obj)).symm)⟩
  have : D.IsEquivalence := {}
  exact ⟨D.asEquivalence, ⟨Iso.refl _⟩⟩

/-- The support formula accompanying Stacks Tag 087T, by the stalk calculation of
Sheaves, Tag 00AE (blueprint: lem-weil-pbc-closed-immersion-coherent-equivalence).
Proof (node step 5): outside the closed image the stalk of the pushforward is zero;
at i(z) it is isomorphic, as an additive group, to the stalk at z
(lem-weil-pbc-closed-pushforward-stalks). A zero stalk is precisely a subsingleton stalk
(def-weil-pbc-closed-subset-proper-over-base). Injectivity of the closed immersion
therefore gives equality with the image of the nonzero-stalk locus. -/
theorem closedImmersion_coherent_support {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] [IsLocallyNoetherian X] [IsLocallyNoetherian Z]
    (G : CoherentModules Z) :
    {x : X | ¬ Subsingleton (((Scheme.Modules.pushforward i).obj G.obj).presheaf.stalk x)} =
      i '' {z : Z | ¬ Subsingleton (G.obj.presheaf.stalk z)} := by
  classical
  obtain ⟨hoff, hon, _⟩ := closedImmersion_pushforward_stalks i i.isClosedEmbedding G.obj
  ext x
  constructor
  · intro hx
    have hr : x ∈ Set.range i.base := by
      by_contra h
      exact hx (hoff x h)
    obtain ⟨z, rfl⟩ := hr
    refine ⟨z, ?_, rfl⟩
    intro hz
    have := hz
    exact hx (hon z).1.1.subsingleton
  · rintro ⟨z, hz, rfl⟩ hx
    have : Subsingleton (((TopCat.Presheaf.pushforward Ab i.base).obj
        G.obj.presheaf).stalk (i.base z)) := hx
    exact hz (hon z).1.2.subsingleton

/-- The termwise closed pushforward equivalence and its natural completion comparison.
Source: Stacks Tags 088A, 088C, 088E, using Tag 087T without further mention; completion
is equation 0880 (blueprint: lem-weil-pbc-closed-immersion-coherent-equivalence).
Proof (node steps 6--10): the closed subscheme of a Noetherian scheme is Noetherian
(pqf-def-locnoeth, def-weil-closed-immersion). The extended ideal is I.comap i
(def-nagata-extended-ideal). Ideal powers commute with pushforward on products, and
pushforward identifies their quotients, naturally and compatibly with quotient maps
(lem-weil-pbc-closed-immersion-pushforward-ideal-powers). Thus termwise pushforward
preserves the defining adic-system conditions (def-weil-pbc-coherent-formal-module).
The termwise maps are fully faithful by step 3. Conversely choose coherent preimages
of each term by step 4; full faithfulness uniquely lifts the transition maps. The
quotient comparison and reflection of zero objects and isomorphisms give the adic
conditions on these preimages. This proves essential surjectivity onto precisely the
systems annihilated by i.ker. Finally the natural quotient comparisons assemble into
a natural isomorphism of completion systems, because they respect all transitions.
The displayed projection equation specifies these as the canonical quotient comparisons.
The index op n represents positive level n+1. -/
theorem closedImmersion_coherentFormal_equivalence {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] [IsNoetherian X] (I : X.IdealSheafData) :
    (∃ E : @CoherentFormalModule Z (isNoetherian_of_locallyOfFiniteType i) (I.comap i) ≌
        ObjectProperty.FullSubcategory (fun M : CoherentFormalModule X I ↦
          SupportedOn I M i),
      Nonempty (E.functor ⋙
        ObjectProperty.ι (fun M : CoherentFormalModule X I ↦ SupportedOn I M i) ⋙
        ObjectProperty.ι (IsCoherentFormalModule I) ≅
        ObjectProperty.ι (IsCoherentFormalModule (I.comap i)) ⋙
          (Functor.whiskeringRight ℕᵒᵖ Z.Modules X.Modules).obj (Scheme.Modules.pushforward i))) ∧
    (∃ θ : ObjectProperty.ι (RingedSpace.IsCoherent Z.toRingedSpace) ⋙
        Scheme.Modules.pushforward i ⋙ formalCompletionFunctor I ≅
        ObjectProperty.ι (RingedSpace.IsCoherent Z.toRingedSpace) ⋙
        formalCompletionFunctor (I.comap i) ⋙
          (Functor.whiskeringRight ℕᵒᵖ Z.Modules X.Modules).obj (Scheme.Modules.pushforward i),
      ∀ (G : CoherentModules Z) (n : ℕ),
        formalModuleQuotientπ I (n + 1) ((Scheme.Modules.pushforward i).obj G.obj) ≫
          (θ.hom.app G).app (op n) =
        (Scheme.Modules.pushforward i).map (formalModuleQuotientπ (I.comap i) (n + 1) G.obj))
    := by
  refine ⟨?_, ?_⟩
  · exact closedImmersion_coherentFormal_equivalence_termwise i I
  · exact closedImmersion_coherentFormal_equivalence_completion i I

end AlgebraicGeometry
