/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.GlobalSectionScalarExtension
public import WeilConjectures.AlgebraicGeometry.RingTensorCechCoordinates
import WeilConjectures.AlgebraicGeometry.GlobalSectionModuleMonoidal
import all WeilConjectures.CategoryTheory.RingedKoszulFactorColimit
import all WeilConjectures.CategoryTheory.RingedLocalizationFactorRestriction

/-! # Scalar extension and tensor localization factors

Source: Stacks Project, algebraization.tex, Tags 0996 and 099E;
algebra.tex, Tag 00DK.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open CategoryTheory.MonoidalCategory
namespace CategoryTheory

attribute [local instance] ringFamilyGlobalExtension_additive
private theorem globalExtension_scalar
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    (s : (O.obj ⋙ forget CommRingCat).sections) :
    (ringFamilyGlobalExtension O).map (ringedKoszulScalar
        (CochainComplex.onePointRingSheaf (ringFamilyGlobalRing O))
        (ringTensorCechSection (ringFamilyGlobalRing O) s)).asHom ≫
        ringFamilyGlobalExtensionUnit O =
      ringFamilyGlobalExtensionUnit O ≫ (ringedKoszulScalar O s).asHom := by
  let a := PresheafOfModules.pullbackPushforwardAdjunction (ringFamilyGlobalEvaluation O)
  let b := PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).obj)
  change (PresheafOfModules.sheafification _).map
    ((PresheafOfModules.pullback _).map ((ringFamilyConstantPresheaf O).map _)) ≫ _ = _
  apply (b.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  apply (a.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  dsimp only [a, b]
  simp only [ringFamilyGlobalExtensionUnit, Equiv.apply_symm_apply]
  ext X
  rfl

private theorem globalExtension_localization
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    (s : (O.obj ⋙ forget CommRingCat).sections)
    [IsIso (ringFamilyGlobalExtensionUnit O)] :
    ∃ loc : (ringFamilyGlobalExtension O).obj
        (ringedSectionLocalization
          (CochainComplex.onePointRingSheaf (ringFamilyGlobalRing O))
          (ringTensorCechSection (ringFamilyGlobalRing O) s)) ≅
        ringedSectionLocalization O s,
      (ringFamilyGlobalExtension O).map (ringedSectionLocalizationUnit
          (CochainComplex.onePointRingSheaf (ringFamilyGlobalRing O))
          (ringTensorCechSection (ringFamilyGlobalRing O) s)) ≫ loc.hom =
        ringFamilyGlobalExtensionUnit O ≫ ringedSectionLocalizationUnit O s := by
  let L := ringFamilyGlobalExtension O
  let R := CochainComplex.onePointRingSheaf (ringFamilyGlobalRing O)
  let t := ringTensorCechSection (ringFamilyGlobalRing O) s
  have := ringFamilyGlobalExtension_preservesColimits O ℕ
  let c := localizationSheafCocone R t
  let d := localizationSheafCocone O s
  let eunit := asIso (ringFamilyGlobalExtensionUnit O)
  let F := Functor.ofSequence (X := fun _ : ℕ ↦ ringComplexUnit (ringFamilyGlobalRing O))
    (fun _ ↦ (ringedKoszulScalar R t).asHom)
  let G := Functor.ofSequence (X := fun _ : ℕ ↦
    SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
      (fun _ ↦ (ringedKoszulScalar O s).asHom)
  let τ : F ⋙ L ⟶ G := NatTrans.ofSequence (fun _ ↦ eunit.hom) (by
    intro n
    simp only [F, G, Functor.comp_map, Functor.ofSequence_map_homOfLE_succ]
    exact globalExtension_scalar O s)
  let e : F ⋙ L ≅ G :=
    NatIso.ofComponents (fun _ ↦ eunit) (fun f ↦ τ.naturality f)
  let hc := isColimitOfPreserves L (localizationSheafCoconeIsColimit R t)
  let hd := (IsColimit.precomposeHomEquiv e d).symm
    (localizationSheafCoconeIsColimit O s)
  let loc := hc.coconePointUniqueUpToIso hd
  refine ⟨loc, ?_⟩
  have hleg : L.map (localizationSheafMap R t 1) ≫ loc.hom =
      eunit.hom ≫ localizationSheafMap O s 1 :=
    hc.comp_coconePointUniqueUpToIso_hom hd 0
  have hsrc : (ringedKoszulScalar R t).asHom ≫ localizationSheafMap R t 1 =
      ringedSectionLocalizationUnit R t := by
    rw [localizationSheafMap_step, localizationSheafMap_zero]
  have htgt : (ringedKoszulScalar O s).asHom ≫ localizationSheafMap O s 1 =
      ringedSectionLocalizationUnit O s := by
    rw [localizationSheafMap_step, localizationSheafMap_zero]
  rw [← hsrc, L.map_comp, Category.assoc, hleg, ← Category.assoc]
  rw [show L.map (ringedKoszulScalar R t).asHom ≫ eunit.hom =
    eunit.hom ≫ (ringedKoszulScalar O s).asHom from globalExtension_scalar O s]
  rw [Category.assoc, htgt]
  rfl

/-- Scalar extension identifies a single augmented two-term localization complex.
Source: Stacks Project, algebraization.tex, Tag 0996; algebra.tex, Tag 00DK.
(auxiliary; not a blueprint node).

Proof: transpose the fixed multiplication map through its two defining adjunctions.
Its transpose is evaluation of sections, which commutes with multiplication by s.
The module unit constraint therefore identifies the scalar-multiplication sequences.
Use the already proved sheaf localization cocones, whose n-th leg sends a to a/s^(n+1).
Scalar extension preserves their colimits, so their universal properties give the
localization isomorphism. The successor-fraction identity at n=0 says that scalar
multiplication followed by the first leg is the localization unit; hence this
isomorphism commutes with the specified unit arrow. The existing generic factorArrow
construction assembles this square into an isomorphism of the two-term complexes.
Its degree-zero component is the fixed multiplication map and its remaining nonzero
component is the localization isomorphism. Reverse this isomorphism and cancel it in
the arrow-commutativity equation to obtain the displayed augmentation equality.
Zero sections, units, zero rings and empty sites are covered by the same cocones. -/
theorem ringFamilyGlobalExtension_localization_factor
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    (s : (O.obj ⋙ forget CommRingCat).sections) :
    ∃ e : ringedLocalizationTwoTerm O s ≅ ringFamilyGlobalExtensionComplex O
        (ringedLocalizationTwoTerm (CochainComplex.onePointRingSheaf (ringFamilyGlobalRing O))
          (ringTensorCechSection (ringFamilyGlobalRing O) s)),
      e.hom ≫ ringFamilyGlobalExtensionAugmentation O
        (ringedLocalizationTwoTermAugmentation
          (CochainComplex.onePointRingSheaf (ringFamilyGlobalRing O))
          (ringTensorCechSection (ringFamilyGlobalRing O) s)) =
        ringedLocalizationTwoTermAugmentation O s := by
  let R := CochainComplex.onePointRingSheaf (ringFamilyGlobalRing O)
  let t := ringTensorCechSection (ringFamilyGlobalRing O) s
  let F := ringFamilyGlobalExtension O
  let := SheafOfModules.monoidalCategory O
  let := SheafOfModules.monoidalCategory R
  obtain ⟨mon, hmon⟩ := ringFamilyGlobalExtension_module_monoidal O
  let := mon
  have : IsIso (ringFamilyGlobalExtensionUnit O) := hmon ▸ inferInstance
  obtain ⟨loc, hloc⟩ := globalExtension_localization O s
  let h : Arrow.mk (F.map (ringedSectionLocalizationUnit R t)) ≅
      Arrow.mk (ringedSectionLocalizationUnit O s) :=
    Arrow.isoMk (asIso (ringFamilyGlobalExtensionUnit O)) loc hloc.symm
  let e := factorArrow R O F t s h
  refine ⟨(Arrow.leftFunc.mapIso e).symm, ?_⟩
  have he := e.hom.w.symm
  change ((F.mapHomologicalComplex (.up ℤ)).map
    (ringedLocalizationTwoTermAugmentation R t)) ≫
      (ringIso R O F t s h).hom =
    (complexIso R O F t s h).hom ≫ ringedLocalizationTwoTermAugmentation O s at he
  change (complexIso R O F t s h).inv ≫ _ = _
  exact (Iso.inv_comp_eq (complexIso R O F t s h)).2 he

end CategoryTheory
