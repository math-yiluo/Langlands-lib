/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.KInjectiveMayerVietorisData
import WeilConjectures.AlgebraicGeometry.OpenModuleImageSectionRestriction

/-! # OpenModuleImageAmalgamation

Source: Stacks Project, Cohomology, Tags 08BV and 01EB.
(blueprint: lem-pc-open-module-image-gluing-existence).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace
set_option autoImplicit false
namespace AlgebraicGeometry

private theorem unit_sections_injective
    (X : Scheme.{u}) (U V : X.Opens) (hcover : U ⊔ V = ⊤)
    (M : SheafOfModules.{u} (moduleRings X.toRingedSpace)) (T : X.Opens)
    {x y : M.val.obj (.op T)}
    (hu : ((schemeOpenModuleAdjunction X U).unit.app M).val.app (.op T) x =
      ((schemeOpenModuleAdjunction X U).unit.app M).val.app (.op T) y)
    (hv : ((schemeOpenModuleAdjunction X V).unit.app M).val.app (.op T) x =
      ((schemeOpenModuleAdjunction X V).unit.app M).val.app (.op T) y) : x = y := by
  have unit_eq (A : X.Opens)
      (h : ((schemeOpenModuleAdjunction X A).unit.app M).val.app (.op T) x =
        ((schemeOpenModuleAdjunction X A).unit.app M).val.app (.op T) y) :
      ((Scheme.Modules.restrictAdjunction A.ι).unit.app M).val.app (.op T) x =
        ((Scheme.Modules.restrictAdjunction A.ι).unit.app M).val.app (.op T) y := by
    simp only [schemeOpenModuleAdjunction, Adjunction.ofNatIsoLeft_unit,
      NatTrans.comp_app, Functor.whiskerRight_app, SheafOfModules.comp_val,
      PresheafOfModules.comp_app, ConcreteCategory.comp_apply] at h
    have : IsIso (((Scheme.Modules.pushforward A.ι).map
        ((Scheme.Modules.overFunctorEquiv A).inv.app M)).val.app (.op T)) :=
      inferInstanceAs (IsIso ((SheafOfModules.evaluation
        (moduleRings X.toRingedSpace) (.op T)).map
          ((Scheme.Modules.pushforward A.ι).map
            ((Scheme.Modules.overFunctorEquiv A).inv.app M))))
    exact (ConcreteCategory.bijective_of_isIso
      (((Scheme.Modules.pushforward A.ι).map
        ((Scheme.Modules.overFunctorEquiv A).inv.app M)).val.app (.op T))).1 h
  apply TopCat.Sheaf.eq_of_locally_eq₂
    (F := ⟨Scheme.Modules.presheaf M, Scheme.Modules.isSheaf M⟩)
    (homOfLE (U.ι.image_preimage_le T))
    (homOfLE (V.ι.image_preimage_le T))
    (by rw [Scheme.Hom.image_preimage_eq_opensRange_inf,
        Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
        Scheme.Opens.opensRange_ι, ← inf_sup_right, hcover, top_inf_eq])
  · exact unit_eq U hu
  · exact unit_eq V hv

/-- Compatible sections of the two direct images have an amalgamation.
Source: Stacks Project, Cohomology, Tag 01EB (lemma-mayer-vietoris), first
sentence of proof, and Tag 08BV (lemma-exact-sequence-j-star).
Proof: Use overFunctorEquiv to identify the sections of the image at T with
M(T ∩ U) and M(T ∩ V). Under this comparison the transported unit is ordinary
restriction, by restrictAdjunction_unit_app_app. Expanding the overlap mate,
the inverse composition comparison, counit, and forward comparison cancel,
so its component is restriction to T ∩ U ∩ V. Thus the displayed equality
is precisely compatibility of these two sections. The underlying abelian
sheaf axiom for the two opens T ∩ U and T ∩ V, whose union is T, gives a
section of M(T). The sheaf gluing equations, transported back through the
two comparison isomorphisms, give both asserted equalities. This needs no
nonemptiness: for empty X or T it is the empty-cover sheaf axiom; an empty
member and repeated covering opens obey the same two-open sheaf axiom.
-/
private theorem section_amalgamation
    (X : Scheme.{u}) (U V : X.Opens) (hcover : U ⊔ V = ⊤)
    (M : SheafOfModules.{u} (moduleRings X.toRingedSpace)) (T : X.Opens)
    (a : ((schemeOpenModuleImage X U).obj M).val.obj (.op T))
    (b : ((schemeOpenModuleImage X V).obj M).val.obj (.op T))
    (hab : ((schemeOpenModuleImageRestriction X
      (homOfLE (inf_le_left : U ⊓ V ≤ U))).app M).val.app (.op T) a =
      ((schemeOpenModuleImageRestriction X
        (homOfLE (inf_le_right : U ⊓ V ≤ V))).app M).val.app (.op T) b) :
    ∃ x : M.val.obj (.op T),
      ((schemeOpenModuleAdjunction X U).unit.app M).val.app (.op T) x = a ∧
      ((schemeOpenModuleAdjunction X V).unit.app M).val.app (.op T) x = b := by
  classical
  let P := U.ι ''ᵁ (U.ι ⁻¹ᵁ T)
  let Q := V.ι ''ᵁ (V.ι ⁻¹ᵁ T)
  let R := (U ⊓ V).ι ''ᵁ ((U ⊓ V).ι ⁻¹ᵁ T)
  let e (A : X.Opens) := (Scheme.Modules.pushforward A.ι).mapIso
    ((Scheme.Modules.overFunctorEquiv A).app M)
  let a' : M.val.obj (.op P) := (e U).hom.val.app (.op T) a
  let b' : M.val.obj (.op Q) := (e V).hom.val.app (.op T) b
  have hR : R = P ⊓ Q := by
    dsimp [R, P, Q]
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf,
      Scheme.Hom.image_preimage_eq_opensRange_inf,
      Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      Scheme.Opens.opensRange_ι, Scheme.Opens.opensRange_ι]
    ac_rfl
  have hcompat : M.val.presheaf.map (homOfLE (inf_le_left : P ⊓ Q ≤ P)).op a' =
      M.val.presheaf.map (homOfLE (inf_le_right : P ⊓ Q ≤ Q)).op b' := by
    have h := (schemeOpenModuleImage_section_restriction X
      (homOfLE (inf_le_left : U ⊓ V ≤ U)) M T a).symm.trans
        ((congrArg (fun z ↦ (e (U ⊓ V)).hom.val.app (.op T) z) hab).trans
          (schemeOpenModuleImage_section_restriction X
            (homOfLE (inf_le_right : U ⊓ V ≤ V)) M T b))
    change M.val.presheaf.map (homOfLE (show R ≤ P by rw [hR]; exact inf_le_left)).op a' =
      M.val.presheaf.map (homOfLE (show R ≤ Q by rw [hR]; exact inf_le_right)).op b' at h
    have h' := congrArg (fun x ↦ M.val.presheaf.map (eqToHom hR.symm).op x) h
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp] at h'
    convert h' using 1
  let F : TopCat.Sheaf AddCommGrpCat X := ⟨M.val.presheaf, M.isSheaf⟩
  let O : Bool → X.Opens := fun j ↦ if j then P else Q
  let sf : ∀ j : Bool, (F.obj.obj (.op (O j))) := fun j ↦ by
    cases j
    · exact b'
    · exact a'
  have hc : TopCat.Presheaf.IsCompatible F.obj O sf := by
    intro j k
    cases j <;> cases k
    · rfl
    · change M.val.presheaf.map (Opens.infLELeft Q P).op b' =
        M.val.presheaf.map (Opens.infLERight Q P).op a'
      have h' := congrArg
        (fun x ↦ M.val.presheaf.map (eqToHom (inf_comm Q P)).op x) hcompat.symm
      simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp] at h'
      convert h' using 1
    · simpa [O, sf, F, Opens.infLELeft, Opens.infLERight] using hcompat
    · rfl
  have hcover' : T ≤ ⨆ j, O j := by
    have hpq : P ⊔ Q = T := by
      dsimp [P, Q]
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf,
        Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
        Scheme.Opens.opensRange_ι, ← inf_sup_right, hcover, top_inf_eq]
    rw [← hpq]
    exact sup_le (le_iSup_of_le true (by simp [O]))
      (le_iSup_of_le false (by simp [O]))
  obtain ⟨x, hx, _⟩ := F.existsUnique_gluing' O T
    (fun j ↦ homOfLE (by cases j <;> exact Scheme.Hom.image_preimage_le _ T))
    hcover' sf hc
  refine ⟨x, ?_, ?_⟩
  · apply (ConcreteCategory.bijective_of_isIso
      ((SheafOfModules.evaluation (moduleRings X.toRingedSpace) (.op T)).map
        (e U).hom)).1
    change ((e U).hom.val.app (.op T))
      (((schemeOpenModuleAdjunction X U).unit.app M).val.app (.op T) x) = a'
    have he : (schemeOpenModuleAdjunction X U).unit.app M ≫ (e U).hom =
        (Scheme.Modules.restrictAdjunction U.ι).unit.app M := by
      simp [schemeOpenModuleAdjunction, e, Adjunction.ofNatIsoLeft_unit]
    have hex := congrArg (fun k ↦ k.val.app (.op T) x) he
    exact hex.trans (hx true)
  · apply (ConcreteCategory.bijective_of_isIso
      ((SheafOfModules.evaluation (moduleRings X.toRingedSpace) (.op T)).map
        (e V).hom)).1
    change ((e V).hom.val.app (.op T))
      (((schemeOpenModuleAdjunction X V).unit.app M).val.app (.op T) x) = b'
    have he : (schemeOpenModuleAdjunction X V).unit.app M ≫ (e V).hom =
        (Scheme.Modules.restrictAdjunction V.ι).unit.app M := by
      simp [schemeOpenModuleAdjunction, e, Adjunction.ofNatIsoLeft_unit]
    have hex := congrArg (fun k ↦ k.val.app (.op T) x) he
    exact hex.trans (hx false)


/-- Existence half of the sheaf gluing universal property.
Source: Stacks Project, Cohomology, Tags 08BV and 01EB.
(blueprint: lem-pc-open-module-image-gluing-existence)
Proof: At each test open T and each section z of Z(T), identify the two image
objects' sections with M(T ∩ U) and M(T ∩ V) via overFunctorEquiv. The ordinary
restriction unit is the restriction map by restrictAdjunction_unit_app_app.
In the overlap mate the inverse composition comparison, restricted counit, and
forward comparison cancel repeated restriction and give restriction to T ∩ U ∩ V.
The compatibility hypothesis therefore says b(z) and c(z) agree there. Since
(T ∩ U) ∪ (T ∩ V) = T, the sheaf axiom gives an amalgamation in M(T).
Uniqueness of section amalgamation proves compatibility with restriction in T:
both restrictions have the same images on the two covering opens. It also proves
additivity and linearity, since the sum or scalar multiple of amalgamations has
the prescribed restrictions. These sectionwise linear maps assemble to a module
sheaf morphism l, and the two gluing equations give the required composites.
The empty scheme, empty covering member, and repeated opens use the same axiom.
-/
theorem schemeOpenModuleImage_pullback_exists
    (X : Scheme.{u}) (U V : X.Opens) (hcover : U ⊔ V = ⊤)
    (M : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    {Z : SheafOfModules.{u} (moduleRings X.toRingedSpace)}
    (b : Z ⟶ (schemeOpenModuleImage X U).obj M)
    (c : Z ⟶ (schemeOpenModuleImage X V).obj M)
    (hbc : b ≫ (schemeOpenModuleImageRestriction X
      (homOfLE (inf_le_left : U ⊓ V ≤ U))).app M =
      c ≫ (schemeOpenModuleImageRestriction X
        (homOfLE (inf_le_right : U ⊓ V ≤ V))).app M) :
    ∃ l : Z ⟶ M,
      l ≫ (schemeOpenModuleAdjunction X U).unit.app M = b ∧
      l ≫ (schemeOpenModuleAdjunction X V).unit.app M = c := by
  classical
  have hex (T : X.Opens) (z : Z.val.obj (.op T)) :
      ∃ x : M.val.obj (.op T),
        ((schemeOpenModuleAdjunction X U).unit.app M).val.app (.op T) x =
          b.val.app (.op T) z ∧
        ((schemeOpenModuleAdjunction X V).unit.app M).val.app (.op T) x =
          c.val.app (.op T) z := by
    apply section_amalgamation X U V hcover M T
    exact congrArg (fun k ↦ k.val.app (.op T) z) hbc
  -- The two unit images determine this section uniquely by unit_sections_injective.
  let f (T : X.Opens) (z : Z.val.obj (.op T)) := (hex T z).choose
  have hfU (T : X.Opens) (z : Z.val.obj (.op T)) :
      ((schemeOpenModuleAdjunction X U).unit.app M).val.app (.op T) (f T z) =
        b.val.app (.op T) z := (hex T z).choose_spec.1
  have hfV (T : X.Opens) (z : Z.val.obj (.op T)) :
      ((schemeOpenModuleAdjunction X V).unit.app M).val.app (.op T) (f T z) =
        c.val.app (.op T) z := (hex T z).choose_spec.2
  let l : Z ⟶ M := ⟨{
    app := fun T ↦ ModuleCat.ofHom {
      toFun := f T.unop
      map_add' := by
        intro x y
        apply unit_sections_injective X U V hcover M T.unop
        · simp only [hfU, map_add]
        · simp only [hfV, map_add]
      map_smul' := by
        intro r x
        apply unit_sections_injective X U V hcover M T.unop
        · simp only [hfU, map_smul, RingHom.id_apply]
        · simp only [hfV, map_smul, RingHom.id_apply] }
    naturality := fun {T S} i ↦ by
      ext z
      apply unit_sections_injective X U V hcover M S.unop
      · change ((schemeOpenModuleAdjunction X U).unit.app M).val.app S
          (f S.unop (Z.val.map i z)) =
            ((schemeOpenModuleAdjunction X U).unit.app M).val.app S
              (M.val.map i (f T.unop z))
        exact (hfU S.unop (Z.val.map i z)).trans
          ((PresheafOfModules.naturality_apply b.val i z).trans
            ((congrArg (fun x ↦ ((schemeOpenModuleImage X U).obj M).val.map i x)
              (hfU T.unop z).symm).trans
                (PresheafOfModules.naturality_apply
                  ((schemeOpenModuleAdjunction X U).unit.app M).val i
                    (f T.unop z)).symm))
      · change ((schemeOpenModuleAdjunction X V).unit.app M).val.app S
          (f S.unop (Z.val.map i z)) =
            ((schemeOpenModuleAdjunction X V).unit.app M).val.app S
              (M.val.map i (f T.unop z))
        exact (hfV S.unop (Z.val.map i z)).trans
          ((PresheafOfModules.naturality_apply c.val i z).trans
            ((congrArg (fun x ↦ ((schemeOpenModuleImage X V).obj M).val.map i x)
              (hfV T.unop z).symm).trans
                (PresheafOfModules.naturality_apply
                  ((schemeOpenModuleAdjunction X V).unit.app M).val i
                    (f T.unop z)).symm)) }⟩
  refine ⟨l, ?_, ?_⟩
  · apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro T
    ext z
    exact hfU T.unop z
  · apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro T
    ext z
    exact hfV T.unop z

end AlgebraicGeometry
