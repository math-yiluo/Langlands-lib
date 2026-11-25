/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomComplex
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Localization.Prod
public import Mathlib.CategoryTheory.Localization.Opposite
public import Mathlib.CategoryTheory.Functor.Currying
import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap

/-!
# Derived internal Hom on a ringed site

Source: Stacks Project, sites-cohomology.tex, Sections 08J7, 0A8X and 07A5
(blueprint: def-pur-derived-internal-hom).

`derivedInternalHom J R : D(O)ᵒᵖ × D(O) ⥤ D(O)` is the functor induced, through the
product localization `Q.op.prod Q`, by `(L, M) ↦ Q (Hom^•(L, I(M)))`, where `I` is the
functorial K-injective resolution `CochainComplex.kInjectiveResolutionFunctor` of the
Grothendieck abelian category of `O`-modules (`SheafOfModules.isGrothendieckAbelian`).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace CategoryTheory

/-- After any functorial K-injective replacement `I` in the second variable, the
localized Hom-complex bifunctor sends quasi-isomorphisms in either variable to
isomorphisms.

Source: Stacks Project, sites-cohomology.tex, Section 08J7, Lemma 0A95
(blueprint: def-pur-derived-internal-hom).

Proof:
1. A morphism of `W.op.prod W` is a pair `(t.op, s)` of quasi-isomorphisms; it factors as
   `(t.op, 𝟙) ≫ (𝟙, s)`, so it suffices to treat each variable separately.
2. For `s : M ⟶ M'` a quasi-isomorphism, naturality `η.app M ≫ I.map s = s ≫ η.app M'`
   and two-out-of-three make `I.map s` a quasi-isomorphism between K-injective complexes.
3. `quasiIso_homComplex_map` (`lem-pur-rhom-well-defined`), with `t = 𝟙` resp. `s = 𝟙`,
   makes the induced Hom-complex maps quasi-isomorphisms, so `DerivedCategory.Q` inverts
   them. -/
theorem derivedInternalHom_inverts
    {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
    (I : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ ⥤
      CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)
    (η : 𝟭 (CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ) ⟶ I)
    (hI : ∀ M : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ,
      QuasiIso (η.app M) ∧ (I.obj M).IsKInjective) :
    ((HomologicalComplex.quasiIso (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) (ComplexShape.up ℤ)).op.prod
      (HomologicalComplex.quasiIso (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) (ComplexShape.up ℤ))).IsInvertedBy
      ((𝟭 _).prod I ⋙ Functor.uncurry.obj (homComplexFunctor (R := R)) ⋙
        DerivedCategory.Q) := by
  intro X Y f hf
  have : QuasiIso f.1.unop := hf.1
  have : QuasiIso f.2 := hf.2
  have : QuasiIso (η.app X.2) := (hI X.2).1
  have : QuasiIso (η.app Y.2) := (hI Y.2).1
  have : (I.obj X.2).IsKInjective := (hI X.2).2
  have : (I.obj Y.2).IsKInjective := (hI Y.2).2
  have hη : QuasiIso ((η.app X.2) ≫ I.map f.2) := by
    rw [← η.naturality f.2]
    dsimp
    infer_instance
  have : QuasiIso (I.map f.2) :=
    (quasiIso_iff_comp_left _ _).mp hη
  apply (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr
  exact quasiIso_homComplex_map (I.map f.2) f.1.unop

/-- Derived internal Hom `R𝓗om_O : D(O)ᵒᵖ × D(O) ⥤ D(O)` on a small ringed site: the
functor induced through the localization `Q.op.prod Q` by
`(L, M) ↦ Q (𝓗om^•(L, I(M)))`, with `I` the functorial K-injective resolution
`CochainComplex.kInjectiveResolutionFunctor` of the Grothendieck abelian category of
`O`-modules. The Hom complex is `homComplexFunctor` (`def-pur-hom-complex`). For a fixed
first variable it agrees with the internal hom `DerivedCategory.internalHomQhObj` of the derived
tensor product (`derivedInternalHomIsoInternalHomQhObj`).

Source: Stacks Project, sites-cohomology.tex, Sections 08J7, 0A8X and 07A5
(blueprint: def-pur-derived-internal-hom). -/
noncomputable def derivedInternalHom
    {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))] :
    (DerivedCategory (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)))ᵒᵖ ×
      DerivedCategory (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ⥤ DerivedCategory (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :=
  haveI : IsGrothendieckAbelian.{u} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :=
    SheafOfModules.isGrothendieckAbelian _
  Localization.lift
    ((𝟭 _).prod (CochainComplex.kInjectiveResolutionFunctor.{u} _) ⋙
      Functor.uncurry.obj (homComplexFunctor (R := R)) ⋙ DerivedCategory.Q)
    (derivedInternalHom_inverts J R _ (CochainComplex.toKInjectiveResolution.{u} _)
      (fun M ↦ ⟨(CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} _ M).2,
        CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u} _ M⟩))
    ((DerivedCategory.Q).op.prod DerivedCategory.Q)

/-- Computation of derived internal Hom with any functorial K-injective replacement
`η : 𝟭 ⟶ I`: `R𝓗om(Q L, Q M) ≅ Q (𝓗om^•(L, I(M)))`, naturally in both variables
(contravariant in `L`, covariant in `M`).

Source: Stacks Project, sites-cohomology.tex, Section 08J7 and Lemma 0A95
(blueprint: def-pur-derived-internal-hom).

Proof:
1. For the resolution used in `derivedInternalHom`, this is `Localization.fac`.
2. For another replacement `I`, the maps `I₀(M) ← M → I(M)` are quasi-isomorphisms into
   K-injective complexes, so `Q(η₀)⁻¹ ≫ Q(η)` lifts to a homotopy class of chain maps
   `I₀(M) ⟶ I(M)`, natural up to homotopy, each a quasi-isomorphism.
3. `quasiIso_homComplex_map` (`lem-pur-rhom-well-defined`) makes the induced maps of Hom
   complexes quasi-isomorphisms; homotopic maps give equal maps after `Q`, so these form a
   natural isomorphism after localization. -/
theorem derivedInternalHom_comparison
    {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
    (I : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ ⥤
      CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)
    (η : 𝟭 (CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ) ⟶ I)
    (hI : ∀ M : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ,
      QuasiIso (η.app M) ∧ (I.obj M).IsKInjective) :
    Nonempty ((DerivedCategory.Q.op).prod DerivedCategory.Q ⋙ derivedInternalHom J R ≅
        (𝟭 _).prod I ⋙ Functor.uncurry.obj (homComplexFunctor (R := R)) ⋙
          DerivedCategory.Q) := by
  let A := SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
  let : IsGrothendieckAbelian.{u} A := SheafOfModules.isGrothendieckAbelian _
  let I₀ := CochainComplex.kInjectiveResolutionFunctor.{u} A
  let η₀ := CochainComplex.toKInjectiveResolution.{u} A
  let H := Functor.uncurry.obj (homComplexFunctor (R := R)) ⋙ DerivedCategory.Q
  have hinv (F G : CochainComplex A ℤ ⥤ CochainComplex A ℤ) (α : F ⟶ G)
      (hα : ∀ M, QuasiIso (α.app M))
      (hF : ∀ M, (F.obj M).IsKInjective)
      (hG : ∀ M, (G.obj M).IsKInjective) :
      IsIso (Functor.whiskerRight (NatTrans.prod (𝟙 (𝟭 _)) α) H) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro X
    have : QuasiIso (α.app X.2) := hα X.2
    have : (F.obj X.2).IsKInjective := hF X.2
    have : (G.obj X.2).IsKInjective := hG X.2
    apply (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr
    exact quasiIso_homComplex_map (α.app X.2) (𝟙 X.1.unop)
  let α := Functor.whiskerRight (NatTrans.prod (𝟙 (𝟭 _)) (Functor.whiskerLeft I₀ η)) H
  let β := Functor.whiskerRight (NatTrans.prod (𝟙 (𝟭 _)) (Functor.whiskerRight η₀ I)) H
  have : IsIso α := hinv _ _ _ (fun M ↦ (hI (I₀.obj M)).1)
    (fun M ↦ CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u} A M)
    (fun M ↦ (hI (I₀.obj M)).2)
  have : IsIso β := hinv _ _ _ (fun M ↦ by
      have : QuasiIso (η.app M) := (hI M).1
      have : QuasiIso (η.app (I₀.obj M)) := (hI (I₀.obj M)).1
      have : QuasiIso (η₀.app M) :=
        (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} A M).2
      apply (quasiIso_iff_comp_left (η.app M) _).mp
      change QuasiIso (η.app M ≫ I.map (η₀.app M))
      have hn := η.naturality (η₀.app M)
      dsimp at hn
      rw [← hn]
      infer_instance)
    (fun M ↦ (hI M).2) (fun M ↦ (hI (I₀.obj M)).2)
  exact ⟨Localization.fac _
      (derivedInternalHom_inverts J R I₀ η₀ (fun M ↦
        ⟨(CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} A M).2,
          CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u} A M⟩))
      ((DerivedCategory.Q).op.prod DerivedCategory.Q) ≪≫
    asIso α ≪≫ (asIso β).symm⟩

/-- Independence of the representatives and of an arbitrary K-injective target:
for complexes `Lc` representing `L` and a K-injective `Ic` representing `M`,
`R𝓗om(L, M) ≅ Q (𝓗om^•(Lc, Ic))`.

Source: Stacks Project, sites-cohomology.tex, Section 08J7 and Lemma 0A95
(blueprint: def-pur-derived-internal-hom).

Proof:
1. Compute with the functorial resolution via `derivedInternalHom_comparison`.
2. Represent the comparison `Q(I₀(Ic)) ≅ Q(Ic)` of two K-injective complexes by a chain
   map; it is a quasi-isomorphism since it represents an isomorphism.
3. Lemma 0A95 (`lem-pur-rhom-well-defined`) makes the induced Hom-complex map a
   quasi-isomorphism, hence an isomorphism after localization.
4. Apply the functor to the representative isomorphisms of `L` and `M` and compose. -/
theorem derivedInternalHom_obj_iso
    {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
    (L M : DerivedCategory (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)))
    (Lc Ic : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ) [Ic.IsKInjective]
    (_eL : DerivedCategory.Q.obj Lc ≅ L) (_eM : DerivedCategory.Q.obj Ic ≅ M) :
    Nonempty ((derivedInternalHom J R).obj (op L, M) ≅
      DerivedCategory.Q.obj (homComplex (C := C) (J := J) (R := R) Lc Ic)) := by
  let A := SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
  let : IsGrothendieckAbelian.{u} A := SheafOfModules.isGrothendieckAbelian _
  let I₀ := CochainComplex.kInjectiveResolutionFunctor.{u} A
  let η₀ := CochainComplex.toKInjectiveResolution.{u} A
  obtain ⟨e⟩ := derivedInternalHom_comparison J R I₀ η₀ (fun M ↦
    ⟨(CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} A M).2,
      CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u} A M⟩)
  have : QuasiIso (η₀.app Ic) :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} A Ic).2
  have : (I₀.obj Ic).IsKInjective :=
    CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u} A Ic
  let f := ((homComplexFunctor (R := R)).obj (op Lc)).map (η₀.app Ic)
  have : QuasiIso f := by
    simpa using quasiIso_homComplex_map (I' := Ic) (I := I₀.obj Ic) (η₀.app Ic) (𝟙 Lc)
  have : IsIso (DerivedCategory.Q.map f) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ f).mpr inferInstance
  exact ⟨(derivedInternalHom J R).mapIso (_eL.op.prod _eM.symm) ≪≫
    e.app (op Lc, Ic) ≪≫ (asIso (DerivedCategory.Q.map f)).symm⟩

end CategoryTheory
