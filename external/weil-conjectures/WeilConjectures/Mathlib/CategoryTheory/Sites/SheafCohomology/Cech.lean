/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import WeilConjectures.Algebra.Homology.ExactCouple.DoubleComplex
public import WeilConjectures.Algebra.Homology.TotalComplexRowResolution
public import WeilConjectures.CategoryTheory.Sites.CechSheaf
public import WeilConjectures.CategoryTheory.Sites.SheafCohomology.InjectiveResolution
public import WeilConjectures.Mathlib.Algebra.Category.Grp.Injective
public import WeilConjectures.Algebra.Homology.DerivedCategory.Ext.ChgUniv
public import WeilConjectures.Mathlib.Algebra.Homology.TotalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.SpectralSequence.Basic
public import WeilConjectures.Algebra.Homology.SpectralSequence.Transport

/-!
# The Čech-to-derived spectral sequence

Let `C` be an essentially small site with fibre products, `X : C` and `𝔘 = {Uᵢ ⟶ X}` a covering
of `X`. For an abelian sheaf `F` on `C` there is a first quadrant cohomological spectral sequence
`E₂^{p, q} = Ȟ^p(𝔘, ℋ^q(F)) ⟹ H^{p + q}(X, F)`, where `ℋ^q(F)` is the presheaf
`V ↦ H^q(V, F)`.

Both sides are taken from Mathlib: `ℋ^q(F)` is `CategoryTheory.Sheaf.cohomologyPresheaf`,
`H^n(X, F)` is `CategoryTheory.Sheaf.H'`, and the Čech complex of the covering is
`CategoryTheory.cechComplexFunctor` applied to the family `fun i ↦ Over.mk (π i)` of objects of
`Over X` — the finite products of `Over X` used there are exactly the fibre products
`Uᵢ ×[X] Uⱼ ×[X] ⋯`, so `Ȟ^p(𝔘, P)` is the `p`-th cohomology of that complex, evaluated on the
restriction of `P` to `Over X`.

## Main definitions

- `CategoryTheory.Sheaf.cohomologyPresheafULiftIso`: the cohomology presheaves computed with
  `Ext`-groups in two different universes agree after lifting both to a common universe.
- `CategoryTheory.Functor.mapHomologicalComplexCompHomologyFunctorIso`: an additive functor
  preserving homology commutes with taking homology of complexes.

## Main statements

- `CategoryTheory.Sheaf.exists_cechToDerivedSpectralSequence`: the Čech-to-derived spectral
  sequence of a covering of an object of an essentially small site.
- `CategoryTheory.Sheaf.exists_cechDoubleComplex`: when abelian sheaves have enough injectives,
  the double complex `C^p(𝔘, I^q)` attached to an injective resolution `F → I^•`, through its
  column cohomology and the cohomology of its total complex.
- `CategoryTheory.Sheaf.exists_cechDoubleComplex_uliftFunctor`: the same double complex for an
  essentially small site, a covering indexed by a type in an arbitrary universe `w` and
  cohomology computed in `AddCommGrpCat.{w}`, after lifting everything to `AddCommGrpCat.{max v w}`.

## Implementation notes

The statement `exists_cechToDerivedSpectralSequence` assumes that the site is essentially small
(`EssentiallySmall.{v} C`). The sites of the Stacks project are small, and the proof needs an
injective resolution of `F`: for an essentially small site the category of abelian sheaves is a
Grothendieck abelian category (`Sheaf.isGrothendieckAbelian_of_essentiallySmall`), hence has
enough injectives, while abelian sheaves on a large site need not have enough injectives.

The covering is indexed by `ι : Type w` and cohomology is computed in `AddCommGrpCat.{w}` for an
arbitrary universe `w`. The groups `C^p(𝔘, I^q)` of the Čech double complex are products indexed
by `ι^{p + 1}` of `v`-small groups, so the double complex lives in `AddCommGrpCat.{max v w}`: we
lift the injective resolution along `AddCommGrpCat.uliftFunctor` (the lift of an injective
presheaf is still injective, `Presheaf.injective_comp_uliftFunctor`), compare `Ext`-groups in the
universes `v` and `w` with `Ext.chgUniv`, and finally bring the spectral sequence back to
`AddCommGrpCat.{w}` with `SpectralSequence.exists_of_uliftFunctor`: from the `E₂`-page on, all its
terms are `w`-small. The special case where all universes agree and only enough injectives are
assumed is `CategoryTheory.Sheaf.exists_cechToDerivedSpectralSequence_of_enoughInjectives`, in
`WeilConjectures.CategoryTheory.Sites.CechSpectralSequence`.
-/

@[expose] public section

universe w' w v u

namespace CategoryTheory

open Limits Opposite

attribute [local instance] Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} [HasFiniteWidePullbacks C]
  [HasSheafify J AddCommGrpCat.{v}]

/-- The cohomology presheaves `V ↦ H^n(V, F)` computed with `Ext`-groups in the universes `w` and
`w'` agree after lifting both to `AddCommGrpCat.{max w w'}`; the isomorphism is
`Ext.chgUniv`. -/
noncomputable def Sheaf.cohomologyPresheafULiftIso [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]
    [HasExt.{w'} (Sheaf J AddCommGrpCat.{v})] (F : Sheaf J AddCommGrpCat.{v}) (n : ℕ) :
    Sheaf.cohomologyPresheaf.{w} F n ⋙ AddCommGrpCat.uliftFunctor.{w'} ≅
      Sheaf.cohomologyPresheaf.{w'} F n ⋙ AddCommGrpCat.uliftFunctor.{w} :=
  NatIso.ofComponents
    (fun V ↦ AddEquiv.toAddCommGrpIso (AddEquiv.ulift.trans
      ((Abelian.Ext.chgUnivAddEquiv.{w', w} _ _ n).trans AddEquiv.ulift.symm)))
    (fun {V V'} h ↦ by
      ext x
      refine ULift.ext ?_
      change Abelian.Ext.chgUniv.{w'} ((Abelian.Ext.mk₀ _).comp x.down (zero_add n)) =
        (Abelian.Ext.mk₀ _).comp (Abelian.Ext.chgUniv.{w'} x.down) (zero_add n)
      rw [Abelian.Ext.chgUniv_comp, Abelian.Ext.chgUniv_mk₀])

/-- **The Čech double complex of a covering.** Let `𝔘 = {π i : U i ⟶ X}` generate a covering
sieve of `X` and let `F` be an abelian sheaf, on a site whose abelian sheaves have enough
injectives. There is a first quadrant double complex `D` of abelian groups such that

* for every `q`, the complex `p ↦ H^q(D^{p, •})` is the Čech complex `C^•(𝔘, ℋ^q(F))` of the
  presheaf `ℋ^q(F) : V ↦ H^q(V, F)`;
* the total complex of `D` computes the cohomology `H^n(X, F)`.

It is `D^{p, q} = C^p(𝔘, I^q)` for an injective resolution `F → I^•`: the cohomology of the
complex `I^•(V)` is `H^•(V, F)` (`Sheaf.cohomologyPresheafIso`) and cohomology commutes with the
products defining the Čech complex, so the columns compute `C^p(𝔘, ℋ^q(F))` (Step 2); the
augmented Čech complex of the injective sheaf `I^q` is exact (Stacks `03F6`, `03AW`), so
`I^•(X) ⟶ Tot D` is a quasi-isomorphism and the total complex computes
`H^n(I^•(X)) = H^n(X, F)` (Step 3).

The groups `I^q(V)` are only `v`-small, so `D` lives in `AddCommGrpCat.{v}`; this is why the
covering is indexed by `ι : Type v` and the cohomology is computed in `AddCommGrpCat.{v}`. See
`Sheaf.exists_cechDoubleComplex_uliftFunctor` for other universes.

(blueprint: `lemma-coherent-base-change-invertible-sheaves--1`, Steps 1 to 3 of the proof) -/
theorem Sheaf.exists_cechDoubleComplex [HasExt.{v} (Sheaf J AddCommGrpCat.{v})]
    [EnoughInjectives (Sheaf J AddCommGrpCat.{v})] (F : Sheaf J AddCommGrpCat.{v}) (X : C)
    {ι : Type v} {U : ι → C} (π : ∀ i, U i ⟶ X) (hπ : Sieve.ofArrows U π ∈ J X) :
    ∃ D : HomologicalComplex₂ AddCommGrpCat.{v} (ComplexShape.up ℕ) (ComplexShape.up ℕ),
      (∀ q : ℕ, Nonempty
        (((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) q).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj D ≅
        (cechComplexFunctor fun i ↦ Over.mk (π i)).obj
          ((Over.forget X).op ⋙ F.cohomologyPresheaf q))) ∧
      ∀ n : ℕ, Nonempty ((D.total (ComplexShape.up ℕ)).homology n ≅ F.H' n X) := by
  have : HasProducts.{v} (CochainComplex AddCommGrpCat.{v} ℕ) :=
    fun _ ↦ HomologicalComplex.instHasLimitsOfShape
  let R : InjectiveResolution F := injectiveResolution F
  let V : ι → Over X := fun i ↦ Over.mk (π i)
  -- the presheaf of complexes `V ↦ I^•(V)` on `Over X`
  let Pc : (Over X)ᵒᵖ ⥤ CochainComplex AddCommGrpCat.{v} ℕ :=
    (Over.forget X).op ⋙ Sheaf.complexSections R.cocomplex
  let D : HomologicalComplex₂ AddCommGrpCat.{v} (ComplexShape.up ℕ) (ComplexShape.up ℕ) :=
    (cechComplexFunctor V).obj Pc
  refine ⟨D, fun q ↦ ⟨?_⟩, fun n ↦ ⟨?_⟩⟩
  · exact cechComplexFunctorMapIso V (HomologicalComplex.homologyFunctor _ _ q) Pc ≪≫
      (cechComplexFunctor V).mapIso
        (Functor.isoWhiskerLeft (Over.forget X).op (Sheaf.cohomologyPresheafIso R q))
  -- the rows of `D` are the Čech complexes of the injective sheaves `I^q`
  let e (q : ℕ) := cechComplexFunctorMapIso V (HomologicalComplex.eval _ _ q) Pc
  let ε := cechAugmentation V Over.mkIdTerminal Pc
  have hε : ε ≫ D.d 0 1 = 0 := cechAugmentation_d V Over.mkIdTerminal Pc
  have hfac (q : ℕ) : ε.f q ≫ (e q).hom.f 0 =
      cechAugmentation V Over.mkIdTerminal ((Over.forget X).op ⋙ (R.cocomplex.X q).obj) :=
    map_cechAugmentation_comp V Over.mkIdTerminal (HomologicalComplex.eval _ _ q) Pc
  have h₀ (q : ℕ) : Mono (ε.f q) := by
    have : Mono (ε.f q ≫ (e q).hom.f 0) := by
      rw [hfac]
      exact Presheaf.mono_cechAugmentation_of_isSheaf (V := V) (R.cocomplex.X q).property hπ
    exact mono_of_mono _ ((e q).hom.f 0)
  have h₁ (q : ℕ) : (ShortComplex.mk (ε.f q) ((D.d 0 1).f q)
      (by rw [← HomologicalComplex.comp_f, hε, HomologicalComplex.zero_f])).Exact := by
    have h := Presheaf.exact_cechAugmentation_of_isSheaf (V := V) (R.cocomplex.X q).property hπ
    refine (ShortComplex.exact_iff_of_iso ?_).2 h
    refine ShortComplex.isoMk (Iso.refl _) (HomologicalComplex.Hom.isoApp (e q) 0)
      (HomologicalComplex.Hom.isoApp (e q) 1) ?_ ((e q).hom.comm 0 1)
    rw [Iso.refl_hom, Category.id_comp]
    exact (hfac q).symm
  have hrow (p q : ℕ) : (ShortComplex.mk ((D.d p (p + 1)).f q) ((D.d (p + 1) (p + 2)).f q)
      (by rw [← HomologicalComplex.comp_f, HomologicalComplex.d_comp_d,
        HomologicalComplex.zero_f])).Exact := by
    have := Sheaf.injective_obj (R.cocomplex.X q)
    exact (ShortComplex.exact_iff_of_iso
      ((HomologicalComplex.shortComplexFunctor' _ _ p (p + 1) (p + 2)).mapIso (e q))).2
      (Presheaf.exact_cechComplexFunctor_of_injective V (R.cocomplex.X q).obj p)
  have := HomologicalComplex₂.quasiIso_toTotalOfAugmentation (hε := hε) h₀ h₁ hrow
  exact (isoOfQuasiIsoAt (D.toTotalOfAugmentation ε hε) n).symm ≪≫
    Sheaf.cohomologyPresheafIsoApp R n (op X)

/-- For an additive functor `G` preserving homology, taking the `q`-th homology of complexes
commutes with `G`. -/
noncomputable def Functor.mapHomologicalComplexCompHomologyFunctorIso {A B : Type*}
    [Category* A] [Category* B] [Abelian A] [Abelian B] (G : A ⥤ B) [G.Additive]
    [G.PreservesHomology] {ι : Type*} (c : ComplexShape ι) (q : ι) :
    G.mapHomologicalComplex c ⋙ HomologicalComplex.homologyFunctor B c q ≅
      HomologicalComplex.homologyFunctor A c q ⋙ G :=
  NatIso.ofComponents (fun K ↦ (K.sc q).mapHomologyIso G)
    (fun f ↦ ShortComplex.mapHomologyIso_hom_naturality
      ((HomologicalComplex.shortComplexFunctor A c q).map f) G)

/-- **The Čech double complex of a covering, in arbitrary universes.** Let `C` be an essentially
small site, `𝔘 = {π i : U i ⟶ X}` (with `ι : Type w`) generate a covering sieve of `X` and let
`F` be an abelian sheaf, with cohomology computed in `AddCommGrpCat.{w}`. There is a first
quadrant double complex `D` in `AddCommGrpCat.{max v w}` such that

* for every `q`, the complex `p ↦ H^q(D^{p, •})` is the universe lift of the Čech complex
  `C^•(𝔘, ℋ^q(F))`;
* the total complex of `D` computes the universe lift of `H^n(X, F)`.

As in `Sheaf.exists_cechDoubleComplex`, it is `D^{p, q} = C^p(𝔘, I^q)` for an injective
resolution `F → I^•`, where `I^q` is lifted to `AddCommGrpCat.{max v w}`.

(blueprint: `lemma-coherent-base-change-invertible-sheaves--1`, Steps 1 to 3 of the proof) -/
theorem Sheaf.exists_cechDoubleComplex_uliftFunctor [EssentiallySmall.{v} C]
    [HasExt.{w} (Sheaf J AddCommGrpCat.{v})] (F : Sheaf J AddCommGrpCat.{v}) (X : C)
    {ι : Type w} {U : ι → C} (π : ∀ i, U i ⟶ X) (hπ : Sieve.ofArrows U π ∈ J X) :
    ∃ D : HomologicalComplex₂ AddCommGrpCat.{max v w} (ComplexShape.up ℕ) (ComplexShape.up ℕ),
      (∀ q : ℕ, Nonempty
        (((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) q).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj D ≅
        (AddCommGrpCat.uliftFunctor.{v}.mapHomologicalComplex (ComplexShape.up ℕ)).obj
          ((cechComplexFunctor fun i ↦ Over.mk (π i)).obj
            ((Over.forget X).op ⋙ (F.cohomologyPresheaf q : Cᵒᵖ ⥤ AddCommGrpCat.{w}))))) ∧
      ∀ n : ℕ, Nonempty ((D.total (ComplexShape.up ℕ)).homology n ≅
        AddCommGrpCat.uliftFunctor.{v}.obj (F.H' n X : AddCommGrpCat.{w})) := by
  have : HasProducts.{max v w} (CochainComplex AddCommGrpCat.{max v w} ℕ) :=
    fun _ ↦ HomologicalComplex.instHasLimitsOfShape
  have := Sheaf.isGrothendieckAbelian_of_essentiallySmall J AddCommGrpCat.{v}
  let G := AddCommGrpCat.uliftFunctor.{w, v}
  let R : InjectiveResolution F := injectiveResolution F
  let V : ι → Over X := fun i ↦ Over.mk (π i)
  -- the presheaf of complexes `V ↦ I^•(V)` on `Over X`, lifted to `AddCommGrpCat.{max v w}`
  let Pc : (Over X)ᵒᵖ ⥤ CochainComplex AddCommGrpCat.{max v w} ℕ :=
    (Over.forget X).op ⋙ Sheaf.complexSections R.cocomplex ⋙
      G.mapHomologicalComplex (ComplexShape.up ℕ)
  let D : HomologicalComplex₂ AddCommGrpCat.{max v w} (ComplexShape.up ℕ) (ComplexShape.up ℕ) :=
    (cechComplexFunctor V).obj Pc
  refine ⟨D, fun q ↦ ⟨?_⟩, fun n ↦ ⟨?_⟩⟩
  · let eq : Pc ⋙ HomologicalComplex.homologyFunctor _ _ q ≅
        (Over.forget X).op ⋙ Sheaf.cohomologyPresheaf.{w} F q ⋙
          AddCommGrpCat.uliftFunctor.{v} :=
      Functor.isoWhiskerLeft (Over.forget X).op
        (Functor.isoWhiskerLeft (Sheaf.complexSections R.cocomplex)
          (G.mapHomologicalComplexCompHomologyFunctorIso (ComplexShape.up ℕ) q) ≪≫
        Functor.isoWhiskerRight (Sheaf.cohomologyPresheafIso R q) G ≪≫
        Sheaf.cohomologyPresheafULiftIso.{w, v} F q)
    exact cechComplexFunctorMapIso V (HomologicalComplex.homologyFunctor _ _ q) Pc ≪≫
      (cechComplexFunctor V).mapIso eq ≪≫
      (cechComplexFunctorMapIso V AddCommGrpCat.uliftFunctor.{v}
        ((Over.forget X).op ⋙ Sheaf.cohomologyPresheaf.{w} F q)).symm
  -- the rows of `D` are the Čech complexes of the lifted injective sheaves `I^q`
  let e (q : ℕ) := cechComplexFunctorMapIso V (HomologicalComplex.eval _ _ q) Pc
  let ε := cechAugmentation V Over.mkIdTerminal Pc
  have hε : ε ≫ D.d 0 1 = 0 := cechAugmentation_d V Over.mkIdTerminal Pc
  have hfac (q : ℕ) : ε.f q ≫ (e q).hom.f 0 =
      cechAugmentation V Over.mkIdTerminal ((Over.forget X).op ⋙ (R.cocomplex.X q).obj ⋙ G) :=
    map_cechAugmentation_comp V Over.mkIdTerminal (HomologicalComplex.eval _ _ q) Pc
  have hsheaf (q : ℕ) : Presheaf.IsSheaf J ((R.cocomplex.X q).obj ⋙ G) :=
    GrothendieckTopology.HasSheafCompose.isSheaf _ (R.cocomplex.X q).property
  have h₀ (q : ℕ) : Mono (ε.f q) := by
    have : Mono (ε.f q ≫ (e q).hom.f 0) := by
      rw [hfac]
      exact Presheaf.mono_cechAugmentation_of_isSheaf (V := V) (hsheaf q) hπ
    exact mono_of_mono _ ((e q).hom.f 0)
  have h₁ (q : ℕ) : (ShortComplex.mk (ε.f q) ((D.d 0 1).f q)
      (by rw [← HomologicalComplex.comp_f, hε, HomologicalComplex.zero_f])).Exact := by
    have h := Presheaf.exact_cechAugmentation_of_isSheaf (V := V) (hsheaf q) hπ
    refine (ShortComplex.exact_iff_of_iso ?_).2 h
    refine ShortComplex.isoMk (Iso.refl _) (HomologicalComplex.Hom.isoApp (e q) 0)
      (HomologicalComplex.Hom.isoApp (e q) 1) ?_ ((e q).hom.comm 0 1)
    rw [Iso.refl_hom, Category.id_comp]
    exact (hfac q).symm
  have hrow (p q : ℕ) : (ShortComplex.mk ((D.d p (p + 1)).f q) ((D.d (p + 1) (p + 2)).f q)
      (by rw [← HomologicalComplex.comp_f, HomologicalComplex.d_comp_d,
        HomologicalComplex.zero_f])).Exact := by
    have := Sheaf.injective_obj (R.cocomplex.X q)
    have := Presheaf.injective_comp_uliftFunctor.{w} (R.cocomplex.X q).obj
    exact (ShortComplex.exact_iff_of_iso
      ((HomologicalComplex.shortComplexFunctor' _ _ p (p + 1) (p + 2)).mapIso (e q))).2
      (Presheaf.exact_cechComplexFunctor_of_injective V ((R.cocomplex.X q).obj ⋙ G) p)
  have := HomologicalComplex₂.quasiIso_toTotalOfAugmentation (hε := hε) h₀ h₁ hrow
  exact (isoOfQuasiIsoAt (D.toTotalOfAugmentation ε hε) n).symm ≪≫
    (((Sheaf.complexSections R.cocomplex).obj (op X)).sc n).mapHomologyIso G ≪≫
    G.mapIso (Sheaf.cohomologyPresheafIsoApp R n (op X)) ≪≫
    (Sheaf.cohomologyPresheafULiftIso.{w, v} F n).app (op X)

/-- **The Čech-to-derived spectral sequence.** Let `C` be an essentially small site with fibre
products, `X : C` and `𝔘 = {π i : U i ⟶ X}` a family of morphisms generating a covering sieve
of `X`. For an abelian sheaf `F` on `C` there is a first quadrant cohomological spectral sequence
with `E₂^{p, q} ≅ Ȟ^p(𝔘, ℋ^q(F))` abutting to `H^{p + q}(X, F)`, where `ℋ^q(F)` is the presheaf
`V ↦ H^q(V, F)`.

The `E₂`-term is the `p`-th cohomology of the Čech complex of the family `fun i ↦ Over.mk (π i)`
of objects of `Over X` with coefficients in the restriction of `ℋ^q(F)` to `Over X`.

The site is assumed essentially small, as are the sites of the Stacks project: this provides
injective resolutions of abelian sheaves, which need not exist on a large site.

(blueprint: `lemma-coherent-base-change-invertible-sheaves--1`, `lem-sc-cech-spectral`) -/
theorem Sheaf.exists_cechToDerivedSpectralSequence [EssentiallySmall.{v} C]
    [HasExt.{w} (Sheaf J AddCommGrpCat.{v})] (F : Sheaf J AddCommGrpCat.{v}) (X : C)
    {ι : Type w} {U : ι → C} (π : ∀ i, U i ⟶ X) (hπ : Sieve.ofArrows U π ∈ J X) :
    ∃ E : E₂CohomologicalSpectralSequenceNat AddCommGrpCat.{w},
      (∀ p q : ℕ, Nonempty ((E.page 2).X (p, q) ≅
        ((cechComplexFunctor fun i ↦ Over.mk (π i)).obj
          ((Over.forget X).op ⋙ F.cohomologyPresheaf q)).homology p)) ∧
      E.AbutsTo fun n ↦ F.H' n X := by
  obtain ⟨D, hcol, htot⟩ := F.exists_cechDoubleComplex_uliftFunctor X π hπ
  obtain ⟨E', hE'₂, hE'⟩ := D.exists_spectralSequence
  let G := AddCommGrpCat.uliftFunctor.{v, w}
  let K (q : ℕ) : CochainComplex AddCommGrpCat.{w} ℕ :=
    (cechComplexFunctor fun i ↦ Over.mk (π i)).obj
      ((Over.forget X).op ⋙ (F.cohomologyPresheaf q : Cᵒᵖ ⥤ AddCommGrpCat.{w}))
  let e (p q : ℕ) : (E'.page 2).X (p, q) ≅ G.obj ((K q).homology p) :=
    (hE'₂ p q).some ≪≫ HomologicalComplex.homologyMapIso (hcol q).some p ≪≫
      ((K q).sc p).mapHomologyIso G
  obtain ⟨E, hE₂, hE⟩ := SpectralSequence.exists_of_uliftFunctor E' (fun n ↦ F.H' n X)
    (fun pq ↦ ⟨_, ⟨(e pq.1 pq.2).symm⟩⟩) (hE'.of_iso fun n ↦ (htot n).some)
  exact ⟨E, fun p q ↦ ⟨G.preimageIso ((hE₂ (p, q)).some ≪≫ e p q)⟩, hE⟩

end CategoryTheory
