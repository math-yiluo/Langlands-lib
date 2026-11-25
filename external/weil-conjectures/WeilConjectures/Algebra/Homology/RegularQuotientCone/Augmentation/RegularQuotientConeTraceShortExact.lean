/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.RegularQuotientCone.Augmentation.RegularQuotientConeBoundary
import WeilConjectures.Algebra.Homology.RegularQuotientCone.ScalarConeHomotopy
import WeilConjectures.Algebra.Homology.RegularQuotientCone.RegularQuotientConeAdjoint
import WeilConjectures.Algebra.Homology.RegularQuotientCone.RegularQuotientConeChain
import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Localization.Predicate
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-! # The coinduction trace on a short exact sequence of the regular scalar

If `0 ⟶ A ⟶ X ⟶ X ⟶ 0` is a short exact sequence of complexes whose second map is the regular
scalar, with `A⟦1⟧` restricted from the quotient coefficients, and if the counit of a right
adjoint of derived restriction is computed at `X⟦1⟧` by the restricted ordinary counit, then the
quotient-linear coinduction trace is invertible at `X⟦1⟧`.

Source: Stacks Tags 06YP, 06YY, 07A6, 0A70 and 08FZ; the principal short exact sequence of
complexes and its cone-boundary/coinduction comparison.
(blueprint: lem-sf-regular-quotient-trace-on-injective-terms). -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v r wR wS
open CategoryTheory CategoryTheory.Limits
namespace SheafOfModules.RegularQuotientCone

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
  [EssentiallySmall.{r} C]
  {R S : Sheaf J CommRingCat.{r}} {φ : R ⟶ S}
  [HasDerivedCategory.{wR} (Modules R)] [HasDerivedCategory.{wS} (Modules S)]
  {t : (unit (derivedChangeRingIndependentCoefficients J R)).sections}
  {d : DerivedChangeOfRingsCochainModel.{u, v, r, wR, wS} φ}

/-- Derived restriction of a normalized augmentation is additive and conservative.
Source: Stacks Tags 05SS and 06YY; restriction is exact and faithful, so it commutes with
cohomology and reflects isomorphisms of module sheaves
(blueprint: lem-sf-regular-quotient-trace-on-injective-terms). -/
theorem Augmentation.V_additive_and_reflectsIsomorphisms (b : Augmentation φ t d) :
    b.V.Additive ∧ b.V.ReflectsIsomorphisms := by
  obtain ⟨hlim, hcol, -⟩ := sheafRingCoefficientOrdinaryAdjunction φ
  have : PreservesFiniteLimits (restriction φ) := hlim
  have : PreservesFiniteColimits (restriction φ) := hcol
  let e : b.V ≅ (restriction φ).mapDerivedCategory :=
    Localization.liftNatIso DerivedCategory.Q (HomologicalComplex.quasiIso (Modules S) (.up ℤ))
      (DerivedCategory.Q ⋙ b.V) (DerivedCategory.Q ⋙ (restriction φ).mapDerivedCategory)
      b.V (restriction φ).mapDerivedCategory
      (b.restriction_factor ≪≫ (restriction φ).mapDerivedCategoryFactors.symm)
  have hr : (restriction φ).ReflectsIsomorphisms := ⟨fun {M N} g hg ↦ by
    have : IsIso ((toSheaf _).map g) :=
      inferInstanceAs (IsIso ((toSheaf _).map ((restriction φ).map g)))
    exact isIso_of_reflects_iso g (toSheaf _)⟩
  have hd : (restriction φ).mapDerivedCategory.ReflectsIsomorphisms := by
    refine ⟨fun g _ ↦ ?_⟩
    rw [DerivedCategory.isIso_iff]
    intro n
    have : IsIso ((restriction φ).map ((DerivedCategory.homologyFunctor _ n).map g)) :=
      (NatIso.isIso_map_iff ((restriction φ).mapDerivedCategoryHomologyFunctorIso n) g).2
        (by rw [Functor.comp_map]; infer_instance)
    exact isIso_of_reflects_iso _ (restriction φ)
  exact ⟨Functor.additive_of_iso e.symm, reflectsIsomorphisms_of_iso e.symm⟩

/-- Shifting back the shift by `-1` of an isomorphism `z : Z⟦1⟧ ≅ W` recovers `z`.
Source: Stacks Tag 0145; the compatibilities of the shift functors
(auxiliary; not a blueprint node). -/
theorem shift_one_neg_one_transpose {D : Type*} [Category D] [HasShift D ℤ] {Z W : D}
    (z : Z⟦(1 : ℤ)⟧ ≅ W) :
    ((shiftFunctorCompIsoId D (1 : ℤ) (-1) (by omega)).symm.app Z ≪≫
        (shiftFunctor D (-1 : ℤ)).mapIso z).hom⟦(1 : ℤ)⟧' ≫
      (shiftFunctorCompIsoId D (-1 : ℤ) 1 (by omega)).hom.app W = z.hom := by
  simp only [Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.map_comp,
    Category.assoc]
  have hn : (shiftFunctor D (1 : ℤ)).map ((shiftFunctor D (-1 : ℤ)).map z.hom) ≫
      (shiftFunctorCompIsoId D (-1 : ℤ) 1 (by omega)).hom.app W =
      (shiftFunctorCompIsoId D (-1 : ℤ) 1 (by omega)).hom.app _ ≫ z.hom :=
    (shiftFunctorCompIsoId D (-1 : ℤ) 1 (by omega)).hom.naturality z.hom
  rw [hn, shift_shiftFunctorCompIsoId_inv_app]
  simp

/-- The normalized cone boundary at a localized complex is the localized strict cone projection.
Source: Stacks Tags 06YP and 07A6; the definition of the descended boundary
(blueprint: lem-sf-regular-quotient-cone-boundary). -/
theorem Augmentation.boundary_app_Q (b : Augmentation φ t d)
    (P : CochainComplex (Modules R) ℤ) :
    b.boundary.app (DerivedCategory.Q.obj P) =
      b.A.inv.app (DerivedCategory.Q.obj P) ≫ b.cone_factor.hom.app P ≫
        DerivedCategory.Q.map ((chainBoundary (R := R) (t := t)).app P) ≫
          (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app P := by
  simp [Augmentation.boundary, Localization.liftNatTrans_app]

open CochainComplex CochainComplex.mappingCone in
/-- The quotient-linear coinduction trace is invertible at `Y ≅ X⟦1⟧` whenever
`0 ⟶ A ⟶ X ⟶ X ⟶ 0` is a short exact sequence of complexes with the regular scalar as second
map, `A⟦1⟧` is restricted from a quotient complex `N`, and the counit of the right adjoint at
`Y` is computed by a strict map `N ⟶ Y` extending `ε⟦1⟧`.
Source: Stacks Tags 06YP, 06YY, 07A6, 0A70 and 08FZ; the principal short exact sequence of
complexes and its cone-boundary/coinduction comparison
(blueprint: lem-sf-regular-quotient-trace-on-injective-terms).

Proof: let `P` be the mapping cone of `ε`, a model of `X` through the quasi-isomorphism
`p : P ⟶ X`. The cone boundary `P ⟶ A⟦1⟧` is killed by the scalar, and the augmentation
adjoint formula identifies restriction of its adjoint transpose with the strict scalar-cone
augmentation of `P`, which is a quasi-isomorphism. As derived restriction is conservative, the
transpose is invertible. The chain homotopy between this augmentation and the cone boundary
shows that, after the identification of `P` with `X`, the transpose is minus the adjoint
transpose of the normalized trace counit. Hence the trace is invertible. -/
theorem Augmentation.isIso_coinductionTrace_app_of_shortExact (b : Augmentation φ t d)
    (ht : (scalar R t).app (unit (derivedChangeRingIndependentCoefficients J R)) ≫
      ringMap φ = 0)
    {G : DerivedCategory (Modules R) ⥤ DerivedCategory (Modules S)} (a : b.V ⊣ G)
    {A X : CochainComplex (Modules R) ℤ} (ε : A ⟶ X)
    (hε : ε ≫ (complexScalar R t).app X = 0)
    (hS : (ShortComplex.mk ε ((complexScalar R t).app X) hε).ShortExact)
    {N : CochainComplex (Modules S) ℤ}
    (e : A⟦(1 : ℤ)⟧ ≅ ((restriction φ).mapHomologicalComplex (.up ℤ)).obj N)
    {Y : CochainComplex (Modules R) ℤ} (w : X⟦(1 : ℤ)⟧ ≅ Y)
    (εN : ((restriction φ).mapHomologicalComplex (.up ℤ)).obj N ⟶ Y)
    (he : e.hom ≫ εN = ε⟦(1 : ℤ)⟧' ≫ w.hom)
    (γ : G.obj (DerivedCategory.Q.obj Y) ≅ DerivedCategory.Q.obj N)
    (hγ : b.V.map γ.inv ≫ a.counit.app (DerivedCategory.Q.obj Y) =
      b.restriction_factor.hom.app N ≫ DerivedCategory.Q.map εN) :
    IsIso ((b.coinductionTrace a).app (DerivedCategory.Q.obj Y)) := by
  obtain ⟨hadd, hrefl⟩ := b.V_additive_and_reflectsIsomorphisms
  let P := mappingCone ε
  let tP := (complexScalar R t).app P
  let p := descShortComplex (ShortComplex.mk ε ((complexScalar R t).app X) hε)
  have : QuasiIso p := quasiIso_descShortComplex hS
  have hA : (complexScalar R t).app (A⟦(1 : ℤ)⟧) = 0 := by
    have h0 : (complexScalar R t).app
        (((restriction φ).mapHomologicalComplex (.up ℤ)).obj N) = 0 := by
      ext n : 1
      exact scalar_restriction_zero t φ ht (N.X n)
    have hn : e.hom ≫ (complexScalar R t).app
          (((restriction φ).mapHomologicalComplex (.up ℤ)).obj N) =
        (complexScalar R t).app (A⟦(1 : ℤ)⟧) ≫ e.hom :=
      (complexScalar R t).naturality e.hom
    rw [h0, comp_zero] at hn
    rw [← cancel_mono e.hom, zero_comp]
    exact hn.symm
  have hf : tP ≫ (triangle ε).mor₃ = 0 := scalar_triangle_mor₃_zero _ ε hA
  let f' := (triangle ε).mor₃ ≫ e.hom
  have hf' : tP ≫ f' = 0 := by simp [f', reassoc_of% hf]
  let m := desc tP 0 (triangle ε).mor₃ (by simp [hf])
  have hm : IsIso (DerivedCategory.Q.map m) :=
    isIso_Q_map_scalarConeDesc (complexScalar R t) ε (scalar R t) (fun _ _ ↦ rfl) hε hA hS
  have hh := DerivedCategory.Q_map_eq_of_homotopy _
    (scalarConeHomotopy (τ := complexScalar R t) (ε := ε) (s := scalar R t)
      (hτ := fun _ _ ↦ rfl) (hε := hε) (hA := hA))
  have hdesc : desc tP 0 f' (by simp [hf']) = m ≫ e.hom := by
    apply HomologicalComplex.hom_ext
    intro j
    apply ext_from _ (j + 1) j rfl <;> simp [m, f']
  have hadj := augmentation_adjoint φ t d b P N f' hf'
  let σ0 : d.T.obj (DerivedCategory.Q.obj P) ⟶ DerivedCategory.Q.obj N :=
    (b.adjunction.homEquiv (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj N)).symm
      (DerivedCategory.Q.map f' ≫ b.restriction_factor.inv.app N)
  have hVσ0 : b.V.map σ0 = b.A.inv.app (DerivedCategory.Q.obj P) ≫ b.cone_factor.hom.app P ≫
      DerivedCategory.Q.map m ≫ DerivedCategory.Q.map e.hom ≫
        b.restriction_factor.inv.app N := by
    rw [← DerivedCategory.Q.map_comp_assoc, ← hdesc]
    exact hadj
  have hσ0 : IsIso σ0 := by
    have : IsIso (b.V.map σ0) := by
      rw [hVσ0]
      infer_instance
    exact isIso_of_reflects_iso σ0 b.V
  let z : (DerivedCategory.Q.obj X)⟦(1 : ℤ)⟧ ≅ DerivedCategory.Q.obj Y :=
    (DerivedCategory.Q.commShiftIso (1 : ℤ)).symm.app X ≪≫ DerivedCategory.Q.mapIso w
  let v : DerivedCategory.Q.obj X ≅ (DerivedCategory.Q.obj Y)⟦(-1 : ℤ)⟧ :=
    (shiftFunctorCompIsoId _ (1 : ℤ) (-1) (by omega)).symm.app _ ≪≫
      (CategoryTheory.shiftFunctor _ (-1 : ℤ)).mapIso z
  have hv := shift_one_neg_one_transpose z
  let ψ : (DerivedCategory.Q.obj Y)⟦(-1 : ℤ)⟧ ≅ DerivedCategory.Q.obj P :=
    v.symm ≪≫ (asIso (DerivedCategory.Q.map p)).symm
  let σ := d.T.map ψ.hom ≫ σ0 ≫ γ.inv
  have key : DerivedCategory.Q.map ((CategoryTheory.shiftFunctor _ (1 : ℤ)).map p) ≫
      DerivedCategory.Q.map w.hom =
      (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app P ≫ ψ.inv⟦(1 : ℤ)⟧' ≫
        (shiftFunctorCompIsoId _ (-1 : ℤ) 1 (by omega)).hom.app (DerivedCategory.Q.obj Y) := by
    have hψ : ψ.inv = DerivedCategory.Q.map p ≫ v.hom := rfl
    rw [hψ, Functor.map_comp, Category.assoc, ← Functor.commShiftIso_hom_naturality_assoc]
    erw [hv]
    simp [z]
  have hT : b.traceCounit.app (DerivedCategory.Q.obj Y) =
      b.boundary.app ((DerivedCategory.Q.obj Y)⟦(-1 : ℤ)⟧) ≫
        (shiftFunctorCompIsoId _ (-1 : ℤ) 1 (by omega)).hom.app (DerivedCategory.Q.obj Y) := by
    simp [Augmentation.traceCounit]
  have hB : b.boundary.app ((DerivedCategory.Q.obj Y)⟦(-1 : ℤ)⟧) =
      b.V.map (d.T.map ψ.hom) ≫ b.boundary.app (DerivedCategory.Q.obj P) ≫
        ψ.inv⟦(1 : ℤ)⟧' := by
    have hn := b.boundary.naturality ψ.hom
    simp only [Functor.comp_map] at hn
    rw [reassoc_of% hn, ← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id,
      Category.comp_id]
  have hσ : b.V.map σ ≫ a.counit.app (DerivedCategory.Q.obj Y) =
      -(b.traceCounit.app (DerivedCategory.Q.obj Y)) := by
    rw [hT, hB, b.boundary_app_Q]
    simp only [σ, Functor.map_comp, Category.assoc, hγ, hVσ0, Iso.inv_hom_id_app_assoc]
    rw [← DerivedCategory.Q.map_comp e.hom εN, he, Functor.map_comp,
      ← DerivedCategory.Q.map_comp_assoc m]
    erw [hh]
    rw [← key]
    simp only [Functor.map_neg, Functor.map_comp, Preadditive.neg_comp, Preadditive.comp_neg,
      Category.assoc]
    rfl
  have htr : (b.coinductionTrace a).app (DerivedCategory.Q.obj Y) = -σ := by
    change a.homEquiv _ _ (b.traceCounit.app _) = -σ
    rw [← neg_neg (b.traceCounit.app _), ← hσ, ← Preadditive.neg_comp, ← b.V.map_neg,
]
    exact (a.homEquiv _ _).apply_symm_apply (-σ)
  rw [htr]
  have : IsIso σ := by dsimp only [σ]; infer_instance
  exact ⟨-inv σ, by simp, by simp⟩

end SheafOfModules.RegularQuotientCone
