/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Algebra.Category.ModuleCat.DerivedBaseChange
import WeilConjectures.Algebra.Homology.FreeComplexResidueDegreeCancellation

/-! # Residue exactness of a finite free complex is universal in one degree

Source: Stacks Project, More on Algebra, Tags 068U and 068V.
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace CochainComplex

private theorem exactAt_extendScalars_iff
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ) :
    (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).obj P).ExactAt i ↔
      (((tensorRight ((ModuleCat.restrictScalars f).obj
        (ModuleCat.of S S))).mapHomologicalComplex (.up ℤ)).obj P).ExactAt i := by
  let F := ModuleCat.extendScalars f
  let G := ModuleCat.restrictScalars f
  let c :
      ((G.mapHomologicalComplex (.up ℤ)).obj ((F.mapHomologicalComplex (.up ℤ)).obj P)) ≅
        (((tensorRight (G.obj (ModuleCat.of S S))).mapHomologicalComplex (.up ℤ)).obj P) :=
    ((Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).app P) ≪≫
      ((NatIso.mapHomologicalComplex (ModuleCat.extendScalarsCompRestrictScalarsIso f)
        (.up ℤ)).app P)
  have h : ((((F.mapHomologicalComplex (.up ℤ)).obj P).sc i).map G).Exact ↔
      ((F.mapHomologicalComplex (.up ℤ)).obj P).ExactAt i :=
    (((F.mapHomologicalComplex (.up ℤ)).obj P).sc i).exact_map_iff_of_faithful G
  constructor
  · intro hp
    have hh : ((G.mapHomologicalComplex (.up ℤ)).obj
        ((F.mapHomologicalComplex (.up ℤ)).obj P)).ExactAt i := h.mpr hp
    exact hh.of_iso c
  · intro hp
    exact h.mp (hp.of_iso c.symm)

private theorem residue_fraction_exact
    {R : Type u} [CommRing R] (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (i : ℤ) (m : Ideal R) [m.IsMaximal]
    (h : IsZero
      ((((tensorRight (ModuleCat.of R (R ⧸ m))).mapHomologicalComplex (.up ℤ)).obj P).homology i)) :
    IsZero
      ((((ModuleCat.extendScalars
        ((algebraMap (R ⧸ m) (FractionRing (R ⧸ m))).comp
          (Ideal.Quotient.mk m))).mapHomologicalComplex (.up ℤ)).obj P).homology i) := by
  let := Ideal.Quotient.field m
  let k := R ⧸ m
  let K := FractionRing k
  let f := Ideal.Quotient.mk m
  let g := algebraMap k K
  let E := ((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).obj P
  have hE : E.ExactAt i := (exactAt_extendScalars_iff f P i).2
    ((HomologicalComplex.exactAt_iff_isZero_homology _ _).2 h)
  have ht : (((tensorRight ((ModuleCat.restrictScalars g).obj
      (ModuleCat.of K K))).mapHomologicalComplex (.up ℤ)).obj E).ExactAt i :=
    Module.Flat.rTensor_shortComplex_exact _ _ hE
  have hF := (exactAt_extendScalars_iff g E i).2 ht
  let c : ((ModuleCat.extendScalars g).mapHomologicalComplex (.up ℤ)).obj E ≅
      (((ModuleCat.extendScalars (g.comp f)).mapHomologicalComplex (.up ℤ)).obj P) :=
    ((Functor.mapHomologicalComplexCompIso (Iso.refl
      (ModuleCat.extendScalars f ⋙ ModuleCat.extendScalars g)) (.up ℤ)).app P) ≪≫
      ((NatIso.mapHomologicalComplex (ModuleCat.extendScalarsComp f g).symm (.up ℤ)).app P)
  exact (hF.of_iso c).isZero_homology

private theorem localized_tensor_exact_of_homotopy
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (Q : CochainComplex (ModuleCat.{u} S) ℤ)
    (e : HomotopyEquiv (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).obj P) Q)
    (i : ℤ) (hi : IsZero (Q.X i)) (M : ModuleCat.{u} R) :
    (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).obj
      (((tensorRight M).mapHomologicalComplex (.up ℤ)).obj P)).ExactAt i := by
  let F := ModuleCat.extendScalars f
  let c :
      ((F.mapHomologicalComplex (.up ℤ)).obj
        (((tensorRight M).mapHomologicalComplex (.up ℤ)).obj P)) ≅
      (((tensorRight (F.obj M)).mapHomologicalComplex (.up ℤ)).obj
        ((F.mapHomologicalComplex (.up ℤ)).obj P)) :=
    ((Functor.mapHomologicalComplexCompIso (Iso.refl (tensorRight M ⋙ F))
      (.up ℤ)).app P) ≪≫
      ((NatIso.mapHomologicalComplex (Functor.Monoidal.commTensorRight F M).symm
        (.up ℤ)).app P) ≪≫
      ((Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ tensorRight (F.obj M)))
        (.up ℤ)).app P).symm
  have hz : IsZero
      ((((tensorRight (F.obj M)).mapHomologicalComplex (.up ℤ)).obj Q).homology i) :=
    (HomologicalComplex.ExactAt.of_isZero
      ((tensorRight (F.obj M)).map_isZero hi)).isZero_homology
  have he := ((tensorRight (F.obj M)).mapHomotopyEquiv e).toHomologyIso i
  exact ((HomologicalComplex.exactAt_iff_isZero_homology _ _).2
    (hz.of_iso he)).of_iso c.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem exactAt_of_principal_localizations
    {R : Type u} [CommRing R] (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (i : ℤ) (s : Set R) (hs : Ideal.span s = ⊤)
    (hex : ∀ f : s,
      (((ModuleCat.extendScalars (algebraMap R
        (Localization.Away f.val))).mapHomologicalComplex (.up ℤ)).obj P).ExactAt i) :
    P.ExactAt i := by
  let S := P.sc i
  let N (f : s) (M : ModuleCat.{u} R) :=
    (tensorLeft (ModuleCat.of R (Localization.Away f.val))).obj M
  let l (f : s) (M : ModuleCat.{u} R) : M →ₗ[R] N f M :=
    TensorProduct.mk R (Localization.Away f.val) M 1
  have hl (f : s) (M : ModuleCat.{u} R) : IsLocalizedModule.Away f.val (l f M) :=
    IsLocalization.tensorProduct_isLocalizedModule _ _
  have hm (f : s) {M M' : ModuleCat.{u} R} (g : M ⟶ M') :
      IsLocalizedModule.map (.powers f.val) (l f M) (l f M') g.hom =
        ((tensorLeft (ModuleCat.of R (Localization.Away f.val))).map g).hom := by
    have := hl f M
    have := hl f M'
    apply IsLocalizedModule.linearMap_ext (.powers f.val) (l f M) (l f M')
    ext x
    rw [LinearMap.comp_apply, IsLocalizedModule.map_apply]
    rfl
  have : S.Exact := by
    rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
    apply exact_of_isLocalized_span s hs
      (fun f ↦ N f S.X₁) (fun f ↦ l f S.X₁)
      (fun f ↦ N f S.X₂) (fun f ↦ l f S.X₂)
      (fun f ↦ N f S.X₃) (fun f ↦ l f S.X₃) S.f.hom S.g.hom
    intro f
    rw [hm f S.f, hm f S.g]
    have he := (exactAt_extendScalars_iff
      (algebraMap R (Localization.Away f.val)) P i).1 (hex f)
    let e : (ModuleCat.restrictScalars
        (algebraMap R (Localization.Away f.val))).obj
          (ModuleCat.of (Localization.Away f.val) (Localization.Away f.val)) ≅
        ModuleCat.of R (Localization.Away f.val) :=
      (AddEquiv.toLinearEquiv
        (M := ↑((ModuleCat.restrictScalars
          (algebraMap R (Localization.Away f.val))).obj
            (ModuleCat.of (Localization.Away f.val) (Localization.Away f.val))))
        (M₂ := ↑(ModuleCat.of R (Localization.Away f.val)))
        (AddEquiv.refl _) (fun r x ↦ by
          exact (Algebra.smul_def r (show Localization.Away f.val from x)).symm)).toModuleIso
    let c := (NatIso.mapHomologicalComplex
      ((tensoringRight (ModuleCat R)).mapIso e) (.up ℤ)).app P ≪≫
        ((NatIso.mapHomologicalComplex
          (BraidedCategory.tensorLeftIsoTensorRight
            (ModuleCat.of R (Localization.Away f.val))) (.up ℤ)).app P).symm
    exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (he.of_iso c)
  exact this

/-- Exactness in one degree of every maximal residue fibre of a termwise finite free
complex implies exactness in that degree after tensoring with every module.

Source: Stacks Project, More on Algebra, Tag 068U, the matrix cancellation proof,
and Tag 068V, the maximal-localization argument.
Proof: At each maximal ideal, identify its quotient field with the fraction field
of the quotient and apply degree cancellation. On a principal neighborhood avoiding
that ideal the complex is homotopy equivalent to a complex with zero middle term.
Tensoring with an arbitrary localized module preserves the homotopy equations;
its homology in that degree is therefore zero. Localization is exact and commutes
with termwise tensor and homology. The principal neighborhoods cover the maximal
spectrum, so exactness of the three-term sequence descends by localization.
This argument uses only the three adjacent finite free terms, no boundedness.
It includes the zero ring: exactness follows from the empty principal cover.
(auxiliary; not a blueprint node). -/
theorem isZero_homology_tensor_of_residue
    {R : Type u} [CommRing R] (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hfree : ∀ j : ℤ, Module.Free R (P.X j))
    (hfinite : ∀ j : ℤ, Module.Finite R (P.X j)) (i : ℤ)
    (hresidue : ∀ (m : Ideal R), m.IsMaximal → IsZero
      ((((tensorRight (ModuleCat.of R (R ⧸ m))).mapHomologicalComplex (.up ℤ)).obj P).homology
        i)) (M : ModuleCat.{u} R) :
    IsZero ((((tensorRight M).mapHomologicalComplex (.up ℤ)).obj P).homology i) := by
  let T := ((tensorRight M).mapHomologicalComplex (.up ℤ)).obj P
  let s : Set R := {f | (((ModuleCat.extendScalars
    (algebraMap R (Localization.Away f))).mapHomologicalComplex (.up ℤ)).obj T).ExactAt i}
  have hs : Ideal.span s = ⊤ := by
    by_contra h
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal (Ideal.span s) h
    have : m.IsMaximal := hm
    obtain ⟨f, hfm, Q, -, -, ⟨e⟩, hi, -⟩ :=
      exists_localized_homotopyEquiv_zero_degree m i P hfree hfinite
        (residue_fraction_exact P i m (hresidue m hm))
    have hf : f ∈ s := localized_tensor_exact_of_homotopy
      (algebraMap R (Localization.Away f)) P Q e i hi M
    exact hfm (hle (Ideal.subset_span hf))
  exact (exactAt_of_principal_localizations T i s hs (fun f ↦ f.property)).isZero_homology

end CochainComplex
