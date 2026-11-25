/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.RegularQuotientCone.RegularQuotientConeBasic
import WeilConjectures.Algebra.Homology.RegularQuotientCone.RegularQuotientConeQuasiIso
import WeilConjectures.CategoryTheory.Cochain.CochainDerivedAdjunction
import WeilConjectures.CategoryTheory.Cochain.CochainAugmentationDescent
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings

/-! # Normalized principal-quotient cone augmentation

Source: Stacks Project, Tags 06YP, 06YY and 07A6.
(blueprint: lem-cbc-regular-quotient-cone-augmentation).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v r wR wS
open CategoryTheory CategoryTheory.Limits

open scoped ChangeOfRings

namespace SheafOfModules.RegularQuotientCone

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasSheafify J AddCommGrpCat.{r}]

variable [EssentiallySmall.{r} C]
  {R S : Sheaf J CommRingCat.{r}} (φ : R ⟶ S)
  [HasDerivedCategory.{wR} (Modules R)] [HasDerivedCategory.{wS} (Modules S)]

/-- The chain augmentation and its normalized descent, with the existing universal
change-of-rings model. The section equation fixes the coefficient unit, and the cone
component equation fixes the augmentation, including its zero shifted component.
The factorization isomorphisms specify localizations, not freely chosen comparisons.
Source: Stacks 06YP, 06YY and 07A6
(blueprint: lem-cbc-regular-quotient-cone-augmentation). -/
structure Augmentation
    (t : (unit (derivedChangeRingIndependentCoefficients J R)).sections)
    (d : DerivedChangeOfRingsCochainModel.{u, v, r, wR, wS} φ) where
  /-- The ordinary coefficient unit on complexes. -/
  ρ : 𝟭 (CochainComplex (Modules R) ℤ) ⟶
    d.E.mapHomologicalComplex (.up ℤ) ⋙ (restriction φ).mapHomologicalComplex (.up ℤ)
  /-- Its local formula is the sheafification of `1 ⊗ x`, in scalar-first convention. -/
  ρ_sections : ∀ (P : CochainComplex (Modules R) ℤ) (n : ℤ) (U : Cᵒᵖ)
    (x : (P.X n).val.obj U),
    (eqToHom (d.obj_eq (P.X n))).val.app U (((ρ.app P).f n).val.app U x) =
      (((PresheafOfModules.sheafificationAdjunction.{r}
        (J := J) (R := derivedChangeRingIndependentCoefficients J S)
        (𝟙 (derivedChangeRingIndependentCoefficients J S).obj)).unit.app
        (changeOfRingsPresheaf φ (P.X n))).app U
        ((ModuleCat.extendRestrictScalarsAdj (φ.hom.app U).hom).unit.app
          ((P.X n).val.obj U) x))
  /-- The chain augmentation, natural for chain maps (in particular K-flat ones). -/
  a : cone R t ⟶
    d.E.mapHomologicalComplex (.up ℤ) ⋙ (restriction φ).mapHomologicalComplex (.up ℤ)
  /-- In coordinates `(y,x)` it is `1 ⊗ y`; the shifted component is zero. -/
  a_components : ∀ (P : CochainComplex (Modules R) ℤ) (n : ℤ),
    (a.app P).f n =
      (CochainComplex.mappingCone.snd ((complexScalar R t).app P)).v n n (add_zero n) ≫
        (ρ.app P).f n
  /-- The augmentation is a quasi-isomorphism for every K-flat complex. -/
  quasiIso : ∀ P : CochainComplex (Modules R) ℤ,
    CochainComplex.IsKFlatIndependentCoefficients (R := R) P → QuasiIso (a.app P)
  /-- The strict equality before localization. -/
  augmentation_inclusion : inclusion R t ≫ a = ρ
  /-- Cone formation preserves quasi-isomorphisms between K-flat complexes. -/
  cone_preserves : ∀ {P Q : CochainComplex (Modules R) ℤ} (h : P ⟶ Q),
    CochainComplex.IsKFlatIndependentCoefficients (R := R) P →
    CochainComplex.IsKFlatIndependentCoefficients (R := R) Q → QuasiIso h →
      QuasiIso ((cone R t).map h)
  /-- The restricted ordinary tensor preserves the same quasi-isomorphisms. -/
  tensor_preserves : ∀ {P Q : CochainComplex (Modules R) ℤ} (h : P ⟶ Q),
    CochainComplex.IsKFlatIndependentCoefficients (R := R) P →
    CochainComplex.IsKFlatIndependentCoefficients (R := R) Q → QuasiIso h →
      QuasiIso (((d.E.mapHomologicalComplex (.up ℤ)) ⋙
        (restriction φ).mapHomologicalComplex (.up ℤ)).map h)
  /-- Restriction on derived categories, characterized by exact termwise restriction. -/
  V : DerivedCategory (Modules S) ⥤ DerivedCategory (Modules R)
  /-- The canonical factorization comparison for restriction. -/
  restriction_factor : DerivedCategory.Q ⋙ V ≅
    (restriction φ).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  /-- The actual derived coefficient adjunction. -/
  adjunction : d.T ⊣ V
  /-- Its unit is normalized by the ordinary coefficient map on K-flat models. -/
  unit_normalization : ∀ P : CochainComplex (Modules R) ℤ,
    CochainComplex.IsKFlatIndependentCoefficients (R := R) P →
      adjunction.unit.app (DerivedCategory.Q.obj P) ≫ V.map (d.ε.app P) ≫
        restriction_factor.hom.app ((d.E.mapHomologicalComplex (.up ℤ)).obj P) =
          DerivedCategory.Q.map (ρ.app P)
  /-- The localized cone functor. -/
  D : DerivedCategory (Modules R) ⥤ DerivedCategory (Modules R)
  /-- Cone formation is localized on all complexes. -/
  cone_factor : DerivedCategory.Q ⋙ D ≅ cone R t ⋙ DerivedCategory.Q
  /-- The localized cone inclusion. -/
  i : 𝟭 (DerivedCategory (Modules R)) ⟶ D
  /-- Its component is the localization of the strict inclusion. -/
  inclusion_components : ∀ P : CochainComplex (Modules R) ℤ,
    i.app (DerivedCategory.Q.obj P) ≫ cone_factor.hom.app P =
      DerivedCategory.Q.map ((inclusion R t).app P)
  /-- Natural for every derived morphism, including resolution-comparison roofs. -/
  A : D ≅ d.T ⋙ V
  /-- The component at every K-flat complex uses exactly the universal counit. -/
  A_components : ∀ P : CochainComplex (Modules R) ℤ,
    CochainComplex.IsKFlatIndependentCoefficients (R := R) P →
      A.hom.app (DerivedCategory.Q.obj P) ≫ V.map (d.ε.app P) ≫
        restriction_factor.hom.app ((d.E.mapHomologicalComplex (.up ℤ)).obj P) =
          cone_factor.hom.app P ≫ DerivedCategory.Q.map (a.app P)
  /-- After localization the inclusion becomes the actual scalar-extension unit. -/
  unit_identity : i ≫ A.hom = adjunction.unit

/-- The normalized principal-quotient augmentation, without termwise flatness.
The zero composite says precisely `φ(t) = 0`; short exactness is in module sheaves,
so no surjectivity on sections or existence of points is assumed.

Source: Stacks Project, sites-cohomology.tex, Tags 06YP, 06YS, 06YT, 06YY and 07A6
(blueprint: lem-cbc-regular-quotient-cone-augmentation).

Proof:
1. Use the normalized ordinary coefficient adjunction to define its unit termwise.
The zero coefficient composite implies that the scalar annihilates restricted modules;
naturality of the scalar therefore says that this unit kills multiplication by t.
The mapping-cone descent construction gives the strict augmentation with zero shifted
component, its naturality and its composite with the unshifted inclusion.
2. For flat-term complexes, tensor the given coefficient short exact sequence degreewise.
The regular tensor unitor and normalized scalar-extension comparison identify its maps
with the scalar and the coefficient unit. The short-exact-sequence cone projection is
therefore the augmentation and is a quasi-isomorphism. Resolve an arbitrary K-flat
complex by a flat-term K-flat complex. Cone invariance, preservation by the specified
ordinary extension model, exact restriction and naturality give the result for it too.
Cone invariance itself follows from the two-isomorphisms property of cone triangles.
3. Transfer the specified universal cochain left-derived pair to homotopy categories.
Apply derived-adjunction compatibility using the resolving K-flat class and exact
restriction. Its representative formula at the identity, transported through the canonical
quotient/localization comparisons, gives the normalized cochain unit equation.
4. Localize the scalar cone and its inclusion. Postcomposing the universal cochain
counit with the derived right adjoint preserves its Kan extension property. Thus the
strict augmentation factors uniquely through this counit. The factor is invertible
on K-flats, hence on all complexes by resolutions and naturality, and on every derived
object by essential surjectivity. This constructs A with the prescribed components.
5. On K-flats, cancel the invertible universal counit and use the strict inclusion
identity to identify i followed by A with the derived unit. Resolve arbitrary complexes
to extend the equality by naturality, then use essential surjectivity of localization.
The result is a natural isomorphism on the whole derived category, so its naturality
also includes every resolution-comparison roof and its cocycle identities. -/
theorem nonempty_augmentation
    (t : (unit (derivedChangeRingIndependentCoefficients J R)).sections)
    (ht : (scalar R t).app (unit (derivedChangeRingIndependentCoefficients J R)) ≫
      ringMap φ = 0)
    (_hexact : (ShortComplex.mk
      ((scalar R t).app (unit (derivedChangeRingIndependentCoefficients J R)))
      (ringMap φ) ht).ShortExact)
    (d : DerivedChangeOfRingsCochainModel.{u, v, r, wR, wS} φ) :
    Nonempty (Augmentation φ t d) := by
  classical
  obtain ⟨hlim, hcol, ho⟩ := sheafRingCoefficientOrdinaryAdjunction φ
  obtain ⟨adj, ha⟩ := ho d.E d.obj_eq d.map_eq
  have : PreservesFiniteLimits (restriction φ) := hlim
  have : PreservesFiniteColimits (restriction φ) := hcol
  have := d.universal
  have := d.pointwise
  let ρ := coefficientUnit φ d.E adj
  have hsections (M : Modules R) (U : Cᵒᵖ) (x : M.val.obj U) :
      (eqToHom (d.obj_eq M)).val.app U ((adj.unit.app M).val.app U x) =
        (toSheafify J (changeOfRingsPresheaf φ M).presheaf).app U
          ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U,(φ.hom.app U).hom] x) := by
    have h := ha M (changeOfRings φ M) (𝟙 _) U x
    simp only [Category.comp_id, Adjunction.homEquiv_unit] at h
    change (eqToHom (d.obj_eq M)).val.app U ((adj.unit.app M).val.app U x) =
      (toSheafify J (changeOfRingsPresheaf φ M).presheaf).app U
        ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U,(φ.hom.app U).hom] x) at h
    exact h
  have hρ : ∀ (P : CochainComplex (Modules R) ℤ) (n : ℤ) (U : Cᵒᵖ)
      (x : (P.X n).val.obj U),
      (eqToHom (d.obj_eq (P.X n))).val.app U (((ρ.app P).f n).val.app U x) =
        (((PresheafOfModules.sheafificationAdjunction.{r}
          (J := J) (R := derivedChangeRingIndependentCoefficients J S)
          (𝟙 (derivedChangeRingIndependentCoefficients J S).obj)).unit.app
          (changeOfRingsPresheaf φ (P.X n))).app U
          ((ModuleCat.extendRestrictScalarsAdj (φ.hom.app U).hom).unit.app
            ((P.X n).val.obj U) x)) := by
    intro P n U x
    exact hsections (P.X n) U x
  let a := chainAugmentation t _ ρ (coefficientUnit_zero t φ d.E adj ht)
  have haQ (P : CochainComplex (Modules R) ℤ)
      (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P) :
      QuasiIso (a.app P) := chainAugmentation_quasiIso φ t ht _hexact d adj hsections P hP
  let good : ObjectProperty (CochainComplex (Modules R) ℤ) :=
    fun P ↦ CochainComplex.IsKFlatIndependentCoefficients (R := R) P
  have hres : ∀ P : CochainComplex (Modules R) ℤ,
      ∃ (F : CochainComplex (Modules R) ℤ) (p : F ⟶ P), good F ∧ QuasiIso p := by
    intro P
    obtain ⟨F, p, hF, _, hp, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := R) P
    exact ⟨F, p, hF, hp⟩
  obtain ⟨dadj, hnorm⟩ := Functor.exists_cochainDerivedAdjunction
    d.E (restriction φ) adj d.T d.ε good hres d.computes
  have : (restriction φ).mapDerivedCategory.IsRightAdjoint := ⟨_, ⟨dadj⟩⟩
  obtain ⟨D, e, i, hi, A, hA⟩ := Functor.exists_cochainAugmentationDescent
    d.E (restriction φ) d.T d.ε good hres d.computes
    (cone R t) (inclusion R t) (fun f hf ↦ cone_quasiIso t f hf) a haQ
  have hn (P : CochainComplex (Modules R) ℤ) :
      dadj.unit.app (DerivedCategory.Q.obj P) ≫
          (restriction φ).mapDerivedCategory.map (d.ε.app P) ≫
          (restriction φ).mapDerivedCategoryFactors.hom.app
            ((d.E.mapHomologicalComplex (.up ℤ)).obj P) =
        DerivedCategory.Q.map (ρ.app P) := by
    exact hnorm P
  have hiA : i ≫ A.hom = dadj.unit := by
    have hgood (P : CochainComplex (Modules R) ℤ) (hP : good P) :
        (i ≫ A.hom).app (DerivedCategory.Q.obj P) =
          dadj.unit.app (DerivedCategory.Q.obj P) := by
      have := d.computes P hP
      apply (cancel_mono
        ((restriction φ).mapDerivedCategory.map (d.ε.app P) ≫
          (restriction φ).mapDerivedCategoryFactors.hom.app
            ((d.E.mapHomologicalComplex (.up ℤ)).obj P))).1
      simp only [NatTrans.comp_app, Category.assoc]
      rw [hA, ← Category.assoc, hi, ← DerivedCategory.Q.map_comp, hn]
      apply DerivedCategory.Q.congr_map
      exact congrArg (fun f ↦ f.app P)
        (inclusion_chainAugmentation t _ ρ (coefficientUnit_zero t φ d.E adj ht))
    have hall (P : CochainComplex (Modules R) ℤ) :
        (i ≫ A.hom).app (DerivedCategory.Q.obj P) =
          dadj.unit.app (DerivedCategory.Q.obj P) := by
      obtain ⟨F, p, hF, hp⟩ := hres P
      have : IsIso (DerivedCategory.Q.map p) :=
        Localization.inverts DerivedCategory.Q
          (HomologicalComplex.quasiIso (Modules R) (.up ℤ)) p hp
      apply (cancel_epi (DerivedCategory.Q.map p)).1
      have hl := (i ≫ A.hom).naturality (DerivedCategory.Q.map p)
      have hr := dadj.unit.naturality (DerivedCategory.Q.map p)
      simp only [Functor.id_map] at hl hr
      exact hl.trans ((congrArg
        (fun f ↦ f ≫ (d.T ⋙ (restriction φ).mapDerivedCategory).map
          (DerivedCategory.Q.map p)) (hgood F hF)).trans hr.symm)
    apply NatTrans.ext
    funext X
    let Q := DerivedCategory.Q (C := Modules R)
    let eX := Q.objObjPreimageIso X
    apply (cancel_epi eX.hom).1
    simpa only [Functor.id_map] using
      ((i ≫ A.hom).naturality eX.hom).trans
        ((congrArg (fun f ↦ f ≫ (d.T ⋙ (restriction φ).mapDerivedCategory).map eX.hom)
          (hall (Q.objPreimage X))).trans (dadj.unit.naturality eX.hom).symm)
  exact ⟨{
    ρ := ρ
    ρ_sections := hρ
    a := a
    a_components := chainAugmentation_components t _ ρ _
    quasiIso := haQ
    augmentation_inclusion := inclusion_chainAugmentation t _ ρ _
    cone_preserves := fun f _ _ hf ↦ cone_quasiIso t f hf
    tensor_preserves := by
      intro P Q f hP hQ hf
      have := d.preserves f hP hQ hf
      exact HomologicalComplex.quasiIso_map_of_preservesHomology _ (restriction φ)
    V := (restriction φ).mapDerivedCategory
    restriction_factor := (restriction φ).mapDerivedCategoryFactors
    adjunction := dadj
    unit_normalization := fun P _ ↦ hn P
    D := D
    cone_factor := e
    i := i
    inclusion_components := hi
    A := A
    A_components := fun P _ ↦ hA P
    unit_identity := hiA }⟩

end SheafOfModules.RegularQuotientCone
