/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Triangulated.Functor
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
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
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.CategoryTheory.Limits.Final
import WeilConjectures.CategoryTheory.RightKanExtensionCoherentShift
import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import WeilConjectures.CategoryTheory.LeftDerivedKanSourceTriangles
import Mathlib.CategoryTheory.Localization.Triangulated
import WeilConjectures.Mathlib.CategoryTheory.Functor.Derived.LeftDerivedEquivalence

/-! # The counit-compatible shift of derived scalar extension

Source: Stacks Project, derived.tex, Tags 05SU(2), 05SE (left derived functor part),
and sites-cohomology.tex, Tag 06YY
(blueprint: lem-sbc-derived-scalar-extension-counit-shift).

The ordinary functor is identified on both objects and maps with the existing
change of rings. Its induced homotopy functor has the canonical shift comparison
induced by identity maps in each degree, not a freely chosen shift structure.
The conclusion specifies a natural degree-one isomorphism, uniqueness among all
natural isomorphisms satisfying the counit equation, and preservation of every
distinguished triangle with precisely that isomorphism on the last arrow.
This statement is re-recorded by group NM on 2026-10-17.
-/

@[expose] public section

set_option autoImplicit false

universe u v r wR wS

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace SheafOfModules

/-- The derived scalar-extension counit determines a unique natural shift comparison,
and this comparison makes derived scalar extension triangulated.
Source: Stacks Project, derived.tex, Tags 05SU(2), 05SE (LF part), and
sites-cohomology.tex, Tag 06YY
(blueprint: lem-sbc-derived-scalar-extension-counit-shift).

Here `E` is ordinary change of rings on module sheaves; its homotopy functor is the
statement's termwise functor. The objects and maps of `E` are fixed by `h` and `hmap`.
The `commShiftIso` of `E.mapHomotopyCategory` is induced by
`E.mapCochainComplexShiftIso`, whose degree components are identities. Thus the
right side of the equation is exactly the composite of the derived counit,
`Q_S(theta_P)` and the localization shift isomorphism, in that order.
No coherent shift structure on `F`, flatness of `S`, or bound on complexes is assumed.

Proof:
1. Termwise change of rings is additive. It preserves the cone biproduct and its
matrix differential, and carries a homotopy dh+hd to the corresponding homotopy.
Consequently it descends to the homotopy category and preserves cone triangles,
including the negative projection (def-pur-sheaf-tensor-product,
def-weil-abstract-derived-category, lem-pur-homotopy-category-triangulated).
2. Use the class of K-flat complexes with flat terms. Every complex has such a
resolution (lem-pc-kflat-resolution), and tensor inverts quasi-isomorphisms between
these resolutions (lem-pur-derived-change-of-rings). The resolving-class theorem
(lem-pur-left-derived-from-kflat-class) gives the everywhere-defined universal
pair, with invertible counit on that class. The given pair is such a left derived pair.
3. For every integer n, termwise tensor of the shifted complex and the shift of
its tensor have the same terms and signed differentials. Identity maps in every
degree give the coherent shift isomorphism. Composing with localization gives
the comparison of B = E.mapHomotopyCategory followed by Q_S.
4. Apply lem-pur-right-kan-extension-coherent-shift to Q_R, B and the given
universal pair F, epsilon. Its degree-one counit square is the displayed equation.
5. For uniqueness, postcomposition by shift preserves the right Kan property.
For two competing natural isomorphisms, cancel F(s_P) in their counit equations.
Injectivity of the Kan universal correspondence for the shifted target functor
identifies their natural transformations, hence their isomorphisms. Equivalently,
shift back and use the universal correspondence of
lem-pur-left-derived-from-kflat-class. No coherence or triangle preservation is
required of the competing degree-one isomorphism.
6. Quasi-isomorphisms are a saturated triangulated multiplicative system
(lem-pur-quasi-isos-saturated-triangulated). The same resolving class gives
essential constancy of the denominator diagrams
(lem-pur-resolving-class-essential-constancy). Apply
lem-pur-left-derived-kan-source-triangles with the counit-compatible coherent
shift from step 4: images of distinguished homotopy triangles are distinguished.
Every distinguished derived triangle is isomorphic to such an image
(lem-pur-localization-triangles-05r6). Applying F to the three isomorphisms gives
an isomorphism of image triangles; its last square uses naturality of sigma.
Closure under isomorphism proves the final clause for the very same sigma
(def-weil-triangulated-category). Exactness also gives additivity of F. -/
theorem derivedScalarExtension_counitShift
    {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasSheafify J AddCommGrpCat.{r}]
    {R S : Sheaf J CommRingCat.{r}} (φ : R ⟶ S)
    [HasDerivedCategory.{wR} (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J R))]
    [HasDerivedCategory.{wS} (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J S))]
    (E : ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R) ⥤
      ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J S))
    (h : ∀ M : ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R),
      E.obj M = changeOfRings.{v, u, r} φ M)
    (hmap : ∀ {M N : ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R)}
      (f : M ⟶ N),
      E.map f = eqToHom (h M) ≫ changeOfRingsHom.{v, u, r} φ M f ≫ eqToHom (h N).symm)
    [E.Additive]
    (F : DerivedCategory (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R)) ⥤
      DerivedCategory (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J S)))
    (ε : DerivedCategory.Qh ⋙ F ⟶ E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    [F.IsLeftDerivedFunctor ε
      (HomotopyCategory.quasiIso
        (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R)) (.up ℤ))] :
    ∃ σ : shiftFunctor _ (1 : ℤ) ⋙ F ≅ F ⋙ shiftFunctor _ (1 : ℤ),
      (∀ P : HomotopyCategory
          (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R)) (.up ℤ),
        F.map ((DerivedCategory.Qh.commShiftIso (1 : ℤ)).hom.app P) ≫
            σ.hom.app (DerivedCategory.Qh.obj P) ≫
            (shiftFunctor _ (1 : ℤ)).map (ε.app P) =
          ε.app ((shiftFunctor _ (1 : ℤ)).obj P) ≫
            DerivedCategory.Qh.map
              (((E.mapHomotopyCategory (.up ℤ)).commShiftIso (1 : ℤ)).hom.app P) ≫
            (DerivedCategory.Qh.commShiftIso (1 : ℤ)).hom.app
              ((E.mapHomotopyCategory (.up ℤ)).obj P)) ∧
      (∀ τ : shiftFunctor _ (1 : ℤ) ⋙ F ≅ F ⋙ shiftFunctor _ (1 : ℤ),
        (∀ P : HomotopyCategory
            (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R)) (.up ℤ),
          F.map ((DerivedCategory.Qh.commShiftIso (1 : ℤ)).hom.app P) ≫
              τ.hom.app (DerivedCategory.Qh.obj P) ≫
              (shiftFunctor _ (1 : ℤ)).map (ε.app P) =
            ε.app ((shiftFunctor _ (1 : ℤ)).obj P) ≫
              DerivedCategory.Qh.map
                (((E.mapHomotopyCategory (.up ℤ)).commShiftIso (1 : ℤ)).hom.app P) ≫
              (DerivedCategory.Qh.commShiftIso (1 : ℤ)).hom.app
                ((E.mapHomotopyCategory (.up ℤ)).obj P)) → τ = σ) ∧
      F.Additive ∧
      ∀ T : Triangle (DerivedCategory
          (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R))),
        T ∈ distTriang _ →
          Triangle.mk (F.map T.mor₁) (F.map T.mor₂)
            (F.map T.mor₃ ≫ σ.hom.app T.obj₁) ∈ distTriang _ := by
  classical
  let A := ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R)
  let A' := ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J S)
  let B := E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh
  let W := HomotopyCategory.quasiIso A (.up ℤ)
  have hkan : F.IsRightKanExtension ε :=
    Functor.IsLeftDerivedFunctor.isRightKanExtension F ε W
  let : F.IsRightKanExtension ε := hkan
  obtain ⟨hshift, hcounit⟩ :=
    Functor.rightKanExtension_coherentShift B DerivedCategory.Qh F ε hkan
  let : F.CommShift ℤ := hshift
  let : NatTrans.CommShift ε ℤ := hcounit
  have hcompat (P : HomotopyCategory A (.up ℤ)) :
      F.map ((DerivedCategory.Qh.commShiftIso (1 : ℤ)).hom.app P) ≫
          (F.commShiftIso (1 : ℤ)).hom.app (DerivedCategory.Qh.obj P) ≫
          (shiftFunctor _ (1 : ℤ)).map (ε.app P) =
        ε.app ((shiftFunctor _ (1 : ℤ)).obj P) ≫
          DerivedCategory.Qh.map
            (((E.mapHomotopyCategory (.up ℤ)).commShiftIso (1 : ℤ)).hom.app P) ≫
          (DerivedCategory.Qh.commShiftIso (1 : ℤ)).hom.app
            ((E.mapHomotopyCategory (.up ℤ)).obj P) := by
    simpa only [Functor.commShiftIso_comp_hom_app, Category.assoc] using
      NatTrans.shift_app_comm ε (1 : ℤ) P
  -- Identify the prescribed ordinary functor with the current change-of-rings model.
  have hquasi : ∀ {P Q : CochainComplex A ℤ} (f : P ⟶ Q),
      CochainComplex.IsKFlatIndependentCoefficients (R := R) P →
      CochainComplex.IsKFlatIndependentCoefficients (R := R) Q → QuasiIso f →
        QuasiIso ((E.mapHomologicalComplex (.up ℤ)).map f) := by
    obtain ⟨m⟩ := nonempty_derivedChangeOfRingsCochainModel.{u, v, r, wR, wS} φ
    have heq : E = m.E := by
      refine CategoryTheory.Functor.ext (fun M ↦ (h M).trans (m.obj_eq M).symm) ?_
      intro M N f
      simp only [hmap, m.map_eq, Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
    subst E
    intro P Q f hp hq hf
    exact m.preserves f hp hq hf
  -- Represent the resolving class in the homotopy category by K-flat complexes.
  let P : Set (HomotopyCategory A (.up ℤ)) :=
    { X | ∃ K : CochainComplex A ℤ,
      CochainComplex.IsKFlatIndependentCoefficients (R := R) K ∧
        (HomotopyCategory.quotient A (.up ℤ)).obj K = X }
  have hres : ∀ X : HomotopyCategory A (.up ℤ),
      ∃ (X' : HomotopyCategory A (.up ℤ)) (s : X' ⟶ X), X' ∈ P ∧ W s := by
    intro X
    obtain ⟨G, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    obtain ⟨K, s, hK, _, hs, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := R) G
    exact ⟨_, (HomotopyCategory.quotient A (.up ℤ)).map s, ⟨K, hK, rfl⟩,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff s).2 hs⟩
  have hinv : ∀ X Y : HomotopyCategory A (.up ℤ), ∀ s : X ⟶ Y,
      X ∈ P → Y ∈ P → W s → IsIso (B.map s) := by
    intro X Y s hX hY hs
    obtain ⟨K, hK, rfl⟩ := hX
    obtain ⟨L, hL, rfl⟩ := hY
    obtain ⟨a, rfl⟩ := (HomotopyCategory.quotient A (.up ℤ)).map_surjective s
    have ha := (HomotopyCategory.quotient_map_mem_quasiIso_iff a).1 hs
    have hEa := hquasi a hK hL ha
    dsimp only [B, Functor.comp_map, Functor.mapHomotopyCategory_map]
    apply Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso _ _)
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 hEa
  obtain ⟨hleft, hright, htri, hsat, htwo, _, _, _, _⟩ :=
    HomotopyCategory.quasiIso_saturated_triangulated A
  let : W.HasLeftCalculusOfFractions := hleft
  let : W.HasRightCalculusOfFractions := hright
  let : W.HasTwoOutOfThreeProperty := htwo
  have hW : W.IsSaturatedTriangulatedMultiplicativeSystem :=
    ⟨⟨⟨hleft, hright⟩, fun _ _ _ _ f g k ↦ hsat _ _ _ _ g f k⟩, htri⟩
  have hdefined : ∀ X, B.IsTriangulatedLeftDerivedDefinedAt W hW X := by
    intro X
    obtain ⟨Y, _, hc, _, _⟩ :=
      Functor.resolvingClass_essentialConstancy W B P hres hinv X
    exact ⟨Y, hc⟩
  -- Use the source-triangle theorem for the very shift constructed from epsilon.
  have hsource : (DerivedCategory.Qh ⋙ F).IsTriangulated := by
    constructor
    intro T hT
    exact Functor.leftDerived_kan_map_source_distinguished _ _ _ B W hW
      DerivedCategory.Qh F ε hkan hdefined hcounit T hT
  let : (DerivedCategory.Qh ⋙ F).IsTriangulated := hsource
  have := Localization.essSurj_mapArrow (DerivedCategory.Qh (C := A)) W
  have hFtri : F.IsTriangulated := by
    constructor
    intro T hT
    obtain ⟨T₀, e, hT₀⟩ := (DerivedCategory.Qh.distTriang_iff T).1 hT
    exact isomorphic_distinguished _
      ((DerivedCategory.Qh ⋙ F).map_distinguished T₀ hT₀) _
      (F.mapTriangle.mapIso e ≪≫
        (Functor.mapTriangleCompIso DerivedCategory.Qh F).symm.app T₀)
  let : F.IsTriangulated := hFtri
  refine ⟨F.commShiftIso (1 : ℤ), hcompat, ?_, inferInstance, ?_⟩
  · intro τ hτ
    let H := shiftFunctor (DerivedCategory A') (1 : ℤ)
    let γ := (Functor.associator DerivedCategory.Qh F H).inv ≫
      Functor.whiskerRight ε H
    -- Apply preservation by an equivalence before specializing to these derived categories.
    have hpost : (F ⋙ H).IsRightKanExtension γ :=
      Functor.isRightKanExtension_comp_of_isEquivalence F ε H
    let : (F ⋙ H).IsRightKanExtension γ := hpost
    apply Iso.ext
    apply (F ⋙ H).hom_ext_of_isRightKanExtension γ
    ext X
    simp only [γ, NatTrans.comp_app, Functor.associator_inv_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Category.id_comp]
    change τ.hom.app (DerivedCategory.Qh.obj X) ≫ H.map (ε.app X) =
      (F.commShiftIso (1 : ℤ)).hom.app (DerivedCategory.Qh.obj X) ≫ H.map (ε.app X)
    apply (cancel_epi (F.map ((DerivedCategory.Qh.commShiftIso (1 : ℤ)).hom.app X))).1
    simpa only [Category.assoc] using (hτ X).trans (hcompat X).symm
  · intro T hT
    exact F.map_distinguished T hT

end SheafOfModules
