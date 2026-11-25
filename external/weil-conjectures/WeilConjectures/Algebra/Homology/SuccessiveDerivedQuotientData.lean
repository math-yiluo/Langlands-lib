/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.CategoryTheory.RingedSiteModules

/-! # Normalized presentations of derived coefficient extension

Source: Stacks Project, sites-cohomology.tex, Tags 06YY, 07A6, 0D6D;
sites-modules.tex, Tags 03D7 and 03EK.
(auxiliary; not a blueprint node).

These definitions are extracted, without changing their data, from the successive
normalization theorem module. They package the canonical ordinary scalar extension,
its universal left-derived presentation, and the normalization laws. Existence of
such presentations and laws belongs to the separate theorem, not to this definition.
-/

@[expose] public section
set_option autoImplicit false
universe u v r w
open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings
namespace SheafOfModules.SuccessiveDerivedQuotient
variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]

/-- The existing module-sheaf category, with no new objects or morphisms.
Source: Stacks 03D7 (auxiliary; not a blueprint node). -/
abbrev Modules (R : Sheaf J CommRingCat.{r}) :=
  ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R)

/-- The existing restriction-of-scalars functor.
Source: Stacks 03D7 (auxiliary; not a blueprint node). -/
noncomputable abbrev restriction {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) :
    Modules S ⥤ Modules R :=
  restrictScalars ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map a)

/-- The sheafification image of a sectionwise scalar-first pure tensor.
Source: Stacks 03EK (auxiliary; not a blueprint node). -/
noncomputable def pure {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S)
    (M : Modules R) (U : Cᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) :
    (changeOfRings a M).val.obj U :=
  (CategoryTheory.toSheafify J (changeOfRingsPresheaf a M).presheaf).app U
    (s ⊗ₜ[R.obj.obj U, (a.hom.app U).hom] x)

variable [hD : ∀ R : Sheaf J CommRingCat.{r}, HasDerivedCategory.{w} (Modules R)]

/-- A presentation of the already defined derived coefficient extension. The object and
map equations fix the ordinary functor, and the universal counit fixes the derived pair
up to its unique compatible isomorphism. This bundles the interfaces of 06YY and 07A6;
it introduces no alternative tensor product or derived-category construction.
Source: Stacks 06YY, 07A6 (auxiliary; not a blueprint node). -/
structure Presentation {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) where
  /-- The ordinary, sheafified scalar-extension functor. -/
  ordinary : Modules R ⥤ Modules S
  /-- Its objects are the recorded change-of-rings objects. -/
  obj_eq : ∀ M : Modules R, ordinary.obj M = changeOfRings a M
  /-- Its maps are the recorded sheafified tensor maps. -/
  map_eq : ∀ {M N : Modules R} (f : M ⟶ N), ordinary.map f =
    eqToHom (obj_eq M) ≫ changeOfRingsHom a M f ≫ eqToHom (obj_eq N).symm
  /-- Additivity needed for passage to homotopy categories. -/
  additive : ordinary.Additive
  /-- The unbounded left derived functor. -/
  derived : DerivedCategory (Modules R) ⥤ DerivedCategory (Modules S)
  /-- The universal left-derived computation morphism. -/
  counit : DerivedCategory.Qh ⋙ derived ⟶
    @Functor.mapHomotopyCategory _ _ _ _ _ _ _ ordinary additive (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh
  /-- The universal property, rather than a freely chosen computation map. -/
  universal : derived.IsLeftDerivedFunctor counit
    (HomotopyCategory.quasiIso (Modules R) (ComplexShape.up ℤ))

attribute [instance] Presentation.additive

/-- A pure section of the presented ordinary extension, transported only by `obj_eq`.
Source: Stacks 03EK (auxiliary; not a blueprint node). -/
noncomputable def sectionTensor {R S : Sheaf J CommRingCat.{r}} {a : R ⟶ S}
    (p : Presentation a) (M : Modules R) (U : Cᵒᵖ) (s : S.obj.obj U)
    (x : M.val.obj U) : (p.ordinary.obj M).val.obj U :=
  (eqToHom (p.obj_eq M).symm).val.app U (pure a M U s x)

/-- The canonical coefficient-change square made from two composition comparisons.
The equality is the commuting square of ring maps, not a chosen module comparison.
Source: Stacks 0D6D (auxiliary; not a blueprint node). -/
noncomputable def squareComparison
    (p : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S), Presentation a)
    (δ : ∀ {R S T : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (b : S ⟶ T),
      (p a).derived ⋙ (p b).derived ≅ (p (a ≫ b)).derived)
    {R S R' S' : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (a' : R' ⟶ S')
    (α : R ⟶ R') (β : S ⟶ S') (h : a ≫ β = α ≫ a') :
    (p a).derived ⋙ (p β).derived ≅ (p α).derived ⋙ (p a').derived :=
  δ a β ≪≫ eqToIso (congrArg (fun f ↦ (p f).derived) h) ≪≫ (δ α a').symm

/-- The complete normalized, coherent family of successive extensions. The fields
spell out the tensor formulas, their descent through the universal counits, the
restriction identifications, the scalar-extension units, and coefficient naturality.
Source: Stacks 0D6D, 0G7E, 06YY and 07A6
(auxiliary; not a blueprint node). -/
structure Normalization
    (p : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S), Presentation a) where
  /-- The actual ordinary scalar-extension comparison, natural in the module. -/
  ordinary : ∀ {R S T : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (b : S ⟶ T),
    (p a).ordinary ⋙ (p b).ordinary ≅ (p (a ≫ b)).ordinary
  /-- The forward tensor formula, in the scalar-first convention. -/
  ordinary_hom : ∀ {R S T : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (b : S ⟶ T)
    (M : Modules R) (U : Cᵒᵖ) (x : M.val.obj U) (s : S.obj.obj U) (t : T.obj.obj U),
    ((ordinary a b).hom.app M).val.app U
      (sectionTensor (p b) ((p a).ordinary.obj M) U t (sectionTensor (p a) M U s x)) =
      sectionTensor (p (a ≫ b)) M U ((b.hom.app U).hom s * t) x
  /-- The inverse tensor formula. -/
  ordinary_inv : ∀ {R S T : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (b : S ⟶ T)
    (M : Modules R) (U : Cᵒᵖ) (x : M.val.obj U) (t : T.obj.obj U),
    ((ordinary a b).inv.app M).val.app U (sectionTensor (p (a ≫ b)) M U t x) =
      sectionTensor (p b) ((p a).ordinary.obj M) U t (sectionTensor (p a) M U 1 x)
  /-- The derived comparison is a natural isomorphism, not just objectwise existence. -/
  derived : ∀ {R S T : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (b : S ⟶ T),
    (p a).derived ⋙ (p b).derived ≅ (p (a ≫ b)).derived
  /-- Canonical computation is invertible on each flat-term K-flat representative. -/
  computed : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S)
    (P : CochainComplex (Modules R) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P →
    (∀ n : ℤ, IsFlatOnSite (R := R) (P.X n)) →
    IsIso ((p a).counit.app ((HomotopyCategory.quotient _ _).obj P))
  /-- The second computation is also invertible on the extended representative. -/
  intermediate_computed : ∀ {R S T : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (b : S ⟶ T)
    (P : CochainComplex (Modules R) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P →
    (∀ n : ℤ, IsFlatOnSite (R := R) (P.X n)) →
    IsIso ((p b).counit.app
      (((p a).ordinary.mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient _ _).obj P)))
  /-- The derived comparison is represented by the displayed termwise tensor comparison. -/
  representative : ∀ {R S T : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (b : S ⟶ T)
    (P : CochainComplex (Modules R) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P →
    (∀ n : ℤ, IsFlatOnSite (R := R) (P.X n)) →
    (derived a b).hom.app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj P)) ≫
      (p (a ≫ b)).counit.app ((HomotopyCategory.quotient _ _).obj P) =
    (p b).derived.map ((p a).counit.app ((HomotopyCategory.quotient _ _).obj P)) ≫
      (p b).counit.app (((p a).ordinary.mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient _ _).obj P)) ≫
      DerivedCategory.Qh.map
        ((Functor.mapHomotopyCategoryCompIso (ordinary a b) (ComplexShape.up ℤ)).hom.app
          ((HomotopyCategory.quotient _ _).obj P))
  /-- Ordinary extension/restriction adjunctions. -/
  ordinaryAdjunction : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S),
    (p a).ordinary ⊣ restriction a
  /-- The units are the specified scalar-extension units. -/
  ordinary_unit : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (M : Modules R)
    (U : Cᵒᵖ) (x : M.val.obj U),
    ((ordinaryAdjunction a).unit.app M).val.app U x = sectionTensor (p a) M U 1 x
  /-- Termwise restriction on unbounded derived categories. -/
  right : ∀ {R S : Sheaf J CommRingCat.{r}} (_a : R ⟶ S),
    DerivedCategory (Modules S) ⥤ DerivedCategory (Modules R)
  /-- Its canonical localization factorization. -/
  right_factors : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S),
    DerivedCategory.Qh ⋙ right a ≅
      (restriction a).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh
  /-- The normalized derived coefficient adjunction. -/
  adjunction : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S), (p a).derived ⊣ right a
  /-- Normalization of its unit through the universal derived computation. -/
  adjunction_normalization : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S)
    (P : CochainComplex (Modules R) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P →
    (∀ n : ℤ, IsFlatOnSite (R := R) (P.X n)) →
    (adjunction a).unit.app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj P)) ≫
      (right a).map ((p a).counit.app ((HomotopyCategory.quotient _ _).obj P)) ≫
      (right_factors a).hom.app
        (((p a).ordinary.mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.quotient _ _).obj P)) =
    DerivedCategory.Qh.map
      (((ordinaryAdjunction a).mapHomotopyCategory (ComplexShape.up ℤ)).unit.app
        ((HomotopyCategory.quotient _ _).obj P))
  /-- Ordinary composite restriction leaves every underlying section unchanged. -/
  restrictionComp : ∀ {R S T : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (b : S ⟶ T),
    restriction b ⋙ restriction a ≅ restriction (a ≫ b)
  /-- It is the identity on underlying sheaves, not an arbitrary comparison. -/
  restrictionComp_sections : ∀ {R S T : Sheaf J CommRingCat.{r}}
    (a : R ⟶ S) (b : S ⟶ T) (N : Modules T) (U : Cᵒᵖ) (x : N.val.obj U),
    ((restrictionComp a b).hom.app N).val.app U x = x
  /-- The induced comparison between derived restrictions. -/
  rightComp : ∀ {R S T : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (b : S ⟶ T),
    right b ⋙ right a ≅ right (a ≫ b)
  /-- The comparison is the localization of the ordinary identity on sections. -/
  rightComp_normalization : ∀ {R S T : Sheaf J CommRingCat.{r}}
    (a : R ⟶ S) (b : S ⟶ T)
    (H : HomotopyCategory (Modules T) (ComplexShape.up ℤ)),
    (rightComp a b).hom.app (DerivedCategory.Qh.obj H) ≫
      (right_factors (a ≫ b)).hom.app H =
    (right a).map ((right_factors b).hom.app H) ≫
      (right_factors a).hom.app
        (((restriction b).mapHomotopyCategory (ComplexShape.up ℤ)).obj H) ≫
      DerivedCategory.Qh.map
        ((Functor.mapHomotopyCategoryCompIso (restrictionComp a b)
          (ComplexShape.up ℤ)).hom.app H)
  /-- The composite scalar-extension unit is the unit for the composite ring map. -/
  unit_comp : ∀ {R S T : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (b : S ⟶ T)
    (X : DerivedCategory (Modules R)),
    (adjunction a).unit.app X ≫
      (right a).map ((adjunction b).unit.app ((p a).derived.obj X)) ≫
      (rightComp a b).hom.app ((p b).derived.obj ((p a).derived.obj X)) ≫
      (right (a ≫ b)).map ((derived a b).hom.app X) = (adjunction (a ≫ b)).unit.app X
  /-- All parenthesizations of three successive extensions agree. This gives agreement
  for every finite iteration by the usual induction on parenthesizations. -/
  associative : ∀ {R S T V : Sheaf J CommRingCat.{r}}
    (a : R ⟶ S) (b : S ⟶ T) (c : T ⟶ V) (X : DerivedCategory (Modules R)),
    (p c).derived.map ((derived a b).hom.app X) ≫ (derived (a ≫ b) c).hom.app X =
      (derived b c).hom.app ((p a).derived.obj X) ≫ (derived a (b ≫ c)).hom.app X ≫
        eqToHom (congrArg (fun f ↦ (p f).derived.obj X) (Category.assoc a b c).symm)
  /-- Naturality in a commuting diagram of composable coefficient maps: pasting its
  two squares gives the outer square, compatibly with the composition comparison.
  The outer equality merely records the composite of the two commuting squares. -/
  coefficient_naturality : ∀ {R S T R' S' T' : Sheaf J CommRingCat.{r}}
    (a : R ⟶ S) (b : S ⟶ T) (a' : R' ⟶ S') (b' : S' ⟶ T')
    (α : R ⟶ R') (β : S ⟶ S') (γ : T ⟶ T')
    (ha : a ≫ β = α ≫ a') (hb : b ≫ γ = β ≫ b')
    (hab : (a ≫ b) ≫ γ = α ≫ (a' ≫ b')) (X : DerivedCategory (Modules R)),
    (p γ).derived.map ((derived a b).hom.app X) ≫
      (squareComparison p derived (a ≫ b) (a' ≫ b') α γ hab).hom.app X =
    (squareComparison p derived b b' β γ hb).hom.app ((p a).derived.obj X) ≫
      (p b').derived.map ((squareComparison p derived a a' α β ha).hom.app X) ≫
      (derived a' b').hom.app ((p α).derived.obj X)

end SheafOfModules.SuccessiveDerivedQuotient
