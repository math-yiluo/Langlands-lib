/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
public import WeilConjectures.Algebra.Homology.System.SystemScalarCoherence
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactScalarCoherence
public import WeilConjectures.SixFunctors.Etale.Derived.CoefficientChange

/-! # Ordinary étale compact-support system presentations

Source: Zheng, Construction 4.1, Constructions 5.14--5.15; Stacks Project, Tag 0GL6
(blueprint: def-pur-etale-system-projection-data).

All module categories below are the recorded modules on the vertical sequence site.
Ordinary direct image is specified on that site, including its horizontal restrictions.
The inverse and open functors are specified by adjunctions to that direct image.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures.SemilinearSections
namespace AlgebraicGeometry.Etale.SystemProjection

/-- Constant coefficients at each positive level; n represents n+1.
Source: Zheng Construction 4.1 (blueprint: def-pur-etale-system-projection-data). -/
abbrev coefficients (W : Scheme.{u}) (B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}) (n : ℕ) :=
  (constantSheaf W.smallEtaleTopology CommRingCat.{u + 1}).obj (B.obj (op n))

/-- The given, unrestricted adjacent coefficient maps.
Source: Zheng Construction 4.1 (blueprint: def-pur-etale-system-projection-data). -/
abbrev transitions (W : Scheme.{u}) (B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}) (n : ℕ) :=
  (constantSheaf W.smallEtaleTopology CommRingCat.{u + 1}).map
    (B.map (homOfLE (Nat.le_succ n)).op)

/-- Strict systems are the existing module sheaves on the ringed sequence site.
Source: Zheng Construction 4.1 (blueprint: def-pur-etale-system-projection-data). -/
abbrev Modules (W : Scheme.{u}) (B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}) :=
  Systems.{u + 1, u, u + 1} W.smallEtaleTopology (coefficients W B) (transitions W B)

/-- Their ordinary unbounded derived category, without a cartesianness condition.
Source: Stacks Tag 05RU (blueprint: def-pur-etale-system-projection-data). -/
abbrev Derived (W : Scheme.{u}) (B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}) :=
  DS.{u + 1, u, u + 1} W.smallEtaleTopology (coefficients W B) (transitions W B)

/-- The actual ring sheaf on the vertical sequence site.
Source: Zheng Construction 4.1 (blueprint: def-pur-etale-system-projection-data). -/
abbrev rings (W : Scheme.{u}) (B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}) :=
  systemRing.{u + 1, u, u + 1} W.smallEtaleTopology (coefficients W B) (transitions W B)

/-- The coefficient-system map, with its compatibility supplied by naturality.
Source: Zheng Construction 4.1 (blueprint: def-pur-etale-system-projection-data). -/
def ringMap (W : Scheme.{u}) {B C : ℕᵒᵖ ⥤ CommRingCat.{u + 1}} (a : B ⟶ C) :
    rings W B ⟶ rings W C :=
  systemMap.{u + 1, u, u + 1} W.smallEtaleTopology (coefficients W B) (transitions W B)
    (coefficients W C) (transitions W C)
    (fun n ↦ (constantSheaf W.smallEtaleTopology CommRingCat.{u + 1}).map (a.app (op n)))
    (fun n ↦ by
      rw [← Functor.map_comp, ← Functor.map_comp]
      exact congrArg
        (fun h ↦ (constantSheaf W.smallEtaleTopology CommRingCat.{u + 1}).map h)
        (a.naturality (homOfLE (Nat.le_succ n)).op).symm)

/-- Exact scalar restriction on the actual ordinary derived systems.
Source: Stacks Tag 03CZ (blueprint: def-pur-etale-system-projection-data). -/
abbrev restriction (W : Scheme.{u}) {B C : ℕᵒᵖ ⥤ CommRingCat.{u + 1}} (a : B ⟶ C) :=
  resD.{u + 1, u, u + 1} (ringMap W a)

/-- Base change of an étale object, retaining the coefficient index.
Source: Stacks Tag 03Q2 (blueprint: def-pur-etale-system-projection-data). -/
abbrev siteMap {X Y : Scheme.{u}} (g : X ⟶ Y) :=
  (𝟭 ℕ).prod (MorphismProperty.Over.pullback @Etale ⊤ g)

/-- A normalized structural ring map on the actual sequence sites. Its normalization
on constant generators determines the map uniquely, by sheafification.
Source: Zheng Construction 4.1; Stacks 00W1, 03D7
(blueprint: def-pur-etale-system-projection-data). -/
structure DirectImage {X Y : Scheme.{u}} (g : X ⟶ Y)
    (B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}) where
  [continuous : (siteMap g).IsContinuous (WeilConjectures.coefficientSequenceTopology
    Y.smallEtaleTopology) (WeilConjectures.coefficientSequenceTopology X.smallEtaleTopology)]
  structural : rings Y B ⟶ ((siteMap g).sheafPushforwardContinuous CommRingCat.{u + 1}
    (WeilConjectures.coefficientSequenceTopology Y.smallEtaleTopology)
    (WeilConjectures.coefficientSequenceTopology X.smallEtaleTopology)).obj (rings X B)
  constants : ∀ (n : ℕ) (U : Y.Etaleᵒᵖ) (b : B.obj (op n)),
    (structural.hom.app (op (n, U.unop)))
      ((toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj
        (B.obj (op n)))).app U b) =
      (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj
        (B.obj (op n)))).app
          ((MorphismProperty.Over.pullback @Etale ⊤ g).op.obj U) b

/-- The direct image is the actual module-sheaf pushforward along the structural map;
thus its maps include all the strict-system transition maps.
Source: Stacks Tag 03D7 (blueprint: def-pur-etale-system-projection-data). -/
def DirectImage.push {X Y : Scheme.{u}} {g : X ⟶ Y}
    {B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}} (d : DirectImage g B) : Modules X B ⥤ Modules Y B :=
  letI := d.continuous
  SheafOfModules.pushforward (F := siteMap g)
    ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map d.structural)

/-- Ordinary image and exact inverse image with their actual adjunction. The inverse
is determined up to its unique unit-compatible isomorphism by the fixed pushforward.
Source: Zheng Construction 4.1; Stacks Tag 03D2
(blueprint: def-pur-etale-system-projection-data). -/
structure Image {X Y : Scheme.{u}} (g : X ⟶ Y)
    (B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}) extends DirectImage g B where
  inverse : Modules Y B ⥤ Modules X B
  adjunction : inverse ⊣ toDirectImage.push
  [inverseAdditive : inverse.Additive]
  [inverseLimits : PreservesFiniteLimits inverse]
  [inverseColimits : PreservesFiniteColimits inverse]
  [pushAdditive : toDirectImage.push.Additive]
  [kinjectives : Abelian.HasKInjectiveResolutions (Modules X B)]

/-- The normalized ordinary-derived geometric adjunction.
Source: Stacks Tag 07A4 (blueprint: def-pur-etale-system-projection-data). -/
abbrev Image.derivedAdjunction {X Y : Scheme.{u}} {g : X ⟶ Y}
    {B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}} (d : Image g B) :=
  letI := d.inverseAdditive
  letI := d.inverseLimits
  letI := d.inverseColimits
  letI := d.pushAdditive
  letI := d.kinjectives
  d.adjunction.mapDerivedCategoryRightDerivedAdjunction

/-- Exact extension by zero, characterized as the left adjoint of the actual open
inverse image. All data are ordinary functors before termwise localization.
Source: Zheng Construction 5.14; Stacks Tag 03S2
(blueprint: def-pur-etale-system-projection-data). -/
structure OpenImage {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}) extends Image j B where
  [targetKinjectives : Abelian.HasKInjectiveResolutions (Modules Z B)]
  extension : Modules X B ⥤ Modules Z B
  openAdjunction : extension ⊣ inverse
  [extensionAdditive : extension.Additive]
  [extensionLimits : PreservesFiniteLimits extension]
  [extensionColimits : PreservesFiniteColimits extension]

/-- The actual proper/open presentation for a fixed compactification.
Source: Zheng Constructions 5.14--5.15
(blueprint: def-pur-etale-system-projection-data). -/
structure Support {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}) where
  proper : Image c.g B
  openImage : OpenImage c.i B

/-- Ordinary unbounded compact support: exact open extension followed by the total
right derived proper direct image, with no bound on the input.
Source: Zheng Construction 5.15 (blueprint: def-pur-etale-system-projection-data). -/
def Support.F {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    {B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}} (s : Support c B) : Derived X B ⥤ Derived Y B :=
  letI := s.openImage.extensionAdditive
  letI := s.openImage.extensionLimits
  letI := s.openImage.extensionColimits
  letI := s.proper.pushAdditive
  letI := s.proper.kinjectives
  s.openImage.extension.mapDerivedCategory ⋙ s.proper.toDirectImage.push.rightDerivedFunctor

/-- The canonical inverse-image functor on ordinary unbounded systems.
Source: Stacks Tag 07A4 (blueprint: def-pur-etale-system-projection-data). -/
abbrev Image.P {X Y : Scheme.{u}} {g : X ⟶ Y}
    {B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}} (d : Image g B) :=
  letI := d.inverseAdditive
  letI := d.inverseLimits
  letI := d.inverseColimits
  d.inverse.mapDerivedCategory

/-- The total right derived image computed on the system category itself.
Source: Stacks Tag 07A4 (blueprint: def-pur-etale-system-projection-data). -/
abbrev Image.R {X Y : Scheme.{u}} {g : X ⟶ Y}
    {B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}} (d : Image g B) :=
  letI := d.pushAdditive
  letI := d.kinjectives
  d.toDirectImage.push.rightDerivedFunctor

/-- Exact open extension localized termwise.
Source: Stacks Tag 03S2 (blueprint: def-pur-etale-system-projection-data). -/
abbrev OpenImage.J {X Z : Scheme.{u}} {j : X ⟶ Z} [IsOpenImmersion j]
    {B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}} (d : OpenImage j B) :=
  letI := d.extensionAdditive
  letI := d.extensionLimits
  letI := d.extensionColimits
  d.extension.mapDerivedCategory

/-- The exact derived open adjunction with its ordinary unit normalization.
Source: Stacks Tag 03S2 (blueprint: def-pur-etale-system-projection-data). -/
abbrev OpenImage.derivedAdjunction {X Z : Scheme.{u}} {j : X ⟶ Z} [IsOpenImmersion j]
    {B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}} (d : OpenImage j B) :=
  letI := d.extensionAdditive
  letI := d.extensionLimits
  letI := d.extensionColimits
  letI := d.inverseAdditive
  letI := d.inverseLimits
  letI := d.inverseColimits
  letI := d.targetKinjectives
  (d.openAdjunction.mapDerivedCategoryRightDerivedAdjunction).ofNatIsoRight
    d.inverse.rightDerivedFunctorIsoMapDerivedCategory

/-- The ordinary restriction/direct-image identification is identity on all sections.
The inverse-image comparison is its mate; the derived image comparison is the mate
of its exact localization. This specifies the normalization before any evaluation.
Source: Stacks Tag 0GL6 and Zheng Lemma 5.16
(blueprint: def-pur-etale-system-projection-data). -/
structure RestrictionImage {X Y : Scheme.{u}} {g : X ⟶ Y}
    {B C : ℕᵒᵖ ⥤ CommRingCat.{u + 1}} (a : B ⟶ C)
    (d : Image g B) (e : Image g C) where
  ordinary : res (ringMap X a) ⋙ d.toDirectImage.push ≅
    e.toDirectImage.push ⋙ res (ringMap Y a)
  sections : ∀ (M : Modules X C) (n : ℕ) (U : Y.Etaleᵒᵖ)
    (x : (e.toDirectImage.push.obj M).val.obj (op (n, U.unop))),
    HEq (((ordinary.hom.app M).val.app (op (n, U.unop))) x) x
  inverseImage : res (ringMap Y a) ⋙ d.inverse ≅ e.inverse ⋙ res (ringMap X a)
  inverseImage_mate : inverseImage.hom =
    ((mateEquiv e.adjunction d.adjunction).symm
      (TwoSquare.mk _ _ _ _ ordinary.inv))
  derivedInverse : restriction Y a ⋙ d.P ≅ e.P ⋙ restriction X a
  derivedInverse_termwise : derivedInverse =
    (letI := d.inverseAdditive
     letI := d.inverseLimits
     letI := d.inverseColimits
     letI := e.inverseAdditive
     letI := e.inverseLimits
     letI := e.inverseColimits
     Functor.mapDerivedCategorySquareIso inverseImage)
  derived : e.R ⋙ restriction Y a ≅ restriction X a ⋙ d.R
  derived_mate : derived.hom =
    (mateEquiv e.derivedAdjunction d.derivedAdjunction
      (TwoSquare.mk _ _ _ _ derivedInverse.hom))

/-- Open restriction is the mate of the fixed inverse-image comparison.
Source: Stacks 03S2 and 0GL6
(blueprint: def-pur-etale-system-projection-data). -/
structure RestrictionOpen {X Z : Scheme.{u}} {j : X ⟶ Z} [IsOpenImmersion j]
    {B C : ℕᵒᵖ ⥤ CommRingCat.{u + 1}} (a : B ⟶ C)
    (d : OpenImage j B) (e : OpenImage j C) where
  image : RestrictionImage a d.toImage e.toImage
  ordinary : res (ringMap X a) ⋙ d.extension ≅ e.extension ⋙ res (ringMap Z a)
  mate : ordinary.hom = ((mateEquiv e.openAdjunction d.openAdjunction).symm
    (TwoSquare.mk _ _ _ _ image.inverseImage.inv))

/-- Exact localization of the canonical open restriction identification.
Source: Stacks 03S2 and 0GL6
(blueprint: def-pur-etale-system-projection-data). -/
def RestrictionOpen.derived {X Z : Scheme.{u}} {j : X ⟶ Z} [IsOpenImmersion j]
    {B C : ℕᵒᵖ ⥤ CommRingCat.{u + 1}} {a : B ⟶ C}
    {d : OpenImage j B} {e : OpenImage j C} (r : RestrictionOpen a d e) :
    restriction X a ⋙ d.J ≅ e.J ⋙ restriction Z a :=
  letI := d.extensionAdditive
  letI := d.extensionLimits
  letI := d.extensionColimits
  letI := e.extensionAdditive
  letI := e.extensionLimits
  letI := e.extensionColimits
  Functor.mapDerivedCategorySquareIso r.ordinary

/-- Restriction comparisons for the fixed proper/open factorization.
Source: Stacks 0GL6 (blueprint: def-pur-etale-system-projection-data). -/
structure RestrictionSupport {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    {B C : ℕᵒᵖ ⥤ CommRingCat.{u + 1}} (a : B ⟶ C)
    (s : Support c B) (t : Support c C) where
  proper : RestrictionImage a s.proper t.proper
  openImage : RestrictionOpen a s.openImage t.openImage

/-- The canonical restriction comparison is pasted before evaluation.
Source: Stacks 0GL6 (blueprint: def-pur-etale-system-projection-data). -/
def RestrictionSupport.iso {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    {B C : ℕᵒᵖ ⥤ CommRingCat.{u + 1}} {a : B ⟶ C}
    {s : Support c B} {t : Support c C} (r : RestrictionSupport a s t) :
    t.F ⋙ restriction Y a ≅ restriction X a ⋙ s.F :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft t.openImage.J r.proper.derived ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight r.openImage.derived.symm s.proper.R ≪≫
    Functor.associator _ _ _

/-- A scalar model uses the actual cochain change of rings, with the insertion unit
and its derived transpose fixed by the recorded universal localization comparison.
Source: Stacks 03D7, 06YY (blueprint: def-pur-etale-system-projection-data). -/
abbrev Scalar (W : Scheme.{u}) {B C : ℕᵒᵖ ⥤ CommRingCat.{u + 1}} (a : B ⟶ C) :=
  SheafOfModules.SystemScalarModel.{u + 1, u, u + 1} (ringMap W a)

/-- The coefficient projection is the unique scalar adjunct of the inverse
restriction comparison. This is an actual natural transformation on derived systems.
Source: Stacks 0GL6 (blueprint: def-pur-etale-system-projection-data). -/
def projection {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    {B C : ℕᵒᵖ ⥤ CommRingCat.{u + 1}} {a : B ⟶ C}
    {s : Support c B} {t : Support c C} (r : RestrictionSupport a s t)
    (x : Scalar X a) (y : Scalar Y a) : s.F ⋙ y.model.T ⟶ x.model.T ⋙ t.F :=
  ((mateEquiv x.adjunction y.adjunction).symm
    (TwoSquare.mk _ _ _ _ r.iso.inv))

/-- Restriction from the constant ring sheaf to constant scalars, leaving sections
unchanged. Source: Stacks 03CV
(blueprint: def-pur-etale-system-projection-data). -/
def constantModule (W : Scheme.{u}) (A : CommRingCat.{u + 1}) :
    WeilConjectures.SemilinearSections.Mod.{u + 1, u, u + 1} W.smallEtaleTopology
      ((constantSheaf W.smallEtaleTopology CommRingCat.{u + 1}).obj A) ⥤
        Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A) where
  obj N :=
    let P : PresheafOfModules.{u + 1}
        ((Functor.const W.Etaleᵒᵖ).obj (RingCat.of A)) :=
      (PresheafOfModules.restrictScalars
        (Functor.whiskerRight (toSheafify W.smallEtaleTopology
          ((Functor.const W.Etaleᵒᵖ).obj A))
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}))).obj N.val
    { obj :=
        { obj := fun U ↦ P.obj U
          map := fun h ↦ P.map h
          map_id := fun _ ↦ by ext x; simp; rfl
          map_comp := fun _ _ ↦ by ext x; simp; rfl }
      property := by
        apply Presheaf.isSheaf_of_isSheaf_comp W.smallEtaleTopology _
          (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})
        exact N.isSheaf }
  map h := ObjectProperty.homMk
    { app := fun U ↦ (ModuleCat.restrictScalars
        (((toSheafify W.smallEtaleTopology
          ((Functor.const W.Etaleᵒᵖ).obj A)).app U).hom)).map (h.val.app U)
      naturality := fun {_ _} g ↦ by
        ext x
        exact PresheafOfModules.naturality_apply h.val g x }
  map_id _ := by ext U x; rfl
  map_comp _ _ := by ext U x; rfl

/-- Evaluation at a coefficient level followed by the actual restriction to constant
scalars. Source: Zheng 4.1 (blueprint: def-pur-etale-system-projection-data). -/
def level (W : Scheme.{u}) (B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}) (n : ℕ) :
    Modules W B ⥤ Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} (B.obj (op n))) :=
  evaluation W.smallEtaleTopology (coefficients W B) (transitions W B) n ⋙
    constantModule W (B.obj (op n))

/-- Exactness data for the specified evaluation, not a choice of evaluation functor.
Source: Zheng 4.1 (blueprint: def-pur-etale-system-projection-data). -/
structure Evaluation (W : Scheme.{u}) (B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}) (n : ℕ) where
  [additive : (level W B n).Additive]
  [limits : PreservesFiniteLimits (level W B n)]
  [colimits : PreservesFiniteColimits (level W B n)]

/-- Exact ordinary evaluation localized to the whole unbounded derived category.
Source: Stacks 05RU (blueprint: def-pur-etale-system-projection-data). -/
abbrev Evaluation.E {W : Scheme.{u}} {B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}} {n : ℕ}
    (e : Evaluation W B n) :=
  letI := e.additive
  letI := e.limits
  letI := e.colimits
  (level W B n).mapDerivedCategory

/-- Normalized evaluation of geometric direct image. The ordinary comparison is
identity on sections, inverse image is its mate, and derived image is the mate after
exact localization. Source: Zheng 4.1; Stacks 03D2, 07A4
(blueprint: def-pur-etale-system-projection-data). -/
structure ImageEvaluation {X Y : Scheme.{u}} {g : X ⟶ Y}
    {B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}} (d : Image g B) (n : ℕ)
    (ex : Evaluation X B n) (ey : Evaluation Y B n)
    (L : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} (B.obj (op n))) ⥤
      Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (B.obj (op n))))
    [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (adj : L ⊣ lowerStar (ModuleCat.{u + 1} (B.obj (op n))) g) where
  ordinary : d.toDirectImage.push ⋙ level Y B n ≅
    level X B n ⋙ lowerStar (ModuleCat.{u + 1} (B.obj (op n))) g
  sections : ∀ (M : Modules X B) (U : Y.Etaleᵒᵖ)
    (x : ((level Y B n).obj (d.toDirectImage.push.obj M)).obj.obj U),
    HEq (((ordinary.hom.app M).hom.app U) x) x
  inverse : level Y B n ⋙ L ≅ d.inverse ⋙ level X B n
  inverse_mate : inverse.hom = ((mateEquiv d.adjunction adj).symm
    (TwoSquare.mk _ _ _ _ ordinary.hom))
  derivedInverse : ey.E ⋙ L.mapDerivedCategory ≅ d.P ⋙ ex.E
  derivedInverse_termwise : derivedInverse =
    (letI := ex.additive
     letI := ex.limits
     letI := ex.colimits
     letI := ey.additive
     letI := ey.limits
     letI := ey.colimits
     letI := d.inverseAdditive
     letI := d.inverseLimits
     letI := d.inverseColimits
     Functor.mapDerivedCategorySquareIso inverse)
  derived : d.R ⋙ ey.E ≅ ex.E ⋙
    (lowerStar (ModuleCat.{u + 1} (B.obj (op n))) g).rightDerivedFunctor
  derived_mate : derived.hom = (mateEquiv d.derivedAdjunction
    adj.mapDerivedCategoryRightDerivedAdjunction
      (TwoSquare.mk _ _ _ _ derivedInverse.hom))

/-- Open restriction preserves finite colimits because it is left adjoint to
ordinary direct image. Source: Stacks 03S2
(blueprint: def-pur-etale-system-projection-data). -/
instance openRestrictionColimits {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (A : CommRingCat.{u + 1}) :
    PreservesFiniteColimits (openImmersionRestriction (ModuleCat.{u + 1} A) j) :=
  letI := (openImmersionRestrictionLowerStarAdjunction (ModuleCat.{u + 1} A) j).isLeftAdjoint
  inferInstance

/-- Normalized open evaluation: the comparison is fixed by the ordinary open
adjunction, then localized exactly. Source: Zheng 4.1, 5.14
(blueprint: def-pur-etale-system-projection-data). -/
structure OpenEvaluation {X Z : Scheme.{u}} {j : X ⟶ Z} [IsOpenImmersion j]
    {B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}} (d : OpenImage j B) (n : ℕ)
    (ex : Evaluation X B n) (ez : Evaluation Z B n) where
  image :
    letI := (openImmersionRestrictionLowerStarAdjunction
      (ModuleCat.{u + 1} (B.obj (op n))) j).isLeftAdjoint
    ImageEvaluation d.toImage n ex ez
    (openImmersionRestriction (ModuleCat.{u + 1} (B.obj (op n))) j)
    (openImmersionRestrictionLowerStarAdjunction (ModuleCat.{u + 1} (B.obj (op n))) j)
  ordinary : d.extension ⋙ level Z B n ≅
    level X B n ⋙ openImmersionLowerShriek (ModuleCat.{u + 1} (B.obj (op n))) j
  mate : ordinary.inv = ((mateEquiv d.openAdjunction
    (openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} (B.obj (op n))) j)).symm
      (TwoSquare.mk _ _ _ _ image.inverse.inv))

/-- Exact localization of normalized open evaluation.
Source: Zheng 4.1, 5.14 (blueprint: def-pur-etale-system-projection-data). -/
def OpenEvaluation.derived {X Z : Scheme.{u}} {j : X ⟶ Z} [IsOpenImmersion j]
    {B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}} {d : OpenImage j B} {n : ℕ}
    {ex : Evaluation X B n} {ez : Evaluation Z B n} (e : OpenEvaluation d n ex ez) :
    d.J ⋙ ez.E ≅ ex.E ⋙
      (openImmersionLowerShriek (ModuleCat.{u + 1} (B.obj (op n))) j).mapDerivedCategory :=
  letI := ex.additive
  letI := ex.limits
  letI := ex.colimits
  letI := ez.additive
  letI := ez.limits
  letI := ez.colimits
  letI := d.extensionAdditive
  letI := d.extensionLimits
  letI := d.extensionColimits
  Functor.mapDerivedCategorySquareIso e.ordinary

/-- Evaluation data for each factor of compact support.
Source: Zheng 4.1, 5.14--5.15 (blueprint: def-pur-etale-system-projection-data). -/
structure SupportEvaluation {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    {B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}} (s : Support c B) (n : ℕ)
    (ex : Evaluation X B n) (ez : Evaluation c.Z B n) (ey : Evaluation Y B n) where
  proper : ImageEvaluation s.proper n ez ey
    (upperStar (ModuleCat.{u + 1} (B.obj (op n))) c.g)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} (B.obj (op n))) c.g)
  openImage : OpenEvaluation s.openImage n ex ez

/-- The proper/open evaluation comparison obtained by pasting the normalized factors.
Source: Zheng 4.1, 5.15 (blueprint: def-pur-etale-system-projection-data). -/
def SupportEvaluation.iso {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    {B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}} {s : Support c B} {n : ℕ}
    {ex : Evaluation X B n} {ez : Evaluation c.Z B n} {ey : Evaluation Y B n}
    (e : SupportEvaluation s n ex ez ey) :
    s.F ⋙ ey.E ≅ ex.E ⋙
      rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} (B.obj (op n))) c :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft s.openImage.J e.proper.derived ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight e.openImage.derived
      (lowerStar (ModuleCat.{u + 1} (B.obj (op n))) c.g).rightDerivedFunctor ≪≫
    Functor.associator _ _ _

/-- Evaluation of the scalar adjunction: restriction is identity on sections, and the
scalar comparison is its adjoint mate, rather than a freely chosen isomorphism.
Source: Stacks 03D7, 06YY; Zheng 4.1
(blueprint: def-pur-etale-system-projection-data). -/
structure ScalarEvaluation (W : Scheme.{u}) {B C : ℕᵒᵖ ⥤ CommRingCat.{u + 1}}
    (a : B ⟶ C) (s : Scalar W a) (n : ℕ)
    (eb : Evaluation W B n) (ec : Evaluation W C n) where
  ordinary : res (ringMap W a) ⋙ level W B n ≅
    level W C n ⋙ Sheaf.restrictScalars W.smallEtaleTopology (a.app (op n)).hom
  sections : ∀ (M : Modules W C) (U : W.Etaleᵒᵖ)
    (x : ((level W B n).obj ((res (ringMap W a)).obj M)).obj.obj U),
    HEq (((ordinary.hom.app M).hom.app U) x) x
  restriction : restriction W a ⋙ eb.E ≅ ec.E ⋙
    Sheaf.derivedRestrictScalars W.smallEtaleTopology (a.app (op n)).hom
  restriction_termwise : restriction =
    (letI := eb.additive
     letI := eb.limits
     letI := eb.colimits
     letI := ec.additive
     letI := ec.limits
     letI := ec.colimits
     Functor.mapDerivedCategorySquareIso ordinary)
  iso : s.model.T ⋙ ec.E ≅ eb.E ⋙ scalarExtension (a.app (op n)).hom W
  mate : iso.inv = ((mateEquiv s.adjunction
    (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars W.smallEtaleTopology (a.app (op n)).hom))).symm
        (TwoSquare.mk _ _ _ _ restriction.hom))

/-- Finite coefficient sequences with unrestricted, possibly nonflat, transition maps.
The exponent may depend on the level; exponent zero includes the zero ring.
Source: Zheng 4.1; Stacks 0GL6
(blueprint: def-pur-etale-system-projection-data). -/
structure Coefficients (l : ℕ) where
  rings : ℕᵒᵖ ⥤ CommRingCat.{u + 1}
  finite : ∀ n : ℕ, Finite (rings.obj (op n))
  torsion : ∀ n : ℕ, ∃ m : ℕ, (l ^ m : rings.obj (op n)) = 0

/-- The actual coefficient ring-sheaf functor. Functor laws follow on each section
from the constant-sheaf functor laws and uniqueness of the ring-system map.
Source: Zheng 4.1 (blueprint: def-pur-etale-system-projection-data). -/
def coefficientFunctor (W : Scheme.{u}) :
    (ℕᵒᵖ ⥤ CommRingCat.{u + 1}) ⥤
      Sheaf (WeilConjectures.coefficientSequenceTopology W.smallEtaleTopology)
        CommRingCat.{u + 1} := by
  have hc : ∀ {B C : ℕᵒᵖ ⥤ CommRingCat.{u + 1}} (a : B ⟶ C)
      (U : (ℕ × W.Etale)ᵒᵖ),
      (ringMap W a).hom.app U =
        ((constantSheaf W.smallEtaleTopology CommRingCat.{u + 1}).map
          (a.app (op U.unop.1))).hom.app (op U.unop.2) := by
    intro B C a U
    exact (systemMap_existsUnique W.smallEtaleTopology
      (coefficients W B) (transitions W B) (coefficients W C) (transitions W C)
      (fun n ↦ (constantSheaf W.smallEtaleTopology CommRingCat.{u + 1}).map
        (a.app (op n))) (fun n ↦ by
          rw [← Functor.map_comp, ← Functor.map_comp]
          exact congrArg
            (fun h ↦ (constantSheaf W.smallEtaleTopology CommRingCat.{u + 1}).map h)
            (a.naturality (homOfLE (Nat.le_succ n)).op).symm)).exists.choose_spec
              U.unop.1 (op U.unop.2)
  refine { obj := rings W, map := fun a ↦ ringMap W a, map_id := ?_, map_comp := ?_ }
  · intro B
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    rw [hc]
    simp
    rfl
  · intro B C D a b
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    rw [hc]
    change _ = (ringMap W a).hom.app U ≫ (ringMap W b).hom.app U
    rw [hc, hc]
    simp

/-- Canonical balanced tensor associator, determined by normalized scalar adjunctions.
On representatives it multiplies the two coefficient factors.
Source: Stacks 03EK and 06YT (blueprint: def-pur-etale-system-projection-data). -/
def associator (W : Scheme.{u}) {B C D : ℕᵒᵖ ⥤ CommRingCat.{u + 1}}
    {a : B ⟶ C} {b : C ⟶ D} (x : Scalar W a) (y : Scalar W b)
    (z : Scalar W (a ≫ b)) : x.model.T ⋙ y.model.T ≅ z.model.T :=
  SheafOfModules.systemScalarModelDerivedComposition
    ((coefficientFunctor W).map_comp a b) x y z

/-- The canonical tensor unit comparison for an identity coefficient map.
Source: Stacks 03EK and 06YT (blueprint: def-pur-etale-system-projection-data). -/
def unit (W : Scheme.{u}) (B : ℕᵒᵖ ⥤ CommRingCat.{u + 1})
    (x : Scalar W (𝟙 B)) : x.model.T ≅ 𝟭 (Derived W B) :=
  SheafOfModules.systemScalarModelDerivedUnit ((coefficientFunctor W).map_id B) x

/-- Normalized ordinary étale system operations for a fixed compactification.
All categories, scalar models and evaluation functors are the actual constructions
above; the comparison fields are fixed by ordinary section maps and adjunction mates.
No projection invertibility or coherence law is assumed here.
Source: Zheng 4.1, 5.14--5.16; Stacks 0GL6
(blueprint: def-pur-etale-system-projection-data). -/
structure Theory {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) (l : ℕ) where
  support : ∀ B : Coefficients.{u} l, Support c B.rings
  evaluationX : ∀ (B : Coefficients.{u} l) (n : ℕ), Evaluation X B.rings n
  evaluationZ : ∀ (B : Coefficients.{u} l) (n : ℕ), Evaluation c.Z B.rings n
  evaluationY : ∀ (B : Coefficients.{u} l) (n : ℕ), Evaluation Y B.rings n
  supportEvaluation : ∀ (B : Coefficients.{u} l) (n : ℕ), SupportEvaluation (support B) n
    (evaluationX B n) (evaluationZ B n) (evaluationY B n)
  scalarX : ∀ {B C : Coefficients.{u} l} (a : B.rings ⟶ C.rings), Scalar X a
  scalarY : ∀ {B C : Coefficients.{u} l} (a : B.rings ⟶ C.rings), Scalar Y a
  scalarEvaluationX : ∀ {B C : Coefficients.{u} l} (a : B.rings ⟶ C.rings) (n : ℕ),
    ScalarEvaluation X a (scalarX a) n (evaluationX B n) (evaluationX C n)
  scalarEvaluationY : ∀ {B C : Coefficients.{u} l} (a : B.rings ⟶ C.rings) (n : ℕ),
    ScalarEvaluation Y a (scalarY a) n (evaluationY B n) (evaluationY C n)
  restriction : ∀ {B C : Coefficients.{u} l} (a : B.rings ⟶ C.rings),
    RestrictionSupport a (support B) (support C)

/-- The specified coefficient projection for the normalized ordinary system operations.
Source: Stacks 0GL6 (blueprint: def-pur-etale-system-projection-data). -/
abbrev Theory.q {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f} {l : ℕ}
    (t : Theory c l) {B C : Coefficients.{u} l} (a : B.rings ⟶ C.rings) :=
  projection (t.restriction a) (t.scalarX a) (t.scalarY a)

/-- The ordinary single-ring restriction comparison, pasted from the canonical
proper restriction mate and the exact open restriction identification.
Source: Stacks 0GL6 (blueprint: def-pur-etale-system-projection-data). -/
def singleRestriction {A B : CommRingCat.{u + 1}} (a : A ⟶ B)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c ⋙
        Sheaf.derivedRestrictScalars Y.smallEtaleTopology a.hom ⟶
      Sheaf.derivedRestrictScalars X.smallEtaleTopology a.hom ⋙
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c :=
  Functor.whiskerLeft
      (openImmersionLowerShriek (ModuleCat.{u + 1} B) c.i).mapDerivedCategory
      (scalarRestrictionDirectImageMap a.hom c.g) ≫
    Functor.whiskerRight (derivedRestrictScalarsCompOpenImmersionLowerShriekIso
      a.hom c.i).inv (lowerStar (ModuleCat.{u + 1} A) c.g).rightDerivedFunctor

/-- The single-ring composition word under the published balanced scalar associators.
Source: Stacks 0GL6 (blueprint: def-pur-etale-system-projection-data). -/
def singlePath {A B D : CommRingCat.{u + 1}} (a : A ⟶ B) (b : B ⟶ D)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⋙
        scalarExtension (a ≫ b).hom Y ⟶
      scalarExtension (a ≫ b).hom X ⋙
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} D) c :=
  Functor.whiskerLeft _ (ProEtale.pbcFixedScalarExtensionComp Y.smallEtaleTopology
      a.hom b.hom (a ≫ b).hom rfl).inv ≫
    Functor.whiskerRight (compactScalarMap a.hom c) (scalarExtension b.hom Y) ≫
    Functor.whiskerLeft (scalarExtension a.hom X) (compactScalarMap b.hom c) ≫
    Functor.whiskerRight (ProEtale.pbcFixedScalarExtensionComp X.smallEtaleTopology
      a.hom b.hom (a ≫ b).hom rfl).hom
        (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} D) c)

end AlgebraicGeometry.Etale.SystemProjection
