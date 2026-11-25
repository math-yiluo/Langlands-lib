/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.AlgebraicGeometry.Refinement.RefinementComparisonIsomorphism
public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalOriginCompactSupportComposition
import all WeilConjectures.AlgebraicGeometry.Canonical.CanonicalOriginCompactSupportComposition
public import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportExchangeTransport
import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportFiniteTorsion
import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportComparisons
import WeilConjectures.AlgebraicGeometry.FixedComparisonDirectImageMate
public import WeilConjectures.Compactification.RefinementCategory

/-! # Compact-support site coherence

Source: Stacks Project, Tags 0F7C, 0F7D and 0F7F; the agent-formulated normalized
site-coherence calculation in the DAG (blueprint: lem-pur-compact-support-site-coherence).

The diagram generators are the recorded refinement, composition and open-restriction
maps on both sites. A diagram may contain identity edges, composites, and whiskering
by compact support or inverse image, and insertion of compatible boundary isomorphisms.
Its two boundary maps are constructed independently;
commutativity is the theorem, never a field of a generator.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale

/-- Finiteness of the existing positive-level coefficient, without a new coefficient ring.
Source: def-pur-conventions, A = O_E/(varpi_E^n), n positive
(blueprint: lem-pur-compact-support-site-coherence). -/
instance compactSupportCoherenceCoefficientFinite (P : WeilConjectures.PurityFiniteSetting.{u}) :
    Finite P.Coefficient :=
  letI : Finite P.Ring :=
    Padic.finite_coefficientExtensionRing P.coefficients.l P.extension P.level P.level_pos
  Finite.of_equiv P.Ring Equiv.ulift.symm

/-- Four successive morphisms, retained as a named map.
Source: compactification comparison calculus
(blueprint: lem-pur-compact-support-site-coherence). -/
def coherenceFourMap {C : Type*} [Category* C] {a b c d e : C}
    (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e) : a ⟶ e :=
  f ≫ g ≫ h ≫ i

/-- Six successive morphisms, retained as a named map.
Source: compactification comparison calculus
(blueprint: lem-pur-compact-support-site-coherence). -/
def coherenceSixMap {C : Type*} [Category* C] {a b c d e f g : C}
    (i : a ⟶ b) (j : b ⟶ c) (k : c ⟶ d) (l : d ⟶ e) (m : e ⟶ f) (n : f ⟶ g) :
    a ⟶ g := i ≫ j ≫ k ≫ l ≫ m ≫ n

/-- Cancellation of the four factors against their inverses.
Source: the isomorphism laws (blueprint: lem-pur-compact-support-site-coherence). -/
theorem coherenceFourMap_hom_inv {C : Type*} [Category* C] {a b c d e : C}
    (i : a ≅ b) (j : b ≅ c) (k : c ≅ d) (l : d ≅ e) :
    coherenceFourMap i.hom j.hom k.hom l.hom ≫
        (l.inv ≫ k.inv ≫ j.inv ≫ i.inv) = 𝟙 a := by
  simp [coherenceFourMap, Category.assoc]

/-- Cancellation in the opposite order.
Source: the isomorphism laws (blueprint: lem-pur-compact-support-site-coherence). -/
theorem coherenceFourMap_inv_hom {C : Type*} [Category* C] {a b c d e : C}
    (i : a ≅ b) (j : b ≅ c) (k : c ≅ d) (l : d ≅ e) :
    (l.inv ≫ k.inv ≫ j.inv ≫ i.inv) ≫
        coherenceFourMap i.hom j.hom k.hom l.hom = 𝟙 e := by
  simp [coherenceFourMap, Category.assoc]

/-- The canonical fourfold composite, with a named hom field.
Source: compactification comparison calculus
(blueprint: lem-pur-compact-support-site-coherence). -/
def coherenceIsoFour {C : Type*} [Category* C] {a b c d e : C}
    (i : a ≅ b) (j : b ≅ c) (k : c ≅ d) (l : d ≅ e) : a ≅ e where
  hom := coherenceFourMap i.hom j.hom k.hom l.hom
  inv := l.inv ≫ k.inv ≫ j.inv ≫ i.inv
  hom_inv_id := coherenceFourMap_hom_inv i j k l
  inv_hom_id := coherenceFourMap_inv_hom i j k l

/-- The canonical factors of a composition square, with fixed endpoint types.
This structure records maps only; no field asserts any commutative square.
Source: the five-square compactification pasting calculation
(blueprint: lem-pur-compact-support-site-coherence). -/
structure CoherencePastingData {C D : Type*} [Category* C] [Category* D] (N : C ⥤ D)
    (a₀ a₁ a₂ a₃ a₄ : C) (b₀ b₁ b₂ v₀ v₁ v₂ p q : D)
    (bin : N.obj a₀ ⟶ v₀) (bout : N.obj a₄ ⟶ q) where
  e₀ : a₀ ≅ a₁
  e₁ : a₁ ≅ a₂
  e₂ : a₂ ≅ a₃
  e₃ : a₃ ≅ a₄
  s₀ : N.obj a₀ ⟶ b₀
  s₁ : N.obj a₁ ⟶ b₁
  s₂ : N.obj a₂ ⟶ b₂
  s₃ : N.obj a₃ ⟶ p
  r₀ : b₀ ⟶ v₀
  r₁ : v₀ ⟶ v₁
  r₂ : v₁ ⟶ b₁
  rd : b₁ ⟶ b₂
  rb : b₂ ⟶ v₂
  o : v₂ ⟶ p
  re : p ⟶ q
  n : b₀ ⟶ b₁

/-- The four recorded etale factors.
Source: canonical composition (blueprint: lem-pur-compact-support-site-coherence). -/
def CoherencePastingData.etaleIso {C D : Type*} [Category* C] [Category* D] {N : C ⥤ D}
    {a₀ a₁ a₂ a₃ a₄ : C} {b₀ b₁ b₂ v₀ v₁ v₂ p q : D}
    {bin : N.obj a₀ ⟶ v₀} {bout : N.obj a₄ ⟶ q}
    (t : CoherencePastingData N a₀ a₁ a₂ a₃ a₄ b₀ b₁ b₂ v₀ v₁ v₂ p q bin bout) : a₀ ≅ a₄ :=
  coherenceIsoFour t.e₀ t.e₁ t.e₂ t.e₃

/-- The six recorded pro-etale factors.
Source: canonical composition (blueprint: lem-pur-compact-support-site-coherence). -/
def CoherencePastingData.proMap {C D : Type*} [Category* C] [Category* D] {N : C ⥤ D}
    {a₀ a₁ a₂ a₃ a₄ : C} {b₀ b₁ b₂ v₀ v₁ v₂ p q : D}
    {bin : N.obj a₀ ⟶ v₀} {bout : N.obj a₄ ⟶ q}
    (t : CoherencePastingData N a₀ a₁ a₂ a₃ a₄ b₀ b₁ b₂ v₀ v₁ v₂ p q bin bout) : v₀ ⟶ q :=
  coherenceSixMap t.r₁ t.r₂ t.rd t.rb t.o t.re

/-- Evaluate a compositor with explicit object endpoints.
Source: evaluation of a natural isomorphism
(blueprint: lem-pur-compact-support-site-coherence). -/
def coherenceEvaluateCompositor {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E) (a : F ⋙ G ≅ H) (L : C) :
    G.obj (F.obj L) ≅ H.obj L := a.app L

/-- Evaluate a site-comparison square with explicit object endpoints.
Source: evaluation of a natural isomorphism
(blueprint: lem-pur-compact-support-site-coherence). -/
def coherenceEvaluateSquare {C D E B : Type*}
    [Category* C] [Category* D] [Category* E] [Category* B]
    (F : C ⥤ D) (N : D ⥤ B) (M : C ⥤ E) (G : E ⥤ B)
    (a : F ⋙ N ≅ M ⋙ G) (L : C) : N.obj (F.obj L) ≅ G.obj (M.obj L) := a.app L

/-- The evaluated square is natural, with both functor compositions expanded.
Source: naturality of a natural isomorphism
(blueprint: lem-pur-compact-support-site-coherence). -/
theorem coherenceEvaluateSquare_naturality {C D E B : Type*}
    [Category* C] [Category* D] [Category* E] [Category* B]
    (F : C ⥤ D) (N : D ⥤ B) (M : C ⥤ E) (G : E ⥤ B)
    (a : F ⋙ N ≅ M ⋙ G) {L K : C} (t : L ⟶ K) :
    N.map (F.map t) ≫ (coherenceEvaluateSquare F N M G a K).hom =
      (coherenceEvaluateSquare F N M G a L).hom ≫ G.map (M.map t) :=
  a.hom.naturality t

/-- Evaluate a three-factor compositor with explicit object endpoints.
Source: evaluation of a natural isomorphism
(blueprint: lem-pur-compact-support-site-coherence). -/
def coherenceEvaluateTriple {C D E B : Type*}
    [Category* C] [Category* D] [Category* E] [Category* B]
    (N : C ⥤ D) (F : D ⥤ E) (G : E ⥤ B) (H : D ⥤ B)
    (a : N ⋙ F ⋙ G ≅ N ⋙ H) (L : C) :
    G.obj (F.obj (N.obj L)) ≅ H.obj (N.obj L) := a.app L

/-- Naturality of the four canonical factors in a change of compositors.
Source: naturality and functoriality in the compactification comparison calculus
(blueprint: lem-pur-compact-support-site-coherence). -/
theorem coherenceCompositorOfChanges_naturality
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (F F' : C ⥤ D) (G G' : D ⥤ E) (H H' : C ⥤ E)
    (a : F ≅ F') (b : G ≅ G') (c : F' ⋙ G' ≅ H) (d : H ≅ H')
    {L M : C} (t : L ⟶ M) :
    G.map (F.map t) ≫
        (G.map (a.hom.app M) ≫ b.hom.app (F'.obj M) ≫ c.hom.app M ≫ d.hom.app M) =
      (G.map (a.hom.app L) ≫ b.hom.app (F'.obj L) ≫ c.hom.app L ≫ d.hom.app L) ≫
        H'.map t := by
  simp only [Category.assoc]
  rw [← G.map_comp_assoc, a.hom.naturality, G.map_comp_assoc,
    b.hom.naturality_assoc]
  have hc := c.hom.naturality_assoc t (d.hom.app M)
  dsimp only [Functor.comp_map] at hc
  rw [hc, d.hom.naturality]

/-- Paste the four change-of-compositor isomorphisms objectwise.
Source: compactification comparison calculus
(blueprint: lem-pur-compact-support-site-coherence). -/
def coherenceCompositorOfChanges
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (F F' : C ⥤ D) (G G' : D ⥤ E) (H H' : C ⥤ E)
    (a : F ≅ F') (b : G ≅ G') (c : F' ⋙ G' ≅ H) (d : H ≅ H') :
    F ⋙ G ≅ H' :=
  NatIso.ofComponents
    (fun L ↦ coherenceIsoFour (G.mapIso (a.app L))
      (b.app (F'.obj L)) (c.app L) (d.app L))
    (fun t ↦ coherenceCompositorOfChanges_naturality F F' G G' H H' a b c d t)

variable (A : Type (u + 1)) [CommRing A] [Finite A]

/-- The ambient derived site comparison, with its functor structure named.
Source: the derived etale to pro-etale inverse image
(blueprint: lem-pur-compact-support-site-coherence). -/
def coherenceSiteFunctor (X : Scheme.{u}) :
    DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) :=
  (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory

/-- The derived site comparison on bounded-below etale inputs.
Source: bounded-below inclusion and derived site comparison
(blueprint: lem-pur-compact-support-site-coherence). -/
def coherenceBoundedSiteFunctor (X : Scheme.{u}) :
    DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) :=
  DerivedCategory.Plus.ι ⋙ coherenceSiteFunctor A X

/-- The bounded-below etale compact-support functor with its functor structure hidden
behind a definition. Source: etale derived lower shriek
(blueprint: lem-pur-compact-support-site-coherence). -/
def coherenceEtaleFunctor {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ⥤
      DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
  Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) c

/-- The ambient pro-etale compact-support functor with its derived construction behind
a definition. Source: ambient compact support from a compactification
(blueprint: lem-pur-compact-support-site-coherence). -/
def coherenceProEtaleFunctor {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A)) :=
  rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c

/-- The canonical site comparison with the compact-support functor displayed.
Source: the bounded-below compact-support site comparison
(blueprint: lem-pur-compact-support-site-coherence). -/
def coherenceBoundaryIso {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    coherenceEtaleFunctor A c ⋙ coherenceBoundedSiteFunctor A Y ≅
      coherenceBoundedSiteFunctor A X ⋙ coherenceProEtaleFunctor A c :=
  compactExchangeTransportComparison A c

/-- The canonical comparison at a bounded-below object, with explicit endpoints.
Source: compactExchangeTransportComparison
(blueprint: lem-pur-compact-support-site-coherence). -/
def coherenceBoundaryComponent {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (coherenceBoundedSiteFunctor A Y).obj ((coherenceEtaleFunctor A c).obj L) ≅
      (coherenceProEtaleFunctor A c).obj ((coherenceBoundedSiteFunctor A X).obj L) :=
  coherenceEvaluateSquare (coherenceEtaleFunctor A c) (coherenceBoundedSiteFunctor A Y)
    (coherenceBoundedSiteFunctor A X) (coherenceProEtaleFunctor A c)
    (coherenceBoundaryIso A c) L

/-- The canonical change isomorphism with the displayed compact-support endpoints.
Source: etale compactification independence
(blueprint: lem-pur-compact-support-site-coherence). -/
def coherenceEtaleChangeIso {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    (c d : Compactification f) : coherenceEtaleFunctor A c ≅ coherenceEtaleFunctor A d :=
  Etale.rightDerivedLowerShriekOfCompactificationPlusIso A c d

/-- The canonical etale compositor with its chosen compactification functors displayed.
This records the same isomorphism, while avoiding conversion of whole derived functors
inside later compositions. Source: Stacks 0F7J and proposition-composition-base-change-rf-shriek--1
(blueprint: lem-pur-compact-support-site-coherence). -/
def coherenceChosenEtaleCompositorIso {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g] :
    coherenceEtaleFunctor A
        (HasCompactification.compactification f) ⋙
      coherenceEtaleFunctor A
        (HasCompactification.compactification g) ≅
      coherenceEtaleFunctor A
        (HasCompactification.compactification (f ≫ g)) :=
  Etale.rightDerivedLowerShriekPlusCompIso A f g

/-- The canonical origin compositor, viewed in the ambient derived categories.
The etale-origin inclusion has the same underlying object and morphism maps as this
bounded-below comparison. Source: originCompositionModel
(blueprint: lem-pur-compact-support-site-coherence). -/
def coherenceChosenProEtaleCompositorIso {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g] :
    coherenceBoundedSiteFunctor A X ⋙
          coherenceProEtaleFunctor A
            (HasCompactification.compactification f) ⋙
          coherenceProEtaleFunctor A
            (HasCompactification.compactification g) ≅
      coherenceBoundedSiteFunctor A X ⋙
          coherenceProEtaleFunctor A
            (HasCompactification.compactification (f ≫ g)) :=
  originCompositionModel A f g

/-- The chosen etale compositor with explicit object endpoints.
Source: canonical etale composition
(blueprint: lem-pur-compact-support-site-coherence). -/
def coherenceChosenEtaleCompositorComponent {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g]
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (coherenceEtaleFunctor A (HasCompactification.compactification g)).obj
        ((coherenceEtaleFunctor A (HasCompactification.compactification f)).obj L) ≅
      (coherenceEtaleFunctor A (HasCompactification.compactification (f ≫ g))).obj L :=
  coherenceEvaluateCompositor
    (coherenceEtaleFunctor A (HasCompactification.compactification f))
    (coherenceEtaleFunctor A (HasCompactification.compactification g))
    (coherenceEtaleFunctor A (HasCompactification.compactification (f ≫ g)))
    (coherenceChosenEtaleCompositorIso A f g) L

/-- The chosen origin compositor with explicit ambient object endpoints.
Source: canonical origin composition
(blueprint: lem-pur-compact-support-site-coherence). -/
def coherenceChosenProEtaleCompositorComponent {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g]
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (coherenceProEtaleFunctor A (HasCompactification.compactification g)).obj
        ((coherenceProEtaleFunctor A (HasCompactification.compactification f)).obj
          ((coherenceBoundedSiteFunctor A X).obj L)) ≅
      (coherenceProEtaleFunctor A (HasCompactification.compactification (f ≫ g))).obj
        ((coherenceBoundedSiteFunctor A X).obj L) :=
  coherenceEvaluateTriple (coherenceBoundedSiteFunctor A X)
    (coherenceProEtaleFunctor A (HasCompactification.compactification f))
    (coherenceProEtaleFunctor A (HasCompactification.compactification g))
    (coherenceProEtaleFunctor A (HasCompactification.compactification (f ≫ g)))
    (coherenceChosenProEtaleCompositorIso A f g) L

/-- The etale compositor evaluated using precisely the three supplied compactifications.
Source: Stacks 0F7J; proposition-construction-independence-rf-shriek--7
(blueprint: lem-pur-compact-support-site-coherence). -/
def coherenceEtaleCompositor {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    [QuasiCompact f] [QuasiCompact g]
    (c : Compactification f) (d : Compactification g) (e : Compactification (f ≫ g)) :
    Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) c ⋙
        Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) d ≅
      Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) e :=
  letI := c.hasCompactification
  letI := d.hasCompactification
  letI := e.hasCompactification
  coherenceCompositorOfChanges
    (coherenceEtaleFunctor A c)
    (coherenceEtaleFunctor A (HasCompactification.compactification f))
    (coherenceEtaleFunctor A d)
    (coherenceEtaleFunctor A (HasCompactification.compactification g))
    (coherenceEtaleFunctor A (HasCompactification.compactification (f ≫ g)))
    (coherenceEtaleFunctor A e)
    (coherenceEtaleChangeIso A c (HasCompactification.compactification f))
    (coherenceEtaleChangeIso A d (HasCompactification.compactification g))
    (coherenceChosenEtaleCompositorIso A f g)
    (coherenceEtaleChangeIso A (HasCompactification.compactification (f ≫ g)) e)

/-- The canonical c-to-d comparison, through the specified common refinement. Each leg
is the actual proper-composition/inverse-proper-open construction, not a site conjugate.
Source: proposition-construction-independence-rf-shriek, common-refinement comparison; node step 6
(blueprint: lem-pur-compact-support-site-coherence). -/
def coherenceCompactificationChange {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    (c d : Compactification f)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (coherenceProEtaleFunctor A c).obj
        ((coherenceBoundedSiteFunctor A X).obj L) ≅
      (coherenceProEtaleFunctor A d).obj
        ((coherenceBoundedSiteFunctor A X).obj L) :=
  (properTransportRefinement A (Compactification.infFst c d) L).symm ≪≫
    properTransportRefinement A (Compactification.infSnd c d) L

/-- The source boundary of the composition square is B_g followed by F_g^p(B_f).
Only canonical bounded-below inclusions are inserted.
Source: the displayed composition equation of the node, proof step 5
(blueprint: lem-pur-compact-support-site-coherence). -/
def coherenceCompositionSource {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (c : Compactification f) (d : Compactification g)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (coherenceBoundedSiteFunctor A Z).obj
        ((coherenceEtaleFunctor A d).obj ((coherenceEtaleFunctor A c).obj L)) ≅
      (coherenceProEtaleFunctor A d).obj
        ((coherenceProEtaleFunctor A c).obj
          ((coherenceBoundedSiteFunctor A X).obj L)) :=
  coherenceBoundaryComponent A d ((coherenceEtaleFunctor A c).obj L) ≪≫
    (coherenceProEtaleFunctor A d).mapIso
      (coherenceBoundaryComponent A c L)

/-- The independently constructed etale and pro-etale composition factors.
No commutativity proof is stored in this data. Source: the canonical compactification
comparisons and canonical origin compositor
(blueprint: lem-pur-compact-support-site-coherence). -/
def coherenceCompositionDataOfChoice {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    [QuasiCompact f] [QuasiCompact g]
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    (c : Compactification f) (d : Compactification g) (e : Compactification (f ≫ g))
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
  let cf := HasCompactification.compactification f
  let dg := HasCompactification.compactification g
  let egf := HasCompactification.compactification (f ≫ g)
  let NX := coherenceBoundedSiteFunctor A X
  let NY := coherenceBoundedSiteFunctor A Y
  let NZ := coherenceBoundedSiteFunctor A Z
  let Ec := coherenceEtaleFunctor A c
  let Ea := coherenceEtaleFunctor A cf
  let Ed := coherenceEtaleFunctor A d
  let Eb := coherenceEtaleFunctor A dg
  let Efg := coherenceEtaleFunctor A egf
  let Ee := coherenceEtaleFunctor A e
  let Fc := coherenceProEtaleFunctor A c
  let Fa := coherenceProEtaleFunctor A cf
  let Fd := coherenceProEtaleFunctor A d
  let Fb := coherenceProEtaleFunctor A dg
  let Ffg := coherenceProEtaleFunctor A egf
  let Fe := coherenceProEtaleFunctor A e
  let M := Ea.obj L
  CoherencePastingData NZ (Ed.obj (Ec.obj L)) (Ed.obj M) (Eb.obj M) (Efg.obj L)
    (Ee.obj L) (Fd.obj (NY.obj (Ec.obj L))) (Fd.obj (NY.obj M)) (Fb.obj (NY.obj M))
    (Fd.obj (Fc.obj (NX.obj L))) (Fd.obj (Fa.obj (NX.obj L)))
    (Fb.obj (Fa.obj (NX.obj L))) (Ffg.obj (NX.obj L)) (Fe.obj (NX.obj L))
    (coherenceCompositionSource A c d L).hom (coherenceBoundaryComponent A e L).hom :=
  let cf := HasCompactification.compactification f
  let dg := HasCompactification.compactification g
  let egf := HasCompactification.compactification (f ≫ g)
  let NY := coherenceBoundedSiteFunctor A Y
  let Ec := coherenceEtaleFunctor A c
  let Ea := coherenceEtaleFunctor A cf
  let Ed := coherenceEtaleFunctor A d
  let Fd := coherenceProEtaleFunctor A d
  let Fb := coherenceProEtaleFunctor A dg
  let M := Ea.obj L
  { e₀ := Ed.mapIso ((coherenceEtaleChangeIso A c cf).app L)
    e₁ := (coherenceEtaleChangeIso A d dg).app M
    e₂ := coherenceChosenEtaleCompositorComponent A f g L
    e₃ := (coherenceEtaleChangeIso A egf e).app L
    s₀ := (coherenceBoundaryComponent A d (Ec.obj L)).hom
    s₁ := (coherenceBoundaryComponent A d M).hom
    s₂ := (coherenceBoundaryComponent A dg M).hom
    s₃ := (coherenceBoundaryComponent A egf L).hom
    r₀ := Fd.map (coherenceBoundaryComponent A c L).hom
    r₁ := Fd.map (coherenceCompactificationChange A c cf L).hom
    r₂ := Fd.map (coherenceBoundaryComponent A cf L).inv
    rd := (coherenceCompactificationChange A d dg M).hom
    rb := Fb.map (coherenceBoundaryComponent A cf L).hom
    o := (coherenceChosenProEtaleCompositorComponent A f g L).hom
    re := (coherenceCompactificationChange A egf e L).hom
    n := Fd.map (NY.map ((coherenceEtaleChangeIso A c cf).hom.app L)) }

/-- The canonical factors with the choices supplied by the three compactifications.
Source: compactification independence (blueprint: lem-pur-compact-support-site-coherence). -/
def coherenceCompositionData {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    [QuasiCompact f] [QuasiCompact g]
    (c : Compactification f) (d : Compactification g) (e : Compactification (f ≫ g))
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
  letI := c.hasCompactification
  letI := d.hasCompactification
  letI := e.hasCompactification
  let cf := HasCompactification.compactification f
  let dg := HasCompactification.compactification g
  let egf := HasCompactification.compactification (f ≫ g)
  let NX := coherenceBoundedSiteFunctor A X
  let NY := coherenceBoundedSiteFunctor A Y
  let NZ := coherenceBoundedSiteFunctor A Z
  let Ec := coherenceEtaleFunctor A c
  let Ea := coherenceEtaleFunctor A cf
  let Ed := coherenceEtaleFunctor A d
  let Eb := coherenceEtaleFunctor A dg
  let Efg := coherenceEtaleFunctor A egf
  let Ee := coherenceEtaleFunctor A e
  let Fc := coherenceProEtaleFunctor A c
  let Fa := coherenceProEtaleFunctor A cf
  let Fd := coherenceProEtaleFunctor A d
  let Fb := coherenceProEtaleFunctor A dg
  let Ffg := coherenceProEtaleFunctor A egf
  let Fe := coherenceProEtaleFunctor A e
  let M := Ea.obj L
  CoherencePastingData NZ (Ed.obj (Ec.obj L)) (Ed.obj M) (Eb.obj M) (Efg.obj L)
    (Ee.obj L) (Fd.obj (NY.obj (Ec.obj L))) (Fd.obj (NY.obj M)) (Fb.obj (NY.obj M))
    (Fd.obj (Fc.obj (NX.obj L))) (Fd.obj (Fa.obj (NX.obj L)))
    (Fb.obj (Fa.obj (NX.obj L))) (Ffg.obj (NX.obj L)) (Fe.obj (NX.obj L))
    (coherenceCompositionSource A c d L).hom (coherenceBoundaryComponent A e L).hom :=
  letI := c.hasCompactification
  letI := d.hasCompactification
  letI := e.hasCompactification
  coherenceCompositionDataOfChoice A c d e L

/-- The four canonical etale factors, with explicit object endpoints.
Source: compactification independence and canonical composition
(blueprint: lem-pur-compact-support-site-coherence). -/
def coherenceEtaleCompositorComponent {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    [QuasiCompact f] [QuasiCompact g]
    (c : Compactification f) (d : Compactification g) (e : Compactification (f ≫ g))
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (coherenceEtaleFunctor A d).obj ((coherenceEtaleFunctor A c).obj L) ≅
      (coherenceEtaleFunctor A e).obj L :=
  (coherenceCompositionData A c d e L).etaleIso

/-- The recorded pro-etale alpha, evaluated on the identity etale-origin witness.
Its compactifications are the same c, d, e as in the etale compositor.
Source: proposition-composition-base-change-rf-shriek--1, normalized compatible-tower construction
(blueprint: lem-pur-compact-support-site-coherence). -/
def coherenceProEtaleCompositor {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    [QuasiCompact f] [QuasiCompact g]
    (c : Compactification f) (d : Compactification g) (e : Compactification (f ≫ g))
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (coherenceProEtaleFunctor A d).obj
        ((coherenceProEtaleFunctor A c).obj
          ((coherenceBoundedSiteFunctor A X).obj L)) ⟶
      (coherenceProEtaleFunctor A e).obj
        ((coherenceBoundedSiteFunctor A X).obj L) :=
  (coherenceCompositionData A c d e L).proMap

/-- A boundary comparison C_T(E) to M. This records the endpoints of the site-coherence
squares, including whiskered endpoints; it does not assert that any square commutes.
Source: node proof step 10, boundaries B_in and B_out of a pasted diagram
(blueprint: lem-pur-compact-support-site-coherence). -/
structure CompactSupportSiteBoundary (T : Scheme.{u}) where
  etale : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
  proEtale : _root_.DerivedCategory
    (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))
  comparison :
    (coherenceBoundedSiteFunctor A T).obj etale ≅ proEtale

/-- The boundary B_f^c = Rp_*(e_j) beta_p at L, in the ambient target category.
Source: node's defining equation for B, and proof step 2
(blueprint: lem-pur-compact-support-site-coherence). -/
def coherenceCompactificationBoundary {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    CompactSupportSiteBoundary A Y where
  etale := (coherenceEtaleFunctor A c).obj L
  proEtale := (coherenceProEtaleFunctor A c).obj
    ((coherenceBoundedSiteFunctor A X).obj L)
  comparison := coherenceBoundaryComponent A c L

/-- The boundary (F_g^p B_f)(B_g F_f^e) of the composition equation.
Source: node's second displayed coherence equation, proof step 5
(blueprint: lem-pur-compact-support-site-coherence). -/
def coherenceCompositionBoundary {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (c : Compactification f) (d : Compactification g)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    CompactSupportSiteBoundary A Z where
  etale := (coherenceEtaleFunctor A d).obj
    ((coherenceEtaleFunctor A c).obj L)
  proEtale := (coherenceProEtaleFunctor A d).obj
    ((coherenceCompactificationBoundary A c L).proEtale)
  comparison := coherenceCompositionSource A c d L

/-- The source boundary v_p^*(B_f), with the canonical inverse-image comparison a_v.
Source: node's open-restriction equation, proof steps 7--9
(blueprint: lem-pur-compact-support-site-coherence). -/
def coherenceRestrictionSource {X Y Y' : Scheme.{u}} {f : X ⟶ Y}
    (v : Y' ⟶ Y) (c : Compactification f)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    CompactSupportSiteBoundary A Y' where
  etale := (Etale.upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategoryPlus.obj
    ((coherenceCompactificationBoundary A c L).etale)
  proEtale := (upperStar (ModuleCat.{u + 1} A) v).leftDerivedFunctor.obj
    ((coherenceCompactificationBoundary A c L).proEtale)
  comparison := (compactExchangeTransportSource A v c).app L

/-- The target boundary B_f' followed by F_f'^p(a_u), for the pulled-back compactification.
Source: remark-base-change-compactification--1 and the node's open-restriction equation, step 9
(blueprint: lem-pur-compact-support-site-coherence). -/
def coherenceRestrictionTarget {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {u' : X' ⟶ X} {v : Y' ⟶ Y} (sq : IsPullback u' f' f v) (c : Compactification f)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    CompactSupportSiteBoundary A Y' where
  etale := (coherenceEtaleFunctor A
    (c.ofIsPullback sq)).obj
      ((Etale.upperStar (ModuleCat.{u + 1} A) u').mapDerivedCategoryPlus.obj L)
  proEtale := (coherenceProEtaleFunctor A
    (c.ofIsPullback sq)).obj
      ((upperStar (ModuleCat.{u + 1} A) u').leftDerivedFunctor.obj
        ((coherenceBoundedSiteFunctor A X).obj L))
  comparison := (compactExchangeTransportTarget A sq c).app L

/-- Whisker a boundary by the chosen compact-support pair, using its named B comparison.
Source: node proof step 10, horizontal pasting and naturality of B
(blueprint: lem-pur-compact-support-site-coherence). -/
def coherencePushBoundary {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (b : CompactSupportSiteBoundary A X) : CompactSupportSiteBoundary A Y where
  etale := (coherenceEtaleFunctor A c).obj
    b.etale
  proEtale := (coherenceProEtaleFunctor A c).obj b.proEtale
  comparison := (coherenceBoundaryIso A c).app b.etale ≪≫
    (coherenceProEtaleFunctor A c).mapIso b.comparison

/-- Whisker a boundary by inverse image, inserting the canonical comparison a_v.
Source: proposition-comparison-etale-derived-category--5 and node proof steps 1 and 10
(blueprint: lem-pur-compact-support-site-coherence). -/
def coherencePullBoundary {X Y : Scheme.{u}} (v : X ⟶ Y)
    (b : CompactSupportSiteBoundary A Y) : CompactSupportSiteBoundary A X where
  etale := (Etale.upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategoryPlus.obj b.etale
  proEtale := (upperStar (ModuleCat.{u + 1} A) v).leftDerivedFunctor.obj b.proEtale
  comparison := (leftDerivedUpperStarComparisonIso v A).app b.etale ≪≫
    (upperStar (ModuleCat.{u + 1} A) v).leftDerivedFunctor.mapIso b.comparison

/-- Formal finite diagrams in the three named compactification comparisons. No constructor
assumes its site-comparison square. Identity, concatenation, and whiskering explicitly
include identity diagrams and horizontal, vertical and mixed pasting. The geometric
vertices of generators are finite-type k-schemes, with no separatedness of their structure
maps. Over morphisms retain compatibility with k. The change constructor inserts compatible
boundary identifications (associators, pullback comparisons, or an etale-origin witness);
its two hypotheses concern only these endpoint isomorphisms, never a generator square.
Source: node's three displayed equations and final sentence; proof steps 4--10
(blueprint: lem-pur-compact-support-site-coherence). -/
inductive CompactSupportSiteDiagram (P : WeilConjectures.PurityFiniteSetting.{u}) :
    {T : Scheme.{u}} → CompactSupportSiteBoundary P.Coefficient T →
      CompactSupportSiteBoundary P.Coefficient T → Type (u + 2)
  | refinement {X Y : Over (Spec (.of P.field.k))}
      [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
      [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
      {f : X ⟶ Y} [IsSeparated f.left] [LocallyOfFiniteType f.left] [QuasiCompact f.left]
      {c d : Compactification f.left} (r : c.Refinement d)
      (L : DerivedCategory.Plus (Sheaf X.left.smallEtaleTopology
        (ModuleCat.{u + 1} P.Coefficient))) :
      CompactSupportSiteDiagram P (coherenceCompactificationBoundary P.Coefficient c L)
        (coherenceCompactificationBoundary P.Coefficient d L)
  | composition {X Y Z : Over (Spec (.of P.field.k))}
      [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
      [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
      [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
      {f : X ⟶ Y} {g : Y ⟶ Z}
      [IsSeparated f.left] [LocallyOfFiniteType f.left] [QuasiCompact f.left]
      [IsSeparated g.left] [LocallyOfFiniteType g.left] [QuasiCompact g.left]
      (c : Compactification f.left) (d : Compactification g.left)
      (e : Compactification (f.left ≫ g.left))
      (L : DerivedCategory.Plus (Sheaf X.left.smallEtaleTopology
        (ModuleCat.{u + 1} P.Coefficient))) :
      CompactSupportSiteDiagram P (coherenceCompositionBoundary P.Coefficient c d L)
        (coherenceCompactificationBoundary P.Coefficient e L)
  | restriction {X X' Y Y' : Over (Spec (.of P.field.k))}
      [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
      [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
      [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
      [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom]
      {f : X ⟶ Y} {f' : X' ⟶ Y'} {u' : X' ⟶ X} {v : Y' ⟶ Y}
      [IsSeparated f.left] [LocallyOfFiniteType f.left] [QuasiCompact f.left]
      [IsOpenImmersion v.left]
      (sq : IsPullback u'.left f'.left f.left v.left) (c : Compactification f.left)
      (L : DerivedCategory.Plus (Sheaf X.left.smallEtaleTopology
        (ModuleCat.{u + 1} P.Coefficient))) :
      CompactSupportSiteDiagram P (coherenceRestrictionSource P.Coefficient v.left c L)
        (coherenceRestrictionTarget P.Coefficient sq c L)
  | identity {T : Scheme.{u}} (b : CompactSupportSiteBoundary P.Coefficient T) :
      CompactSupportSiteDiagram P b b
  | comp {T : Scheme.{u}} {b₀ b₁ b₂ : CompactSupportSiteBoundary P.Coefficient T}
      (D : CompactSupportSiteDiagram P b₀ b₁) (E : CompactSupportSiteDiagram P b₁ b₂) :
      CompactSupportSiteDiagram P b₀ b₂
  | push {X Y : Over (Spec (.of P.field.k))}
      [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
      [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
      {f : X ⟶ Y} [IsSeparated f.left] [LocallyOfFiniteType f.left] [QuasiCompact f.left]
      (c : Compactification f.left) {b₀ b₁ : CompactSupportSiteBoundary P.Coefficient X.left}
      (D : CompactSupportSiteDiagram P b₀ b₁) :
      CompactSupportSiteDiagram P (coherencePushBoundary P.Coefficient c b₀)
        (coherencePushBoundary P.Coefficient c b₁)
  | pull {X Y : Over (Spec (.of P.field.k))}
      [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
      [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
      (v : X ⟶ Y) [IsOpenImmersion v.left]
      {b₀ b₁ : CompactSupportSiteBoundary P.Coefficient Y.left}
      (D : CompactSupportSiteDiagram P b₀ b₁) :
      CompactSupportSiteDiagram P (coherencePullBoundary P.Coefficient v.left b₀)
        (coherencePullBoundary P.Coefficient v.left b₁)
  | change {T : Scheme.{u}}
      {b₀ b₁ c₀ c₁ : CompactSupportSiteBoundary P.Coefficient T}
      (e₀ : b₀.etale ≅ c₀.etale) (e₁ : b₁.etale ≅ c₁.etale)
      (p₀ : b₀.proEtale ≅ c₀.proEtale) (p₁ : b₁.proEtale ≅ c₁.proEtale)
      (h₀ : (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T).mapDerivedCategory.map
          (DerivedCategory.Plus.ι.map e₀.hom) ≫ c₀.comparison.hom =
        b₀.comparison.hom ≫ p₀.hom)
      (h₁ : (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T).mapDerivedCategory.map
          (DerivedCategory.Plus.ι.map e₁.hom) ≫ c₁.comparison.hom =
        b₁.comparison.hom ≫ p₁.hom)
      (D : CompactSupportSiteDiagram P b₀ b₁) : CompactSupportSiteDiagram P c₀ c₁

/-- The etale boundary composite, constructed solely with the recorded etale maps.
The refinement uses the inverse of the upstream comparison because its upstream direction
is d to c, whereas the node's rho is c to d.
Source: proposition-construction-independence-rf-shriek--7, prose-05-31, and node proof step 10
(blueprint: lem-pur-compact-support-site-coherence). -/
def CompactSupportSiteDiagram.etaleMap {P : WeilConjectures.PurityFiniteSetting.{u}}
    {T : Scheme.{u}} {b₀ b₁ : CompactSupportSiteBoundary P.Coefficient T}
    (D : CompactSupportSiteDiagram P b₀ b₁) : b₀.etale ⟶ b₁.etale :=
  match D with
  | @CompactSupportSiteDiagram.refinement .(P) _ _ _ _ _ _ _ _ _ _ _ _ r L =>
      (Etale.rightDerivedLowerShriekOfCompactificationPlusRefinementIso P.Coefficient r).inv.app L
  | @CompactSupportSiteDiagram.composition .(P) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ c d e L =>
      (coherenceEtaleCompositorComponent P.Coefficient c d e L).hom
  | @CompactSupportSiteDiagram.restriction .(P) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sq c L =>
      (Etale.rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap P.Coefficient sq c).app L
  | @CompactSupportSiteDiagram.identity .(P) _ b => 𝟙 b.etale
  | @CompactSupportSiteDiagram.comp .(P) _ _ _ _ D E => D.etaleMap ≫ E.etaleMap
  | @CompactSupportSiteDiagram.push .(P) _ _ _ _ _ _ _ _ _ _ c _ _ D =>
      (Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} P.Coefficient)
        c).map D.etaleMap
  | @CompactSupportSiteDiagram.pull .(P) _ _ _ _ _ _ v _ _ _ D =>
      (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) v.left).mapDerivedCategoryPlus.map
        D.etaleMap
  | @CompactSupportSiteDiagram.change .(P) _ _ _ _ _ e₀ e₁ _ _ _ _ D =>
      e₀.inv ≫ D.etaleMap ≫ e₁.hom

omit [Finite A] in
private theorem comparison_comp_named {U V W : Scheme.{u}}
    (r : U ⟶ V) (p : V ⟶ W) (q : U ⟶ W) (h : r ≫ p = q)
    (L : DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    let := Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) r)
    (comparisonUpperStar (ModuleCat.{u + 1} A) W).mapDerivedCategoryPlus.map
      ((Functor.rightDerivedFunctorPlusCompIso'
        (Etale.lowerStar (ModuleCat.{u + 1} A) r)
        (Etale.lowerStar (ModuleCat.{u + 1} A) p)
        (Etale.lowerStarComp (ModuleCat.{u + 1} A) r p q h.symm)).hom.app L) ≫
      (fixedComparisonDirectImageMatePlus A q).app L =
    (fixedComparisonDirectImageMatePlus A p).app
      ((Etale.lowerStar (ModuleCat.{u + 1} A) r).rightDerivedFunctorPlus.obj L) ≫
      (lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctorPlus.map
        ((fixedComparisonDirectImageMatePlus A r).app L) ≫
      (proEtaleComparisonDirectImageCompIso A r p).hom.app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) U).mapDerivedCategoryPlus.obj L) ≫
      (properTransportDirectImageCongr A h.symm).inv.app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) U).mapDerivedCategoryPlus.obj L) := by
  subst q
  simpa only [properTransportDirectImageCongr_rfl, Iso.refl_hom, Iso.refl_inv,
    NatTrans.id_app, Category.comp_id,
    etaleComparisonDirectImageCompIso, fixedComparisonDirectImageMatePlus] using
    comparisonDirectImagePlus_comp A r p L

private theorem refinement_square_core
    {C₁ C₂ C₃ D₁ D₂ D₃ : Type*}
    [Category* C₁] [Category* C₂] [Category* C₃]
    [Category* D₁] [Category* D₂] [Category* D₃]
    (N₁ : C₁ ⥤ D₁) (N₂ : C₂ ⥤ D₂) (N₃ : C₃ ⥤ D₃)
    (E₁ : C₁ ⥤ C₂) (E₂ : C₂ ⥤ C₃) (E₁₂ : C₁ ⥤ C₃)
    (P₁ : D₁ ⥤ D₂) (P₂ : D₂ ⥤ D₃) (P₁₂ : D₁ ⥤ D₃)
    (b₁ : E₁ ⋙ N₂ ⟶ N₁ ⋙ P₁) (b₂ : E₂ ⋙ N₃ ⟶ N₂ ⋙ P₂)
    (b₁₂ : E₁₂ ⋙ N₃ ⟶ N₁ ⋙ P₁₂)
    (ce : E₁ ⋙ E₂ ≅ E₁₂) (cp : P₁ ⋙ P₂ ≅ P₁₂)
    (M₁ : C₁) (M₂ : C₂) (J₁ : D₁) (J₂ : D₂)
    (ec : N₁.obj M₁ ≅ J₁) (ed : N₂.obj M₂ ≅ J₂)
    (ae : M₂ ⟶ E₁.obj M₁) (ap : J₂ ⟶ P₁.obj J₁)
    (hc : N₃.map (ce.hom.app M₁) ≫ b₁₂.app M₁ =
      b₂.app (E₁.obj M₁) ≫ P₂.map (b₁.app M₁) ≫ cp.hom.app (N₁.obj M₁))
    (ho : ed.hom ≫ ap = N₂.map ae ≫ b₁.app M₁ ≫ P₁.map ec.hom) :
    N₃.map (E₂.map ae ≫ ce.hom.app M₁) ≫ b₁₂.app M₁ ≫ P₁₂.map ec.hom =
      b₂.app M₂ ≫ P₂.map ed.hom ≫ P₂.map ap ≫ cp.hom.app J₁ := by
  simp only [N₃.map_comp, Category.assoc]
  rw [reassoc_of% hc]
  have hp := cp.hom.naturality ec.hom
  change P₂.map (P₁.map ec.hom) ≫ cp.hom.app J₁ =
    cp.hom.app (N₁.obj M₁) ≫ P₁₂.map ec.hom at hp
  rw [← hp]
  have hn := b₂.naturality ae
  change N₃.map (E₂.map ae) ≫ b₂.app (E₁.obj M₁) =
    b₂.app M₂ ≫ P₂.map (N₂.map ae) at hn
  rw [reassoc_of% hn]
  simpa only [P₂.map_comp, Category.assoc] using
    congrArg (fun t ↦ b₂.app M₂ ≫ P₂.map t ≫ cp.hom.app J₁) ho.symm

private theorem site_plus_hom {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (compactSupportSiteComparisonPlus A c).hom.app L =
    (fixedComparisonDirectImageMatePlus A c.g).app
      ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategoryPlus.obj L) ≫
      (lowerStar (ModuleCat.{u + 1} A) c.g).rightDerivedFunctorPlus.map
        ((properOpenSiteExtensionIso A c.i).hom.app L) := by
  simp only [compactSupportSiteComparisonPlus, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, asIso_hom]

private theorem refinement_plus_inv {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (properTransportRefinementPlus A r L).inv =
      (lowerStar (ModuleCat.{u + 1} A) d.g).rightDerivedFunctorPlus.map
        (properOpenProEtaleIsoPlus A r.hom c.i d.i r.i_hom L).hom ≫
      (proEtaleComparisonDirectImageCompIso A r.hom d.g).hom.app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategoryPlus.obj
          ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategoryPlus.obj L)) ≫
      (properTransportDirectImageCongr A r.hom_g.symm).inv.app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategoryPlus.obj
          ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategoryPlus.obj L)) := by
  simp only [properTransportRefinementPlus, Iso.trans_inv, Iso.app_inv,
    Iso.symm_inv, Functor.mapIso_inv, Category.assoc]

private theorem refinement_plus_inverse {X Y : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y] {f : X ⟶ Y}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    {c d : Compactification f} (r : c.Refinement d)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategoryPlus.map
        ((Etale.rightDerivedLowerShriekOfCompactificationPlusRefinementIso A r).hom.app L) ≫
      (compactSupportSiteComparisonPlus A c).hom.app L =
    (compactSupportSiteComparisonPlus A d).hom.app L ≫
      (properTransportRefinementPlus A r L).inv := by
  let M := (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategoryPlus.obj L
  let N := (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) d.i).mapDerivedCategoryPlus.obj L
  let P := (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategoryPlus.obj
    ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategoryPlus.obj L)
  let Q := (openImmersionLowerShriek (ModuleCat.{u + 1} A) d.i).mapDerivedCategoryPlus.obj
    ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategoryPlus.obj L)
  let := Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) r.hom)
  let ce := Functor.rightDerivedFunctorPlusCompIso'
    (Etale.lowerStar (ModuleCat.{u + 1} A) r.hom)
    (Etale.lowerStar (ModuleCat.{u + 1} A) d.g)
    (Etale.lowerStarComp (ModuleCat.{u + 1} A) r.hom d.g c.g r.hom_g.symm)
  let cp := proEtaleComparisonDirectImageCompIso A r.hom d.g ≪≫
    (properTransportDirectImageCongr A r.hom_g.symm).symm
  have hc := comparison_comp_named A r.hom d.g c.g r.hom_g M
  have ho : (properOpenSiteExtensionIso A d.i).hom.app L ≫
      (properOpenProEtaleIsoPlus A r.hom c.i d.i r.i_hom L).hom =
    (comparisonUpperStar (ModuleCat.{u + 1} A) d.Z).mapDerivedCategoryPlus.map
      (Etale.properOpenComparison A r.hom c.i d.i r.i_hom L) ≫
      (fixedComparisonDirectImageMatePlus A r.hom).app M ≫
      (lowerStar (ModuleCat.{u + 1} A) r.hom).rightDerivedFunctorPlus.map
        ((properOpenSiteExtensionIso A c.i).hom.app L) := by
    simp only [properOpenProEtaleIsoPlus, Iso.trans_hom, Iso.app_hom, Iso.symm_hom,
      Functor.mapIso_hom, asIso_hom, fixedComparisonDirectImageMatePlus,
      Iso.hom_inv_id_app_assoc]
    rfl
  have h := refinement_square_core
    (comparisonUpperStar (ModuleCat.{u + 1} A) c.Z).mapDerivedCategoryPlus
    (comparisonUpperStar (ModuleCat.{u + 1} A) d.Z).mapDerivedCategoryPlus
    (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategoryPlus
    (Etale.lowerStar (ModuleCat.{u + 1} A) r.hom).rightDerivedFunctorPlus
    (Etale.lowerStar (ModuleCat.{u + 1} A) d.g).rightDerivedFunctorPlus
    (Etale.lowerStar (ModuleCat.{u + 1} A) c.g).rightDerivedFunctorPlus
    (lowerStar (ModuleCat.{u + 1} A) r.hom).rightDerivedFunctorPlus
    (lowerStar (ModuleCat.{u + 1} A) d.g).rightDerivedFunctorPlus
    (lowerStar (ModuleCat.{u + 1} A) c.g).rightDerivedFunctorPlus
    (fixedComparisonDirectImageMatePlus A r.hom)
    (fixedComparisonDirectImageMatePlus A d.g) (fixedComparisonDirectImageMatePlus A c.g)
    ce cp M N P Q ((properOpenSiteExtensionIso A c.i).app L)
    ((properOpenSiteExtensionIso A d.i).app L)
    (Etale.properOpenComparison A r.hom c.i d.i r.i_hom L)
    (properOpenProEtaleIsoPlus A r.hom c.i d.i r.i_hom L).hom
    (by simpa only [cp, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc] using hc) ho
  rw [Etale.etaleCompactSupport_refinementComparison_eq A f r L,
    site_plus_hom, site_plus_hom, refinement_plus_inv]
  simpa only [ce, cp, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.map_comp,
    Category.assoc,
    Etale.derivedPlusFormalism_pfComp'_inv, Etale.rightDerivedLowerStarPlus,
    M, N, P, Q, Iso.app_hom] using h

private theorem inverse_square
    {C D : Type*} [Category* C] [Category* D] (N : C ⥤ D)
    {a b : C} {p q : D} (e : b ≅ a) (bc : N.obj a ≅ p) (bd : N.obj b ≅ q)
    (r : p ≅ q) (h : N.map e.hom ≫ bc.hom = bd.hom ≫ r.inv) :
    N.map e.inv ≫ bd.hom = bc.hom ≫ r.hom := by
  apply (cancel_mono r.inv).mp
  rw [Category.assoc, ← h, ← N.map_comp_assoc, e.inv_hom_id, N.map_id]
  simp

private theorem inclusion_square
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (N : C ⥤ D) (I : D ⥤ E)
    {a b : C} {x y : D} {p q : E} (t : a ⟶ b)
    (bc : N.obj a ≅ x) (bd : N.obj b ≅ y) (r : x ⟶ y)
    (xc : I.obj x ≅ p) (xd : I.obj y ≅ q)
    (h : N.map t ≫ bd.hom = bc.hom ≫ r) :
    I.map (N.map t) ≫ (I.mapIso bd ≪≫ xd).hom =
      (I.mapIso bc ≪≫ xc).hom ≫ (xc.inv ≫ I.map r ≫ xd.hom) := by
  simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  rw [Iso.hom_inv_id_assoc, ← I.map_comp_assoc, h, I.map_comp, Category.assoc]

private theorem boundary_comparison_hom {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (coherenceBoundaryIso A c).hom.app L =
      DerivedCategory.Plus.ι.map ((compactSupportSiteComparisonPlus A c).hom.app L) ≫
      (rightDerivedLowerShriekOfCompactificationPlusCompatibility
        (ModuleCat.{u + 1} A) c).hom.app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategoryPlus.obj L) := by
  dsimp only [coherenceEtaleFunctor, coherenceProEtaleFunctor, coherenceSiteFunctor,
    coherenceBoundedSiteFunctor]
  simp only [coherenceBoundaryIso, compactExchangeTransportComparison,
    compactSupportSiteComparison,
    Functor.mapDerivedCategoryPlusCompatibility,
    Iso.trans_hom,
    Iso.trans_inv,
    Iso.symm_hom,
    Iso.symm_inv,
    NatTrans.comp_app,
    Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerRight_inv,
    Functor.whiskerLeft_app,
    Functor.whiskerRight_app,
    Functor.associator_hom_app,
    Functor.associator_inv_app,
    Iso.refl_hom,
    Iso.refl_inv,
    NatTrans.id_app,
    Category.id_comp,
    Category.comp_id,
    Category.assoc]
  erw [← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  simp only [Functor.comp_map,
    CategoryTheory.Functor.map_id]
  erw [Category.id_comp, Category.comp_id]

omit [Finite A] in
private theorem inclusion_comparison_map (X : Scheme.{u})
    {L M : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))}
    (t : L ⟶ M) :
    DerivedCategory.Plus.ι.map
      ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategoryPlus.map t) =
      (coherenceSiteFunctor A X).map
        (DerivedCategory.Plus.ι.map t) := rfl

private theorem refinement_site_square {X Y : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y] {f : X ⟶ Y}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    {c d : Compactification f} (r : c.Refinement d)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (coherenceSiteFunctor A Y).map
        (DerivedCategory.Plus.ι.map
          ((Etale.rightDerivedLowerShriekOfCompactificationPlusRefinementIso A r).inv.app L)) ≫
      (coherenceBoundaryIso A d).hom.app L =
    (coherenceBoundaryIso A c).hom.app L ≫
      (properTransportRefinement A r L).hom := by
  have hp := inverse_square
    (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategoryPlus
    ((Etale.rightDerivedLowerShriekOfCompactificationPlusRefinementIso A r).app L)
    ((compactSupportSiteComparisonPlus A c).app L)
    ((compactSupportSiteComparisonPlus A d).app L)
    (properTransportRefinementPlus A r L) (refinement_plus_inverse A r L)
  have h := inclusion_square
    (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategoryPlus
    DerivedCategory.Plus.ι
    ((Etale.rightDerivedLowerShriekOfCompactificationPlusRefinementIso A r).inv.app L)
    ((compactSupportSiteComparisonPlus A c).app L)
    ((compactSupportSiteComparisonPlus A d).app L)
    (properTransportRefinementPlus A r L).hom
    ((rightDerivedLowerShriekOfCompactificationPlusCompatibility
      (ModuleCat.{u + 1} A) c).app
      ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategoryPlus.obj L))
    ((rightDerivedLowerShriekOfCompactificationPlusCompatibility
      (ModuleCat.{u + 1} A) d).app
      ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategoryPlus.obj L)) hp
  rw [boundary_comparison_hom, boundary_comparison_hom]
  simp only [properTransportRefinement,
    Iso.trans_hom,
    Functor.mapIso_hom,
    Iso.symm_hom,
    Iso.app_hom,
    Iso.app_inv,
    Category.assoc,
    inclusion_comparison_map,
    Functor.mapDerivedCategoryPlusCompatibility,
    Iso.refl_hom,
    Iso.refl_inv,
    NatTrans.id_app,
    Functor.comp_map] at h ⊢
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp,
    CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.comp_id]
  exact h

private theorem compactification_change_square {X Y : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y] {f : X ⟶ Y}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c d : Compactification f)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (coherenceSiteFunctor A Y).map
        (DerivedCategory.Plus.ι.map
          ((coherenceEtaleChangeIso A c d).hom.app L)) ≫
      (coherenceBoundaryIso A d).hom.app L =
    (coherenceBoundaryIso A c).hom.app L ≫
      (coherenceCompactificationChange A c d L).hom := by
  let N := DerivedCategory.Plus.ι ⋙
    (coherenceSiteFunctor A Y)
  let r := Compactification.infFst c d
  let t := Compactification.infSnd c d
  have hr := inverse_square N
    ((Etale.rightDerivedLowerShriekOfCompactificationPlusRefinementIso A r).symm.app L)
    ((coherenceBoundaryIso A c).app L)
    ((coherenceBoundaryIso A (Compactification.inf c d)).app L)
    (properTransportRefinement A r L).symm (refinement_site_square A r L)
  simp only [N, Functor.comp_map, Iso.app_inv, Iso.symm_inv, Iso.app_hom, Iso.symm_hom] at hr
  have ht := refinement_site_square A t L
  rw [coherenceEtaleChangeIso,
    Etale.rightDerivedLowerShriekOfCompactificationPlusIso_eq_refinementIso A r t]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.map_comp,
    Category.assoc, coherenceCompactificationChange]
  rw [ht, ← Category.assoc, hr, Category.assoc]

private theorem conjugate_composition
    {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {a b : C} {x y z : D} (e : a ≅ b) (eg : F.obj b ≅ y) (efg : z ≅ x)
    (alpha : F.obj a ⟶ z) (t : y ⟶ x)
    (h : alpha ≫ efg.hom = F.map e.hom ≫ eg.hom ≫ t) :
    t ≫ efg.inv = eg.inv ≫ F.map e.inv ≫ alpha := by
  apply (cancel_mono efg.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [h, ← F.map_comp_assoc, e.inv_hom_id, F.map_id, Category.id_comp,
    eg.inv_hom_id_assoc]

private theorem origin_comparison_inv {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f] [QuasiCompact f]
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) Y).ι.map
        ((originComparison A f).inv.app L) =
      (coherenceBoundaryIso A
        (HasCompactification.compactification f)).hom.app L := by
  dsimp only [coherenceEtaleFunctor, coherenceProEtaleFunctor, coherenceSiteFunctor,
    coherenceBoundedSiteFunctor]
  simp only [coherenceBoundaryIso, originComparison,
    coherenceBoundaryIso, compactExchangeTransportComparison,
    Iso.trans_hom,
    Iso.symm_hom,
    NatTrans.comp_app,
    Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app,
    Functor.associator_hom_app,
    Functor.associator_inv_app,
    Category.id_comp]
  rfl

private theorem chosen_composition_square {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) [HasCompactification f] [HasCompactification g]
    [HasCompactification (f ≫ g)] [QuasiCompact f] [QuasiCompact g]
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (coherenceSiteFunctor A Z).map
        (DerivedCategory.Plus.ι.map ((coherenceChosenEtaleCompositorIso A f g).hom.app L)) ≫
      (coherenceBoundaryIso A
        (HasCompactification.compactification (f ≫ g))).hom.app L =
    (coherenceCompositionSource A (HasCompactification.compactification f)
      (HasCompactification.compactification g) L).hom ≫
      (coherenceChosenProEtaleCompositorIso A f g).hom.app L := by
  have h := congr_app (originComparison_comp A f g) L
  have hh := conjugate_composition (originCompactSupport A g)
    ((originComparison A f).app L)
    ((originComparison A g).app ((Etale.rightDerivedLowerShriekPlus
      (ModuleCat.{u + 1} A) f).obj L))
    ((originComparison A (f ≫ g)).app L)
    ((originComposition A f g).hom.app
      ((comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) X).obj L))
    ((comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) Z).map
      ((Etale.rightDerivedLowerShriekPlusCompIso A f g).hom.app L)) h
  have ha := congrArg
    ((DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) Z).ι.map) hh
  have hi : (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) Z).ι.map
      ((originCompactSupport A g).map ((originComparison A f).inv.app L)) =
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g).map
        ((coherenceBoundaryIso A
          (HasCompactification.compactification f)).hom.app L) := by
    change (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g).map
      ((DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) Y).ι.map
        ((originComparison A f).inv.app L)) = _
    rw [origin_comparison_inv]
  simp only [Functor.map_comp, Iso.app_inv, origin_comparison_inv, hi] at ha
  have hn : (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) Z).ι.map
      ((comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) Z).map
        ((Etale.rightDerivedLowerShriekPlusCompIso A f g).hom.app L)) =
      (coherenceSiteFunctor A Z).map
        (DerivedCategory.Plus.ι.map
          ((Etale.rightDerivedLowerShriekPlusCompIso A f g).hom.app L)) := rfl
  rw [hn] at ha
  have hm := congr_app (originComposition_model A f g) L
  dsimp only [Functor.whiskerLeft_app, Functor.whiskerRight_app] at hm
  erw [hm] at ha
  simpa only [coherenceCompositionSource, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    Category.assoc, Etale.rightDerivedLowerShriekPlus_eq, rightDerivedLowerShriek_eq,
    coherenceChosenEtaleCompositorIso, coherenceChosenProEtaleCompositorIso,
    coherenceBoundaryComponent, coherenceEvaluateSquare, coherenceBoundaryIso,
    coherenceEtaleFunctor, coherenceProEtaleFunctor, coherenceSiteFunctor,
    coherenceBoundedSiteFunctor] using ha

private theorem map_cancel_boundary
    {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {a b c d : C} (B : d ≅ c) (x : a ⟶ b) (y : b ⟶ c) (z : a ⟶ d)
    (h : z ≫ B.hom = x ≫ y) :
    F.map x ≫ F.map y ≫ F.map B.inv = F.map z := by
  rw [← F.map_comp, ← F.map_comp, ← Category.assoc, ← h]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

private theorem paste_composition
    {C : Type*} [Category* C]
    {a₀ a₁ a₂ a₃ a₄ b₀ b₁ b₂ v₀ v₁ v₂ p q : C}
    {l₀ : a₀ ⟶ a₁} {l₁ : a₁ ⟶ a₂} {l₂ : a₂ ⟶ a₃} {l₃ : a₃ ⟶ a₄}
    {s₀ : a₀ ⟶ b₀} {s₁ : a₁ ⟶ b₁} {s₂ : a₂ ⟶ b₂}
    {s₃ : a₃ ⟶ p} {s₄ : a₄ ⟶ q}
    {r₀ : b₀ ⟶ v₀} {r₁ : v₀ ⟶ v₁} {r₂ : v₁ ⟶ b₁}
    {rd : b₁ ⟶ b₂} {rb : b₂ ⟶ v₂} {o : v₂ ⟶ p} {re : p ⟶ q}
    {n : b₀ ⟶ b₁}
    (he : l₃ ≫ s₄ = s₃ ≫ re)
    (hc : l₂ ≫ s₃ = s₂ ≫ rb ≫ o)
    (hd : l₁ ≫ s₂ = s₁ ≫ rd)
    (hn : l₀ ≫ s₁ = s₀ ≫ n)
    (hf : r₀ ≫ r₁ ≫ r₂ = n) :
    l₀ ≫ l₁ ≫ l₂ ≫ l₃ ≫ s₄ =
      s₀ ≫ r₀ ≫ r₁ ≫ r₂ ≫ rd ≫ rb ≫ o ≫ re := by
  rw [he, reassoc_of% hc, reassoc_of% hd, reassoc_of% hn, reassoc_of% hf]

private theorem mapped_paste_composition
    {C D : Type*} [Category* C] [Category* D] (N : C ⥤ D)
    {a₀ a₁ a₂ a₃ a₄ : C} {b₀ b₁ b₂ v₀ v₁ v₂ p q : D}
    {l₀ : a₀ ⟶ a₁} {l₁ : a₁ ⟶ a₂} {l₂ : a₂ ⟶ a₃} {l₃ : a₃ ⟶ a₄}
    {s₀ : N.obj a₀ ⟶ b₀} {s₁ : N.obj a₁ ⟶ b₁} {s₂ : N.obj a₂ ⟶ b₂}
    {s₃ : N.obj a₃ ⟶ p} {s₄ : N.obj a₄ ⟶ q}
    {r₀ : b₀ ⟶ v₀} {r₁ : v₀ ⟶ v₁} {r₂ : v₁ ⟶ b₁}
    {rd : b₁ ⟶ b₂} {rb : b₂ ⟶ v₂} {o : v₂ ⟶ p} {re : p ⟶ q}
    {n : b₀ ⟶ b₁}
    (he : N.map l₃ ≫ s₄ = s₃ ≫ re)
    (hc : N.map l₂ ≫ s₃ = s₂ ≫ rb ≫ o)
    (hd : N.map l₁ ≫ s₂ = s₁ ≫ rd)
    (hn : N.map l₀ ≫ s₁ = s₀ ≫ n)
    (hf : r₀ ≫ r₁ ≫ r₂ = n) :
    N.map (coherenceFourMap l₀ l₁ l₂ l₃) ≫ s₄ =
      (s₀ ≫ r₀) ≫ coherenceSixMap r₁ r₂ rd rb o re := by
  simp only [coherenceFourMap, coherenceSixMap, N.map_comp, Category.assoc]
  exact paste_composition he hc hd hn hf

private theorem CoherencePastingData.coherent {C D : Type*} [Category* C] [Category* D] {N : C ⥤ D}
    {a₀ a₁ a₂ a₃ a₄ : C} {b₀ b₁ b₂ v₀ v₁ v₂ p q : D}
    {bin : N.obj a₀ ⟶ v₀} {bout : N.obj a₄ ⟶ q}
    (t : CoherencePastingData N a₀ a₁ a₂ a₃ a₄ b₀ b₁ b₂ v₀ v₁ v₂ p q bin bout)
    (hb : bin = t.s₀ ≫ t.r₀)
    (he : N.map t.e₃.hom ≫ bout = t.s₃ ≫ t.re)
    (hc : N.map t.e₂.hom ≫ t.s₃ = (t.s₂ ≫ t.rb) ≫ t.o)
    (hd : N.map t.e₁.hom ≫ t.s₂ = t.s₁ ≫ t.rd)
    (hn : N.map t.e₀.hom ≫ t.s₁ = t.s₀ ≫ t.n)
    (hf : t.r₀ ≫ t.r₁ ≫ t.r₂ = t.n) :
    N.map t.etaleIso.hom ≫ bout = bin ≫ t.proMap := by
  calc
    _ = (t.s₀ ≫ t.r₀) ≫ t.proMap := mapped_paste_composition N he
      (hc.trans (Category.assoc _ _ _)) hd hn hf
    _ = _ := congrArg (fun z ↦ z ≫ t.proMap) hb.symm

private theorem boundary_component_naturality {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f)
    {L M : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))}
    (t : L ⟶ M) :
    (coherenceBoundedSiteFunctor A Y).map ((coherenceEtaleFunctor A c).map t) ≫
        (coherenceBoundaryComponent A c M).hom =
      (coherenceBoundaryComponent A c L).hom ≫
        (coherenceProEtaleFunctor A c).map ((coherenceBoundedSiteFunctor A X).map t) :=
  coherenceEvaluateSquare_naturality (coherenceEtaleFunctor A c)
    (coherenceBoundedSiteFunctor A Y) (coherenceBoundedSiteFunctor A X)
    (coherenceProEtaleFunctor A c) (coherenceBoundaryIso A c) t

private theorem compactification_change_square_component {X Y : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y] {f : X ⟶ Y}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c d : Compactification f)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (coherenceBoundedSiteFunctor A Y).map ((coherenceEtaleChangeIso A c d).hom.app L) ≫
        (coherenceBoundaryComponent A d L).hom =
      (coherenceBoundaryComponent A c L).hom ≫
        (coherenceCompactificationChange A c d L).hom := by
  exact compactification_change_square A c d L

private theorem chosen_composition_square_component {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g]
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (coherenceBoundedSiteFunctor A Z).map
        (coherenceChosenEtaleCompositorComponent A f g L).hom ≫
      (coherenceBoundaryComponent A (HasCompactification.compactification (f ≫ g)) L).hom =
    ((coherenceBoundaryComponent A (HasCompactification.compactification g)
        ((coherenceEtaleFunctor A (HasCompactification.compactification f)).obj L)).hom ≫
      (coherenceProEtaleFunctor A (HasCompactification.compactification g)).map
        (coherenceBoundaryComponent A (HasCompactification.compactification f) L).hom) ≫
      (coherenceChosenProEtaleCompositorComponent A f g L).hom := by
  exact chosen_composition_square A f g L

section
attribute [local irreducible] compactExchangeTransportComparison coherenceCompactificationChange
  originComposition originCompositionModel coherenceChosenProEtaleCompositorIso
  coherenceBoundaryIso coherenceEtaleChangeIso coherenceEtaleFunctor coherenceProEtaleFunctor
  coherenceSiteFunctor coherenceBoundedSiteFunctor
  Etale.rightDerivedLowerShriekOfCompactificationPlusIso
  Etale.rightDerivedLowerShriekPlusCompIso coherenceChosenEtaleCompositorIso
  coherenceBoundaryComponent coherenceChosenEtaleCompositorComponent
  coherenceChosenProEtaleCompositorComponent

private theorem composition_data_coherent {X Y Z : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    {f : X ⟶ Y} {g : Y ⟶ Z}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    (c : Compactification f) (d : Compactification g) (e : Compactification (f ≫ g))
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    let t := coherenceCompositionDataOfChoice A c d e L
    (coherenceBoundedSiteFunctor A Z).map t.etaleIso.hom ≫
      (coherenceBoundaryComponent A e L).hom =
    (coherenceCompositionSource A c d L).hom ≫ t.proMap := by
  let cf := HasCompactification.compactification f
  let dg := HasCompactification.compactification g
  let egf := HasCompactification.compactification (f ≫ g)
  let N₁ := coherenceBoundedSiteFunctor A Y
  let N₂ := coherenceBoundedSiteFunctor A Z
  let Fd := coherenceProEtaleFunctor A d
  let M := (coherenceEtaleFunctor A cf).obj L
  let ec := (coherenceEtaleChangeIso A c cf).hom.app L
  let Bc := coherenceBoundaryComponent A c L
  let Ba := coherenceBoundaryComponent A cf L
  let Rc := coherenceCompactificationChange A c cf L
  have hc : N₁.map ec ≫ Ba.hom = Bc.hom ≫ Rc.hom :=
    compactification_change_square_component A c cf L
  have hf := map_cancel_boundary Fd Ba Bc.hom Rc.hom (N₁.map ec) hc
  have hd := compactification_change_square_component A d dg M
  have he := compactification_change_square_component A egf e L
  have hn := boundary_component_naturality A d ec
  refine CoherencePastingData.coherent (coherenceCompositionDataOfChoice A c d e L)
    ?_ ?_ ?_ ?_ ?_ ?_
  · rfl
  · exact he
  · exact chosen_composition_square_component A f g L
  · exact hd
  · exact hn
  · exact hf

private theorem composition_site_square {X Y Z : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    {f : X ⟶ Y} {g : Y ⟶ Z}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (c : Compactification f) (d : Compactification g) (e : Compactification (f ≫ g))
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (coherenceBoundedSiteFunctor A Z).map
        (coherenceEtaleCompositorComponent A c d e L).hom ≫
      (coherenceBoundaryComponent A e L).hom =
    (coherenceCompositionSource A c d L).hom ≫ coherenceProEtaleCompositor A c d e L := by
  let := c.hasCompactification
  let := d.hasCompactification
  let := e.hasCompactification
  exact composition_data_coherent A c d e L

end

attribute [local irreducible] compactExchangeTransportComparison
  leftDerivedUpperStarComparisonIso properTransportRefinement properTransportRefinementPlus
  coherenceProEtaleCompositor coherenceEtaleCompositor originComposition
  properOpenProEtaleIsoPlus compactSupportSiteComparisonPlus compactSupportSiteComparison

end AlgebraicGeometry.ProEtale
