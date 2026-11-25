/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProperOpenCalculus.ProperOpenCalculus
public import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingProperOpenArrows
import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingProperOpenPasting
import WeilConjectures.AlgebraicGeometry.VaryingRing.SemilinearCompositorCoherence

/-! # Packaging the actual varying-ring proper/open calculus

Source: Stacks 0F7B--0F7D; the intrinsic varying-ring pasting theorem.
(blueprint: lem-sp-varying-ring-proper-open-model).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.VaryingRing

attribute [local irreducible] Iso.trans NatTrans.vcomp pComp jComp gComp pId jId gId adj jAdj gamma
  moduleAdj moduleJAdj modulePComp moduleGComp moduleJComp
  Functor.mapDerivedCategory Functor.rightDerivedFunctor

private theorem regroup_four {C : Type*} [Category* C]
    {A B C' D E F H : C} (a : A ⟶ B) (b : B ⟶ C') (c : C' ⟶ H)
    (d : A ⟶ D) (e : D ⟶ E) (f : E ⟶ F) (g : F ⟶ H)
    (h : a ≫ b ≫ c = d ≫ e ≫ f ≫ g) : a ≫ (b ≫ c) = (d ≫ e) ≫ (f ≫ g) := by
  simpa only [Category.assoc] using h

private theorem iso_trans_app {C D : Type*} [Category* C] [Category* D]
    {F G H : C ⥤ D} (i : F ≅ G) (j : G ≅ H) (M : C) :
    (i ≪≫ j).hom.app M = i.hom.app M ≫ j.hom.app M := by
  exact (NatTrans.congr_app (Iso.trans_hom i j) M).trans (NatTrans.comp_app _ _ M)

variable (R : ℕ → CommRingCat.{u + 1}) (φ : ∀ n, R (n + 1) ⟶ R n)

/-- Equality transport of open extension, including the open-immersion instance.
Source: Stacks 03DI (blueprint: lem-sp-varying-ring-proper-open-model). -/
def openCongr {X Y : Scheme.{u}} {f g : X ⟶ Y}
    [IsOpenImmersion f] [IsOpenImmersion g] (h : f = g) : J R φ f ≅ J R φ g := by
  subst g
  exact Iso.refl _

/-- Proper composition with a named composite, retained as a compact term.
Source: actual proper compositor (blueprint: lem-sp-varying-ring-proper-open-model). -/
@[irreducible] def namedPComp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z) (h : f ≫ g = fg) :
    P R φ f ⋙ P R φ g ≅ P R φ fg :=
  pComp R φ f g ≪≫ eqToIso (congrArg (P R φ) h)

/-- Open composition with a named composite, retained as a compact term.
Source: actual open compositor (blueprint: lem-sp-varying-ring-proper-open-model). -/
@[irreducible] def namedJComp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] [IsOpenImmersion fg] (h : f ≫ g = fg) :
    J R φ f ⋙ J R φ g ≅ J R φ fg :=
  jComp R φ f g ≪≫ openCongr R φ h

private theorem namedPComp_hom_app {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z) (h : f ≫ g = fg) (M : Derived R φ X) :
    (namedPComp R φ f g fg h).hom.app M =
      (pComp R φ f g).hom.app M ≫ (eqToIso (congrArg (P R φ) h)).hom.app M := by
  subst fg
  unfold namedPComp
  exact iso_trans_app _ _ M

private theorem namedJComp_hom_app {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] [IsOpenImmersion fg]
    (h : f ≫ g = fg) (M : Derived R φ X) :
    (namedJComp R φ f g fg h).hom.app M =
      (jComp R φ f g).hom.app M ≫
        (eqToIso (congrArg
          (fun a : {a : X ⟶ Z // IsOpenImmersion a} ↦ @J R φ _ _ a.val a.property)
          (@Subtype.ext (X ⟶ Z) (fun a ↦ IsOpenImmersion a)
            ⟨f ≫ g, inferInstance⟩ ⟨fg, inferInstance⟩ h))).hom.app M := by
  subst fg
  unfold namedJComp openCongr
  exact iso_trans_app _ _ M

/-- Reflexive named proper composition is the specified proper compositor.
Source: identity transport (blueprint: lem-sp-varying-ring-proper-open-model). -/
theorem namedPComp_rfl {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    namedPComp R φ f g (f ≫ g) rfl = pComp R φ f g := by
  unfold namedPComp
  exact Iso.trans_refl _

/-- Reflexive named open composition is the specified open compositor.
Source: identity transport (blueprint: lem-sp-varying-ring-proper-open-model). -/
theorem namedJComp_rfl {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] :
    namedJComp R φ f g (f ≫ g) rfl = jComp R φ f g := by
  unfold namedJComp openCongr
  exact Iso.trans_refl _

/-- The proper left unitor with the actual named compositor.
Source: compositor coherence (blueprint: lem-sp-varying-ring-proper-open-model). -/
theorem namedProperLeft {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Derived R φ X) :
    (namedPComp R φ (𝟙 X) f f (Category.id_comp f)).hom.app M =
      (P R φ f).map ((pId R φ X).hom.app M) := by
  rw [namedPComp_hom_app]
  exact (semilinear_compositor_coherence R φ).2.2.2.2.2.1 f M

/-- The proper right unitor with the actual named compositor.
Source: compositor coherence (blueprint: lem-sp-varying-ring-proper-open-model). -/
theorem namedProperRight {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Derived R φ X) :
    (namedPComp R φ f (𝟙 Y) f (Category.comp_id f)).hom.app M =
      (pId R φ Y).hom.app ((P R φ f).obj M) := by
  rw [namedPComp_hom_app]
  exact (semilinear_compositor_coherence R φ).2.2.2.2.2.2.1 f M

/-- The proper named-composite associativity equation.
Source: compositor coherence (blueprint: lem-sp-varying-ring-proper-open-model). -/
theorem namedProperAssoc {X Y Z W : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
    (fg : X ⟶ Z) (gh : Y ⟶ W) (fgh : X ⟶ W)
    (hfg : f ≫ g = fg) (hgh : g ≫ h = gh)
    (hl : fg ≫ h = fgh) (hr : f ≫ gh = fgh) (M : Derived R φ X) :
    (P R φ h).map ((namedPComp R φ f g fg hfg).hom.app M) ≫
      (namedPComp R φ fg h fgh hl).hom.app M =
    (namedPComp R φ g h gh hgh).hom.app ((P R φ f).obj M) ≫
      (namedPComp R φ f gh fgh hr).hom.app M := by
  simp only [namedPComp_hom_app]
  exact regroup_four _ _ _ _ _ _ _
    ((semilinear_compositor_coherence R φ).2.1 f g h fg gh fgh hfg hgh hl hr M)

/-- The open left unitor with the actual named compositor.
Source: compositor coherence (blueprint: lem-sp-varying-ring-proper-open-model). -/
theorem namedOpenLeft {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (M : Derived R φ X) :
    (namedJComp R φ (𝟙 X) f f (Category.id_comp f)).hom.app M =
      (J R φ f).map ((jId R φ X).hom.app M) := by
  rw [namedJComp_hom_app]
  exact (semilinear_compositor_coherence R φ).2.2.2.2.2.2.2.1 f M

/-- The open right unitor with the actual named compositor.
Source: compositor coherence (blueprint: lem-sp-varying-ring-proper-open-model). -/
theorem namedOpenRight {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (M : Derived R φ X) :
    (namedJComp R φ f (𝟙 Y) f (Category.comp_id f)).hom.app M =
      (jId R φ Y).hom.app ((J R φ f).obj M) := by
  rw [namedJComp_hom_app]
  exact (semilinear_compositor_coherence R φ).2.2.2.2.2.2.2.2 f M

/-- The open named-composite associativity equation.
Source: compositor coherence (blueprint: lem-sp-varying-ring-proper-open-model). -/
theorem namedOpenAssoc {X Y Z W : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
    (fg : X ⟶ Z) (gh : Y ⟶ W) (fgh : X ⟶ W)
    [IsOpenImmersion f] [IsOpenImmersion g] [IsOpenImmersion h]
    [IsOpenImmersion fg] [IsOpenImmersion gh] [IsOpenImmersion fgh]
    (hfg : f ≫ g = fg) (hgh : g ≫ h = gh)
    (hl : fg ≫ h = fgh) (hr : f ≫ gh = fgh) (M : Derived R φ X) :
    (J R φ h).map ((namedJComp R φ f g fg hfg).hom.app M) ≫
      (namedJComp R φ fg h fgh hl).hom.app M =
    (namedJComp R φ g h gh hgh).hom.app ((J R φ f).obj M) ≫
      (namedJComp R φ f gh fgh hr).hom.app M := by
  have ht := (semilinear_compositor_coherence R φ).2.2.1
    f g h fg gh fgh hfg hgh hl hr M
  subst fg gh fgh
  simp only [namedJComp_hom_app]
  exact regroup_four _ _ _ _ _ _ _ ht

universe v w

set_option linter.checkUnivs false in
/-- The functor data underlying a proper/open calculus, retaining both universes.
Source: Stacks 0F7B--0F7D (blueprint: lem-sp-varying-ring-proper-open-model). -/
structure ProperOpenInputs (A : Scheme.{u} → Prop) where
  obj : {X : Scheme.{u} // A X} → Type w
  [category (X : {X : Scheme.{u} // A X}) : Category.{v} (obj X)]
  P (X Y : {X : Scheme.{u} // A X}) (p : X.1 ⟶ Y.1) [IsProper p] : obj X ⥤ obj Y
  J (X Y : {X : Scheme.{u} // A X}) (j : X.1 ⟶ Y.1)
    [IsOpenImmersion j] [QuasiCompact j] : obj X ⥤ obj Y
  pId (X : {X : Scheme.{u} // A X}) : P X X (𝟙 X.1) ≅ 𝟭 (obj X)
  jId (X : {X : Scheme.{u} // A X}) : J X X (𝟙 X.1) ≅ 𝟭 (obj X)
  pComp (X Y Z : {X : Scheme.{u} // A X})
    (f : X.1 ⟶ Y.1) (g : Y.1 ⟶ Z.1) (fg : X.1 ⟶ Z.1)
    [IsProper f] [IsProper g] [IsProper fg] (_h : f ≫ g = fg) :
    P X Y f ⋙ P Y Z g ≅ P X Z fg
  jComp (X Y Z : {X : Scheme.{u} // A X})
    (f : X.1 ⟶ Y.1) (g : Y.1 ⟶ Z.1) (fg : X.1 ⟶ Z.1)
    [IsOpenImmersion f] [IsOpenImmersion g] [IsOpenImmersion fg]
    [QuasiCompact f] [QuasiCompact g] [QuasiCompact fg] (_h : f ≫ g = fg) :
    J X Y f ⋙ J Y Z g ≅ J X Z fg
  gamma (U V W Z : {X : Scheme.{u} // A X})
    (k : U.1 ⟶ V.1) (r : U.1 ⟶ W.1) (p : V.1 ⟶ Z.1) (i : W.1 ⟶ Z.1)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p]
    (_h : k ≫ p = r ≫ i) : P U W r ⋙ J W Z i ≅ J U V k ⋙ P V Z p

attribute [instance] ProperOpenInputs.category

/-- The proper/open equations, referring to one fixed record of functor data.
Source: Stacks 0F7B--0F7D (blueprint: lem-sp-varying-ring-proper-open-model). -/
structure ProperOpenEquations {A : Scheme.{u} → Prop}
    (D : ProperOpenInputs.{u, v, w} A) : Prop where
  pAssoc (X Y Z W : {X : Scheme.{u} // A X})
    (f : X.1 ⟶ Y.1) (g : Y.1 ⟶ Z.1) (h : Z.1 ⟶ W.1)
    (fg : X.1 ⟶ Z.1) (gh : Y.1 ⟶ W.1) (fgh : X.1 ⟶ W.1)
    [IsProper f] [IsProper g] [IsProper h]
    [IsProper fg] [IsProper gh] [IsProper fgh]
    (hfg : f ≫ g = fg) (hgh : g ≫ h = gh)
    (hl : fg ≫ h = fgh) (hr : f ≫ gh = fgh) (M : D.obj X) :
    (D.P Z W h).map ((D.pComp X Y Z f g fg hfg).hom.app M) ≫
        (D.pComp X Z W fg h fgh hl).hom.app M =
      (D.pComp Y Z W g h gh hgh).hom.app ((D.P X Y f).obj M) ≫
        (D.pComp X Y W f gh fgh hr).hom.app M
  pLeft (X Y : {X : Scheme.{u} // A X}) (f : X.1 ⟶ Y.1)
    [IsProper f] (M : D.obj X) :
    (D.pComp X X Y (𝟙 X.1) f f (Category.id_comp f)).hom.app M =
      (D.P X Y f).map ((D.pId X).hom.app M)
  pRight (X Y : {X : Scheme.{u} // A X}) (f : X.1 ⟶ Y.1)
    [IsProper f] (M : D.obj X) :
    (D.pComp X Y Y f (𝟙 Y.1) f (Category.comp_id f)).hom.app M =
      (D.pId Y).hom.app ((D.P X Y f).obj M)
  jAssoc (X Y Z W : {X : Scheme.{u} // A X})
    (f : X.1 ⟶ Y.1) (g : Y.1 ⟶ Z.1) (h : Z.1 ⟶ W.1)
    (fg : X.1 ⟶ Z.1) (gh : Y.1 ⟶ W.1) (fgh : X.1 ⟶ W.1)
    [IsOpenImmersion f] [IsOpenImmersion g] [IsOpenImmersion h]
    [QuasiCompact f] [QuasiCompact g] [QuasiCompact h]
    [IsOpenImmersion fg] [IsOpenImmersion gh] [IsOpenImmersion fgh]
    [QuasiCompact fg] [QuasiCompact gh] [QuasiCompact fgh]
    (hfg : f ≫ g = fg) (hgh : g ≫ h = gh)
    (hl : fg ≫ h = fgh) (hr : f ≫ gh = fgh) (M : D.obj X) :
    (D.J Z W h).map ((D.jComp X Y Z f g fg hfg).hom.app M) ≫
        (D.jComp X Z W fg h fgh hl).hom.app M =
      (D.jComp Y Z W g h gh hgh).hom.app ((D.J X Y f).obj M) ≫
        (D.jComp X Y W f gh fgh hr).hom.app M
  jLeft (X Y : {X : Scheme.{u} // A X}) (f : X.1 ⟶ Y.1)
    [IsOpenImmersion f] [QuasiCompact f] (M : D.obj X) :
    (D.jComp X X Y (𝟙 X.1) f f (Category.id_comp f)).hom.app M =
      (D.J X Y f).map ((D.jId X).hom.app M)
  jRight (X Y : {X : Scheme.{u} // A X}) (f : X.1 ⟶ Y.1)
    [IsOpenImmersion f] [QuasiCompact f] (M : D.obj X) :
    (D.jComp X Y Y f (𝟙 Y.1) f (Category.comp_id f)).hom.app M =
      (D.jId Y).hom.app ((D.J X Y f).obj M)
  vertical (U V W Z E F : {X : Scheme.{u} // A X})
    (k : U.1 ⟶ V.1) (i : W.1 ⟶ Z.1) (j : E.1 ⟶ F.1)
    (r₁ : U.1 ⟶ W.1) (r₂ : W.1 ⟶ E.1) (p₁ : V.1 ⟶ Z.1) (p₂ : Z.1 ⟶ F.1)
    [IsOpenImmersion k] [IsOpenImmersion i] [IsOpenImmersion j]
    [QuasiCompact k] [QuasiCompact i] [QuasiCompact j]
    [IsProper r₁] [IsProper r₂] [IsProper p₁] [IsProper p₂]
    (h₁ : k ≫ p₁ = r₁ ≫ i) (h₂ : i ≫ p₂ = r₂ ≫ j)
    (h : k ≫ (p₁ ≫ p₂) = (r₁ ≫ r₂) ≫ j) (M : D.obj U) :
    (D.J E F j).map ((D.pComp U W E r₁ r₂ (r₁ ≫ r₂) rfl).hom.app M) ≫
        (D.gamma U V E F k (r₁ ≫ r₂) (p₁ ≫ p₂) j h).hom.app M ≫
        (D.pComp V Z F p₁ p₂ (p₁ ≫ p₂) rfl).inv.app ((D.J U V k).obj M) =
      (D.gamma W Z E F i r₂ p₂ j h₂).hom.app ((D.P U W r₁).obj M) ≫
        (D.P Z F p₂).map ((D.gamma U V W Z k r₁ p₁ i h₁).hom.app M)
  horizontal (U V E W Z F : {X : Scheme.{u} // A X})
    (k : U.1 ⟶ V.1) (l : V.1 ⟶ E.1) (i : W.1 ⟶ Z.1) (j : Z.1 ⟶ F.1)
    (r : U.1 ⟶ W.1) (p : V.1 ⟶ Z.1) (q : E.1 ⟶ F.1)
    [IsOpenImmersion k] [IsOpenImmersion l] [IsOpenImmersion i] [IsOpenImmersion j]
    [QuasiCompact k] [QuasiCompact l] [QuasiCompact i] [QuasiCompact j]
    [IsProper r] [IsProper p] [IsProper q]
    (h₁ : k ≫ p = r ≫ i) (h₂ : l ≫ q = p ≫ j)
    (h : (k ≫ l) ≫ q = r ≫ (i ≫ j)) (M : D.obj U) :
    (D.jComp W Z F i j (i ≫ j) rfl).hom.app ((D.P U W r).obj M) ≫
        (D.gamma U E W F (k ≫ l) r q (i ≫ j) h).hom.app M ≫
        (D.P E F q).map ((D.jComp U V E k l (k ≫ l) rfl).inv.app M) =
      (D.J Z F j).map ((D.gamma U V W Z k r p i h₁).hom.app M) ≫
        (D.gamma V E Z F l p q j h₂).hom.app ((D.J U V k).obj M)
  verticalIdentity (U V : {X : Scheme.{u} // A X}) (j : U.1 ⟶ V.1)
    [IsOpenImmersion j] [QuasiCompact j] (h : j ≫ 𝟙 V.1 = 𝟙 U.1 ≫ j) (M : D.obj U) :
    (D.gamma U V U V j (𝟙 U.1) (𝟙 V.1) j h).hom.app M ≫
        (D.pId V).hom.app ((D.J U V j).obj M) =
      (D.J U V j).map ((D.pId U).hom.app M)
  horizontalIdentity (U V : {X : Scheme.{u} // A X}) (p : U.1 ⟶ V.1)
    [IsProper p] (h : (𝟙 U.1) ≫ p = p ≫ 𝟙 V.1) (M : D.obj U) :
    (D.gamma U U V V (𝟙 U.1) p p (𝟙 V.1) h).hom.app M ≫
        (D.P U V p).map ((D.jId U).hom.app M) =
      (D.jId V).hom.app ((D.P U V p).obj M)

/-- Combining the supplied functors with their equations gives the calculus.
Source: the defining fields of ProperOpenCalculus
(blueprint: lem-sp-varying-ring-proper-open-model). -/
def assembleProperOpen {A : Scheme.{u} → Prop} (D : ProperOpenInputs.{u, v, w} A)
    (L : ProperOpenEquations D) : ProperOpenCalculus.{u, v, w} A where
  obj := D.obj
  category := D.category
  P := D.P
  J := D.J
  pId := D.pId
  jId := D.jId
  pComp := D.pComp
  pAssoc := L.pAssoc
  pLeft := L.pLeft
  pRight := L.pRight
  jComp := D.jComp
  jAssoc := L.jAssoc
  jLeft := L.jLeft
  jRight := L.jRight
  gamma := D.gamma
  vertical := L.vertical
  horizontal := L.horizontal
  verticalIdentity := L.verticalIdentity
  horizontalIdentity := L.horizontalIdentity

/-- The actual derived functors and their specified comparison isomorphisms.
Source: Stacks 0F7B--0F7D (blueprint: lem-sp-varying-ring-proper-open-model). -/
def actualProperOpenInputs (A : Scheme.{u} → Prop)
    (hgamma : ∀ {U V W Z : Scheme.{u}}
      (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
      [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
      [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i),
      IsIso (gamma R φ k r p i h)) : ProperOpenInputs A where
  obj X := Derived R φ X.val
  P _X _Y p := P R φ p
  J _X _Y j := J R φ j
  pId X := pId R φ X.val
  jId X := jId R φ X.val
  pComp _X _Y _Z f g fg _ _ _ h := namedPComp R φ f g fg h
  jComp _X _Y _Z f g fg _ _ _ _ _ _ h := namedJComp R φ f g fg h
  gamma _U _V _W _Z k r p i _ _ _ _ _ _ h :=
    @asIso _ _ _ _ (gamma R φ k r p i h) (hgamma k r p i h)

/-- The actual proper/open data satisfy all the defining equations.
Source: intrinsic pasting and semilinear compositor coherence
(blueprint: lem-sp-varying-ring-proper-open-model).

Proof: use the named-composite associativity and unit lemmas. On reflexive
composites, the named maps reduce to the original compositors. After unfolding
only the data record, the two pasting and two identity equations are exactly
properOpenPasting and gamma_identities; asIso retains the original hom map. -/
theorem actualProperOpenEquations (A : Scheme.{u} → Prop)
    (hgamma : ∀ {U V W Z : Scheme.{u}}
      (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
      [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
      [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i),
      IsIso (gamma R φ k r p i h))
    : ProperOpenEquations (actualProperOpenInputs R φ A hgamma) := by
  exact {
    pAssoc X Y Z W f g h fg gh fgh _ _ _ _ _ _ hfg hgh hl hr M := by
      subst fg gh fgh
      exact namedProperAssoc R φ f g h (f ≫ g) (g ≫ h) ((f ≫ g) ≫ h)
        rfl rfl rfl (Category.assoc f g h).symm M,
    pLeft X Y f _ M := by
      exact namedProperLeft R φ f M,
    pRight X Y f _ M := by
      exact namedProperRight R φ f M,
    jAssoc X Y Z W f g h fg gh fgh _ _ _ _ _ _ _ _ _ _ _ _ hfg hgh hl hr M := by
      subst fg gh fgh
      exact namedOpenAssoc R φ f g h (f ≫ g) (g ≫ h) ((f ≫ g) ≫ h)
        rfl rfl rfl (Category.assoc f g h).symm M,
    jLeft X Y f _ _ M := by
      exact namedOpenLeft R φ f M,
    jRight X Y f _ _ M := by
      exact namedOpenRight R φ f M,
    vertical U V W Z E F k i j r₁ r₂ p₁ p₂ _ _ _ _ _ _ _ _ _ _ h₁ h₂ h M := by
      dsimp only [actualProperOpenInputs]
      simpa only [namedPComp_rfl, asIso_hom] using
        (properOpenPasting R φ).1 k i j r₁ r₂ p₁ p₂ h₁ h₂ h M,
    horizontal U V E W Z F k l i j r p q _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ h M := by
      dsimp only [actualProperOpenInputs]
      simpa only [namedJComp_rfl, asIso_hom] using
        (properOpenPasting R φ).2 k l i j r p q h₁ h₂ h M,
    verticalIdentity U V j _ _ h M := by
      dsimp only [actualProperOpenInputs]
      simpa only [asIso_hom] using (gamma_identities R φ).1 j h M,
    horizontalIdentity U V p _ h M := by
      dsimp only [actualProperOpenInputs]
      simpa only [asIso_hom] using (gamma_identities R φ).2 p h M }

/-- Invertibility is the only additional input to the existing proper/open equations.
All functors and maps are the actual varying-ring constructions.
Source: Stacks 0F7B--0F7D
(blueprint: lem-sp-varying-ring-proper-open-model).

Proof: use the actual direct images, open extensions and their specified identity
and composition comparisons. Turn the specified gamma into an isomorphism using
its invertibility, without choosing a different arrow. The named-composite
associativity and unit equations are precisely semilinear compositor coherence.
The proper/open vertical, horizontal and identity equations are the existing
pasting equations. Restricting the scheme index to any predicate changes none
of these maps or equations. -/
def properOpenModel (A : Scheme.{u} → Prop)
    (hgamma : ∀ {U V W Z : Scheme.{u}}
      (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
      [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
      [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i),
      IsIso (gamma R φ k r p i h)) : ProperOpenCalculus A :=
  assembleProperOpen (actualProperOpenInputs R φ A hgamma) (actualProperOpenEquations R φ A hgamma)

end AlgebraicGeometry.ProEtale.VaryingRing
