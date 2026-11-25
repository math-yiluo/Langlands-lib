/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Open.OpenImmersionSquare
public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.ExactDerivedAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.Ringed.RingedProjectionRestriction
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.AlgebraicGeometry.ProEtale.Derived.ProEtaleDerivedExtensionZeroBaseChange
public import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenUnitEvaluation
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriekProj
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck

/-!
# Data for normalized open extension, tensor and base change

Source: Stacks 03DI, 0F6Z, 0E8I, 0GL1 and the open-factor sentence of
`fix-prop-coherence` (blueprint: lem-sf-open-tensor-normalization).
All operation presentations below are conclusions of the theorem, not hypotheses.
-/

-- Owning definition node (blueprint: def-sf-open-normalization-data).

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option backward.isDefEq.respectTransparency true
set_option synthInstance.maxSize 4096
set_option linter.checkUnivs false

universe u v h w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProjectionRestriction

namespace SheafOfModules.OpenTensorNormalization

/-- The ordinary site and the ringed diagram site of strict inverse systems.
The latter has arbitrary ring sheaves, hence arbitrary, possibly nonflat,
coefficient transitions. Source: Stacks 00Z4; blueprint open-factor refinement.
(blueprint: lem-sf-open-tensor-normalization). -/
inductive Mode | ordinary | systems

/-- The diagram site uses the category of increasing natural numbers; a presheaf
therefore has transitions from level `n+1` to level `n`.
Source: Stacks 00Z4; blueprint open-factor refinement.
(blueprint: lem-sf-open-tensor-normalization). -/
def Site (m : Mode) (X : Scheme.{u}) : Type (u + 1) :=
  match m with
  | .ordinary => X.ProEt
  | .systems => ℕ × X.ProEt

/-- The site category instance for ordinary and vertical sites.
Source: the product-site construction (blueprint: lem-sf-open-tensor-normalization). -/
instance (m : Mode) (X : Scheme.{u}) : Category.{u} (Site m X) := by
  cases m <;> dsimp [Site] <;> infer_instance

/-- Vertical covering families generate the diagram topology; no covering in
the coefficient direction is imposed. Source: Stacks 00Z4, 00Z8.
(blueprint: lem-sf-open-tensor-normalization). -/
def verticalCoverage (X : Scheme.{u}) : Precoverage (ℕ × X.ProEt) where
  coverings W := {P | ∃ S : Sieve W.2, S ∈ ProEt.topology X W.2 ∧
    P = fun V a => V.1 = W.1 ∧ S a.2}

/-- The original pro-etale topology, or its vertical diagram topology.
Source: Stacks 00Z4 and 09A5; blueprint open-factor refinement.
(blueprint: lem-sf-open-tensor-normalization). -/
def topology (m : Mode) (X : Scheme.{u}) : GrothendieckTopology (Site m X) :=
  match m with
  | .ordinary => ProEt.topology X
  | .systems => (verticalCoverage X).toGrothendieck

/-- Forget the coefficient index. Source: Stacks 00Z4.
(blueprint: lem-sf-open-tensor-normalization). -/
def forgetIndex (m : Mode) (X : Scheme.{u}) : Site m X ⥤ X.ProEt :=
  match m with
  | .ordinary => 𝟭 _
  | .systems => CategoryTheory.Prod.snd _ _

/-- Base change at every coefficient index. Source: Stacks 09A5, 00Z4.
(blueprint: lem-sf-open-tensor-normalization). -/
def baseChange (m : Mode) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Site m Y ⥤ Site m X :=
  match m with
  | .ordinary => proEtaleBaseChange f
  | .systems => (𝟭 ℕ).prod (proEtaleBaseChange f)

/-- Postcomposition with an open immersion on the site, termwise for systems.
Source: Stacks 0F6Z and 09A5.
(blueprint: lem-sf-open-tensor-normalization). -/
def openInclusion (m : Mode) {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] : Site m U ⥤ Site m X :=
  match m with
  | .ordinary => proEtaleOpenComposition j
  | .systems => (𝟭 ℕ).prod
      (proEtaleOpenComposition j)

-- The following vertical-sieve calculation is the universe-independent version of
-- DiagramSiteTopology: Stacks 00Z4 and 00Z8. Only proof helpers are introduced.
set_option backward.isDefEq.respectTransparency false in
private def verticalTopology (C : Type (u + 1)) [Category.{u} C]
    (K : GrothendieckTopology C) : GrothendieckTopology (ℕ × C) where
  sieves X := {S | S.functorPullback (Prod.sectR X.1 C) ∈ K X.2}
  top_mem' X := by
    change (⊤ : Sieve X.2) ∈ K X.2
    exact K.top_mem _
  pullback_stable' {X Y} {S} f hS := by
    apply K.superset_covering _ (K.pullback_stable f.2 hS)
    intro Z g hg
    change S (Prod.mkHom (𝟙 Y.1) g ≫ f)
    change S (Prod.mkHom (𝟙 X.1) (g ≫ f.2)) at hg
    simpa using S.downward_closed hg (Prod.mkHom f.1 (𝟙 Z))
  transitive' {X} {S} hS R hR := by
    apply K.transitive hS
    intro Y f hf
    have H := hR (show S ((Prod.sectR X.1 C).map f) from hf)
    change (R.pullback ((Prod.sectR X.1 C).map f)).functorPullback
      (Prod.sectR X.1 C) ∈ K Y at H
    rwa [Sieve.functorPullback_pullback] at H

set_option backward.isDefEq.respectTransparency false in
private theorem verticalSheaf_iff
    (C : Type (u + 1)) [Category.{u} C]
    (K : GrothendieckTopology C) (P : (ℕ × C)ᵒᵖ ⥤ Type (u + 1)) :
    Presieve.IsSheaf (verticalTopology C K) P ↔
      ∀ j : ℕ, Presieve.IsSheaf K ((Prod.sectR j C).op ⋙ P) := by
  constructor
  · intro hP j U S hS x hx
    let R : Sieve (j, U) := S.functorPullback (X := (j, U)) (CategoryTheory.Prod.snd ℕ C)
    have hR : R ∈ verticalTopology C K (j, U) := by
      change S ∈ K U
      exact hS
    let y : Presieve.FamilyOfElements P R.arrows := fun Y f hf ↦
      P.map (Prod.mkHom f.1 (𝟙 Y.2)).op (x f.2 hf)
    have hy : y.Compatible := by
      apply (Presieve.compatible_iff_sieveCompatible y).2
      rintro ⟨y₀, V₁⟩ ⟨z, W⟩ f g hf
      have H := hx.to_sieveCompatible f.2 g.2 hf
      dsimp only [y, Prod.sectR, Functor.comp_map, Functor.op_map] at H ⊢
      simp only [prod_comp_fst, prod_comp_snd]
      change P.map (Prod.mkHom (g.1 ≫ f.1) (𝟙 W)).op (x (g.2 ≫ f.2) _) = _
      rw [H]
      change (P.map (Prod.mkHom (𝟙 j) g.2).op ≫
        P.map (Prod.mkHom (g.1 ≫ f.1) (𝟙 W)).op) (x f.2 hf) =
        (P.map (Prod.mkHom f.1 (𝟙 V₁)).op ≫ P.map g.op) (x f.2 hf)
      rw [← P.map_comp, ← P.map_comp, ← op_comp, ← op_comp]
      congr 2
      ext; simp
    obtain ⟨t, ht, hut⟩ := hP R hR y hy
    refine ⟨t, ?_, ?_⟩
    · intro V f hf
      have H := ht ((Prod.sectR j C).map f) hf
      simpa [y, Prod.sectR, ← prod_id] using H
    · intro t' ht'
      change P.obj (op (j, U)) at t'
      apply hut t'
      rintro ⟨k, V₁⟩ f hf
      dsimp only [y]
      have H := ht' f.2 hf
      dsimp only [Prod.sectR, Functor.comp_map, Functor.op_map] at H
      rw [← H]
      change P.map f.op t' = (P.map (Prod.mkHom (𝟙 j) f.2).op ≫
        P.map (Prod.mkHom f.1 (𝟙 V₁)).op) t'
      rw [← P.map_comp, ← op_comp]
      congr 2
      ext; simp
  · rintro hP ⟨j, U⟩ R hR x hx
    let V := Prod.sectR j C
    have hV := hP j (R.functorPullback V) hR
    obtain ⟨t, ht, hut⟩ := hV (x.functorPullback V) (hx.functorPullback V)
    refine ⟨t, ?_, ?_⟩
    · rintro ⟨k, V₀⟩ f hf
      apply ((hP k).isSeparated (Sieve.pullback f.2 (R.functorPullback V))
        (K.pullback_stable f.2 hR)).ext
      intro Z g hg
      change P.map (Prod.mkHom (𝟙 k) g).op (P.map f.op t) =
        P.map (Prod.mkHom (𝟙 k) g).op (x f hf)
      have H := hx (Prod.mkHom f.1 (𝟙 Z)) (Prod.mkHom (𝟙 k) g) hg hf
        (by ext <;> simp [V])
      have ht₀ := ht (g ≫ f.2) hg
      change P.map (V.map (g ≫ f.2)).op t = x (V.map (g ≫ f.2)) hg at ht₀
      rw [← H, ← ht₀]
      dsimp only [Prod.sectR, V]
      simp only [← Functor.map_comp_apply, ← op_comp]
      congr 1
      simp
    · intro t' ht'
      apply hut t'
      intro Y f hf
      exact ht' (V.map f) hf

private theorem topology_systems_eq (X : Scheme.{u}) :
    topology .systems X = verticalTopology X.ProEt (ProEt.topology X) := by
  apply le_antisymm
  · apply Precoverage.toGrothendieck_le_iff_le_toPrecoverage.mpr
    intro W P hP
    obtain ⟨S, hS, rfl⟩ := hP
    apply (ProEt.topology X).superset_covering _ hS
    intro V f hf
    exact Sieve.le_generate _ _ _ (show W.1 = W.1 ∧ S f from ⟨rfl, hf⟩)
  · intro W S hS
    let P : Presieve W := fun V a ↦ V.1 = W.1 ∧
      S ((Prod.sectR W.1 X.ProEt).map a.2)
    have hP : P ∈ verticalCoverage X W :=
      ⟨S.functorPullback (Prod.sectR W.1 X.ProEt), hS, rfl⟩
    apply (topology .systems X).superset_covering _
      (Precoverage.generate_mem_toGrothendieck hP)
    apply (Sieve.generate_le_iff _ _).mpr
    rintro ⟨n, V⟩ f ⟨hn, hf⟩
    dsimp only at hn
    subst n
    have hfmap : (Prod.sectR W.1 X.ProEt).map f.2 = f := by
      ext
      · exact Subsingleton.elim _ _
      · rfl
    rwa [hfmap] at hf

private theorem system_continuous {X Y : Scheme.{u}} (F : X.ProEt ⥤ Y.ProEt)
    [F.IsContinuous (ProEt.topology X) (ProEt.topology Y)] :
    ((𝟭 ℕ).prod F).IsContinuous (topology .systems X) (topology .systems Y) := by
  rw [topology_systems_eq X, topology_systems_eq Y]
  constructor
  intro G
  apply (verticalSheaf_iff X.ProEt (ProEt.topology X) _).2
  intro n
  have hG := (verticalSheaf_iff Y.ProEt (ProEt.topology Y) G.obj).1
    ((isSheaf_iff_isSheaf_of_type _ _).1 G.property) n
  have h := F.op_comp_isSheaf_of_isSheaf_type (ProEt.topology X) hG
  exact h

/-- Continuity is tested on the vertical covering families and follows from
continuity of pro-etale base change; the coefficient index is unchanged.
Source: Stacks 09A5 and 00Z4 (blueprint: lem-sf-open-tensor-normalization). -/
theorem baseChange_continuous (m : Mode) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (baseChange m f).IsContinuous (topology m Y) (topology m X) := by
  cases m with
  | ordinary => exact proEtaleBaseChange_isContinuous f
  | systems => exact system_continuous (proEtaleBaseChange f)

/-- Open postcomposition preserves sheaves, since coverings and sections are
those on the localized site. The same check is vertical for systems.
Source: Stacks 0F6Z, 00Z4 (blueprint: lem-sf-open-tensor-normalization). -/
theorem openInclusion_continuous (m : Mode) {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] :
    (openInclusion m j).IsContinuous (topology m U) (topology m X) := by
  have : (proEtaleOpenComposition j).IsContinuous (ProEt.topology U) (ProEt.topology X) :=
    ProEt.isContinuous_overMap (inferInstance : WeaklyEtale j)
  cases m with
  | ordinary => exact this
  | systems => exact system_continuous (proEtaleOpenComposition j)

attribute [instance] baseChange_continuous openInclusion_continuous

/-- Restriction of rings is literal restriction of sections along the open.
It canonically represents `j⁻¹ R`. Source: Stacks 0F6Z.
(blueprint: lem-sf-open-tensor-normalization). -/
abbrev restrictRing (m : Mode) {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (R : Sheaf (topology m X) CommRingCat.{u + 1}) :=
  ((openInclusion m j).sheafPushforwardContinuous CommRingCat.{u + 1}
    (topology m U) (topology m X)).obj R

/-- Open restriction on modules keeps their section modules and restriction
maps. Source: Stacks 0F6Z, 03DJ.
(blueprint: lem-sf-open-tensor-normalization). -/
def restrict (m : Mode) {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (R : Sheaf (topology m X) CommRingCat.{u + 1}) :
    Mod R ⥤ Mod (restrictRing m j R) :=
  SheafOfModules.pushforward.{u + 1} (F := openInclusion m j) (𝟙 _)

/-- The sectionwise module direct image, with the prescribed ring map.
Source: Stacks 03D7, 04J0.
(blueprint: lem-sf-open-tensor-normalization). -/
def direct (m : Mode) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (topology m Y) CommRingCat.{u + 1})
    (S : Sheaf (topology m X) CommRingCat.{u + 1})
    (c : R ⟶ ((baseChange m f).sheafPushforwardContinuous CommRingCat.{u + 1}
      (topology m Y) (topology m X)).obj S) : Mod S ⥤ Mod R :=
  SheafOfModules.pushforward.{u + 1} (F := baseChange m f)
    ⟨Functor.whiskerRight c.hom (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩

/-- A left adjoint to the specified sectionwise direct image, together with
its total left derived functor. Universal properties determine these objects
up to their unique compatible isomorphisms; no exactness of scalar extension
is asserted. Source: Stacks 03D7, 07A4.
(blueprint: lem-sf-open-tensor-normalization). -/
structure Pullback {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (R : Sheaf J CommRingCat.{u + 1}) (S : Sheaf K CommRingCat.{u + 1})
    (V : Mod S ⥤ Mod R) where
  ordinary : Mod R ⥤ Mod S
  adjunction : ordinary ⊣ V
  [additive : ordinary.Additive]
  derived : Der R ⥤ Der S
  epsilon : DerivedCategory.Qh ⋙ derived ⟶
    ordinary.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh
  universal : derived.IsLeftDerivedFunctor epsilon
    (HomotopyCategory.quasiIso (Mod R) (.up ℤ))
  flat : ∀ P : CochainComplex (Mod R) ℤ, resolving R P →
    IsIso (derivedPullbackComplexComparison ordinary derived epsilon P)

attribute [instance] Pullback.additive

/-- An exact open extension, specified as the left adjoint to the actual
restriction of section modules. Source: Stacks 03DI, 03DJ.
(blueprint: lem-sf-open-tensor-normalization). -/
structure OpenExtension (m : Mode) {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (R : Sheaf (topology m X) CommRingCat.{u + 1}) where
  ordinary : Mod (restrictRing m j R) ⥤ Mod R
  adjunction : ordinary ⊣ restrict m j R
  /-- Canonical identification of the restriction of the extension with its
  original sectionwise module. -/
  sectionIso : ∀ M : Mod (restrictRing m j R),
    (restrict m j R).obj (ordinary.obj M) ≅ M
  /-- The open unit is the identity under the canonical section identification. -/
  sectionUnit : ∀ M : Mod (restrictRing m j R),
    adjunction.unit.app M ≫ (sectionIso M).hom = 𝟙 M
  [additive : ordinary.Additive]
  [limits : PreservesFiniteLimits ordinary]
  [colimits : PreservesFiniteColimits ordinary]

attribute [instance] OpenExtension.additive OpenExtension.limits OpenExtension.colimits

/-- Only the geometry and coefficient map are input. The displayed map is
adjoint to `g⁻¹R ⟶ S`. Source: Stacks 03D7, 0GL1.
(blueprint: lem-sf-open-tensor-normalization). -/
structure Input (m : Mode) where
  U : Scheme.{u}
  U' : Scheme.{u}
  X : Scheme.{u}
  X' : Scheme.{u}
  gU : U' ⟶ U
  j' : U' ⟶ X'
  j : U ⟶ X
  g : X' ⟶ X
  square : OpenImmersionSquare gU j' j g
  j_open : IsOpenImmersion j := square.isOpenImmersion
  j'_open : IsOpenImmersion j' := square.isOpenImmersion'
  R : Sheaf (topology m X) CommRingCat.{u + 1}
  S : Sheaf (topology m X') CommRingCat.{u + 1}
  coefficient : R ⟶ ((baseChange m g).sheafPushforwardContinuous CommRingCat.{u + 1}
    (topology m X) (topology m X')).obj S

/-- Convert precisely the inverse-image ring map in the node into its
adjoint sectionwise form, without assuming the ring map invertible or flat.
Source: Stacks 03D7; the recorded pro-etale sheaf adjunction
(blueprint: lem-sf-open-tensor-normalization). -/
def ordinaryInput {U' U X' X : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) (sq : OpenImmersionSquare gU j' j g)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X') CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj R ⟶ S) :
    Input .ordinary where
  U := U
  U' := U'
  X := X
  X' := X'
  gU := gU
  j' := j'
  j := j
  g := g
  square := sq
  R := R
  S := S
  coefficient := (proEtaleSheafAdjunction g CommRingCat.{u + 1}).unit.app R ≫
    (proEtaleSheafDirectImage g CommRingCat.{u + 1}).map c

/-- The open condition is inherited from the chosen square. Source: Stacks 03S6
(blueprint: lem-sf-open-tensor-normalization). -/
instance {m : Mode} (d : Input.{u} m) : IsOpenImmersion d.j := d.j_open
/-- The ambient open-immersion instance inherited from the chosen square.
Source: `OpenImmersionSquare` (blueprint: lem-sf-open-tensor-normalization). -/
instance {m : Mode} (d : Input.{u} m) : IsOpenImmersion d.j' := d.j'_open

/-- First fibre-product projection, with the coefficient index unchanged.
Source: Stacks 09A5.
(blueprint: lem-sf-open-tensor-normalization). -/
def baseFirst (m : Mode) {X Y : Scheme.{u}} (f : X ⟶ Y) (W : Site m Y) :
    ((forgetIndex m X).obj ((baseChange m f).obj W)).left ⟶
      ((forgetIndex m Y).obj W).left := by
  cases m with
  | ordinary => exact pullback.fst W.hom f
  | systems => exact pullback.fst W.2.hom f

/-- The site comparison is fixed by the first projection and by being a map
over `X'` (the second projection). These characterize the fibre-product map.
Source: Stacks 04J0, 03S6.
(blueprint: lem-sf-open-tensor-normalization). -/
structure SiteSquare {m : Mode} (d : Input.{u} m) where
  iso : openInclusion m d.j ⋙ baseChange m d.g ≅
    baseChange m d.gU ⋙ openInclusion m d.j'
  first : ∀ W : Site m d.U,
    HEq (((forgetIndex m d.X').map (iso.inv.app W)).left ≫
      baseFirst m d.g ((openInclusion m d.j).obj W))
        (baseFirst m d.gU W)

/-- The open-corner structural map is forced by restriction of the given
ambient map and the specified geometric comparison. Source: Stacks 04J0.
(blueprint: lem-sf-open-tensor-normalization). -/
def cornerCoefficient {m : Mode} {d : Input.{u} m} (t : SiteSquare d) :
    restrictRing m d.j d.R ⟶
      ((baseChange m d.gU).sheafPushforwardContinuous CommRingCat.{u + 1}
        (topology m d.U) (topology m d.U')).obj (restrictRing m d.j' d.S) :=
  ⟨Functor.whiskerLeft (openInclusion m d.j).op d.coefficient.hom ≫
    Functor.whiskerRight (NatTrans.op t.iso.inv) d.S.obj⟩

private theorem system_cocontinuous {X Y : Scheme.{u}} (F : X.ProEt ⥤ Y.ProEt)
    [F.IsCocontinuous (ProEt.topology X) (ProEt.topology Y)] :
    ((𝟭 ℕ).prod F).IsCocontinuous (topology .systems X) (topology .systems Y) := by
  rw [topology_systems_eq X, topology_systems_eq Y]
  constructor
  intro W S hS
  exact F.cover_lift (ProEt.topology X) (ProEt.topology Y) hS

set_option backward.isDefEq.respectTransparency false in
private def systemAdjunction {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    {F : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G) : (𝟭 ℕ).prod F ⊣ (𝟭 ℕ).prod G where
  unit :=
    { app X := Prod.mkHom (𝟙 X.1) (a.unit.app X.2)
      naturality := by
        intro X Y f
        ext
        · simp
        · exact a.unit.naturality f.2 }
  counit :=
    { app X := Prod.mkHom (𝟙 X.1) (a.counit.app X.2)
      naturality := by
        intro X Y f
        ext
        · simp
        · exact a.counit.naturality f.2 }
  left_triangle_components X := by
    ext
    · simp
    · exact a.left_triangle_components X.2
  right_triangle_components X := by
    ext
    · simp
    · exact a.right_triangle_components X.2

set_option backward.isDefEq.respectTransparency false in
/-- Restriction is sectionwise and exact: kernels and finite limits are
sectionwise; cokernels commute with restriction by slice sheafification.
The same calculation is vertical for systems. Source: Stacks 03DJ, 0F6Z
(blueprint: lem-sf-open-tensor-normalization). -/
theorem restriction_exact (m : Mode) {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (R : Sheaf (topology m X) CommRingCat.{u + 1}) :
    (restrict m j R).Additive ∧ PreservesFiniteLimits (restrict m j R) ∧
      PreservesFiniteColimits (restrict m j R) := by
  have hc : (proEtaleOpenComposition j).IsCocontinuous
      (ProEt.topology U) (ProEt.topology X) :=
    ProEt.isCocontinuous_overMap (inferInstance : WeaklyEtale j)
  let a := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ j
    (inferInstance : WeaklyEtale j) trivial
  have : (openInclusion m j).IsCocontinuous (topology m U) (topology m X) := by
    cases m with
    | ordinary => exact hc
    | systems => exact system_cocontinuous (proEtaleOpenComposition j)
  have : (openInclusion m j).IsLeftAdjoint := by
    cases m with
    | ordinary => exact a.isLeftAdjoint
    | systems => exact (systemAdjunction a).isLeftAdjoint
  have : (restrict m j R).IsLeftAdjoint := by
    unfold restrict
    infer_instance
  have : PreservesFiniteLimits (restrict m j R) := by
    let V := toSheaf ((sheafCompose (topology m U)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (restrictRing m j R))
    have : PreservesFiniteLimits (restrict m j R ⋙ V) := by
      change PreservesFiniteLimits (toSheaf _ ⋙
        (openInclusion m j).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
          (topology m U) (topology m X))
      infer_instance
    exact preservesFiniteLimits_of_reflects_of_preserves _ V
  exact ⟨Functor.additive_of_preserves_binary_products _, inferInstance, inferInstance⟩

/-- Restriction is additive because it is sectionwise pushforward.
Source: Stacks 03DJ (blueprint: lem-sf-open-tensor-normalization). -/
instance (m : Mode) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology m X) CommRingCat.{u + 1}) : (restrict m j R).Additive :=
  (restriction_exact m j R).1
/-- Restriction preserves finite limits sectionwise.
Source: Stacks 03DJ (blueprint: lem-sf-open-tensor-normalization). -/
instance (m : Mode) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology m X) CommRingCat.{u + 1}) : PreservesFiniteLimits (restrict m j R) :=
  (restriction_exact m j R).2.1
/-- Restriction preserves finite colimits by localized sheafification.
Source: Stacks 03DJ (blueprint: lem-sf-open-tensor-normalization). -/
instance (m : Mode) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology m X) CommRingCat.{u + 1}) : PreservesFiniteColimits (restrict m j R) :=
  (restriction_exact m j R).2.2

/-- The two open extensions. All functors here are constructed conclusions,
not assumptions on the geometric input. Source: Stacks 03DI.
(blueprint: lem-sf-open-tensor-normalization). -/
structure OpenDerived {m : Mode} (d : Input.{u} m) where
  extension : OpenExtension m d.j d.R
  extension' : OpenExtension m d.j' d.S

/-- The derived extension by zero component of `OpenDerived`.
Source: Stacks 015F (blueprint: lem-sf-open-tensor-normalization). -/
abbrev OpenDerived.jShriek {m : Mode} {d : Input.{u} m} (o : OpenDerived d) :=
  o.extension.ordinary.mapDerivedCategory
/-- The derived extension by zero component for the base-changed open.
Source: Stacks 015F (blueprint: lem-sf-open-tensor-normalization). -/
abbrev OpenDerived.jShriek' {m : Mode} {d : Input.{u} m} (o : OpenDerived d) :=
  o.extension'.ordinary.mapDerivedCategory
/-- The derived restriction component of `OpenDerived`.
Source: Stacks 0F6Z (blueprint: lem-sf-open-tensor-normalization). -/
abbrev OpenDerived.jStar {m : Mode} {d : Input.{u} m} (_o : OpenDerived d) :=
  (restrict m d.j d.R).mapDerivedCategory
/-- The derived restriction component for the base-changed open.
Source: Stacks 0F6Z (blueprint: lem-sf-open-tensor-normalization). -/
abbrev OpenDerived.jStar' {m : Mode} {d : Input.{u} m} (_o : OpenDerived d) :=
  (restrict m d.j' d.S).mapDerivedCategory

/-- The derived extension/restriction adjunction on the ambient site.
Source: Stacks 015F (blueprint: lem-sf-open-tensor-normalization). -/
abbrev OpenDerived.adj {m : Mode} {d : Input.{u} m} (o : OpenDerived d) :=
  exactDerivedAdjunction o.extension.adjunction
/-- The derived extension/restriction adjunction on the base-changed site.
Source: Stacks 015F (blueprint: lem-sf-open-tensor-normalization). -/
abbrev OpenDerived.adj' {m : Mode} {d : Input.{u} m} (o : OpenDerived d) :=
  exactDerivedAdjunction o.extension'.adjunction

/-- The exact restriction model uses the published exact-functor factorization.
Source: Stacks 015F.
(blueprint: lem-sf-open-tensor-normalization). -/
def restrictionModel {m : Mode} {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (R : Sheaf (topology m X) CommRingCat.{u + 1}) :
    ExactModel (restrict m j R) where
  additive := inferInstance
  functor := (restrict m j R).mapDerivedCategory
  factors := (restrict m j R).mapDerivedCategoryFactors

/-- Simultaneous canonical presentations. Both pullbacks are characterized by
their adjunctions to the *specified* direct images and by left derivation.
The geometric mate and the flat-representative equation fix theta, including
its scalar normalization. Source: Stacks 04J0, 07A4, 0GL1.
(blueprint: lem-sf-open-tensor-normalization). -/
structure Operations {m : Mode} (d : Input.{u} m) (t : SiteSquare d) where
  opens : OpenDerived d
  gPull : Pullback d.R d.S (direct m d.g d.R d.S d.coefficient)
  gUPull : Pullback (restrictRing m d.j d.R) (restrictRing m d.j' d.S)
    (direct m d.gU _ _ (cornerCoefficient t))
  tensorX : TensorModel d.R
  tensorU : TensorModel (restrictRing m d.j d.R)
  tensorX' : TensorModel d.S
  tensorU' : TensorModel (restrictRing m d.j' d.S)
  rightSquare : direct m d.g d.R d.S d.coefficient ⋙ restrict m d.j d.R ≅
    restrict m d.j' d.S ⋙ direct m d.gU _ _ (cornerCoefficient t)
  rightSections : ∀ (N : Mod d.S) (W : (Site m d.U)ᵒᵖ)
      (x : N.val.obj ((openInclusion m d.j ⋙ baseChange m d.g).op.obj W)),
    (rightSquare.hom.app N).val.app W x =
      N.val.map (t.iso.inv.app W.unop).op x
  ordinaryTheta : gPull.ordinary ⋙ restrict m d.j' d.S ≅
    restrict m d.j d.R ⋙ gUPull.ordinary
  ordinaryTheta_mate : ∀ M : Mod d.R,
    gUPull.adjunction.homEquiv _ _ (ordinaryTheta.inv.app M) =
      (restrict m d.j d.R).map (gPull.adjunction.unit.app M) ≫
        rightSquare.hom.app (gPull.ordinary.obj M)
  theta : gPull.derived ⋙ opens.jStar' ≅ opens.jStar ⋙ gUPull.derived
  theta_model : ∀ (P : CochainComplex (Mod d.R) ℤ), resolving d.R P →
    theta.hom.app (DerivedCategory.Q.obj P) ≫
      gUPull.derived.map ((restrict m d.j d.R).mapDerivedCategoryFactors.hom.app P) ≫
      derivedPullbackComplexComparison gUPull.ordinary gUPull.derived gUPull.epsilon
        (((restrict m d.j d.R).mapHomologicalComplex (.up ℤ)).obj P) =
    opens.jStar'.map
      (derivedPullbackComplexComparison gPull.ordinary gPull.derived gPull.epsilon P) ≫
      (restrict m d.j' d.S).mapDerivedCategoryFactors.hom.app
        ((gPull.ordinary.mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex ordinaryTheta.hom (.up ℤ)).app P)
  restrictionTensor : ∀ M N : Mod d.R,
    (restrict m d.j d.R).obj (((tensor d.R).obj M).obj N) ≅
      ((tensor (restrictRing m d.j d.R)).obj ((restrict m d.j d.R).obj M)).obj
        ((restrict m d.j d.R).obj N)
  restrictionTensor_sections : ∀ (M N : Mod d.R) (W : (Site m d.U)ᵒᵖ)
      (x : M.val.obj ((openInclusion m d.j).op.obj W))
      (y : N.val.obj ((openInclusion m d.j).op.obj W)),
    (restrictionTensor M N).hom.val.app W
      (pure d.R M N ((openInclusion m d.j).op.obj W) x y) =
    pure (restrictRing m d.j d.R) ((restrict m d.j d.R).obj M)
      ((restrict m d.j d.R).obj N) W x y
  tensorComparison : TensorComparison (restrict m d.j d.R) (restrictionModel d.j d.R)
    tensorX tensorU restrictionTensor

/-- Every normalization and every arrow of the assertion, for arbitrary
unbounded derived objects. Source: Stacks 0F6Z, 0GL1, 0E8I.
(blueprint: lem-sf-open-tensor-normalization). -/
structure Assertion {m : Mode} {d : Input.{u} m} {t : SiteSquare d}
    (o : Operations d t) where
  unit : ∀ M, IsIso (o.opens.adj.unit.app M)
  unit' : ∀ M, IsIso (o.opens.adj'.unit.app M)
  ordinaryUnit : ∀ M, IsIso (o.opens.extension.adjunction.unit.app M)
  ordinaryUnit' : ∀ M, IsIso (o.opens.extension'.adjunction.unit.app M)
  full : o.opens.jShriek.Full
  faithful : o.opens.jShriek.Faithful
  full' : o.opens.jShriek'.Full
  faithful' : o.opens.jShriek'.Faithful
  beta : o.opens.jShriek ⋙ o.gPull.derived ≅ o.gUPull.derived ⋙ o.opens.jShriek'
  gamma : o.opens.jShriek.prod (𝟭 _) ⋙ o.tensorX.functor ≅
    (𝟭 _).prod o.opens.jStar ⋙ o.tensorU.functor ⋙ o.opens.jShriek
  beta_inverse : ∀ M, o.opens.adj'.homEquiv _ _ (beta.inv.app M) =
    o.gUPull.derived.map (o.opens.adj.unit.app M) ≫
      o.theta.inv.app (o.opens.jShriek.obj M)
  gamma_inverse : ∀ M N, o.opens.adj.homEquiv _ _ (gamma.inv.app (M, N)) =
    o.tensorU.functor.map (CategoryTheory.Prod.mkHom (o.opens.adj.unit.app M) (𝟙 _)) ≫
      o.tensorComparison.comparison.inv.app (o.opens.jShriek.obj M, N)
  beta_restriction : ∀ M,
    o.opens.jStar'.map (beta.hom.app M) =
      o.theta.hom.app (o.opens.jShriek.obj M) ≫
        o.gUPull.derived.map (@inv _ _ _ _ (o.opens.adj.unit.app M) (unit M)) ≫
          o.opens.adj'.unit.app (o.gUPull.derived.obj M)
  gamma_restriction : ∀ M N,
    o.opens.jStar.map (gamma.hom.app (M, N)) =
      o.tensorComparison.comparison.hom.app (o.opens.jShriek.obj M, N) ≫
        o.tensorU.functor.map
          (CategoryTheory.Prod.mkHom (@inv _ _ _ _ (o.opens.adj.unit.app M) (unit M)) (𝟙 _)) ≫
            o.opens.adj.unit.app (o.tensorU.functor.obj (M, o.opens.jStar.obj N))

/-- Fixed finite scalars and their standard (uncompleted) derived category.
Source: Stacks 09AE; the two recorded finite-coefficient dependencies.
(blueprint: lem-sf-open-tensor-normalization). -/
abbrev FiniteModules (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :=
  Sheaf (ProEt.topology X) (ModuleCat.{u + 1} A)
/-- The fixed-scalar ordinary derived category.
Source: Stacks 09AE (blueprint: lem-sf-open-tensor-normalization). -/
abbrev FiniteD (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :=
  DerivedCategory (FiniteModules A X)

/-- The canonical fixed-scalar open extension and inverse image.
Source: the recorded finite-coefficient open base-change declaration.
(blueprint: lem-sf-open-tensor-normalization). -/
def finiteShriek (A : Type (u + 1)) [CommRing A] {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] : FiniteD A U ⥤ FiniteD A X :=
  (ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory
/-- The canonical finite-scalar derived pullback functor.
Source: the recorded finite pullback declaration (blueprint: lem-sf-open-tensor-normalization). -/
def finitePull (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}}
    (f : X ⟶ Y) : FiniteD A Y ⥤ FiniteD A X :=
  (ProEtale.upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory

/-- Intrinsic realization is pinned by its underlying sheaves and by the action
of every constant scalar. Since constant sections locally generate the constant
ring sheaf, these data fix the realization, including on morphisms.
Source: Stacks 00YV, 03D7.
(blueprint: lem-sf-open-tensor-normalization). -/
structure FiniteRealization (A : Type (u + 1)) [CommRing A] (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (i : (Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A) ⟶ R.obj) where
  equivalence : FiniteModules A X ≌ Mod R
  [additive : equivalence.functor.Additive]
  underlying : equivalence.functor ⋙
      toSheaf ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) ≅
    sheafCompose (ProEt.topology X) (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})
  /-- Constants act as the original fixed scalars under the underlying-section comparison. -/
  scalar : ∀ (M : FiniteModules A X) (W : X.ProEtᵒᵖ) (a : A)
      (x : (equivalence.functor.obj M).val.obj W),
    (underlying.hom.app M).hom.app W
      (@SMul.smul
        (((sheafCompose (ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).obj.obj W)
        ((equivalence.functor.obj M).val.obj W) inferInstance (i.app W a) x) =
      @SMul.smul A (M.obj.obj W) inferInstance a ((underlying.hom.app M).hom.app W x)

attribute [instance] FiniteRealization.additive

/-- Realization on the ordinary derived categories is exact termwise
localization of this very section-preserving equivalence. Source: Stacks 015F.
(blueprint: lem-sf-open-tensor-normalization). -/
def FiniteRealization.derived {A : Type (u + 1)} [CommRing A] {X : Scheme.{u}}
    {R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    {i : (Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A) ⟶ R.obj}
    (e : FiniteRealization A X R i) : FiniteD A X ⥤ Der R :=
  e.equivalence.functor.mapDerivedCategory

/-- The constant finite specialization uses the canonical constant-section
structural map, not an arbitrary endomorphism of the constant ring.
Source: Stacks 0H7J, 09AE.
(blueprint: lem-sf-open-tensor-normalization). -/
abbrev finiteInput (A : Type (u + 1)) [CommRing A]
    {U' U X' X : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) (sq : OpenImmersionSquare gU j' j g) : Input .ordinary where
  U := U
  U' := U'
  X := X
  X' := X'
  gU := gU
  j' := j'
  j := j
  g := g
  square := sq
  R := (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).obj (CommRingCat.of A)
  S := (constantSheaf (ProEt.topology X') CommRingCat.{u + 1}).obj (CommRingCat.of A)
  coefficient := proEtaleConstantDirectImageMap g CommRingCat.{u + 1} (CommRingCat.of A)

/-- The published finite projection arrow in the direction of the node's gamma.
This is its actual inverse projection map, with explicit endpoints to keep
elaboration independent of the surrounding realization square.
Source: Stacks 0GL1 and the recorded finite open projection formula
(blueprint: lem-sf-open-tensor-normalization). -/
def finiteGamma (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (M : FiniteD A U) (N : FiniteD A X) :
    (((ProEtale.derivedTensor (ModuleCat.{u + 1} A) X).obj
      ((finiteShriek A j).obj M)).obj N) ⟶
    (finiteShriek A j).obj
      (((ProEtale.derivedTensor (ModuleCat.{u + 1} A) U).obj M).obj
        ((ProEtale.upperStar (ModuleCat.{u + 1} A) j).leftDerivedFunctor.obj N)) :=
  letI : IsNoetherianRing A := isNoetherian_of_finite A A
  ((ProEtale.derivedOpenImmersionLowerShriekProjectionIso
    (ModuleCat.{u + 1} A) j).inv.app M).app N

/-- The exact-operation comparison is pinned on every complex by the ordinary
comparison and the published exact localization factorizations. Source: Stacks 015F
(blueprint: lem-sf-open-tensor-normalization). -/
def FiniteExactPin {A : Type (u + 1)} [CommRing A] {X Y : Scheme.{u}}
    {R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    {S : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}}
    {i : (Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A) ⟶ R.obj}
    {k : (Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of A) ⟶ S.obj}
    (eR : FiniteRealization A X R i) (eS : FiniteRealization A Y S k)
    (F : FiniteModules A X ⥤ FiniteModules A Y) (G : Mod R ⥤ Mod S)
    [F.Additive] [G.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (c : F ⋙ eS.equivalence.functor ≅ eR.equivalence.functor ⋙ G)
    (d : F.mapDerivedCategory ⋙ eS.derived ≅ eR.derived ⋙ G.mapDerivedCategory) : Prop :=
  ∀ P : CochainComplex (FiniteModules A X) ℤ,
    d.hom.app (DerivedCategory.Q.obj P) ≫
      G.mapDerivedCategory.map (eR.equivalence.functor.mapDerivedCategoryFactors.hom.app P) ≫
      G.mapDerivedCategoryFactors.hom.app
        ((eR.equivalence.functor.mapHomologicalComplex (.up ℤ)).obj P) =
    eS.derived.map (F.mapDerivedCategoryFactors.hom.app P) ≫
      eS.equivalence.functor.mapDerivedCategoryFactors.hom.app
        ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex c.hom (.up ℤ)).app P)

/-- Representative equation for the finite pullback comparison, using the
stored additive structure of the specified module left adjoint.
Source: Stacks 07A4 and 09AE (blueprint: lem-sf-open-tensor-normalization). -/
def finitePullModel {A : Type (u + 1)} [CommRing A] {X Y : Scheme.{u}}
    {R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}}
    {S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    {i : (Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of A) ⟶ R.obj}
    {k : (Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A) ⟶ S.obj}
    (eR : FiniteRealization A Y R i) (eS : FiniteRealization A X S k)
    (f : X ⟶ Y) (c : R ⟶ ((baseChange .ordinary f).sheafPushforwardContinuous
      CommRingCat.{u + 1} (topology .ordinary Y) (topology .ordinary X)).obj S)
    (p : Pullback R S (direct .ordinary f R S c))
    (d : finitePull A f ⋙ eS.derived ≅ eR.derived ⋙ p.derived)
    (ordinary : ProEtale.upperStar (ModuleCat.{u + 1} A) f ⋙ eS.equivalence.functor ≅
      eR.equivalence.functor ⋙ p.ordinary) : Prop := by
  letI : p.ordinary.Additive := p.additive
  exact
    ∀ P : CochainComplex (FiniteModules A Y) ℤ,
    d.hom.app (DerivedCategory.Q.obj P) ≫
      p.derived.map (eR.equivalence.functor.mapDerivedCategoryFactors.hom.app P) ≫
      derivedPullbackComplexComparison p.ordinary p.derived p.epsilon
        ((eR.equivalence.functor.mapHomologicalComplex (.up ℤ)).obj P) =
    eS.derived.map
        ((ProEtale.upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategoryFactors.hom.app P) ≫
      eS.equivalence.functor.mapDerivedCategoryFactors.hom.app
        (((ProEtale.upperStar (ModuleCat.{u + 1} A) f).mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex ordinary.hom (.up ℤ)).app P)

/-- Pullback comparisons are the mates of a section-preserving direct-image
comparison, and their derived comparison has that same value on complexes.
Source: Stacks 03D7, 07A4, 09AE (blueprint: lem-sf-open-tensor-normalization). -/
structure FinitePullPin {A : Type (u + 1)} [CommRing A] {X Y : Scheme.{u}}
    {R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}}
    {S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    {i : (Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of A) ⟶ R.obj}
    {k : (Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A) ⟶ S.obj}
    (eR : FiniteRealization A Y R i) (eS : FiniteRealization A X S k)
    (f : X ⟶ Y) (c : R ⟶ ((baseChange .ordinary f).sheafPushforwardContinuous
      CommRingCat.{u + 1} (topology .ordinary Y) (topology .ordinary X)).obj S)
    (p : Pullback R S (direct .ordinary f R S c))
    (d : finitePull A f ⋙ eS.derived ≅ eR.derived ⋙ p.derived) where
  right : ProEtale.lowerStar (ModuleCat.{u + 1} A) f ⋙ eR.equivalence.functor ≅
    eS.equivalence.functor ⋙ direct .ordinary f R S c
  right_sections : ∀ (M : FiniteModules A X) (W : Y.ProEtᵒᵖ)
      (x : (eR.equivalence.functor.obj
        ((ProEtale.lowerStar (ModuleCat.{u + 1} A) f).obj M)).val.obj W),
    (eS.underlying.hom.app M).hom.app ((baseChange .ordinary f).op.obj W)
      ((right.hom.app M).val.app W x) =
    (eR.underlying.hom.app ((ProEtale.lowerStar (ModuleCat.{u + 1} A) f).obj M)).hom.app W x
  ordinary : ProEtale.upperStar (ModuleCat.{u + 1} A) f ⋙ eS.equivalence.functor ≅
    eR.equivalence.functor ⋙ p.ordinary
  mate : ∀ M : FiniteModules A Y,
    eR.equivalence.functor.map
        ((ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).unit.app M) ≫
      right.hom.app ((ProEtale.upperStar (ModuleCat.{u + 1} A) f).obj M) =
    p.adjunction.unit.app (eR.equivalence.functor.obj M) ≫
      (direct .ordinary f R S c).map (ordinary.inv.app M)
  model : finitePullModel eR eS f c p d ordinary

set_option backward.isDefEq.respectTransparency false in
/-- Exact derivation of the specified ordinary open extension, with its stored
exactness instances. Source: Stacks 015F (blueprint: lem-sf-open-tensor-normalization). -/
def openExtensionDerived {U X : Scheme.{u}} {j : U ⟶ X} [IsOpenImmersion j]
    {R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (o : OpenExtension .ordinary j R) :
    Der (restrictRing .ordinary j R) ⥤ Der R := by
  letI : HasDerivedCategory (Mod R) := HasDerivedCategory.standard _
  letI : HasDerivedCategory (Mod (restrictRing .ordinary j R)) := HasDerivedCategory.standard _
  letI : o.ordinary.Additive := o.additive
  letI : PreservesFiniteLimits o.ordinary := o.limits
  letI : PreservesFiniteColimits o.ordinary := o.colimits
  exact Functor.mapDerivedCategory
    (C₁ := Mod (restrictRing .ordinary j R)) (C₂ := Mod R) o.ordinary

set_option backward.isDefEq.respectTransparency false in
/-- Both exact comparison pins use the given ordinary extension and restriction,
with the standard localization factorizations. Source: Stacks 015F and 0F6Z
(blueprint: lem-sf-open-tensor-normalization). -/
def finiteOpenModels {A : Type (u + 1)} [CommRing A] {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    {i : (Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A) ⟶ R.obj}
    {k : (Functor.const U.ProEtᵒᵖ).obj (CommRingCat.of A) ⟶ (restrictRing .ordinary j R).obj}
    (eX : FiniteRealization A X R i) (eU : FiniteRealization A U (restrictRing .ordinary j R) k)
    (o : OpenExtension .ordinary j R)
    (ds : finiteShriek A j ⋙ eX.derived ≅ eU.derived ⋙ openExtensionDerived o)
    (dr : finitePull A j ⋙ eU.derived ≅
      eX.derived ⋙ (restrictionModel (m := .ordinary) j R).functor)
    (star : ProEtale.upperStar (ModuleCat.{u + 1} A) j ⋙ eU.equivalence.functor ≅
      eX.equivalence.functor ⋙ restrict .ordinary j R)
    (shriek : ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j ⋙
      eX.equivalence.functor ≅ eU.equivalence.functor ⋙ o.ordinary) : Prop := by
  letI : HasDerivedCategory (Mod R) := HasDerivedCategory.standard _
  letI : HasDerivedCategory (Mod (restrictRing .ordinary j R)) := HasDerivedCategory.standard _
  letI : o.ordinary.Additive := o.additive
  letI : PreservesFiniteLimits o.ordinary := o.limits
  letI : PreservesFiniteColimits o.ordinary := o.colimits
  letI : (restrict .ordinary j R).Additive := (restriction_exact .ordinary j R).1
  letI : PreservesFiniteLimits (restrict .ordinary j R) := (restriction_exact .ordinary j R).2.1
  letI : PreservesFiniteColimits (restrict .ordinary j R) := (restriction_exact .ordinary j R).2.2
  exact FiniteExactPin (R := restrictRing .ordinary j R) (S := R) eU eX
      (ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j) o.ordinary shriek ds ∧
    FiniteExactPin (R := R) (S := restrictRing .ordinary j R) eX eU
      (ProEtale.upperStar (ModuleCat.{u + 1} A) j)
      (restrict .ordinary j R) star dr

/-- Open comparisons preserve the actual section restriction and its adjunction unit;
the extension and restriction comparisons descend these ordinary comparisons.
Source: Stacks 03DI, 0F6Z, 015F (blueprint: lem-sf-open-tensor-normalization). -/
structure FiniteOpenPin {A : Type (u + 1)} [CommRing A] {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    {i : (Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A) ⟶ R.obj}
    {k : (Functor.const U.ProEtᵒᵖ).obj (CommRingCat.of A) ⟶ (restrictRing .ordinary j R).obj}
    (eX : FiniteRealization A X R i) (eU : FiniteRealization A U (restrictRing .ordinary j R) k)
    (o : OpenExtension .ordinary j R)
    (ds : finiteShriek A j ⋙ eX.derived ≅ eU.derived ⋙ openExtensionDerived o)
    (dr : finitePull A j ⋙ eU.derived ≅
      eX.derived ⋙ (restrictionModel (m := .ordinary) j R).functor) where
  star : ProEtale.upperStar (ModuleCat.{u + 1} A) j ⋙ eU.equivalence.functor ≅
    eX.equivalence.functor ⋙ restrict .ordinary j R
  sections : ∀ (M : FiniteModules A X) (W : U.ProEtᵒᵖ)
      (x : (eU.equivalence.functor.obj
        ((ProEtale.upperStar (ModuleCat.{u + 1} A) j).obj M)).val.obj W),
    (eX.underlying.hom.app M).hom.app ((openInclusion .ordinary j).op.obj W)
        ((star.hom.app M).val.app W x) =
      ((ProEtale.upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} A) j).hom.app M).hom.app W
        ((eU.underlying.hom.app
          ((ProEtale.upperStar (ModuleCat.{u + 1} A) j).obj M)).hom.app W x)
  shriek : ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j ⋙
    eX.equivalence.functor ≅ eU.equivalence.functor ⋙ o.ordinary
  unit : ∀ M : FiniteModules A U,
    eU.equivalence.functor.map
        ((ProEtale.openImmersionLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} A) j).unit.app M) ≫
      star.hom.app ((ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).obj M) ≫
      (restrict .ordinary j R).map (shriek.hom.app M) =
    o.adjunction.unit.app (eU.equivalence.functor.obj M)
  models : finiteOpenModels j R eX eU o ds dr star shriek

/-- A pure fixed-scalar tensor section is the image of the section tensor under
the lax monoidal underlying-presheaf map. Source: Stacks 03EK
(blueprint: lem-sf-open-tensor-normalization). -/
def finitePure {A : Type (u + 1)} [CommRing A] {X : Scheme.{u}}
    (M N : FiniteModules A X) (W : X.ProEtᵒᵖ) (x : M.obj.obj W) (y : N.obj.obj W) :
    ((curriedTensor (FiniteModules A X)).obj M |>.obj N).obj.obj W :=
  ((Functor.LaxMonoidal.μ (sheafToPresheaf (ProEt.topology X) (ModuleCat.{u + 1} A))
    M N).app W).hom (TensorProduct.tmul A x y)

/-- Evaluation of the existing tensor representative comparison at a resolving
pair, with its endpoints explicit. Source: Stacks 06YU
(blueprint: lem-sf-open-tensor-normalization). -/
def tensorRepresentative {X : Scheme.{u}}
    {R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (t : TensorModel R)
    (P Q : CochainComplex (Mod R) ℤ) (hp : resolving R P) (hq : resolving R Q) :
    DerivedCategory.Q.obj ((total R).obj (P, Q)) ⟶
      t.functor.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) :=
  t.representative.hom.app (⟨P, hp⟩, ⟨Q, hq⟩)

/-- The fixed-scalar derived tensor bifunctor with explicit product endpoints.
Source: Stacks 06YU (blueprint: lem-sf-open-tensor-normalization). -/
def finiteTensor (A : Type (u + 1)) [CommRing A] [Finite A] (X : Scheme.{u}) :
    FiniteD A X × FiniteD A X ⥤ FiniteD A X :=
  Functor.uncurry.obj (ProEtale.derivedTensor (ModuleCat.{u + 1} A) X)

/-- Termwise realization of fixed-scalar complexes, with explicit complex categories.
Source: Stacks 015F (blueprint: lem-sf-open-tensor-normalization). -/
def finiteComplexRealization {A : Type (u + 1)} [CommRing A] {X : Scheme.{u}}
    {R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    {i : (Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A) ⟶ R.obj}
    (e : FiniteRealization A X R i) :
    CochainComplex (FiniteModules A X) ℤ ⥤ CochainComplex (Mod R) ℤ :=
  e.equivalence.functor.mapHomologicalComplex (.up ℤ)

/-- The fixed-scalar signed total complex, with its endpoints explicit.
Source: Stacks 06YN (blueprint: lem-sf-open-tensor-normalization). -/
def finiteTotal (A : Type (u + 1)) [CommRing A] (X : Scheme.{u})
    (P Q : CochainComplex (FiniteModules A X) ℤ) : CochainComplex (FiniteModules A X) ℤ :=
  HomologicalComplex.mapBifunctor P Q (curriedTensor (FiniteModules A X)) (.up ℤ)

/-- The source and target of the finite signed-total comparison.
Source: Stacks 06YN (blueprint: lem-sf-open-tensor-normalization). -/
def FiniteTensorTotal {A : Type (u + 1)} [CommRing A] [Finite A] {X : Scheme.{u}}
    {R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    {i : (Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A) ⟶ R.obj}
    (e : FiniteRealization A X R i) : Type _ :=
  ∀ P Q : CochainComplex (FiniteModules A X) ℤ,
    (finiteComplexRealization e).obj
      (finiteTotal A X P Q) ≅
    (total R).obj ((finiteComplexRealization e).obj P,
      (finiteComplexRealization e).obj Q)

set_option backward.isDefEq.respectTransparency false in
/-- The total comparison carries every fixed-scalar pure bidegree summand to the
same ring-sheaf pure summand. Source: Stacks 03EK and 06YN
(blueprint: lem-sf-open-tensor-normalization). -/
def finiteTensorPure {A : Type (u + 1)} [CommRing A] [Finite A] {X : Scheme.{u}}
    {R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    {i : (Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A) ⟶ R.obj}
    (e : FiniteRealization A X R i)
    (totalIso : FiniteTensorTotal e) : Prop :=
  ∀ (P Q : CochainComplex (FiniteModules A X) ℤ)
      (p q n : ℤ) (hn : p + q = n) (W : X.ProEtᵒᵖ)
      (x : (P.X p).obj.obj W) (y : (Q.X q).obj.obj W),
    ((totalIso P Q).hom.f n).val.app W
      ((e.underlying.inv.app _).hom.app W
        ((HomologicalComplex.ιMapBifunctor P Q (curriedTensor (FiniteModules A X))
          (.up ℤ) p q n hn).hom.app W (finitePure (P.X p) (Q.X q) W x y))) =
    (HomologicalComplex.ιMapBifunctor
      ((finiteComplexRealization e).obj P)
      ((finiteComplexRealization e).obj Q)
      (tensor R) (.up ℤ) p q n hn).val.app W
        (pure R (e.equivalence.functor.obj (P.X p)) (e.equivalence.functor.obj (Q.X q)) W
          ((e.underlying.inv.app (P.X p)).hom.app W x)
          ((e.underlying.inv.app (Q.X q)).hom.app W y))

set_option backward.isDefEq.respectTransparency false in
/-- The tensor comparison commutes with the finite localization map and the
ring-sheaf representative comparison. Source: Stacks 06YU and 0GL1
(blueprint: lem-sf-open-tensor-normalization). -/
def finiteTensorModel {A : Type (u + 1)} [CommRing A] [Finite A] {X : Scheme.{u}}
    {R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    {i : (Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A) ⟶ R.obj}
    (e : FiniteRealization A X R i) (t : TensorModel R)
    (d : finiteTensor A X ⋙ e.derived ≅
      (e.derived.prod e.derived) ⋙ t.functor)
    (totalIso : FiniteTensorTotal e) : Prop :=
  ∀ (P Q : CochainComplex (FiniteModules A X) ℤ)
      (hp : resolving R ((finiteComplexRealization e).obj P))
      (hq : resolving R ((finiteComplexRealization e).obj Q)),
    HEq (e.derived.map (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) ≫
      e.equivalence.functor.mapDerivedCategoryFactors.hom.app
        (finiteTotal A X P Q) ≫
      DerivedCategory.Q.map (totalIso P Q).hom ≫
      tensorRepresentative (R := R) t
        ((finiteComplexRealization e).obj P)
        ((finiteComplexRealization e).obj Q) hp hq)
    (d.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
      t.functor.map (CategoryTheory.Prod.mkHom
        (e.equivalence.functor.mapDerivedCategoryFactors.hom.app P)
        (e.equivalence.functor.mapDerivedCategoryFactors.hom.app Q)))

/-- Finite tensor transport is fixed on every total-complex pure summand and then
on all flat K-flat representatives by the two published tensor factorizations.
Source: Stacks 03EK, 06YU, 0GL1 (blueprint: lem-sf-open-tensor-normalization). -/
def FiniteTensorPin {A : Type (u + 1)} [CommRing A] [Finite A] {X : Scheme.{u}}
    {R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    {i : (Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A) ⟶ R.obj}
    (e : FiniteRealization A X R i) (t : TensorModel R)
    (d : finiteTensor A X ⋙ e.derived ≅
      (e.derived.prod e.derived) ⋙ t.functor) : Type _ :=
  { totalIso : FiniteTensorTotal e // finiteTensorPure e totalIso ∧
    finiteTensorModel e t d totalIso }

namespace FiniteTensorPin

variable {A : Type (u + 1)} [CommRing A] [Finite A] {X : Scheme.{u}}
    {R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    {i : (Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A) ⟶ R.obj}
    {e : FiniteRealization A X R i} {t : TensorModel R}
    {d : finiteTensor A X ⋙ e.derived ≅ (e.derived.prod e.derived) ⋙ t.functor}

/-- The total-complex comparison retained in the finite tensor pin.
Source: Stacks 06YU (blueprint: lem-sf-open-tensor-normalization). -/
def totalIso (p : FiniteTensorPin e t d) : FiniteTensorTotal e := p.val

/-- The retained comparison preserves every pure summand.
Source: Stacks 03EK (blueprint: lem-sf-open-tensor-normalization). -/
theorem pure_summands (p : FiniteTensorPin e t d) : finiteTensorPure e p.totalIso :=
  p.property.1

/-- The retained comparison agrees with the derived representative equation.
Source: Stacks 06YU (blueprint: lem-sf-open-tensor-normalization). -/
theorem model (p : FiniteTensorPin e t d) : finiteTensorModel e t d p.totalIso :=
  p.property.2

/-- Assemble a finite tensor pin from the same three original fields.
Source: Stacks 03EK and 06YU (blueprint: lem-sf-open-tensor-normalization). -/
def mk (totalIso : FiniteTensorTotal e) (pure_summands : finiteTensorPure e totalIso)
    (model : finiteTensorModel e t d totalIso) : FiniteTensorPin e t d :=
  ⟨totalIso, pure_summands, model⟩

end FiniteTensorPin

/-- Finite realizations and operation comparisons are fixed independently of
beta and gamma: constants and underlying sections fix the realizations;
section equations, adjunction mates and total-complex equations pin the
comparison isomorphisms. These records are conclusions, not coefficient
hypotheses. Source: Stacks 03S6, 0GL1.
(blueprint: lem-sf-open-tensor-normalization). -/
structure FiniteComparisonsCore (A : Type (u + 1)) [CommRing A] [Finite A]
    {U' U X' X : Scheme.{u}} {gU : U' ⟶ U} {j' : U' ⟶ X'}
    {j : U ⟶ X} {g : X' ⟶ X} {sq : OpenImmersionSquare gU j' j g}
    [_hj : IsOpenImmersion j] [_hj' : IsOpenImmersion j']
    {t : SiteSquare (finiteInput A gU j' j g sq)}
    (o : Operations (finiteInput A gU j' j g sq) t) where
  realizeX : FiniteRealization A X
    ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).obj (CommRingCat.of A))
    (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A)))
  realizeX' : FiniteRealization A X'
    ((constantSheaf (ProEt.topology X') CommRingCat.{u + 1}).obj (CommRingCat.of A))
    (toSheafify (ProEt.topology X') ((Functor.const X'.ProEtᵒᵖ).obj (CommRingCat.of A)))
  realizeU : FiniteRealization A U
    (restrictRing .ordinary j
      ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).obj (CommRingCat.of A)))
    (Functor.whiskerLeft (openInclusion .ordinary j).op
      (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A))))
  realizeU' : FiniteRealization A U'
    (restrictRing .ordinary j'
      ((constantSheaf (ProEt.topology X') CommRingCat.{u + 1}).obj (CommRingCat.of A)))
    (Functor.whiskerLeft (openInclusion .ordinary j').op
      (toSheafify (ProEt.topology X') ((Functor.const X'.ProEtᵒᵖ).obj (CommRingCat.of A))))
  shriek : finiteShriek A j ⋙ realizeX.derived ≅ realizeU.derived ⋙
    o.opens.jShriek
  shriek' : finiteShriek A j' ⋙ realizeX'.derived ≅ realizeU'.derived ⋙
    o.opens.jShriek'
  pull : finitePull A g ⋙ realizeX'.derived ≅ realizeX.derived ⋙ o.gPull.derived
  pullU : finitePull A gU ⋙ realizeU'.derived ≅ realizeU.derived ⋙ o.gUPull.derived
  openPull : (ProEtale.upperStar (ModuleCat.{u + 1} A) j).leftDerivedFunctor ⋙ realizeU.derived ≅
    realizeX.derived ⋙ o.opens.jStar
  tensorX : finiteTensor A X ⋙
    realizeX.derived ≅ (realizeX.derived.prod realizeX.derived) ⋙ o.tensorX.functor
  tensorU : finiteTensor A U ⋙
    realizeU.derived ≅ (realizeU.derived.prod realizeU.derived) ⋙ o.tensorU.functor
  openPull' : finitePull A j' ⋙ realizeU'.derived ≅
    realizeX'.derived ⋙ o.opens.jStar'
  pull_pin : FinitePullPin realizeX realizeX' g
    (proEtaleConstantDirectImageMap g CommRingCat.{u + 1} (CommRingCat.of A))
    o.gPull pull
  pullU_pin : FinitePullPin realizeU realizeU' gU (cornerCoefficient t) o.gUPull pullU
  open_pin : FiniteOpenPin j
    ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).obj (CommRingCat.of A))
    realizeX realizeU o.opens.extension shriek
      (Functor.isoWhiskerRight
        (ProEtale.upperStar (ModuleCat.{u + 1} A)
          j).leftDerivedFunctorIsoMapDerivedCategory.symm
        realizeU.derived ≪≫ openPull)
  open'_pin : FiniteOpenPin j'
    ((constantSheaf (ProEt.topology X') CommRingCat.{u + 1}).obj (CommRingCat.of A))
    realizeX' realizeU' o.opens.extension' shriek' openPull'
  tensorX_pin : FiniteTensorPin realizeX o.tensorX tensorX
  tensorU_pin : FiniteTensorPin realizeU o.tensorU tensorU

/-- Canonical finite comparisons with the open-immersion instances supplied by
the chosen square. Source: Stacks 03S6, 0GL1 (blueprint:
lem-sf-open-tensor-normalization). -/
abbrev FiniteComparisons (A : Type (u + 1)) [CommRing A] [Finite A]
    {U' U X' X : Scheme.{u}} {gU : U' ⟶ U} {j' : U' ⟶ X'}
    {j : U ⟶ X} {g : X' ⟶ X} {sq : OpenImmersionSquare gU j' j g}
    {t : SiteSquare (finiteInput A gU j' j g sq)}
    (o : Operations (finiteInput A gU j' j g sq) t) :
    Type _ := FiniteComparisonsCore (A := A) (U' := U') (U := U) (X' := X')
      (X := X) (gU := gU) (j' := j') (j := j) (g := g) (sq := sq)
      (_hj := sq.isOpenImmersion) (_hj' := sq.isOpenImmersion') (t := t) o

end SheafOfModules.OpenTensorNormalization
