/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Adjunction.CompositionIso

/-!
# Sections of tensor pullbacks on the small étale site

Source: Stacks Project, Descent, Tag 03DR, equation (35.8.1), restricted to the small
étale site as in Tag 03DU (blueprint: lem-sc-etale-qcoherent-presheaf-functorial).
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] tensorPullback tensorPullbackObj
-- Keep scalar instances in terms of scheme modules during elaboration.
attribute [local instance 2000]
  instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensCarrierAbPresheaf
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- The composition isomorphism normalized by the canonical tensor-pullback units.
It is the conjugate of the sectionwise pushforward composition identification.
Source: Stacks, Tag 03DR (blueprint: lem-sc-etale-qcoherent-presheaf-functorial). -/
def tensorSectionsComp {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) :
    tensorPullback b ⋙ tensorPullback a ≅ tensorPullback (a ≫ b) :=
  (conjugateIsoEquiv (Classical.choose (exists_tensorPullbackAdjunction (a ≫ b)))
    ((Classical.choose (exists_tensorPullbackAdjunction b)).comp
      (Classical.choose (exists_tensorPullbackAdjunction a)))).symm
    (pushforwardComp a b).symm

/-- Pullback of global sections by the canonical unit, evaluated at the whole scheme.
Source: Stacks, Tag 03DR (blueprint: lem-sc-etale-qcoherent-presheaf-functorial). -/
def tensorSectionsUnit {A B : Scheme.{u}} (a : A ⟶ B) (G : B.Modules) :
    Γ(G, ⊤) ⟶ Γ((tensorPullback a).obj G, ⊤) :=
  ((Classical.choose (exists_tensorPullbackAdjunction a)).unit.app G).app ⊤ ≫
    ((tensorPullback a).obj G).presheaf.map (homOfLE a.preimage_top.ge).op

/-- The restriction `ρ_g(s) = c_{g,u}(g^*s)`, with transport along `g ≫ u = u'`.
The map is an abelian group homomorphism by its type.
Source: Stacks, Tag 03DR (blueprint: lem-sc-etale-qcoherent-presheaf-functorial). -/
def etaleTensorSectionsRestriction {X : Scheme.{u}} (F : X.Modules)
    {U V : X.Etale} (g : V ⟶ U) :
    Γ((tensorPullback U.hom).obj F, ⊤) ⟶ Γ((tensorPullback V.hom).obj F, ⊤) :=
  tensorSectionsUnit g.left ((tensorPullback U.hom).obj F) ≫
    ((tensorSectionsComp g.left U.hom).hom.app F).app ⊤ ≫
    (eqToHom (congrArg (fun f ↦ (tensorPullback f).obj F) g.w)).app ⊤

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The identity case of normalized left-adjoint composition.
Source: Stacks, Tag 03DR; Mathlib `Adjunction.leftAdjointCompIso_comp_id`
(blueprint: lem-sc-etale-qcoherent-presheaf-functorial). -/
private theorem identityComparison
    (L : ∀ {A B : Scheme.{u}}, (A ⟶ B) → B.Modules ⥤ A.Modules)
    (adj : ∀ {A B : Scheme.{u}} (f : A ⟶ B), L f ⊣ pushforward f)
    {A B : Scheme.{u}} (b : A ⟶ B) (F : B.Modules) :
    (((conjugateIsoEquiv (adj (𝟙 A ≫ b)) ((adj b).comp (adj (𝟙 A)))).symm
      (pushforwardComp (𝟙 A) b).symm).hom.app F) ≫
        eqToHom (congrArg (fun f ↦ (L f).obj F) (Category.id_comp b)) =
      (Adjunction.leftAdjointIdIso (adj (𝟙 A)) (pushforwardId A)).hom.app ((L b).obj F) := by
  have he : pushforwardComp (𝟙 A) b =
      Functor.isoWhiskerRight (pushforwardId A) (pushforward b) ≪≫
        Functor.leftUnitor (pushforward b) := by
    ext M V x
    rfl
  have h := Adjunction.leftAdjointCompIso_comp_id (adj b) (adj (𝟙 A))
    (pushforwardComp (𝟙 A) b) (pushforwardId A) he
  have hc := congrArg (fun e ↦ e.hom.app F) h
  dsimp only [Adjunction.leftAdjointCompIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app] at hc
  erw [Category.comp_id] at hc
  erw [eqToHom_refl, Category.comp_id]
  exact hc

/-- The unit-normalized identity comparison cancels the unit on global sections.
Source: Stacks, Tag 03DR; the conjugate-isomorphism unit equation
(blueprint: lem-sc-etale-qcoherent-presheaf-functorial). -/
private theorem unitId_sections {A : Scheme.{u}} (I : A.Modules ⥤ A.Modules)
    (adj : I ⊣ pushforward (𝟙 A)) (M : A.Modules) :
    (adj.unit.app M).app ⊤ ≫
      ((Adjunction.leftAdjointIdIso adj (pushforwardId A)).hom.app M).app ⊤ = 𝟙 _ := by
  have hu := unit_conjugateEquiv_symm Adjunction.id adj (pushforwardId A).inv M
  change (adj.unit.app M).app ⊤ ≫
    (((conjugateEquiv Adjunction.id adj).symm (pushforwardId A).inv).app M).app ⊤ = _
  have hs := congrArg (fun φ ↦ φ.app ⊤) hu
  change (𝟙 Γ(M, ⊤) ≫ 𝟙 _) = (adj.unit.app M).app ⊤ ≫
    (((conjugateEquiv Adjunction.id adj).symm (pushforwardId A).inv).app M).app ⊤ at hs
  erw [Category.id_comp] at hs
  exact hs.symm

/-- The global-section unit for an arbitrary left adjoint of scheme pushforward.
Source: Stacks, Tag 03DR (blueprint: lem-sc-etale-qcoherent-presheaf-functorial). -/
private def sectionsUnitOfAdjunction {A B : Scheme.{u}} (f : A ⟶ B)
    (L : B.Modules ⥤ A.Modules) (adj : L ⊣ pushforward f) (G : B.Modules) :
    Γ(G, ⊤) ⟶ Γ(L.obj G, ⊤) :=
  (adj.unit.app G).app ⊤ ≫ (L.obj G).presheaf.map (homOfLE f.preimage_top.ge).op

/-- Identity restrictions for any family of left adjoints, before specializing to tensors.
Source: Stacks, Tag 03DR (blueprint: lem-sc-etale-qcoherent-presheaf-functorial). -/
private theorem identitySections
    (L : ∀ {A B : Scheme.{u}}, (A ⟶ B) → B.Modules ⥤ A.Modules)
    (adj : ∀ {A B : Scheme.{u}} (f : A ⟶ B), L f ⊣ pushforward f)
    {A B : Scheme.{u}} (b : A ⟶ B) (F : B.Modules) :
    sectionsUnitOfAdjunction (𝟙 A) (L (𝟙 A)) (adj (𝟙 A)) ((L b).obj F) ≫
      ((((conjugateIsoEquiv (adj (𝟙 A ≫ b)) ((adj b).comp (adj (𝟙 A)))).symm
        (pushforwardComp (𝟙 A) b).symm).hom.app F).app ⊤) ≫
      (eqToHom (congrArg (fun f ↦ (L f).obj F) (Category.id_comp b))).app ⊤ = 𝟙 _ := by
  have hc := identityComparison L adj b F
  have hs := unitId_sections (L (𝟙 A)) (adj (𝟙 A)) ((L b).obj F)
  have hi : homOfLE (𝟙 A : A ⟶ A).preimage_top.ge = 𝟙 (⊤ : Opens A) := rfl
  unfold sectionsUnitOfAdjunction
  erw [hi, op_id, ((L (𝟙 A)).obj ((L b).obj F)).presheaf.map_id, Category.comp_id]
  have hct := congrArg (fun φ ↦ φ.app ⊤) hc
  change (((conjugateIsoEquiv (adj (𝟙 A ≫ b)) ((adj b).comp (adj (𝟙 A)))).symm
      (pushforwardComp (𝟙 A) b).symm).hom.app F).app ⊤ ≫
      (eqToHom (congrArg (fun f ↦ (L f).obj F) (Category.id_comp b))).app ⊤ =
      ((Adjunction.leftAdjointIdIso (adj (𝟙 A)) (pushforwardId A)).hom.app
        ((L b).obj F)).app ⊤ at hct
  erw [hct]
  exact hs

/-- The normalized composition map for a family of left adjoints.
Source: Stacks, Tag 03DR (blueprint: lem-sc-etale-qcoherent-presheaf-functorial). -/
private def compOfAdjunction
    (L : ∀ {A B : Scheme.{u}}, (A ⟶ B) → B.Modules ⥤ A.Modules)
    (adj : ∀ {A B : Scheme.{u}} (f : A ⟶ B), L f ⊣ pushforward f)
    {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) :
    L b ⋙ L a ≅ L (a ≫ b) :=
  (conjugateIsoEquiv (adj (a ≫ b)) ((adj b).comp (adj a))).symm
    (pushforwardComp a b).symm

/-- Naturality of the unit on global sections.
Source: Stacks, Tag 03DR (blueprint: lem-sc-etale-qcoherent-presheaf-functorial). -/
private theorem sectionsUnit_naturality {A B : Scheme.{u}} (f : A ⟶ B)
    (L : B.Modules ⥤ A.Modules) (adj : L ⊣ pushforward f)
    {M N : B.Modules} (φ : M ⟶ N) :
    φ.app ⊤ ≫ sectionsUnitOfAdjunction f L adj N =
      sectionsUnitOfAdjunction f L adj M ≫ (L.map φ).app ⊤ := by
  have hu := congrArg (fun t ↦ t.app ⊤) (adj.unit_naturality φ).symm
  change φ.app ⊤ ≫ (adj.unit.app N).app ⊤ =
    (adj.unit.app M).app ⊤ ≫ (L.map φ).app (f ⁻¹ᵁ ⊤) at hu
  have hn := (L.map φ).val.naturality (homOfLE f.preimage_top.ge).op
  have ht := congrArg (fun t ↦ (forget₂ _ AddCommGrpCat).map t) hn
  change (L.obj M).presheaf.map (homOfLE f.preimage_top.ge).op ≫ (L.map φ).app ⊤ =
    (L.map φ).app (f ⁻¹ᵁ ⊤) ≫
      (L.obj N).presheaf.map (homOfLE f.preimage_top.ge).op at ht
  unfold sectionsUnitOfAdjunction
  rw [← Category.assoc, hu, Category.assoc, ← ht, ← Category.assoc]

/-- The unit equation before taking global sections.
Source: Stacks, Tag 03DR (blueprint: lem-sc-etale-qcoherent-presheaf-functorial). -/
private theorem comp_unit
    (L : ∀ {A B : Scheme.{u}}, (A ⟶ B) → B.Modules ⥤ A.Modules)
    (adj : ∀ {A B : Scheme.{u}} (f : A ⟶ B), L f ⊣ pushforward f)
    {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) (G : C.Modules) :
    (adj (a ≫ b)).unit.app G ≫ (pushforwardComp a b).inv.app _ =
      (adj b).unit.app G ≫ (pushforward b).map ((adj a).unit.app ((L b).obj G)) ≫
        (pushforward a ⋙ pushforward b).map ((compOfAdjunction L adj a b).hom.app G) := by
  exact unit_conjugateEquiv_symm (adj (a ≫ b)) ((adj b).comp (adj a))
    (pushforwardComp a b).inv G

/-- The inverse image of the whole scheme contributes an identity restriction.
Source: Stacks, Tag 03DR (blueprint: lem-sc-etale-qcoherent-presheaf-functorial). -/
private theorem sectionsUnit_eq {A B : Scheme.{u}} (f : A ⟶ B)
    (L : B.Modules ⥤ A.Modules) (adj : L ⊣ pushforward f) (G : B.Modules) :
    sectionsUnitOfAdjunction f L adj G =
      (show Γ(G, ⊤) ⟶ Γ(L.obj G, ⊤) from (adj.unit.app G).app ⊤) := by
  have hi : homOfLE f.preimage_top.ge = 𝟙 (⊤ : Opens A) := rfl
  unfold sectionsUnitOfAdjunction
  erw [hi, op_id, (L.obj G).presheaf.map_id, Category.comp_id]

/-- Successive global-section units agree with the composite unit.
Source: Stacks, Tag 03DR (blueprint: lem-sc-etale-qcoherent-presheaf-functorial). -/
private theorem sectionsUnit_comp
    (L : ∀ {A B : Scheme.{u}}, (A ⟶ B) → B.Modules ⥤ A.Modules)
    (adj : ∀ {A B : Scheme.{u}} (f : A ⟶ B), L f ⊣ pushforward f)
    {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) (G : C.Modules) :
    sectionsUnitOfAdjunction b (L b) (adj b) G ≫
      sectionsUnitOfAdjunction a (L a) (adj a) ((L b).obj G) ≫
      ((compOfAdjunction L adj a b).hom.app G).app ⊤ =
    sectionsUnitOfAdjunction (a ≫ b) (L (a ≫ b)) (adj (a ≫ b)) G := by
  have hu := congrArg (fun t ↦ t.app ⊤) (comp_unit L adj a b G)
  erw [sectionsUnit_eq, sectionsUnit_eq, sectionsUnit_eq]
  simp only [Hom.comp_app, pushforward_map_app, Functor.comp_map,
    pushforwardComp_inv_app_app] at hu
  change ((adj (a ≫ b)).unit.app G).app ⊤ ≫ 𝟙 _ =
    ((adj b).unit.app G).app ⊤ ≫
      ((adj a).unit.app ((L b).obj G)).app ⊤ ≫
      ((compOfAdjunction L adj a b).hom.app G).app ⊤ at hu
  erw [Category.comp_id] at hu
  exact hu.symm

/-- Associativity of the normalized comparison maps.
Source: Stacks, Tag 03DR; Mathlib `Adjunction.leftAdjointCompIso_assoc`
(blueprint: lem-sc-etale-qcoherent-presheaf-functorial). -/
private theorem compOfAdjunction_assoc
    (L : ∀ {A B : Scheme.{u}}, (A ⟶ B) → B.Modules ⥤ A.Modules)
    (adj : ∀ {A B : Scheme.{u}} (f : A ⟶ B), L f ⊣ pushforward f)
    {A B C D : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D) (F : D.Modules) :
    ((compOfAdjunction L adj a b).hom.app ((L c).obj F)) ≫
      (compOfAdjunction L adj (a ≫ b) c).hom.app F ≫
      eqToHom (congrArg (fun f ↦ (L f).obj F) (Category.assoc a b c)) =
    (L a).map ((compOfAdjunction L adj b c).hom.app F) ≫
      (compOfAdjunction L adj a (b ≫ c)).hom.app F := by
  have he : Functor.isoWhiskerLeft (pushforward a) (pushforwardComp b c) ≪≫
      pushforwardComp a (b ≫ c) =
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (pushforwardComp a b) (pushforward c) ≪≫
        pushforwardComp (a ≫ b) c := by
    ext M V x
    rfl
  have h := Adjunction.leftAdjointCompIso_assoc (adj c) (adj b) (adj a)
    (adj (b ≫ c)) (adj (a ≫ b)) (adj (a ≫ (b ≫ c)))
    (pushforwardComp b c) (pushforwardComp a b)
    (pushforwardComp (a ≫ b) c) (pushforwardComp a (b ≫ c)) he
  have hc := congrArg (fun e ↦ e.hom.app F) h
  dsimp only [Adjunction.leftAdjointCompIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.associator_inv_app] at hc
  erw [Category.id_comp] at hc
  erw [eqToHom_refl, Category.comp_id]
  exact hc

/-- The two section maps for three composable scheme morphisms agree.
Source: Stacks, Tag 03DR (blueprint: lem-sc-etale-qcoherent-presheaf-functorial). -/
private theorem tripleSections
    (L : ∀ {A B : Scheme.{u}}, (A ⟶ B) → B.Modules ⥤ A.Modules)
    (adj : ∀ {A B : Scheme.{u}} (f : A ⟶ B), L f ⊣ pushforward f)
    {A B C D : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D) (F : D.Modules) :
    sectionsUnitOfAdjunction (a ≫ b) (L (a ≫ b)) (adj (a ≫ b)) ((L c).obj F) ≫
      ((compOfAdjunction L adj (a ≫ b) c).hom.app F).app ⊤ ≫
      (eqToHom (congrArg (fun f ↦ (L f).obj F) (Category.assoc a b c))).app ⊤ =
    (sectionsUnitOfAdjunction b (L b) (adj b) ((L c).obj F) ≫
      ((compOfAdjunction L adj b c).hom.app F).app ⊤) ≫
    (sectionsUnitOfAdjunction a (L a) (adj a) ((L (b ≫ c)).obj F) ≫
      ((compOfAdjunction L adj a (b ≫ c)).hom.app F).app ⊤) := by
  have ha := congrArg (fun φ ↦ φ.app ⊤) (compOfAdjunction_assoc L adj a b c F)
  simp only [Hom.comp_app] at ha
  rw [← sectionsUnit_comp L adj a b ((L c).obj F)]
  simp only [Category.assoc]
  rw [ha]
  have hn := sectionsUnit_naturality a (L a) (adj a)
    ((compOfAdjunction L adj b c).hom.app F)
  dsimp only [Functor.comp_obj] at hn
  exact (by simpa only [Category.assoc] using
    congrArg (fun t ↦ sectionsUnitOfAdjunction b (L b) (adj b) ((L c).obj F) ≫
      t ≫ ((compOfAdjunction L adj a (b ≫ c)).hom.app F).app ⊤) hn.symm)

/-- Normalized sections restriction along a commutative triangle.
Source: Stacks, Tag 03DR (blueprint: lem-sc-etale-qcoherent-presheaf-functorial). -/
private def restrictionOfAdjunction
    (L : ∀ {A B : Scheme.{u}}, (A ⟶ B) → B.Modules ⥤ A.Modules)
    (adj : ∀ {A B : Scheme.{u}} (f : A ⟶ B), L f ⊣ pushforward f)
    {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) (d : A ⟶ C)
    (p : a ≫ b = d) (F : C.Modules) : Γ((L b).obj F, ⊤) ⟶ Γ((L d).obj F, ⊤) :=
  sectionsUnitOfAdjunction a (L a) (adj a) ((L b).obj F) ≫
    ((compOfAdjunction L adj a b).hom.app F).app ⊤ ≫
    (eqToHom (congrArg (fun f ↦ (L f).obj F) p)).app ⊤

/-- Composition of normalized sections restrictions along commutative triangles.
Source: Stacks, Tag 03DR (blueprint: lem-sc-etale-qcoherent-presheaf-functorial). -/
private theorem restrictionOfAdjunction_comp
    (L : ∀ {A B : Scheme.{u}}, (A ⟶ B) → B.Modules ⥤ A.Modules)
    (adj : ∀ {A B : Scheme.{u}} (f : A ⟶ B), L f ⊣ pushforward f)
    {A B C D : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D)
    (d : B ⟶ D) (e : A ⟶ D) (p : b ≫ c = d) (q : a ≫ d = e)
    (r : (a ≫ b) ≫ c = e) (F : D.Modules) :
    restrictionOfAdjunction L adj (a ≫ b) c e r F =
      restrictionOfAdjunction L adj b c d p F ≫
        restrictionOfAdjunction L adj a d e q F := by
  subst d
  subst e
  unfold restrictionOfAdjunction
  have h := tripleSections L adj a b c F
  simpa only [eqToHom_refl, Hom.id_app, Category.comp_id] using h

/-- Semilinearity of restrictions for arbitrary adjoints of scheme pushforward.
Source: Stacks, Tag 03DR (blueprint: lem-sc-etale-qcoherent-presheaf-functorial). -/
private theorem restrictionOfAdjunction_smul
    (L : ∀ {A B : Scheme.{u}}, (A ⟶ B) → B.Modules ⥤ A.Modules)
    (adj : ∀ {A B : Scheme.{u}} (f : A ⟶ B), L f ⊣ pushforward f)
    {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) (d : A ⟶ C)
    (p : a ≫ b = d) (F : C.Modules) (r : Γ(B, ⊤)) (s : Γ((L b).obj F, ⊤)) :
    restrictionOfAdjunction L adj a b d p F ((((L b).obj F).smul r).asHom.hom s) =
      (((L d).obj F).smul (a.appTop r)).asHom.hom (restrictionOfAdjunction L adj a b d p F s) := by
  change restrictionOfAdjunction L adj a b d p F (r • s) =
    a.appTop r • restrictionOfAdjunction L adj a b d p F s
  have hu : sectionsUnitOfAdjunction a (L a) (adj a) ((L b).obj F) (r • s) =
      a.appTop r • sectionsUnitOfAdjunction a (L a) (adj a) ((L b).obj F) s := by
    rw [sectionsUnit_eq]
    exact Hom.app_smul ((adj a).unit.app ((L b).obj F)) r s
  unfold restrictionOfAdjunction
  simp only [AddCommGrpCat.comp_apply, hu]
  erw [Hom.app_smul, Hom.app_smul]
  rfl

/-- Equality of multiplication endomorphisms is exactly pointwise semilinearity.
Source: Stacks, Tag 03DR (blueprint: lem-sc-etale-qcoherent-presheaf-functorial). -/
private theorem smulHom_eq_iff {A B : Scheme.{u}} (M : B.Modules) (N : A.Modules)
    (ρ : Γ(M, ⊤) ⟶ Γ(N, ⊤)) (r : Γ(B, ⊤)) (t : Γ(A, ⊤)) :
    (M.smul r).asHom ≫ ρ = ρ ≫ (N.smul t).asHom ↔ ∀ s, ρ (r • s) = t • ρ s := by
  constructor
  · intro h s
    exact congrArg (fun φ ↦ φ.hom s) h
  · intro h
    ext s
    exact h s

/-- The semilinearity equation as an equality of additive maps.
Source: Stacks, Tag 03DR (blueprint: lem-sc-etale-qcoherent-presheaf-functorial). -/
private theorem restrictionOfAdjunction_smulHom
    (L : ∀ {A B : Scheme.{u}}, (A ⟶ B) → B.Modules ⥤ A.Modules)
    (adj : ∀ {A B : Scheme.{u}} (f : A ⟶ B), L f ⊣ pushforward f)
    {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) (d : A ⟶ C)
    (p : a ≫ b = d) (F : C.Modules) (r : Γ(B, ⊤)) :
    (((L b).obj F).smul r).asHom ≫ restrictionOfAdjunction L adj a b d p F =
      restrictionOfAdjunction L adj a b d p F ≫ (((L d).obj F).smul (a.appTop r)).asHom := by
  apply (smulHom_eq_iff ((L b).obj F) ((L d).obj F)
    (restrictionOfAdjunction L adj a b d p F) r (a.appTop r)).mpr
  intro s
  exact restrictionOfAdjunction_smul L adj a b d p F r s

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- Restriction is semilinear over the map on global functions.
Source: Stacks, Tag 03DR (blueprint: lem-sc-etale-qcoherent-presheaf-functorial).
Proof: the unit is a module morphism into pushforward, whose scalar action is through
`g^♯`. Thus section pullback is additive and semilinear. The composition isomorphism
and the transport are module morphisms on the source scheme, hence are linear there. -/
theorem etaleTensorSectionsRestriction_smul {X : Scheme.{u}} (F : X.Modules)
    {U V : X.Etale} (g : V ⟶ U) (a : Γ(U.left, ⊤)) :
    (((tensorPullback U.hom).obj F).smul a).asHom ≫ etaleTensorSectionsRestriction F g =
      etaleTensorSectionsRestriction F g ≫
        (((tensorPullback V.hom).obj F).smul (g.left.appTop a)).asHom := by
  exact restrictionOfAdjunction_smulHom (@tensorPullback)
    (fun {A B} f ↦ Classical.choose (exists_tensorPullbackAdjunction f))
    g.left U.hom V.hom g.w F a

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- Identity restrictions are identities.
Source: Stacks, Tag 03DR (blueprint: lem-sc-etale-qcoherent-presheaf-functorial).
Proof: the unit equation for `c_{id,u}` says that `c_{id,u} ∘ η^{id}` and the identity
of `u^*` have the same conjugate under `u^* ⊣ u_*`. Uniqueness of conjugates makes them
equal. Evaluation on global sections gives the identity law. -/
theorem etaleTensorSectionsRestriction_id {X : Scheme.{u}} (F : X.Modules) (U : X.Etale) :
    etaleTensorSectionsRestriction F (𝟙 U) = 𝟙 _ := by
  exact identitySections (@tensorPullback)
    (fun {A B} f ↦ Classical.choose (exists_tensorPullbackAdjunction f)) U.hom F

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Restrictions compose contravariantly.
Source: Stacks, Tag 03DR (blueprint: lem-sc-etale-qcoherent-presheaf-functorial).
Proof: naturality of the unit of `h^* ⊣ h_*` moves `c_{g,u}` past section pullback by
`h`. Evaluating the unit equation of `c_{h,g}` identifies successive section pullbacks
with pullback along `h ≫ g`. The associativity of normalized left-adjoint composition
isomorphisms (lem-sc-left-adjoint-composition-iso-associativity) identifies the two maps
from `h^*g^*u^*F` to `(h ≫ g ≫ u)^*F`. These give `ρ_{h≫g} = ρ_g ≫ ρ_h`. -/
theorem etaleTensorSectionsRestriction_comp {X : Scheme.{u}} (F : X.Modules)
    {U V W : X.Etale} (h : W ⟶ V) (g : V ⟶ U) :
    etaleTensorSectionsRestriction F (h ≫ g) =
      etaleTensorSectionsRestriction F g ≫ etaleTensorSectionsRestriction F h := by
  exact restrictionOfAdjunction_comp (@tensorPullback)
    (fun {A B} f ↦ Classical.choose (exists_tensorPullbackAdjunction f))
    h.left g.left U.hom V.hom W.hom g.w h.w (h ≫ g).w F

/-- The presheaf `u ↦ Γ(U,u^*F)`, with the unit-normalized pullback restrictions.
Source: Stacks, Tag 03DR, equation (35.8.1), and Tag 03DU, item 4
(blueprint: lem-sc-etale-qcoherent-presheaf-functorial). -/
def etaleTensorSectionsPresheaf {X : Scheme.{u}} (F : X.Modules) :
    X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj U := Γ((tensorPullback U.unop.hom).obj F, ⊤)
  map g := etaleTensorSectionsRestriction F g.unop
  map_id U := etaleTensorSectionsRestriction_id F U.unop
  map_comp g h := etaleTensorSectionsRestriction_comp F h.unop g.unop

end
end AlgebraicGeometry.Scheme.Modules
