/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Ringed.Sheaf.RingedSheafSliceConstruction
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-!
# Presheaf extension along the element projection

Source: Stacks Project, Modules on Sites, Tags 04IE and 03DJ
(blueprint: lem-weil-pbc-element-presheaf-extension).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits DirectSum Opposite

namespace CategoryTheory

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Classical in
/-- Restriction of the direct-sum presheaf: the summand indexed by `s` goes to the summand
indexed by `A(v)(s)` through the restriction of `L`.

Source: Stacks Project, sites-modules.tex, Tags 04IE and 03CY
(blueprint: lem-weil-pbc-ringed-sheaf-slice-adjunction). -/
private noncomputable abbrev rawElementDirectSumMap {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u}) (A : Sheaf J (Type u))
    (L : PresheafOfModules.{u} (elementRing R A).obj) {U V : Cᵒᵖ} (f : U ⟶ V) :
    ModuleCat.of (R.obj.obj U) (⨁ s : A.obj.obj U, (L.obj (elementObj A U s) : Type u)) ⟶
      (ModuleCat.restrictScalars (R.obj.map f).hom).obj
        (ModuleCat.of (R.obj.obj V)
          (⨁ t : A.obj.obj V, (L.obj (elementObj A V t) : Type u))) :=
  ModuleCat.ofHom (Y := ((ModuleCat.restrictScalars (R.obj.map f).hom).obj
      (ModuleCat.of (R.obj.obj V)
        (⨁ t : A.obj.obj V, (L.obj (elementObj A V t) : Type u)))))
    (DirectSum.toModule (R.obj.obj U) (A.obj.obj U)
    ((ModuleCat.restrictScalars (R.obj.map f).hom).obj
      (ModuleCat.of (R.obj.obj V)
        (⨁ t : A.obj.obj V, (L.obj (elementObj A V t) : Type u)))) fun s ↦
    ((L.map (elementObjMap A f s) ≫
      (ModuleCat.restrictScalars (R.obj.map f).hom).map
        (ModuleCat.ofHom (DirectSum.lof (R.obj.obj V) (A.obj.obj V)
          (fun t ↦ (L.obj (elementObj A V t) : Type u)) (A.obj.map f s)))) :
      ModuleCat.of (R.obj.obj U) (L.obj (elementObj A U s) : Type u) ⟶ _).hom)

open Classical in
private theorem rawElementDirectSumMap_lof {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u}) (A : Sheaf J (Type u))
    (L : PresheafOfModules.{u} (elementRing R A).obj) {U V : Cᵒᵖ} (f : U ⟶ V)
    (s : A.obj.obj U) (x : L.obj (elementObj A U s)) :
    rawElementDirectSumMap R A L f
      (DirectSum.lof (R.obj.obj U) (A.obj.obj U)
        (fun t ↦ (L.obj (elementObj A U t) : Type u)) s x) =
    DirectSum.lof (R.obj.obj V) (A.obj.obj V)
      (fun t ↦ (L.obj (elementObj A V t) : Type u)) (A.obj.map f s)
      (L.map (elementObjMap A f s) x) := by
  classical
  change (DirectSum.toModule (R.obj.obj U) (A.obj.obj U) _ _)
    (DirectSum.lof (R.obj.obj U) (A.obj.obj U)
      (fun t ↦ (L.obj (elementObj A U t) : Type u)) s x) = _
  rw [DirectSum.toModule_lof]
  rfl

/-- The direct-sum restriction preserves identities.

Source: Stacks Project, sites-modules.tex, Tag 04IE
(blueprint: lem-weil-pbc-ringed-sheaf-slice-adjunction).
Proof: check on each summand indexed by s. The element-map for the identity fixes
(U,s), the restriction of L is the identity after the restriction-of-scalars identity
comparison, and the target summand is again s because A preserves identities.
Thus the two maps agree on every direct-sum inclusion; the direct-sum universal
property gives equality. -/
private theorem rawElementDirectSumMap_id {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u}) (A : Sheaf J (Type u))
    (L : PresheafOfModules.{u} (elementRing R A).obj) (U : Cᵒᵖ) :
    rawElementDirectSumMap R A L (𝟙 U) =
      (ModuleCat.restrictScalarsId' (R.obj.map (𝟙 U)).hom
        (congrArg RingCat.Hom.hom (R.obj.map_id U))).inv.app _ := by
  classical
  ext s x
  simp only [LinearMap.comp_apply]
  change (DirectSum.toModule (R.obj.obj U) (A.obj.obj U) _ _)
    (DirectSum.lof (R.obj.obj U) (A.obj.obj U)
      (fun t ↦ (L.obj (elementObj A U t) : Type u)) s x) = _
  rw [DirectSum.toModule_lof]
  change DirectSum.lof (R.obj.obj U) (A.obj.obj U)
    (fun t ↦ (L.obj (elementObj A U t) : Type u)) (A.obj.map (𝟙 U) s)
    (L.map (elementObjMap A (𝟙 U) s) x) = DirectSum.lof (R.obj.obj U) (A.obj.obj U)
      (fun t ↦ (L.obj (elementObj A U t) : Type u)) s x
  have aux (t : A.obj.obj U) (ht : A.obj.map (𝟙 U) s = t) :
      DirectSum.lof (R.obj.obj U) (A.obj.obj U)
        (fun t ↦ (L.obj (elementObj A U t) : Type u)) t
        (L.map (Functor.Elements.homMk (x := A.obj.elementsMk U s)
          (y := A.obj.elementsMk U t) (𝟙 U) ht).op.op x) =
      DirectSum.lof (R.obj.obj U) (A.obj.obj U)
        (fun t ↦ (L.obj (elementObj A U t) : Type u)) s x := by
    have h : s = t := by simpa only [Functor.map_id_apply] using ht
    cases h
    change DirectSum.lof (R.obj.obj U) (A.obj.obj U)
      (fun t ↦ (L.obj (elementObj A U t) : Type u)) s (L.map (𝟙 _) x) = _
    simp
  exact aux _ rfl

/-- The direct-sum restriction is compatible with composition.

Source: Stacks Project, sites-modules.tex, Tag 04IE
(blueprint: lem-weil-pbc-ringed-sheaf-slice-adjunction).
Proof: check on the summand indexed by s. The two successive restrictions send it to
A(g)(A(f)(s)), which equals A(f followed by g)(s) by functoriality of A. The element
arrows compose accordingly; functoriality of L identifies their linear maps after
restrictScalarsComp. Both direct-sum maps therefore have the same composite with
every summand inclusion. The direct-sum universal property gives the equality. -/
private theorem rawElementDirectSumMap_comp {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u}) (A : Sheaf J (Type u))
    (L : PresheafOfModules.{u} (elementRing R A).obj) {U V W : Cᵒᵖ} (f : U ⟶ V) (g : V ⟶ W) :
    rawElementDirectSumMap R A L (f ≫ g) =
      rawElementDirectSumMap R A L f ≫
        (ModuleCat.restrictScalars _).map (rawElementDirectSumMap R A L g) ≫
          (ModuleCat.restrictScalarsComp' (R.obj.map f).hom (R.obj.map g).hom
            (R.obj.map (f ≫ g)).hom
            (congrArg RingCat.Hom.hom <| R.obj.map_comp f g)).inv.app _ := by
  classical
  ext s x
  simp only [LinearMap.comp_apply]
  change rawElementDirectSumMap R A L (f ≫ g)
    (DirectSum.lof (R.obj.obj U) (A.obj.obj U)
      (fun t ↦ (L.obj (elementObj A U t) : Type u)) s x) =
    rawElementDirectSumMap R A L g
      (rawElementDirectSumMap R A L f
        (DirectSum.lof (R.obj.obj U) (A.obj.obj U)
          (fun t ↦ (L.obj (elementObj A U t) : Type u)) s x))
  have aux (t : A.obj.obj W) (ht : A.obj.map (f ≫ g) s = t) :
      rawElementDirectSumMap R A L (f ≫ g)
        (DirectSum.lof (R.obj.obj U) (A.obj.obj U)
          (fun t ↦ (L.obj (elementObj A U t) : Type u)) s x) =
      DirectSum.lof (R.obj.obj W) (A.obj.obj W)
        (fun t ↦ (L.obj (elementObj A W t) : Type u)) t
        (L.map (Functor.Elements.homMk (x := A.obj.elementsMk U s)
          (y := A.obj.elementsMk W t) (f ≫ g) ht).op.op x) := by
    cases ht
    exact rawElementDirectSumMap_lof R A L (f ≫ g) s x
  rw [aux _ (A.obj.map_comp_apply f g s), rawElementDirectSumMap_lof,
    rawElementDirectSumMap_lof]
  apply congrArg (DirectSum.lof (R.obj.obj W) (A.obj.obj W)
    (fun t ↦ (L.obj (elementObj A W t) : Type u)) (A.obj.map g (A.obj.map f s)))
  have h : (Functor.Elements.homMk (x := A.obj.elementsMk U s)
      (y := A.obj.elementsMk W (A.obj.map g (A.obj.map f s))) (f ≫ g)
        (A.obj.map_comp_apply f g s)).op.op =
      elementObjMap A f s ≫ elementObjMap A g (A.obj.map f s) := by
    apply Quiver.Hom.unop_inj
    apply Quiver.Hom.unop_inj
    apply Functor.Elements.hom_ext
    rfl
  rw [h]
  exact L.map_comp_apply _ _ x

/-- The presheaf of `R`-modules `U ↦ ⨁_{s ∈ A(U)} L(U,s)` whose module sheafification is the
extension by zero of `L`.

Source: Stacks Project, sites-modules.tex, Tags 04IE and 03CY; sites.tex, Tag 0791
(blueprint: lem-weil-pbc-ringed-sheaf-slice-adjunction). -/
private noncomputable abbrev rawElementDirectSumPresheaf {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u}) (A : Sheaf J (Type u))
    (L : PresheafOfModules.{u} (elementRing R A).obj) : PresheafOfModules.{u} R.obj where
  obj U := ModuleCat.of (R.obj.obj U)
    (⨁ s : A.obj.obj U, (L.obj (elementObj A U s) : Type u))
  map f := rawElementDirectSumMap R A L f
  map_id U := rawElementDirectSumMap_id R A L U
  map_comp f g := rawElementDirectSumMap_comp R A L f g

open Classical in
private noncomputable abbrev sumToRestriction
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) (A : Sheaf J (Type u))
    (L : PresheafOfModules.{u} (elementRing R A).obj) (M : PresheafOfModules.{u} R.obj)
    (f : rawElementDirectSumPresheaf R A L ⟶ M) :
    L ⟶ (PresheafOfModules.pushforward (F := elementProjection A)
      (𝟙 (elementRing R A).obj)).obj M where
  app e := ModuleCat.ofHom ((f.app e.unop.unop.1).hom.comp
    (DirectSum.lof (R.obj.obj e.unop.unop.1) (A.obj.obj e.unop.unop.1)
      (fun s ↦ (L.obj (elementObj A e.unop.unop.1 s) : Type u)) e.unop.unop.2))
  naturality := by
    rintro ⟨⟨@⟨U, s⟩⟩⟩ ⟨⟨@⟨V, t⟩⟩⟩ ⟨g, hg⟩
    change U ⟶ V at g
    change A.obj.map g s = t at hg
    subst t
    ext x
    have h := PresheafOfModules.naturality_apply f g
      (DirectSum.lof (R.obj.obj U) (A.obj.obj U)
        (fun s ↦ (L.obj (elementObj A U s) : Type u)) s x)
    simpa only [rawElementDirectSumPresheaf, rawElementDirectSumMap, ModuleCat.hom_comp,
      LinearMap.comp_apply, ModuleCat.hom_ofHom, DirectSum.toModule_lof,
      ModuleCat.restrictScalars, ModuleCat.RestrictScalars.map'] using! h

open Classical in
private noncomputable abbrev restrictionToSum
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) (A : Sheaf J (Type u))
    (L : PresheafOfModules.{u} (elementRing R A).obj) (M : PresheafOfModules.{u} R.obj)
    (f : L ⟶ (PresheafOfModules.pushforward (F := elementProjection A)
      (𝟙 (elementRing R A).obj)).obj M) :
    rawElementDirectSumPresheaf R A L ⟶ M where
  app U := ModuleCat.ofHom (DirectSum.toModule (R.obj.obj U) (A.obj.obj U) (M.obj U)
    (fun s ↦ (f.app (elementObj A U s)).hom))
  naturality := by
    intro U V g
    apply ModuleCat.hom_ext
    apply DirectSum.linearMap_ext
    intro s
    ext x
    have h := PresheafOfModules.naturality_apply f (elementObjMap A g s) x
    change DirectSum.toModule (R.obj.obj V) (A.obj.obj V) (M.obj V)
      (fun t ↦ (f.app (elementObj A V t)).hom)
        (rawElementDirectSumMap R A L g
          (DirectSum.lof (R.obj.obj U) (A.obj.obj U)
            (fun t ↦ (L.obj (elementObj A U t) : Type u)) s x)) = _
    simp only [rawElementDirectSumMap, ModuleCat.hom_ofHom, DirectSum.toModule_lof,
      ModuleCat.hom_comp, LinearMap.comp_apply]
    change DirectSum.toModule (R.obj.obj V) (A.obj.obj V) (M.obj V)
      (fun t ↦ (f.app (elementObj A V t)).hom)
        (DirectSum.lof (R.obj.obj V) (A.obj.obj V)
          (fun t ↦ (L.obj (elementObj A V t) : Type u)) (A.obj.map g s)
            (L.map (elementObjMap A g s) x)) = _
    rw [DirectSum.toModule_lof]
    exact h

open Classical in
private noncomputable abbrev sumHomEquiv
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) (A : Sheaf J (Type u))
    (L : PresheafOfModules.{u} (elementRing R A).obj) (M : PresheafOfModules.{u} R.obj) :
    (rawElementDirectSumPresheaf R A L ⟶ M) ≃
      (L ⟶ (PresheafOfModules.pushforward (F := elementProjection A)
        (𝟙 (elementRing R A).obj)).obj M) where
  toFun := sumToRestriction R A L M
  invFun := restrictionToSum R A L M
  left_inv f := by
    ext U : 1
    apply ModuleCat.hom_ext
    apply DirectSum.linearMap_ext
    intro s
    ext x
    simp only [ModuleCat.hom_ofHom, LinearMap.comp_apply, DirectSum.toModule_lof]
  right_inv f := by
    ext e x
    change DirectSum.toModule (R.obj.obj e.unop.unop.1) (A.obj.obj e.unop.unop.1)
      (M.obj e.unop.unop.1) (fun s ↦ (f.app (elementObj A e.unop.unop.1 s)).hom)
        (DirectSum.lof (R.obj.obj e.unop.unop.1) (A.obj.obj e.unop.unop.1)
          (fun s ↦ (L.obj (elementObj A e.unop.unop.1 s) : Type u))
          e.unop.unop.2 x) = f.app e x
    rw [DirectSum.toModule_lof]
    rfl

@[no_expose] private noncomputable def rawSumFunctor
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) (A : Sheaf J (Type u)) :
    PresheafOfModules.{u} (elementRing R A).obj ⥤ PresheafOfModules.{u} R.obj :=
  Adjunction.leftAdjointOfEquiv (fun L M ↦ sumHomEquiv R A L M)
    (by intro L M N g f; ext e x; rfl)

@[no_expose] private noncomputable def rawSumAdjunction
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) (A : Sheaf J (Type u)) :
    rawSumFunctor R A ⊣ PresheafOfModules.pushforward
      (F := elementProjection A) (𝟙 (elementRing R A).obj) :=
  Adjunction.adjunctionOfEquivLeft (fun L M ↦ sumHomEquiv R A L M)
    (by intro L M N g f; ext e x; rfl)

open Classical in
private theorem rawSumFunctor_map_lof
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) (A : Sheaf J (Type u))
    {L N : PresheafOfModules.{u} (elementRing R A).obj} (f : L ⟶ N)
    (U : Cᵒᵖ) (s : A.obj.obj U) (x : L.obj (elementObj A U s)) :
    ((rawSumFunctor R A).map f).app U
      (DirectSum.lof (R.obj.obj U) (A.obj.obj U)
        (fun s ↦ (L.obj (elementObj A U s) : Type u)) s x) =
    DirectSum.lof (R.obj.obj U) (A.obj.obj U)
      (fun s ↦ (N.obj (elementObj A U s) : Type u)) s (f.app _ x) := by
  change DirectSum.toModule (R.obj.obj U) (A.obj.obj U) _ _
    (DirectSum.lof (R.obj.obj U) (A.obj.obj U)
      (fun t ↦ (L.obj (elementObj A U t) : Type u)) s x) = _
  rw [DirectSum.toModule_lof]
  rfl

private noncomputable abbrev fibreDiagram
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) (A : Sheaf J (Type u)) (U : Cᵒᵖ) :
    PresheafOfModules.{u} (elementRing R A).obj ⥤
      (Discrete (A.obj.obj U) ⥤ ModuleCat.{u} (R.obj.obj U)) where
  obj L := Discrete.functor (fun s ↦ L.obj (elementObj A U s))
  map f := Discrete.natTrans (fun s ↦ f.app (elementObj A U s.as))

private noncomputable instance fibreDiagram_preservesFiniteLimits
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) (A : Sheaf J (Type u)) (U : Cᵒᵖ) :
    PreservesFiniteLimits (fibreDiagram R A U) := by
  apply preservesFiniteLimits_of_evaluation
  intro s
  change PreservesFiniteLimits
    (PresheafOfModules.evaluation (elementRing R A).obj (elementObj A U s.as))
  infer_instance

open Classical in
@[no_expose] private noncomputable def rawSumEvaluationIso
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) (A : Sheaf J (Type u)) (U : Cᵒᵖ) :
    fibreDiagram R A U ⋙ colim ≅
      rawSumFunctor R A ⋙ PresheafOfModules.evaluation R.obj U :=
  NatIso.ofComponents (fun L ↦ by
    exact ModuleCat.coprodIsoDirectSum
      (fun s : A.obj.obj U ↦ (show ModuleCat (R.obj.obj U) from L.obj (elementObj A U s)))) (by
      intro L N f
      apply Sigma.hom_ext
      intro s
      dsimp only [Functor.comp_map, Functor.comp_obj, fibreDiagram, colim_map]
      rw [ι_colimMap_assoc]
      erw [ModuleCat.ι_coprodIsoDirectSum_hom]
      rw [← Category.assoc]
      erw [ModuleCat.ι_coprodIsoDirectSum_hom]
      ext x
      change _ = ((rawSumFunctor R A).map f).app U
        (DirectSum.lof (R.obj.obj U) (A.obj.obj U)
          (fun t ↦ (L.obj (elementObj A U t) : Type u)) s x)
      rw [rawSumFunctor_map_lof]
      rfl)

/-- The direct-sum presheaf is the presheaf left adjoint evaluated on a module sheaf.
Source: Stacks Project, Modules on Sites, Tags 04IE and 03CY
(blueprint: lem-weil-pbc-element-presheaf-extension).
Proof: a linear map from a sum is precisely a family of linear maps from its summands.
Naturality on the lifted element arrows is exactly naturality of this family, giving
an isomorphism by uniqueness of the representing object. -/
theorem element_module_presheaf_extension_formula
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) (A : Sheaf J (Type u))
    (L : ringedSiteModules (elementRing R A)) :
    Nonempty ((PresheafOfModules.pullback.{u}
      (F := elementProjection A) (𝟙 (elementRing R A).obj)).obj L.val ≅
        elementDirectSumPresheaf R A L) := by
  let core : (PresheafOfModules.pushforward (F := elementProjection A)
      (𝟙 (elementRing R A).obj) ⋙ coyoneda.obj (op L.val)).CorepresentableBy
        (elementDirectSumPresheaf R A L) :=
    { homEquiv := sumHomEquiv R A L.val _
      homEquiv_comp := by
        intro M N g f
        change sumToRestriction R A L.val N (f ≫ g) =
          sumToRestriction R A L.val M f ≫ _
        ext e x
        rfl }
  let adj := PresheafOfModules.pullbackPushforwardAdjunction
    (F := elementProjection A) (𝟙 (elementRing R A).obj)
  exact ⟨(adj.corepresentableBy L.val).uniqueUpToIso core⟩

/-- Before sheafification, extension along the element projection is a direct sum
of fibres and preserves finite limits.

Source: Stacks Project, sites-modules.tex, Tags 04IE, 03CY and 03DJ, with the
comma-category calculation of sites.tex, Tag 0791
(blueprint: lem-weil-pbc-element-presheaf-extension).
Proof: At U, compute the presheaf left adjoint as the colimit over triples
(V,t,φ : U → V). Every triple receives a unique map from (U,A(φ)t,id).
Consequently the opposite of the discrete subcategory of these identity triples
is final in the colimit index, and the colimit is the direct sum over s in A(U).
The map on a restriction sends the s inclusion through L of the lifted arrow
to the A(v)s inclusion; these are exactly elementDirectSumMap. This proves the
formula including all restrictions. The same computation applies to arbitrary
presheaves of modules. Their kernels and finite products are computed on sections.
Direct sums preserve finite products and kernels: a finitely supported tuple is
in a kernel precisely when each coordinate is; finite unions of supports give
the inverse for finite products. The zero object is preserved even for an empty
fibre. Thus presheaf extension preserves finite limits. -/
theorem element_module_presheaf_extension
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) (A : Sheaf J (Type u)) :
    PreservesFiniteLimits (PresheafOfModules.pullback.{u}
      (F := elementProjection A) (𝟙 (elementRing R A).obj)) ∧
    (∀ L : ringedSiteModules (elementRing R A),
      Nonempty ((PresheafOfModules.pullback.{u}
        (F := elementProjection A) (𝟙 (elementRing R A).obj)).obj L.val ≅
          elementDirectSumPresheaf R A L)) := by
  classical
  have heval (U : Cᵒᵖ) : PreservesFiniteLimits
      (rawSumFunctor R A ⋙ PresheafOfModules.evaluation R.obj U) := by
    have : PreservesFiniteLimits (fibreDiagram R A U ⋙ colim) :=
      comp_preservesFiniteLimits _ _
    exact preservesFiniteLimits_of_natIso (rawSumEvaluationIso R A U)
  have hraw : PreservesFiniteLimits (rawSumFunctor R A) := by
    constructor
    intro K _ _
    constructor
    intro G
    constructor
    intro c hc
    constructor
    apply PresheafOfModules.evaluationJointlyReflectsLimits
    intro U
    exact isLimitOfPreserves
      (rawSumFunctor R A ⋙ PresheafOfModules.evaluation R.obj U) hc
  refine ⟨?_, element_module_presheaf_extension_formula R A⟩
  exact preservesFiniteLimits_of_natIso
    ((rawSumAdjunction R A).leftAdjointUniq
      (PresheafOfModules.pullbackPushforwardAdjunction
        (F := elementProjection A) (𝟙 (elementRing R A).obj)))

end CategoryTheory
end
