/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

/-!
# Derived change of rings on a ringed site

Source: literature/stacks-project/sites-cohomology.tex, Tags 06YT, 06YY, and
literature/stacks-project/derived.tex, Tag 06XN
(auxiliary; not a blueprint node).

The change of rings `- ⊗_O O'` is the landed `SheafOfModules.changeOfRings φ` on objects
and `SheafOfModules.changeOfRingsHom φ` on morphisms (def-pur-sheaf-tensor-product); the
statement asserts an additive functor `E` with exactly these objects and maps, and uses
`E.mapHomologicalComplex` (termwise change of rings of complexes) and
`E.mapHomotopyCategory ⋙ DerivedCategory.Qh` (the functor `K(O) → D(O')`).

## Main definitions

- `derivedChangeRingIndependentCoefficients`: the underlying ring sheaf in independent site
  universes.

## Main statements

- `derivedChangeOfRingsIndependentCoefficients`: the full derived-change-of-rings statement without
  identifying the object and morphism universes of the site.
-/

@[expose] public section

universe w r u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace SheafOfModules

/-- Forget commutativity without identifying the two universes of the site.
Source: Stacks Tag 06YY (auxiliary; not a blueprint node). -/
noncomputable abbrev derivedChangeRingIndependentCoefficients {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    (O : Sheaf J CommRingCat.{r}) :=
  (sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj O

section IndependentTensor

set_option hygiene false in
local notation "𝓡" R =>
  (sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R

attribute [local instance] isMonoidal_W_independentCoefficients
attribute [local irreducible] monoidalCategory

-- Step 1: the same tensor abelian group, with the two scalar actions identified.
set_option backward.isDefEq.respectTransparency false in
private noncomputable def sectionTensorIso
    {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasWeakSheafify J AddCommGrpCat.{r}]
    {O O' : Sheaf J CommRingCat.{r}} (φ : O ⟶ O')
    (M : SheafOfModules.{r} (𝓡 O))
    (X : Cᵒᵖ) :
    ((PresheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ).hom).obj
        (changeOfRingsPresheaf φ M)).obj X ≅
      (((restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
        (unit (𝓡 O'))).val ⊗ M.val).obj X := by
  let e : (((PresheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ).hom).obj
        (changeOfRingsPresheaf φ M)).obj X) ≃ₗ[O.obj.obj X]
      ((((restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
        (unit (𝓡 O'))).val ⊗ M.val).obj X) :=
    { toFun := fun x ↦ x
      invFun := fun x ↦ x
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := by
        intro r x
        induction x using TensorProduct.inductionOn with
        | tmul s m => rfl
        | add x y hx hy => simpa only [smul_add] using congrArg₂ (· + ·) hx hy }
  exact e.toModuleIso

set_option backward.isDefEq.respectTransparency false in
private noncomputable def presheafTensorIso
    {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasWeakSheafify J AddCommGrpCat.{r}]
    {O O' : Sheaf J CommRingCat.{r}} (φ : O ⟶ O')
    (M : SheafOfModules.{r} (𝓡 O)) :
    (PresheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ).hom).obj
        (changeOfRingsPresheaf φ M) ≅
      ((restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
        (unit (𝓡 O'))).val ⊗ M.val :=
  PresheafOfModules.isoMk (sectionTensorIso φ M) (by
    intro X Y f
    ext x
    induction x using TensorProduct.inductionOn with
    | tmul s m =>
      change changeOfRingsMap φ M f (s ⊗ₜ m) = _
      rw [show changeOfRingsMap φ M f (s ⊗ₜ m) = _ from
        Classical.choose_spec (exists_changeOfRingsMap φ M f) s m]
      rfl
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy)

private noncomputable def changePresheafHom
    {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasWeakSheafify J AddCommGrpCat.{r}]
    {O O' : Sheaf J CommRingCat.{r}} (φ : O ⟶ O')
    {M N : SheafOfModules.{r} (𝓡 O)} (a : M ⟶ N) :
    changeOfRingsPresheaf φ M ⟶ changeOfRingsPresheaf φ N :=
  { app := fun X ↦ (ModuleCat.extendScalars (φ.hom.app X).hom).map (a.val.app X)
    naturality := changeOfRingsHom_naturality φ M a }

set_option backward.isDefEq.respectTransparency false in
private lemma presheafTensorIso_naturality
    {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasWeakSheafify J AddCommGrpCat.{r}]
    {O O' : Sheaf J CommRingCat.{r}} (φ : O ⟶ O')
    {M N : SheafOfModules.{r} (𝓡 O)} (a : M ⟶ N) :
    (PresheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ).hom).map
        (changePresheafHom φ a) ≫ (presheafTensorIso φ N).hom =
      (presheafTensorIso φ M).hom ≫
        ((restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
          (unit (𝓡 O'))).val ◁ a.val := by
  ext X x
  induction x using TensorProduct.inductionOn with
  | tmul s m => rfl
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

-- Step 2: compare the underlying abelian sheaves using the sheafification API.
private noncomputable def underlyingSheafificationIso
    {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasWeakSheafify J AddCommGrpCat.{r}]
    {O O' : Sheaf J CommRingCat.{r}} (φ : O ⟶ O') :
    PresheafOfModules.sheafification (𝟙 (𝓡 O').obj) ⋙ toSheaf (𝓡 O') ≅
      PresheafOfModules.restrictScalars
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ).hom ⋙
        (PresheafOfModules.sheafification (𝟙 (𝓡 O).obj) ⋙ toSheaf (𝓡 O)) :=
  PresheafOfModules.sheafificationCompToSheaf (𝟙 (𝓡 O').obj) ≪≫
    (Functor.isoWhiskerRight (PresheafOfModules.restrictScalarsCompToPresheaf
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ).hom)
      (presheafToSheaf J AddCommGrpCat)).symm ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (PresheafOfModules.sheafificationCompToSheaf (𝟙 (𝓡 O).obj)).symm

-- Step 3: naturality of the existing tensor comparison, from the counit and tensorator.
set_option backward.isDefEq.respectTransparency false in
private lemma tensorComparison_naturality
    {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasWeakSheafify J AddCommGrpCat.{r}]
    {O : Sheaf J CommRingCat.{r}}
    (S : SheafOfModules.{r} (𝓡 O)) {M N : SheafOfModules.{r} (𝓡 O)} (a : M ⟶ N) :
    letI := monoidalCategory O
    (PresheafOfModules.sheafification (𝟙 (𝓡 O).obj)).map (S.val ◁ a.val) ≫
      (tensorObjIsoSheafification S N).inv =
    (tensorObjIsoSheafification S M).inv ≫ S ◁ a := by
  let := monoidalCategory O
  let A := PresheafOfModules.sheafification (𝟙 (𝓡 O).obj)
  let ε : forget (𝓡 O) ⋙ A ≅ 𝟭 _ :=
    asIso (PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 O).obj)).counit
  let c (M : SheafOfModules.{r} (𝓡 O)) : A.obj M.val ≅ M := ε.app M
  apply (cancel_mono (tensorObjIsoSheafification S N).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply (cancel_epi (tensorObjIsoSheafification S M).hom).mp
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  change ((c S).inv ⊗ₘ (c M).inv) ≫
      Functor.LaxMonoidal.μ A S.val M.val ≫ A.map (S.val ◁ a.val) =
    S ◁ a ≫ ((c S).inv ⊗ₘ (c N).inv) ≫
      Functor.LaxMonoidal.μ A S.val N.val
  rw [← Functor.LaxMonoidal.μ_natural_right]
  have hn : (c M).inv ≫ A.map a.val = a ≫ (c N).inv :=
    (ε.inv.naturality a).symm
  have h : ((c S).inv ⊗ₘ (c M).inv) ≫
      (A.obj S.val ◁ A.map a.val) =
      S ◁ a ≫ ((c S).inv ⊗ₘ (c N).inv) := by
    calc
      _ = (c S).inv ⊗ₘ ((c M).inv ≫ A.map a.val) := by
        simpa only [Category.comp_id, id_tensorHom] using
          (tensorHom_comp_tensorHom (c S).inv (c M).inv
            (𝟙 (A.obj S.val)) (A.map a.val))
      _ = (c S).inv ⊗ₘ (a ≫ (c N).inv) :=
        congrArg (fun f ↦ (c S).inv ⊗ₘ f) hn
      _ = _ := by
        simpa only [Category.id_comp, id_tensorHom] using
          (tensorHom_comp_tensorHom (𝟙 S) a (c S).inv (c N).inv).symm
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun f ↦ f ≫ Functor.LaxMonoidal.μ A S.val N.val) h) |>.trans
      (Category.assoc _ _ _)

set_option backward.isDefEq.respectTransparency false in
/-- Source: Stacks Project, Tag 03EK and Tag 06YY, degree-zero tensor comparison.

Proof: Put U = restriction along φ and S = U(O'). Before sheafification the
identity on pure tensors identifies the restricted sectionwise scalar extension
O'(V) tensor over O(V) M(V) with the sectionwise tensor of S and M. It respects
restrictions because both constructions restrict each tensor factor, and respects
module morphisms because both apply id tensor a. The standard natural isomorphisms
for forgetting scalar restriction and module sheafification identify their underlying
abelian sheaves. Sheafifying the presheaf tensor comparison therefore gives the
asserted isomorphisms of abelian sheaves, sufficient to detect acyclicity.
The counit at the already-sheaf module S and the monoidal localization comparison
identify the resulting sheafification with S tensor M. Naturality survives each
comparison and sheafification, giving the displayed equation for every a.
This uses no flatness; the identity on tensors also covers zero rings and modules.
(auxiliary; not a blueprint node) -/
private theorem exists_changeOfRings_tensor_comparison_independent
    {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasWeakSheafify J AddCommGrpCat.{r}]
    {O O' : Sheaf J CommRingCat.{r}} (φ : O ⟶ O') :
    letI := monoidalCategory O
    let U := restrictScalars.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map φ)
    let S := U.obj (unit (𝓡 O'))
    ∃ e : ∀ M : SheafOfModules.{r} (𝓡 O),
      (toSheaf (𝓡 O')).obj (changeOfRings φ M) ≅ (toSheaf (𝓡 O)).obj (S ⊗ M),
      ∀ {M N : SheafOfModules.{r} (𝓡 O)} (a : M ⟶ N),
        (toSheaf (𝓡 O')).map (changeOfRingsHom φ M a) ≫ (e N).hom =
          (e M).hom ≫ (toSheaf (𝓡 O)).map (S ◁ a) := by
  let := monoidalCategory O
  let U := restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)
  let S := U.obj (unit (𝓡 O'))
  let A := PresheafOfModules.sheafification (𝟙 (𝓡 O).obj)
  let V := toSheaf (𝓡 O)
  let e (M : SheafOfModules.{r} (𝓡 O)) :
      (toSheaf (𝓡 O')).obj (changeOfRings φ M) ≅ V.obj (S ⊗ M) :=
    (underlyingSheafificationIso φ).app (changeOfRingsPresheaf φ M) ≪≫
      V.mapIso (A.mapIso (presheafTensorIso φ M) ≪≫
        (tensorObjIsoSheafification S M).symm)
  refine ⟨e, ?_⟩
  intro M N a
  have hr := (underlyingSheafificationIso φ).hom.naturality (changePresheafHom φ a)
  have hp := congrArg (fun f ↦ V.map (A.map f)) (presheafTensorIso_naturality φ a)
  simp only [Functor.map_comp] at hp
  have ht := congrArg V.map (tensorComparison_naturality S a)
  simp only [Functor.map_comp] at ht
  change (toSheaf (𝓡 O')).map
      ((PresheafOfModules.sheafification (𝟙 (𝓡 O').obj)).map (changePresheafHom φ a)) ≫
        (e N).hom = (e M).hom ≫ V.map (S ◁ a)
  dsimp only [e, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_hom]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hr, reassoc_of% hp, ht]

section TensorAcyclicity

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasSheafify J AddCommGrpCat.{r}]
  {O : Sheaf J CommRingCat.{r}}

attribute [local instance] monoidalCategory symmetricCategory
  preservesZeroMorphisms_curriedTensor_independentCoefficients
  preservesZeroMorphisms_curriedTensor_obj_independentCoefficients

private theorem tensorLeft_additive_independent (S : SheafOfModules.{r} (𝓡 O)) :
    (tensorLeft S).Additive := by
  have : (PresheafOfModules.sheafification (𝟙 (𝓡 O).obj)).Additive :=
    (PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 O).obj)).left_adjoint_additive
  have : (tensorLeft S.val).Additive := by
    constructor
    intro M N f g
    apply PresheafOfModules.hom_ext
    intro X
    let : CommRing ((𝓡 O).obj.obj X) := inferInstanceAs (CommRing (O.obj.obj X))
    change S.val.obj X ◁ (f.app X + g.app X) =
      S.val.obj X ◁ f.app X + S.val.obj X ◁ g.app X
    exact MonoidalPreadditive.whiskerLeft_add _ _
  let T := forget (𝓡 O) ⋙ tensorLeft S.val ⋙
    PresheafOfModules.sheafification (𝟙 (𝓡 O).obj)
  have : T.Additive := inferInstance
  let e : T ≅ tensorLeft S := NatIso.ofComponents
    (fun M ↦ (tensorObjIsoSheafification S M).symm)
    (fun a ↦ tensorComparison_naturality S a)
  exact Functor.additive_of_iso e

private theorem monoidalPreadditive_independent :
    MonoidalPreadditive (SheafOfModules.{r} (𝓡 O)) := by
  have (M : SheafOfModules.{r} (𝓡 O)) : (tensorLeft M).Additive :=
    tensorLeft_additive_independent M
  have (M : SheafOfModules.{r} (𝓡 O)) : (tensorRight M).Additive :=
    Functor.additive_of_iso (F := tensorLeft M)
      (BraidedCategory.tensorLeftIsoTensorRight M)
  exact
    { whiskerLeft_zero := fun {X Y Z} ↦ (tensorLeft X).map_zero Y Z
      zero_whiskerRight := fun {X Y Z} ↦ (tensorRight X).map_zero Y Z
      whiskerLeft_add := fun {X Y Z} f g ↦ (tensorLeft X).map_add (f := f) (g := g)
      add_whiskerRight := fun {X Y Z} f g ↦ (tensorRight X).map_add (f := f) (g := g) }

attribute [local instance] monoidalPreadditive_independent

private noncomputable def tensor_symmetry
    (K L : CochainComplex (SheafOfModules.{r} (𝓡 O)) ℤ) :
    letI := monoidalCategory O
    CochainComplex.mapBifunctor K L (curriedTensor _) ≅
      CochainComplex.mapBifunctor L K (curriedTensor _) := by
  letI := monoidalCategory O
  letI := symmetricCategory O
  let T := curriedTensor (SheafOfModules.{r} (𝓡 O))
  let A := ((T.mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj K).obj L
  let B := ((T.flip.mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj K).obj L
  let e : A ≅ B := HomologicalComplex.Hom.isoOfComponents
    (fun p ↦ HomologicalComplex.Hom.isoOfComponents
      (fun q ↦ β_ (K.X p) (L.X q)) (by
        intro q q' hq
        exact (BraidedCategory.braiding_naturality_right (K.X p) (L.d q q')).symm))
    (by
      intro p p' hp
      ext q : 1
      exact (BraidedCategory.braiding_naturality_left (K.d p p') (L.X q)).symm)
  exact (HomologicalComplex₂.total.mapIso e (.up ℤ)) ≪≫
    HomologicalComplex.mapBifunctorFlipIso L K T (.up ℤ)

/-- An acyclic K-flat complex has acyclic total tensor with every complex.
Source: Stacks Project, Tags 06Y0 and 06YT, proof by a K-flat resolution.

Proof: Choose a K-flat resolution r : P → F (Tag 06YS). The cone of r is acyclic.
K-flatness of K makes Tot(Cone(r) ⊗ K) acyclic; the tensor-cone isomorphism
and the cone criterion imply that Tot(r ⊗ id_K) is a quasi-isomorphism.
K-flatness of P applied to the acyclic K makes Tot(K ⊗ P) acyclic.
The signed symmetry sends the (p,q) summand by (-1)^(pq) times the module braiding
and identifies this with Tot(P ⊗ K). It is a chain isomorphism because
(p+1)q = pq+q and p+p(q+1) = pq modulo two. Thus the quasi-isomorphism
Tot(P ⊗ K) → Tot(F ⊗ K) transports vanishing of every homology object.
This also covers F = 0 and K = 0 without any nonzero hypothesis.
(auxiliary; not a blueprint node) -/
private theorem tensor_acyclic_of_isKFlat_independent
    (K : CochainComplex (SheafOfModules.{r} (𝓡 O)) ℤ)
    (hK : K.IsKFlatIndependentCoefficients) (hA : K.Acyclic)
    (F : CochainComplex (SheafOfModules.{r} (𝓡 O)) ℤ) :
    (letI := monoidalCategory O
     (CochainComplex.mapBifunctor F K (curriedTensor _)).Acyclic) := by
  let := monoidalCategory O
  let := monoidalPreadditive_independent (O := O)
  obtain ⟨P, r, hP, _, hr, _⟩ := CochainComplex.exists_isKFlatResolutionIndependentCoefficients F
  have hcone : (CochainComplex.mappingCone r).Acyclic :=
    (CochainComplex.mappingCone.quasiIso_iff_acyclic r).1 hr
  have hc := hK (CochainComplex.mappingCone r) hcone
  let g := HomologicalComplex.mapBifunctorMap r (𝟙 K) (curriedTensor _) (.up ℤ)
  have : QuasiIso g := by
    apply (CochainComplex.mappingCone.quasiIso_iff_acyclic g).2
    exact HomologicalComplex.Acyclic.of_iso hc
      (CochainComplex.mapBifunctorMappingCone₁Iso r K (curriedTensor _))
  have hp : (CochainComplex.mapBifunctor P K (curriedTensor _)).Acyclic :=
    HomologicalComplex.Acyclic.of_iso (hP K hA) (tensor_symmetry K P)
  intro i
  exact (quasiIsoAt_iff_exactAt g i (hp i)).1 inferInstance

private theorem isKFlat_mappingCone_independent
    {P Q : CochainComplex (SheafOfModules.{r} (𝓡 O)) ℤ} (α : P ⟶ Q)
    (hP : P.IsKFlatIndependentCoefficients) (hQ : Q.IsKFlatIndependentCoefficients) :
    (CochainComplex.mappingCone α).IsKFlatIndependentCoefficients := by
  intro F hF
  let g := HomologicalComplex.mapBifunctorMap (𝟙 F) α (curriedTensor _) (.up ℤ)
  let e := CochainComplex.mapBifunctorMappingCone₂Iso F α (curriedTensor _)
  let Z := HomotopyCategory.subcategoryAcyclic (SheafOfModules.{r} (𝓡 O))
  have hP' := hP F hF
  have hQ' := hQ F hF
  rw [← HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hP' hQ' ⊢
  apply Z.prop_of_iso ((HomotopyCategory.quotient _ _).mapIso e.symm)
  exact Z.ext_of_isTriangulatedClosed₃ _
    (HomotopyCategory.mappingCone_triangleh_distinguished g) hP' hQ'

end TensorAcyclicity

/-- The K-flat invariance component needed by derived change of rings.
Source: Stacks Project, Tag 06YT (auxiliary; not a blueprint node).
Proof: the cone of the quasi-isomorphism is acyclic and K-flat. Resolve an arbitrary
complex by a K-flat complex; the tensor-cone comparison and signed symmetry show that
tensoring the acyclic K-flat cone with any complex is acyclic. Specialize to the target
ring in degree zero. The natural comparison with restricted extension of scalars and
faithful exact forgetting to abelian sheaves detect acyclicity of its extension. An
additive functor preserves mapping cones, so the cone criterion gives the conclusion. -/
private theorem derivedChangeOfRingsIndependentCoefficients_kflat_invariance
    {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasSheafify J AddCommGrpCat.{r}]
    {O O' : Sheaf J CommRingCat.{r}} (φ : O ⟶ O')
    (E : SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J O) ⥤
      SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J O'))
    (h : ∀ M, E.obj M = changeOfRings.{v, u, r} φ M)
    (hm : ∀ {M N} (a : M ⟶ N),
      E.map a = eqToHom (h M) ≫ changeOfRingsHom.{v, u, r} φ M a ≫ eqToHom (h N).symm)
    [E.Additive] :
    ∀ {P Q : CochainComplex (SheafOfModules.{r}
      (derivedChangeRingIndependentCoefficients J O)) ℤ} (α : P ⟶ Q),
      P.IsKFlatIndependentCoefficients → Q.IsKFlatIndependentCoefficients → QuasiIso α →
        QuasiIso ((E.mapHomologicalComplex (ComplexShape.up ℤ)).map α) := by
  intro P Q α hP hQ hα
  let := isMonoidal_W_independentCoefficients O
  let := monoidalCategory O
  let := preservesZeroMorphisms_curriedTensor_independentCoefficients O
  let := preservesZeroMorphisms_curriedTensor_obj_independentCoefficients O
  have hkcone := isKFlat_mappingCone_independent α hP hQ
  have hcone := (CochainComplex.mappingCone.quasiIso_iff_acyclic α).1 hα
  let K := CochainComplex.mappingCone α
  let U := restrictScalars.{r}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map φ)
  let S := U.obj (unit (𝓡 O'))
  obtain ⟨e, he⟩ := exists_changeOfRings_tensor_comparison_independent φ
  let V := toSheaf (𝓡 O)
  let V' := toSheaf (𝓡 O')
  let q (i : ℤ) : V'.obj (E.obj (K.X i)) ≅ V.obj (S ⊗ K.X i) :=
    V'.mapIso (eqToIso (h (K.X i))) ≪≫ e (K.X i)
  let L := (E.mapHomologicalComplex (.up ℤ)).obj K
  let Q := (((curriedTensor _).obj S).mapHomologicalComplex (.up ℤ)).obj K
  have hq : ((V'.mapHomologicalComplex (.up ℤ)).obj L) ≅
      ((V.mapHomologicalComplex (.up ℤ)).obj Q) :=
    HomologicalComplex.Hom.isoOfComponents q (by
      intro i j hij
      change (q i).hom ≫ V.map (S ◁ K.d i j) = V'.map (E.map (K.d i j)) ≫ (q j).hom
      dsimp [q]
      rw [hm, Functor.map_comp, Functor.map_comp]
      simp only [Category.assoc]
      rw [← he]
      simp [V'])
  let t := CochainComplex.mapBifunctorSingle₁Iso (curriedTensor _) S K
  have ht := tensor_acyclic_of_isKFlat_independent K hkcone hcone
    ((HomologicalComplex.single _ (.up ℤ) 0).obj S)
  have hQ : Q.Acyclic := by
    intro i
    exact (ht i).of_iso t
  have hEL : L.Acyclic := by
    intro i
    apply ((L.sc i).exact_map_iff_of_faithful V').mp
    exact ShortComplex.exact_of_iso
      ((HomologicalComplex.shortComplexFunctor _ _ i).mapIso hq.symm) ((hQ i).map V)
  apply (CochainComplex.mappingCone.quasiIso_iff_acyclic _).2
  intro i
  apply (HomologicalComplex.exactAt_iff_isZero_homology _ i).2
  exact ((HomologicalComplex.exactAt_iff_isZero_homology _ i).1 (hEL i)).of_iso
    ((HomologicalComplex.homologyFunctor _ _ i).mapIso
      (CochainComplex.mappingCone.mapHomologicalComplexIso α E)).symm

end IndependentTensor

/-- Derived change of rings along a morphism `φ : O ⟶ O'` of sheaves of commutative rings
on a site. There is an additive functor `E : Mod(O) ⥤ Mod(O')` whose objects and maps are
the change of rings `changeOfRings φ` / `changeOfRingsHom φ` (`- ⊗_O O'`), such that
(1) termwise change of rings `E.mapHomologicalComplex` sends every quasi-isomorphism between
K-flat complexes to a quasi-isomorphism, and (2) the functor
`K(O) → D(O')`, `G ↦ Q(G ⊗_O O')`, has an everywhere defined (pointwise) left derived
functor `Lφ^* : D(O) ⥤ D(O')` with counit `ε`, which is triangulated, and `ε` is an
isomorphism at every K-flat complex. Hence for a K-flat resolution `s : P → G` the canonical
map `Lφ^* G ≅ Lφ^* P → P ⊗_O O'` (inverse of `Lφ^*(s)` followed by `ε_P`) is an isomorphism,
and the comparison isomorphisms between two resolutions are composites of these, so
canonical and compatible with composition.
Source: Stacks Project, Tags 06YT, 06YY, and 06XN.
Proof:
1. Form the sectionwise extension-of-scalars functor from changeOfRingsPresheaf and
changeOfRingsHom_naturality (def-pur-sheaf-tensor-product), then compose with sheafification.
Identities and composition hold sectionwise. Both functors are additive by their
adjunctions to additive restriction or forgetful functors (Adjunction.left_adjoint_additive).
This gives E with exactly the specified objects and maps.
2. Apply lem-pur-change-of-rings-kflat-quasi-iso to E with these identifications to obtain
preservation of quasi-isomorphisms between K-flat complexes.
3. Let F be the induced homotopy functor followed by derived localization
(def-weil-abstract-derived-category); it commutes with shifts and is triangulated.
Use homotopy objects represented by K-flat complexes as the resolving class
(def-pc-kflat-complex). Resolve every representative by lem-pc-kflat-resolution and apply
quotient_map_mem_quasiIso_iff to its augmentation. For a quasi-isomorphism between objects
of this class, lift through the full homotopy quotient on chosen K-flat representatives.
Step 2 and localization make its F-image invertible. Apply
lem-pur-left-derived-from-kflat-class to obtain pointwise existence, the universal derived
pair, triangulatedness, and the counit isomorphism on every K-flat complex. The canonical
resolution comparisons are composites of these counit maps and inverses of images of
quasi-isomorphisms, hence are isomorphisms and compatible with a third resolution.
(auxiliary; not a blueprint node) -/
theorem derivedChangeOfRingsIndependentCoefficients
    {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasSheafify J AddCommGrpCat.{r}]
    {O O' : Sheaf J CommRingCat.{r}} (φ : O ⟶ O')
    [HasDerivedCategory.{w} (SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J O))]
    [HasDerivedCategory.{w} (SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J O'))] :
    ∃ (E : SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J O) ⥤ SheafOfModules.{r}
      (derivedChangeRingIndependentCoefficients J O'))
      (h : ∀ M : SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J O), E.obj M =
        changeOfRings.{v, u,
        r} φ M)
      (_ : ∀ {M N : SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J O)} (a : M ⟶ N),
        E.map a = eqToHom (h M) ≫ changeOfRingsHom.{v, u, r} φ M a ≫ eqToHom (h N).symm)
      (_ : E.Additive),
      (∀ {P Q : CochainComplex (SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J O))
        ℤ} (α : P ⟶ Q),
        P.IsKFlatIndependentCoefficients → Q.IsKFlatIndependentCoefficients → QuasiIso α →
          QuasiIso ((E.mapHomologicalComplex (ComplexShape.up ℤ)).map α)) ∧
      (E.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
          (HomotopyCategory.quasiIso (SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J
            O))
            (ComplexShape.up ℤ)) ∧
      ∃ (LF : DerivedCategory (SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J O)) ⥤
          DerivedCategory (SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J O')))
        (ε : DerivedCategory.Qh ⋙ LF ⟶
          E.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh),
        LF.IsLeftDerivedFunctor ε
            (HomotopyCategory.quasiIso (SheafOfModules.{r} (derivedChangeRingIndependentCoefficients
              J O))
              (ComplexShape.up ℤ)) ∧
          (∃ (_ : LF.CommShift ℤ), LF.IsTriangulated) ∧
          ∀ P : CochainComplex (SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J O))
            ℤ, P.IsKFlatIndependentCoefficients →
            IsIso (ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) := by
  have hscalar (U : Cᵒᵖ) : (ModuleCat.extendScalars (φ.hom.app U).hom).Additive :=
    (ModuleCat.extendRestrictScalarsAdj (φ.hom.app U).hom).left_adjoint_additive
  have hsheaf : (PresheafOfModules.sheafification (𝟙 (derivedChangeRingIndependentCoefficients J
    O').obj)).Additive :=
    (PresheafOfModules.sheafificationAdjunction (𝟙 (derivedChangeRingIndependentCoefficients J
      O').obj)).left_adjoint_additive
  let E₀ : SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J O) ⥤ PresheafOfModules.{r}
    (derivedChangeRingIndependentCoefficients J O').obj :=
    { obj := changeOfRingsPresheaf φ
      map := fun a ↦
        { app := fun U ↦ (ModuleCat.extendScalars (φ.hom.app U).hom).map (a.val.app U)
          naturality := changeOfRingsHom_naturality φ _ a }
      map_id := by
        intro M
        apply PresheafOfModules.hom_ext
        intro U
        simp
        rfl
      map_comp := by
        intro M N P a b
        apply PresheafOfModules.hom_ext
        intro U
        simp }
  let E := E₀ ⋙ PresheafOfModules.sheafification (𝟙 (derivedChangeRingIndependentCoefficients J
    O').obj)
  have hE₀ : E₀.Additive := by
    constructor
    intro M N a b
    apply PresheafOfModules.hom_ext
    intro U
    simpa only [E₀, SheafOfModules.add_val, PresheafOfModules.add_app] using
      (ModuleCat.extendScalars (φ.hom.app U).hom).map_add
        (f := a.val.app U) (g := b.val.app U)
  have hE : E.Additive := by infer_instance
  refine ⟨E, fun _ ↦ rfl, ?_, hE, ?_⟩
  · intro M N a
    simp [E, E₀, changeOfRingsHom]
  · have hinv : ∀ {P Q : CochainComplex (SheafOfModules.{r}
    (derivedChangeRingIndependentCoefficients J O)) ℤ} (α : P ⟶ Q),
        P.IsKFlatIndependentCoefficients → Q.IsKFlatIndependentCoefficients → QuasiIso α →
          QuasiIso ((E.mapHomologicalComplex (ComplexShape.up ℤ)).map α) :=
      derivedChangeOfRingsIndependentCoefficients_kflat_invariance φ E (fun _ ↦ rfl)
        (by intro M N a; simp [E, E₀, changeOfRingsHom])
    refine ⟨hinv, ?_⟩
    let F := E.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh
    let S : Set (HomotopyCategory (SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J
      O)) (ComplexShape.up ℤ)) :=
      { X | ∃ P : CochainComplex (SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J O))
        ℤ,
          P.IsKFlatIndependentCoefficients ∧ (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P
            = X }
    have hres : ∀ X : HomotopyCategory (SheafOfModules.{r} (derivedChangeRingIndependentCoefficients
      J O)) (ComplexShape.up ℤ),
        ∃ (X' : HomotopyCategory (SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J O))
          (ComplexShape.up ℤ))
          (s : X' ⟶ X), X' ∈ S ∧ HomotopyCategory.quasiIso _ _ s := by
      intro X
      obtain ⟨G, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
      obtain ⟨P, s, hP, _, hs, _⟩ := CochainComplex.exists_isKFlatResolutionIndependentCoefficients
        G
      refine ⟨_, (HomotopyCategory.quotient _ _).map s, ⟨P, hP, rfl⟩, ?_⟩
      exact (HomotopyCategory.quotient_map_mem_quasiIso_iff s).2 hs
    have hinvS : ∀ X Y : HomotopyCategory (SheafOfModules.{r}
      (derivedChangeRingIndependentCoefficients J O))
        (ComplexShape.up ℤ), ∀ s : X ⟶ Y, X ∈ S → Y ∈ S →
          HomotopyCategory.quasiIso _ _ s → IsIso (F.map s) := by
      intro X Y s hX hY hs
      obtain ⟨P, hP, rfl⟩ := hX
      obtain ⟨Q, hQ, rfl⟩ := hY
      obtain ⟨a, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective s
      have ha := (HomotopyCategory.quotient_map_mem_quasiIso_iff a).1 hs
      have hEa := hinv a hP hQ ha
      dsimp only [F, Functor.comp_map, Functor.mapHomotopyCategory_map]
      apply Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso _ _)
      exact (HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 hEa
    obtain ⟨hpoint, LF, ε, hLF, htri, hε⟩ :=
      Functor.leftDerived_from_resolvingClass _ _ F S hres hinvS
    exact ⟨hpoint, LF, ε, hLF, htri, fun P hP ↦ hε _ ⟨P, hP, rfl⟩⟩

end SheafOfModules
