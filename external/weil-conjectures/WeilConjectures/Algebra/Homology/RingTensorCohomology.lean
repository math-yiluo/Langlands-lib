/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.Algebra.Category.ModuleCat.Descent
import all WeilConjectures.Algebra.Homology.KFlatScalarExtensionDerivedIso

/-!
# Ring tensor cohomology and its comparison map

Source: Stacks Project, More on Algebra, Tag 06Y6 and Tor independence, comparison-map
(blueprint: def-pc-ring-tensor-cohomology).

The two models are extension of scalars of an R-K-flat resolution of the restricted
complex, and extension of scalars of an A-K-flat resolution, respectively. The comparison
uses the common model obtained by resolving the restricted A-resolution over R.

## Main definitions

* `source` and `target`: the two tensor cohomology functors.
* `comparison`: cohomology of the canonical comparison map.
* `baseChangeMap`: flat extension of scalars on cohomology.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace RingTensorCohomology

variable (R : Type u) [CommRing R]

/-- Choose a reduced functorial flat resolution, as in Stacks Tag 06Y6.
(blueprint: def-pc-ring-tensor-cohomology) -/
noncomputable abbrev flatResolution :=
  (Classical.choice (inferInstance : Abelian.HasFunctorialFlatResolution (ModuleCat.{u} R))).reduced

/-- The functorial K-flat resolution on complexes, Stacks Tag 06Y6.
(blueprint: def-pc-ring-tensor-cohomology) -/
noncomputable def resolution : CochainComplex (ModuleCat.{u} R) ℤ ⥤
    CochainComplex (ModuleCat.{u} R) ℤ :=
  (flatResolution R).resolutionFunctor

/-- The resolution augmentation, Stacks Tag 06Y6.
(blueprint: def-pc-ring-tensor-cohomology) -/
noncomputable def augmentation : resolution R ⟶ 𝟭 _ :=
  (flatResolution R).resolutionNatTrans

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-- Additivity inherited from the extension-restriction adjunction, Stacks Tag 06Y6.
(blueprint: def-pc-ring-tensor-cohomology) -/
local instance extendScalarsAdditive (f : R →+* B) :
    (ModuleCat.extendScalars.{u, u, u} f).Additive :=
  (ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).left_adjoint_additive

/-- Restriction of complexes from A to R, Stacks Tag 06Y6.
(blueprint: def-pc-ring-tensor-cohomology) -/
noncomputable abbrev restrict : CochainComplex (ModuleCat.{u} A) ℤ ⥤
    CochainComplex (ModuleCat.{u} R) ℤ :=
  (ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex (.up ℤ)

/-- Extension of complexes from R to B, Stacks Tag 06Y6.
(blueprint: def-pc-ring-tensor-cohomology) -/
noncomputable abbrev extend : CochainComplex (ModuleCat.{u} R) ℤ ⥤
    CochainComplex (ModuleCat.{u} B) ℤ :=
  (ModuleCat.extendScalars (algebraMap R B)).mapHomologicalComplex (.up ℤ)

/-- The model of M tensor-derived-over-R B, Stacks Tag 06Y6.
(blueprint: def-pc-ring-tensor-cohomology) -/
noncomputable def sourceComplex := restrict R A ⋙ resolution R ⋙ extend R B

/-- The model of M tensor-derived-over-A (A tensor-over-R B), Stacks Tag 06Y6.
The natural isomorphism B tensor-over-R P = P tensor-over-A (A tensor-over-R B)
identifies this model with the usual A-derived tensor.
(blueprint: def-pc-ring-tensor-cohomology) -/
noncomputable def targetComplex := resolution A ⋙ restrict R A ⋙ extend R B

/-- Source cohomology, carrying its second-factor B-action, Stacks Tag 06Y6.
(blueprint: def-pc-ring-tensor-cohomology) -/
noncomputable def source (i : ℤ) :=
  sourceComplex R A B ⋙ HomologicalComplex.homologyFunctor (ModuleCat.{u} B) (.up ℤ) i

/-- Target cohomology, carrying its second-factor B-action, Stacks Tag 06Y6.
(blueprint: def-pc-ring-tensor-cohomology) -/
noncomputable def target (i : ℤ) :=
  targetComplex R A B ⋙ HomologicalComplex.homologyFunctor (ModuleCat.{u} B) (.up ℤ) i

/-- The intermediate complex in the comparison span, Stacks Tag 06Y6.
(blueprint: def-pc-ring-tensor-cohomology) -/
noncomputable def middleComplex :=
  resolution A ⋙ restrict R A ⋙ resolution R ⋙ extend R B

/-- The left arrow of the comparison span, Stacks Tag 06Y6.
(blueprint: def-pc-ring-tensor-cohomology) -/
noncomputable def spanLeft : middleComplex R A B ⟶ sourceComplex R A B :=
  Functor.whiskerRight (augmentation A) (restrict R A ⋙ resolution R ⋙ extend R B)

/-- The right arrow of the comparison span, Stacks Tag 06Y6.
(blueprint: def-pc-ring-tensor-cohomology) -/
noncomputable def spanRight : middleComplex R A B ⟶ targetComplex R A B :=
  Functor.whiskerLeft (resolution A ⋙ restrict R A)
    (Functor.whiskerRight (augmentation R) (extend R B))

/-- The left arrow of the comparison span is invertible on cohomology, Stacks Tag 06Y6.
Proof: the A-resolution augmentation remains a quasi-isomorphism after restriction to R.
Its R-resolution is a quasi-isomorphism between K-flat complexes. Tensoring with B preserves
such quasi-isomorphisms, so every cohomology map is invertible.
(blueprint: def-pc-ring-tensor-cohomology) -/
theorem spanLeft_isIso (i : ℤ) :
    IsIso (Functor.whiskerRight (spanLeft R A B)
      (HomologicalComplex.homologyFunctor (ModuleCat.{u} B) (.up ℤ) i)) := by
  apply (NatTrans.isIso_iff_isIso_app _).2
  intro M
  let f := (restrict R A).map ((augmentation A).app M)
  have hA : QuasiIso ((augmentation A).app M) := by
    dsimp [augmentation]
    infer_instance
  have : QuasiIso f := by
    dsimp [f, restrict]
    infer_instance
  have hR (K : CochainComplex (ModuleCat.{u} R) ℤ) :
      QuasiIso ((augmentation R).app K) := by
    dsimp [augmentation]
    infer_instance
  have : QuasiIso ((resolution R).map f) := by
    have := hR ((restrict R A).obj ((resolution A).obj M))
    have := hR ((restrict R A).obj M)
    rw [← quasiIso_iff_comp_right _ ((augmentation R).app _)]
    rw [(augmentation R).naturality f]
    change QuasiIso ((augmentation R).app _ ≫ f)
    infer_instance
  have hk (K : CochainComplex (ModuleCat.{u} R) ℤ) :
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat
        ((resolution R).obj K) :=
    (flatResolution R).kFlat_resolutionFunctor_obj ObjectProperty.flat.essImage_ι_le K
  have : QuasiIso ((extend R B).map ((resolution R).map f)) :=
    CochainComplex.scalarExtension_quasiIso_of_kFlat
      (algebraMap R B) _ inferInstance (hk _) (hk _)
  change IsIso (HomologicalComplex.homologyMap
    ((extend R B).map ((resolution R).map f)) i)
  infer_instance

/-- Cohomology of the canonical comparison morphism, Stacks Tag 06Y6, comparison-map.
(blueprint: def-pc-ring-tensor-cohomology) -/
noncomputable def comparison (i : ℤ) : source R A B i ⟶ target R A B i :=
  letI := spanLeft_isIso R A B i
  inv (Functor.whiskerRight (spanLeft R A B)
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} B) (.up ℤ) i)) ≫
  Functor.whiskerRight (spanRight R A B)
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} B) (.up ℤ) i)

variable (C : Type u) [CommRing C] [Algebra R C] [Algebra B C] [IsScalarTower R B C]

/-- The canonical cohomology base-change map for a flat extension, Stacks Tag 06Y6.
It is the inverse of the standard exact-functor cohomology comparison.
(blueprint: def-pc-ring-tensor-cohomology) -/
noncomputable def flatHomologyMap (h : (algebraMap B C).Flat)
    (K : CochainComplex (ModuleCat.{u} B) ℤ) (i : ℤ) :
    (ModuleCat.extendScalars (algebraMap B C)).obj (K.homology i) ⟶
      ((extend B C).obj K).homology i :=
  letI := ModuleCat.preservesFiniteLimits_extendScalars_of_flat h
  ((K.sc i).mapHomologyIso (ModuleCat.extendScalars (algebraMap B C))).inv

/-- Associativity of termwise extension, Stacks Tag 06Y6.
(blueprint: def-pc-ring-tensor-cohomology) -/
noncomputable def extendCompIso : extend R B ⋙ extend B C ≅ extend R C :=
  Functor.mapHomologicalComplexCompIso
    ((ModuleCat.extendScalarsComp (algebraMap R B) (algebraMap B C)).symm ≪≫
      eqToIso (congrArg (fun f : R →+* C => ModuleCat.extendScalars.{u} f)
        (IsScalarTower.algebraMap_eq R B C).symm)) (.up ℤ)

/-- The canonical flat base-change map of a complex obtained by extension from R.
Stacks Tag 06Y6; (blueprint: def-pc-ring-tensor-cohomology). -/
noncomputable def baseChangeMap (h : (algebraMap B C).Flat)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ) :
    (ModuleCat.extendScalars (algebraMap B C)).obj (((extend R B).obj K).homology i) ⟶
      ((extend R C).obj K).homology i :=
  flatHomologyMap B C h ((extend R B).obj K) i ≫
    HomologicalComplex.homologyMap ((extendCompIso R B C).hom.app K) i

end RingTensorCohomology
