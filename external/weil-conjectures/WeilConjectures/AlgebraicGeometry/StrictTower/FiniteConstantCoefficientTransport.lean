/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerOpenExtension
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportComparisonPullbackCoherence
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
public import WeilConjectures.AlgebraicGeometry.Etale.Origin.EtaleOriginWitness
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalarsLowerStar
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import WeilConjectures.CategoryTheory.Abelian.RightDerived.Comp
import all WeilConjectures.AlgebraicGeometry.ProEtale.Extension.ProEtaleExtensionZero
import WeilConjectures.AlgebraicGeometry.Open.OpenComparisonUnitNormalization

/-!
# Normalized finite coefficient and etale-origin transport

Source: Stacks Project, Tags 0F7B, 0F7C, 0F7D, 0F7F, 07A7 and 09AE, and the explicit
strict-tower refinement in the blueprint (blueprint: def-cbc-finite-constant-coefficient-transport).

The index `n : ℕ` denotes positive level `n+1`. All derived categories below localize
complexes of strict towers, rather than forming towers in separate derived categories.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite

namespace AlgebraicGeometry.ProEtale.StrictTower

variable (B : Type (u + 1)) [CommRing B]

/-- Forgetting commutativity commutes with sheafification at the original site universes.
Source: Stacks, Tags 00W1 and 03DA
(blueprint: def-cbc-finite-constant-coefficient-transport).
Proof: the plus construction uses limits of matching families and filtered colimits
of coverings. Forgetting commutativity creates these limits and preserves these
filtered colimits. Apply the construction twice and its universal property to
identify ring sheafification with forgotten commutative-ring sheafification.
The resulting comparison preserves the sheafification unit. -/
@[instance]
theorem constantRingForget_preservesSheafification (X : Scheme.{u}) :
    (Scheme.ProEt.topology X).PreservesSheafification
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) := by
  exact GrothendieckTopology.instPreservesSheafification _ _

/-- The canonical coefficient map sends a scalar to its constant function after φ.
Source: Stacks, Tags 03DA and 099R
(blueprint: def-cbc-finite-constant-coefficient-transport). -/
noncomputable def finiteScalarMap (X : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ) :
    (sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (coefficients B X) ⟶
        finiteCoefficientRingSheaf X Λ :=
  (constantCommuteCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).hom.app (CommRingCat.of B) ≫
  (constantSheaf (Scheme.ProEt.topology X) RingCat.{u + 1}).map (RingCat.ofHom φ) ≫
  ((sheafificationAdjunction (Scheme.ProEt.topology X) RingCat.{u + 1}).homEquiv
    _ _).symm (finiteCoefficientScalarMap X Λ)

/-- Actual restriction of module scalars along the specified constant-section map.
Source: Stacks, Tag 03DA
(blueprint: def-cbc-finite-constant-coefficient-transport). -/
noncomputable def finiteRestriction (X : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ) :
    FiniteCoefficientModules X Λ ⥤ Modules B X :=
  SheafOfModules.restrictScalars (finiteScalarMap B X Λ φ)

/-- Restriction of scalars is exact; no flatness of φ is required.
Source: Stacks, Tag 03DA
(blueprint: def-cbc-finite-constant-coefficient-transport).
Proof: restriction leaves the underlying additive sheaf, restrictions and maps
unchanged. Kernels and sheafified cokernels have the same restricted scalar action,
so both finite-limit and finite-colimit comparisons are isomorphisms. -/
theorem finiteRestriction_exact (X : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ) :
    (finiteRestriction B X Λ φ).Additive ∧
      PreservesFiniteLimits (finiteRestriction B X Λ φ) ∧
        PreservesFiniteColimits (finiteRestriction B X Λ φ) := by
  let R := (sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (coefficients B X)
  let S := finiteCoefficientRingSheaf X Λ
  let F := finiteRestriction B X Λ φ
  have he : F ⋙ SheafOfModules.toSheaf.{u + 1} R ≅ SheafOfModules.toSheaf.{u + 1} S := Iso.refl _
  have : PreservesFiniteLimits F := by
    have : PreservesFiniteLimits (F ⋙ SheafOfModules.toSheaf.{u + 1} R) :=
      preservesFiniteLimits_of_natIso he.symm
    exact preservesFiniteLimits_of_reflects_of_preserves F (SheafOfModules.toSheaf.{u + 1} R)
  have : ReflectsFiniteColimits (SheafOfModules.toSheaf.{u + 1} R) :=
    { reflects := fun _ ↦ reflectsColimitsOfShape_of_reflectsIsomorphisms }
  have : PreservesFiniteColimits F := by
    have : PreservesFiniteColimits (F ⋙ SheafOfModules.toSheaf.{u + 1} R) :=
      preservesFiniteColimits_of_natIso he.symm
    exact preservesFiniteColimits_of_reflects_of_preserves F (SheafOfModules.toSheaf.{u + 1} R)
  exact ⟨inferInstanceAs (SheafOfModules.restrictScalars (finiteScalarMap B X Λ φ)).Additive,
    inferInstance, inferInstance⟩

/-- Additivity of scalar restriction. Source: Stacks, Tag 03DA
(blueprint: def-cbc-finite-constant-coefficient-transport). -/
noncomputable instance finiteRestriction_additive (X : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ) :
    (finiteRestriction B X Λ φ).Additive := (finiteRestriction_exact B X Λ φ).1

/-- Left exactness of scalar restriction. Source: Stacks, Tag 03DA
(blueprint: def-cbc-finite-constant-coefficient-transport). -/
noncomputable instance finiteRestriction_finiteLimits (X : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ) :
    PreservesFiniteLimits (finiteRestriction B X Λ φ) := (finiteRestriction_exact B X Λ φ).2.1

/-- Right exactness of scalar restriction. Source: Stacks, Tag 03DA
(blueprint: def-cbc-finite-constant-coefficient-transport). -/
noncomputable instance finiteRestriction_finiteColimits (X : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ) :
    PreservesFiniteColimits (finiteRestriction B X Λ φ) := (finiteRestriction_exact B X Λ φ).2.2

/-- A level may have its own finite coefficient ring and its own lower bound. The
etale witness is exactly the recorded dependency's witness, followed by actual
restriction of scalars. Source: blueprint finite-origin hypothesis
(blueprint: def-cbc-finite-constant-coefficient-transport). -/
structure ScalarEtaleOrigin (X : Scheme.{u}) (K : DerivedCategory (Modules B X)) where
  Λ : Type (u + 1)
  [ring : CommRing Λ]
  [finite : Finite Λ]
  [topology : TopologicalSpace Λ]
  [discrete : DiscreteTopology Λ]
  φ : B →+* Λ
  F : FiniteCoefficientDerivedCategoryPlus X Λ
  origin : EtaleOriginWitness X Λ F
  iso : (finiteRestriction B X Λ φ).mapDerivedCategory.obj F.obj ≅ K

attribute [instance] ScalarEtaleOrigin.ring ScalarEtaleOrigin.finite
  ScalarEtaleOrigin.topology ScalarEtaleOrigin.discrete

/-- Realize finite fixed-ring sheaves, then restrict the specified scalar action.
Source: Stacks, Tags 03DA and 099R
(blueprint: def-cbc-finite-constant-coefficient-transport). -/
noncomputable def C (X : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ) :
    Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ) ⥤ Modules B X :=
  finiteCoefficientRealization X Λ ⋙ finiteRestriction B X Λ φ

/-- The realization comparison is uniquely normalized on the sheafification unit.
Source: Stacks, Tag 03DA
(blueprint: def-cbc-finite-constant-coefficient-transport).
Proof: module sheafification has the sheafification of the underlying additive
presheaf as its underlying sheaf. The counit to the original additive sheaf is
an isomorphism and sends each unit section to itself. Local surjectivity of the
unit gives uniqueness. Scalar restriction leaves all these sections unchanged. -/
theorem cUnderlying_existsUnique (X : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ) :
    ∃! e : C B X Λ φ ⋙ SheafOfModules.toSheaf _ ≅
        sheafCompose (Scheme.ProEt.topology X) (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat),
      ∀ (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))
        (U : X.ProEtᵒᵖ) (m : F.obj.obj U),
        (e.hom.app F).hom.app U
          ((toSheafify (Scheme.ProEt.topology X)
            ((finiteCoefficientModulePresheaf X.ProEt Λ).obj F.obj).presheaf).app U m) = m := by
  let J := Scheme.ProEt.topology X
  let D := sheafCompose J (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat)
  let adj := sheafificationAdjunction J AddCommGrpCat.{u + 1}
  let e₀ : (D ⋙ sheafToPresheaf J AddCommGrpCat.{u + 1}) ⋙
      presheafToSheaf J AddCommGrpCat.{u + 1} ≅ D :=
    NatIso.ofComponents (fun F ↦ asIso (adj.counit.app (D.obj F)))
      (fun f ↦ adj.counit.naturality (D.map f))
  let e : C B X Λ φ ⋙ SheafOfModules.toSheaf _ ≅ D := e₀
  have he (F : Sheaf J (ModuleCat.{u + 1} Λ)) :
      toSheafify J (D.obj F).obj ≫ (e.hom.app F).hom = 𝟙 _ :=
    adj.right_triangle_components (D.obj F)
  refine ⟨e, ?_, ?_⟩
  · intro F U m
    exact ConcreteCategory.congr_hom (congr_app (he F) U) m
  · intro e' he'
    apply Iso.ext
    apply NatTrans.ext
    funext F
    apply Sheaf.hom_ext
    apply sheafify_hom_ext J _ _ (D.obj F).property
    ext U m
    exact (he' F U m).trans (ConcreteCategory.congr_hom (congr_app (he F) U) m).symm

/-- The specified underlying-sheaf identification, fixed on all unit sections.
Source: Stacks, Tag 03DA
(blueprint: def-cbc-finite-constant-coefficient-transport). -/
noncomputable def cUnderlying (X : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ) :
    C B X Λ φ ⋙ SheafOfModules.toSheaf _ ≅
      sheafCompose (Scheme.ProEt.topology X) (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat) :=
  Classical.choose (cUnderlying_existsUnique B X Λ φ)

private theorem finiteScalarMap_unit (X : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ) :
    Functor.whiskerRight
        (toSheafify (Scheme.ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of B)))
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ≫
      (finiteScalarMap B X Λ φ).hom =
    (Functor.const X.ProEtᵒᵖ).map (RingCat.ofHom φ) ≫ finiteCoefficientScalarMap X Λ := by
  change _ ≫ ((constantCommuteCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).hom.app (CommRingCat.of B)).hom ≫
    sheafifyMap (Scheme.ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).map (RingCat.ofHom φ)) ≫
    (((sheafificationAdjunction (Scheme.ProEt.topology X) RingCat.{u + 1}).homEquiv
      _ _).symm (finiteCoefficientScalarMap X Λ)).hom = _
  rw [constantCommuteCompose_hom_app_hom]
  simp only [← Category.assoc, sheafComposeIso_inv_fac]
  have hc : (constComp X.ProEtᵒᵖ (CommRingCat.of B)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).hom = 𝟙 _ := rfl
  rw [hc, sheafifyMap_id, Category.comp_id, ← toSheafify_naturality, Category.assoc]
  congr 1
  exact Equiv.apply_symm_apply
    ((sheafificationAdjunction (Scheme.ProEt.topology X) RingCat.{u + 1}).homEquiv _ _)
    (finiteCoefficientScalarMap X Λ)

private noncomputable def scalarUnit (X : Scheme.{u}) :
    (Functor.const X.ProEtᵒᵖ).obj (RingCat.of B) ⟶
      ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (coefficients B X)).obj :=
  Functor.whiskerRight
    (toSheafify (Scheme.ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of B)))
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})

private theorem scalarUnit_surjective (X : Scheme.{u}) :
    Presheaf.IsLocallySurjective (Scheme.ProEt.topology X) (scalarUnit B X) := by
  rw [Presheaf.isLocallySurjective_iff_whisker_forget]
  change Presheaf.IsLocallySurjective (Scheme.ProEt.topology X)
    (Functor.whiskerRight (toSheafify (Scheme.ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of B))) (forget CommRingCat.{u + 1}))
  infer_instance

private theorem cUnderlying_inv_unit (X : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ)
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) :
    ((cUnderlying B X Λ φ).inv.app F).hom =
      toSheafify (Scheme.ProEt.topology X)
        ((finiteCoefficientModulePresheaf X.ProEt Λ).obj F.obj).presheaf := by
  apply (cancel_mono ((cUnderlying B X Λ φ).hom.app F).hom).mp
  ext U m
  exact (ConcreteCategory.congr_hom
    (congr_app (congrArg (sheafToPresheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}).map
        ((cUnderlying B X Λ φ).inv_hom_id_app F)) U) m).trans
      ((Classical.choose_spec (cUnderlying_existsUnique B X Λ φ)).1 F U m).symm

private theorem cUnderlying_unit_smul (X : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ)
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) (U : X.ProEtᵒᵖ)
    (b : B) (m : F.obj.obj U) :
    ((cUnderlying B X Λ φ).inv.app F).hom.app U (φ b • m) =
      HSMul.hSMul (β := ((C B X Λ φ).obj F).val.obj U)
        ((scalarUnit B X).app U b) (((cUnderlying B X Λ φ).inv.app F).hom.app U m) := by
  rw [cUnderlying_inv_unit]
  have h := (((PresheafOfModules.sheafificationAdjunction.{u + 1}
    (finiteCoefficientScalarMap X Λ)).unit.app
      ((finiteCoefficientModulePresheaf X.ProEt Λ).obj F.obj)).app U).hom.map_smul (φ b) m
  have hs := ConcreteCategory.congr_hom (congr_app (finiteScalarMap_unit B X Λ φ) U) b
  change (finiteScalarMap B X Λ φ).hom.app U ((scalarUnit B X).app U b) =
    (finiteCoefficientScalarMap X Λ).app U (φ b) at hs
  change _ = HSMul.hSMul (β := ((finiteCoefficientRealization X Λ).obj F).val.obj U)
    ((finiteScalarMap B X Λ φ).hom.app U ((scalarUnit B X).app U b)) _
  rw [hs]
  exact h

private theorem cUnderlying_hom_smul (X : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ)
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) (U : X.ProEtᵒᵖ)
    (b : B) (m : ((C B X Λ φ).obj F).val.obj U) :
    ((cUnderlying B X Λ φ).hom.app F).hom.app U ((scalarUnit B X).app U b • m) =
      HSMul.hSMul (β := F.obj.obj U) (φ b)
        (((cUnderlying B X Λ φ).hom.app F).hom.app U m) := by
  apply (ConcreteCategory.bijective_of_isIso
    (((cUnderlying B X Λ φ).inv.app F).hom.app U)).1
  have hi (n : ((C B X Λ φ).obj F).val.obj U) :
      ((cUnderlying B X Λ φ).inv.app F).hom.app U
        (((cUnderlying B X Λ φ).hom.app F).hom.app U n) = n :=
    ConcreteCategory.congr_hom (congr_app
      (congrArg (sheafToPresheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}).map
        ((cUnderlying B X Λ φ).hom_inv_id_app F)) U) n
  rw [cUnderlying_unit_smul, hi, hi]

private theorem moduleDirectImage_scalarUnit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Modules B X) (U : Y.ProEtᵒᵖ) (b : B)
    (m : M.val.obj ((Scheme.proEtaleBaseChange f).op.obj U)) :
    HSMul.hSMul (β := ((moduleDirectImage B f).obj M).val.obj U)
      ((scalarUnit B Y).app U b) m =
    (scalarUnit B X).app ((Scheme.proEtaleBaseChange f).op.obj U) b • m := by
  have hρ : Scheme.proEtaleRingDirectImageMap f (coefficients B Y)
      (coefficients B X) (constantRingIso B f) =
      Scheme.proEtaleConstantDirectImageMap f CommRingCat.{u + 1} (CommRingCat.of B) := by
    exact ((Scheme.proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _).apply_symm_apply _
  have hn := Equiv.apply_symm_apply
    ((sheafificationAdjunction (Scheme.ProEt.topology Y)
    CommRingCat.{u + 1}).homEquiv
      ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of B))
      ((Scheme.proEtaleSheafDirectImage f CommRingCat.{u + 1}).obj (coefficients B X)))
      (Functor.whiskerLeft (Scheme.proEtaleBaseChange f).op
        (toSheafify (Scheme.ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of B))))
  change _ ≫ (Scheme.proEtaleConstantDirectImageMap f CommRingCat.{u + 1}
    (CommRingCat.of B)).hom = _ at hn
  have hu := ConcreteCategory.congr_hom (congr_app hn U) b
  change HSMul.hSMul (β := M.val.obj ((Scheme.proEtaleBaseChange f).op.obj U))
    ((Scheme.proEtaleRingDirectImageMap f (coefficients B Y)
      (coefficients B X) (constantRingIso B f)).hom.app U
      ((toSheafify (Scheme.ProEt.topology Y)
        ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of B))).app U b)) m = _
  rw [hρ]
  exact congrArg (fun r ↦ r • m) hu

/-- Direct image commutes with this scalar realization by identity on sections.
Source: Stacks, Tag 0D6E
(blueprint: def-cbc-finite-constant-coefficient-transport).
Proof: after the underlying-sheaf identifications both sides have sections of F
on U ×_Y X. Identity on these sections is B-linear because both coefficient maps
send b to the constant value φ(b). It is natural and invertible. Faithfulness of
underlying additive sheaves proves uniqueness. -/
theorem cDirect_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ) :
    ∃! e : ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f ⋙ C B Y Λ φ ≅
        C B X Λ φ ⋙ moduleDirectImage B f,
      ∀ (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))
        (U : Y.ProEtᵒᵖ)
        (m : ((C B Y Λ φ).obj
          ((ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f).obj F)).val.obj U),
        ((cUnderlying B X Λ φ).hom.app F).hom.app
            ((Scheme.proEtaleBaseChange f).op.obj U) ((e.hom.app F).val.app U m) =
          ((cUnderlying B Y Λ φ).hom.app
            ((ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f).obj F)).hom.app U m := by
  let L := ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f ⋙ C B Y Λ φ
  let R := C B X Λ φ ⋙ moduleDirectImage B f
  let T := SheafOfModules.toSheaf.{u + 1}
    ((sheafCompose (Scheme.ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (coefficients B Y))
  let a : L ⋙ T ≅ R ⋙ T :=
    isoWhiskerLeft (ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f) (cUnderlying B Y Λ φ) ≪≫
      isoWhiskerRight (cUnderlying B X Λ φ).symm (ProEtale.lowerStar AddCommGrpCat.{u + 1} f)
  have : Presheaf.IsLocallySurjective (Scheme.ProEt.topology Y) (scalarUnit B Y) :=
    scalarUnit_surjective B Y
  let g (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) :
      L.obj F ⟶ R.obj F :=
    ⟨(PresheafOfModules.restrictHomEquivOfIsLocallySurjective
      (scalarUnit B Y) (R.obj F).isSheaf).symm
      (PresheafOfModules.homMk (a.hom.app F).hom (fun U b m ↦ by
        change ((cUnderlying B X Λ φ).inv.app F).hom.app
            ((Scheme.proEtaleBaseChange f).op.obj U)
            (((cUnderlying B Y Λ φ).hom.app
              ((ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f).obj F)).hom.app U
                ((scalarUnit B Y).app U b • (show (L.obj F).val.obj U from m))) = _
        rw [cUnderlying_hom_smul, cUnderlying_unit_smul]
        exact (moduleDirectImage_scalarUnit B f ((C B X Λ φ).obj F) U b _).symm))⟩
  have hg (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) :
      T.map (g F) = a.hom.app F := rfl
  let t : L ⟶ R :=
    { app := g
      naturality := fun {F G} h ↦ by
        apply T.map_injective
        simp only [Functor.map_comp, hg]
        exact a.hom.naturality h }
  have ht (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) :
      IsIso (t.app F) := by
    have : IsIso (T.map (t.app F)) := by
      change IsIso (T.map (g F))
      rw [hg]
      infer_instance
    exact isIso_of_reflects_iso _ T
  have : IsIso t := NatIso.isIso_of_isIso_app t
  refine ⟨asIso t, ?_, ?_⟩
  · intro F U m
    change ((cUnderlying B X Λ φ).hom.app F).hom.app
      ((Scheme.proEtaleBaseChange f).op.obj U) ((t.app F).val.app U m) = _
    have he := ConcreteCategory.congr_hom (congr_app
      (congrArg (sheafToPresheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}).map
        ((cUnderlying B X Λ φ).inv_hom_id_app F))
          ((Scheme.proEtaleBaseChange f).op.obj U))
    exact he _
  · intro e he
    apply Iso.ext
    apply NatTrans.ext
    funext F
    apply T.map_injective
    apply Sheaf.hom_ext
    ext U m
    apply (ConcreteCategory.bijective_of_isIso
      (((cUnderlying B X Λ φ).hom.app F).hom.app
        ((Scheme.proEtaleBaseChange f).op.obj U))).1
    exact (he F U m).trans (by
      have h := ConcreteCategory.congr_hom (congr_app
        (congrArg (sheafToPresheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}).map
          ((cUnderlying B X Λ φ).inv_hom_id_app F))
            ((Scheme.proEtaleBaseChange f).op.obj U))
      exact (h _).symm)

/-- The canonical sectionwise scalar/direct-image comparison.
Source: Stacks, Tag 0D6E
(blueprint: def-cbc-finite-constant-coefficient-transport). -/
noncomputable def cDirect {X Y : Scheme.{u}} (f : X ⟶ Y) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ) :
    ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f ⋙ C B Y Λ φ ≅
      C B X Λ φ ⋙ moduleDirectImage B f :=
  Classical.choose (cDirect_existsUnique B f Λ φ)

/-- The actual etale-to-pro-etale comparison followed by scalar realization.
Source: Stacks, Tag 099R
(blueprint: def-cbc-finite-constant-coefficient-transport). -/
noncomputable def H (X : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ) :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⥤ Modules B X :=
  comparisonUpperStar (ModuleCat.{u + 1} Λ) X ⋙ C B X Λ φ

/-- The canonical inverse-image-square mate, followed by identity on scalar sections.
Source: Stacks, Tags 099R, 0D6E and 07A7
(blueprint: def-cbc-finite-constant-coefficient-transport). -/
noncomputable def hDirect {X Y : Scheme.{u}} (f : X ⟶ Y) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ) :
    Etale.lowerStar (ModuleCat.{u + 1} Λ) f ⋙ H B Y Λ φ ⟶
      H B X Λ φ ⋙ moduleDirectImage B f :=
  (Functor.associator _ _ _).inv ≫
  Functor.whiskerRight
    (mateEquiv (cbcEtaleComparisonAdjunction (ModuleCat.{u + 1} Λ) f)
      (cbcProEtaleComparisonAdjunction (ModuleCat.{u + 1} Λ) f)
      (cbcComparisonCoefficientPullbackIso (ModuleCat.{u + 1} Λ) f).inv) (C B Y Λ φ) ≫
  (Functor.associator _ _ _).hom ≫
  Functor.whiskerLeft (comparisonUpperStar (ModuleCat.{u + 1} Λ) X)
    (cDirect B f Λ φ).hom ≫ (Functor.associator _ _ _).inv

/-- The inverse-image comparison is precisely the inverse mate of hDirect.
Source: Stacks, Tags 03EK and 07A7
(blueprint: def-cbc-finite-constant-coefficient-transport). -/
noncomputable def hPullbackInv {X Y : Scheme.{u}} (f : X ⟶ Y) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ) :
    H B Y Λ φ ⋙ modulePullback B f ⟶
      Etale.upperStar (ModuleCat.{u + 1} Λ) f ⋙ H B X Λ φ :=
  (mateEquiv (cbcEtaleComparisonAdjunction (ModuleCat.{u + 1} Λ) f)
    (Scheme.proEtaleRingModuleAdjunction f (coefficients B Y)
      (coefficients B X) (constantRingIso B f))).symm (hDirect B f Λ φ)

section MateHelpers

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {A D E F : Type*} [Category A] [Category D] [Category E] [Category F]
  {G : A ⥤ E} {G' : A ⥤ E} {H : D ⥤ F} {H' : D ⥤ F}
  {L₁ : A ⥤ D} {R₁ : D ⥤ A} {L₂ : E ⥤ F} {R₂ : F ⥤ E}

private theorem inverseMate_isIso_of_equivalences (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂)
    [G.IsEquivalence] [H.IsEquivalence]
    (β : TwoSquare R₁ H G R₂) [IsIso β] :
    IsIso ((mateEquiv a b).symm β) := by
  let eG := G.asEquivalence.toAdjunction
  let eH := H.asEquivalence.toAdjunction
  let α := (mateEquiv a b).symm β
  have hi : IsIso (mateEquiv eH eG β) := by
    dsimp only [mateEquiv, Equiv.coe_fn_mk]
    infer_instance
  have he := iterated_mateEquiv_conjugateEquiv a b eG eH α
  change (mateEquiv eH eG ((mateEquiv a b) ((mateEquiv a b).symm β))) = _ at he
  rw [Equiv.apply_symm_apply] at he
  have : IsIso (conjugateEquiv (a.comp eH) (eG.comp b) α) := he ▸ hi
  exact conjugateEquiv_of_iso (a.comp eH) (eG.comp b) α

private theorem inverseMate_iso_edges (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂)
    (e : G' ≅ G) (f : H ≅ H') (β : TwoSquare R₁ H G R₂)
    [IsIso ((mateEquiv a b).symm β)] :
    IsIso ((mateEquiv a b).symm
      ((β.whiskerRight e.hom).whiskerLeft f.hom)) := by
  have he := mateEquiv_whiskerTop_whiskerBottom a b ((mateEquiv a b).symm β)
    e.hom f.hom
  rw [Equiv.apply_symm_apply] at he
  have he' : (mateEquiv a b).symm ((β.whiskerRight e.hom).whiskerLeft f.hom) =
      (((mateEquiv a b).symm β).whiskerTop e.hom).whiskerBottom f.hom := by
    apply (mateEquiv a b).injective
    exact (Equiv.apply_symm_apply _ _).trans he.symm
  rw [he']
  dsimp only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.mk]
  infer_instance

private theorem inverseMate_ofNatIsoRight (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂)
    {R₁' : D ⥤ A} {R₂' : F ⥤ E} (e : R₁' ≅ R₁) (f : R₂' ≅ R₂)
    (β : TwoSquare R₁ H G R₂) :
    ((mateEquiv (a.ofNatIsoRight e.symm) (b.ofNatIsoRight f.symm)).symm
      (TwoSquare.mk _ _ _ _
        (Functor.whiskerRight e.hom G ≫ β ≫
          Functor.whiskerLeft H f.inv))) =
      ((mateEquiv a b).symm β) := by
  ext X
  dsimp only [mateEquiv, Equiv.coe_fn_symm_mk, Adjunction.ofNatIsoRight_unit,
    Adjunction.ofNatIsoRight_counit, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.comp_obj, Functor.comp_map,
    Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app,
    Functor.associator_hom_app, Functor.associator_inv_app]
  simp only [Category.id_comp, Functor.map_comp, Category.assoc]
  simp only [← Functor.map_comp_assoc, CategoryTheory.Functor.map_id, Category.id_comp]
  simp only [Iso.symm_hom, Iso.symm_inv, Iso.inv_hom_id_app,
    Category.comp_id]

end MateHelpers

section PastingHelpers

variable {A D E F K L : Type*} [Category A] [Category D] [Category E] [Category F]
  [Category K] [Category L]
  {G₁ : A ⥤ E} {G₂ : E ⥤ K} {H₁ : D ⥤ F} {H₂ : F ⥤ L}
  {P₁ : A ⥤ D} {P₂ : E ⥤ F} {P₃ : K ⥤ L}

private theorem isIso_of_hComp (α : TwoSquare G₁ P₁ P₂ H₁)
    (β : TwoSquare G₂ P₂ P₃ H₂) [IsIso β]
    [IsIso (TwoSquare.hComp α β)] [H₂.ReflectsIsomorphisms] :
    IsIso α := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  have : IsIso (β.app (G₁.obj M) ≫ H₂.map (α.app M)) := by
    simpa [TwoSquare.hComp] using
      (inferInstance : IsIso ((TwoSquare.hComp α β).app M))
  have : IsIso (H₂.map (α.app M)) := IsIso.of_isIso_comp_left (β.app (G₁.obj M)) _
  exact isIso_of_reflects_iso _ H₂

private theorem inv_hComp (α : TwoSquare G₁ P₁ P₂ H₁)
    (β : TwoSquare G₂ P₂ P₃ H₂) [IsIso α] [IsIso β]
    [IsIso (TwoSquare.hComp α β)] :
    CategoryTheory.inv (TwoSquare.hComp α β) =
      (TwoSquare.vComp (TwoSquare.mk _ _ _ _ (CategoryTheory.inv α))
        (TwoSquare.mk _ _ _ _ (CategoryTheory.inv β))) := by
  simp [TwoSquare.hComp, TwoSquare.vComp]

variable {J₁ : D ⥤ A} {J₂ : F ⥤ E} {J₃ : L ⥤ K}

private theorem inverseMate_vComp (a : J₁ ⊣ P₁) (b : J₂ ⊣ P₂) (c : J₃ ⊣ P₃)
    (α : TwoSquare P₁ G₁ H₁ P₂) (β : TwoSquare P₂ G₂ H₂ P₃) :
    (mateEquiv a c).symm (TwoSquare.vComp α β) =
      TwoSquare.hComp ((mateEquiv a b).symm α) ((mateEquiv b c).symm β) := by
  apply (mateEquiv a c).injective
  exact (Equiv.apply_symm_apply _ _).trans
    (by simpa only [Equiv.apply_symm_apply] using
      (mateEquiv_vcomp a b c ((mateEquiv a b).symm α)
        ((mateEquiv b c).symm β)).symm)

end PastingHelpers

section FixedCoefficients

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] C cUnderlying

set_option backward.isDefEq.respectTransparency false in
private noncomputable def ringUnitRestrictionPresheaf
    {S : Type (u + 1)} [Category.{u} S] (J : GrothendieckTopology S)
    (R : Sheaf J RingCat.{u + 1})
    (α : (Functor.const Sᵒᵖ).obj (RingCat.of B) ⟶ R.obj) (M : SheafOfModules.{u + 1} R) :
    Sᵒᵖ ⥤ ModuleCat.{u + 1} B :=
  let P := (PresheafOfModules.restrictScalars α).obj M.val
  { obj := P.obj
    map := fun f ↦ P.map f
    map_id := fun V ↦ by ext m; exact ConcreteCategory.congr_hom (P.presheaf.map_id V) m
    map_comp := fun f g ↦ by
      ext m
      exact ConcreteCategory.congr_hom (P.presheaf.map_comp f g) m }

set_option backward.isDefEq.respectTransparency false in
private noncomputable def ringUnitRestriction
    {S : Type (u + 1)} [Category.{u} S] (J : GrothendieckTopology S)
    (R : Sheaf J RingCat.{u + 1})
    (α : (Functor.const Sᵒᵖ).obj (RingCat.of B) ⟶ R.obj) :
    SheafOfModules.{u + 1} R ⥤ Sheaf J (ModuleCat.{u + 1} B) where
  obj M := ⟨ringUnitRestrictionPresheaf B J R α M,
    Presheaf.isSheaf_of_isSheaf_comp _ _
      (forget₂ (ModuleCat.{u + 1} B) AddCommGrpCat.{u + 1}) M.isSheaf⟩
  map f := { hom :=
    { app := fun V ↦ (ModuleCat.restrictScalars (α.app V).hom).map (f.val.app V)
      naturality := fun _ _ h ↦ by
        ext m
        exact PresheafOfModules.naturality_apply f.val h m } }

private noncomputable def fixedRestriction (X : Scheme.{u}) :
    Modules B X ⥤ Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B) :=
  ringUnitRestriction B (Scheme.ProEt.topology X) _ (scalarUnit B X)

set_option backward.isDefEq.respectTransparency false in
private noncomputable def ringUnitRestrictionFullyFaithful
    {S : Type (u + 1)} [Category.{u} S] (J : GrothendieckTopology S)
    (R : Sheaf J RingCat.{u + 1})
    (α : (Functor.const Sᵒᵖ).obj (RingCat.of B) ⟶ R.obj)
    [Presheaf.IsLocallySurjective J α] : (ringUnitRestriction B J R α).FullyFaithful := by
  exact {
    preimage {M N} f := ⟨(PresheafOfModules.restrictHomEquivOfIsLocallySurjective
      α N.isSheaf).symm ((finiteCoefficientModulePresheaf S B).map f.hom)⟩
    map_preimage := by intro M N f; ext V m; rfl
    preimage_map := by intro M N f; ext V m; rfl }

set_option backward.isDefEq.respectTransparency false in
private theorem ringUnitRestriction_equivalence
    {S : Type (u + 1)} [Category.{u} S] (J : GrothendieckTopology S)
    (R : Sheaf J RingCat.{u + 1})
    (α : (Functor.const Sᵒᵖ).obj (RingCat.of B) ⟶ R.obj)
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
    [HasSheafify J AddCommGrpCat.{u + 1}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}] :
    (ringUnitRestriction B J R α).IsEquivalence := by
  have : (ringUnitRestriction B J R α).Full :=
    (ringUnitRestrictionFullyFaithful B J R α).full
  have : (ringUnitRestriction B J R α).Faithful :=
    (ringUnitRestrictionFullyFaithful B J R α).faithful
  have : (ringUnitRestriction B J R α).EssSurj := by
    refine ⟨fun F ↦ ?_⟩
    let P := (finiteCoefficientModulePresheaf S B).obj F.obj
    let M := (PresheafOfModules.sheafification α).obj P
    let η := (PresheafOfModules.sheafificationAdjunction α).unit.app P
    let η' : F ⟶ (ringUnitRestriction B J R α).obj M :=
      { hom := { app := η.app
                 naturality := fun {_ _} f ↦ by
                   ext m
                   exact PresheafOfModules.naturality_apply η f m } }
    have : IsIso η := by
      apply (isIso_iff_of_reflects_iso η (PresheafOfModules.toPresheaf _)).mp
      change IsIso (toSheafify J P.presheaf)
      exact isIso_toSheafify _ ((sheafCompose J
        (forget₂ (ModuleCat.{u + 1} B) AddCommGrpCat.{u + 1})).obj F).property
    have : IsIso η' := by
      apply (isIso_iff_of_reflects_iso η' (sheafToPresheaf _ _)).mp
      change IsIso η'.hom
      have (V : Sᵒᵖ) : IsIso (η'.hom.app V) := by
        apply (isIso_iff_of_reflects_iso _
          (forget₂ (ModuleCat.{u + 1} B) AddCommGrpCat.{u + 1})).mp
        change IsIso (((PresheafOfModules.toPresheaf _).map η).app V)
        infer_instance
      exact NatIso.isIso_of_isIso_app _
    exact ⟨M, ⟨(asIso η').symm⟩⟩
  exact Functor.IsEquivalence.mk

private theorem fixedRestriction_equivalence (X : Scheme.{u}) :
    (fixedRestriction B X).IsEquivalence := by
  have : Presheaf.IsLocallyInjective (Scheme.ProEt.topology X) (scalarUnit B X) := by
    apply (Presheaf.isLocallyInjective_forget_iff _ _).mp
    change Presheaf.IsLocallyInjective (Scheme.ProEt.topology X)
      (Functor.whiskerRight (toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of B))) (forget CommRingCat.{u + 1}))
    infer_instance
  have := scalarUnit_surjective B X
  exact ringUnitRestriction_equivalence B (Scheme.ProEt.topology X)
    ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (coefficients B X)) (scalarUnit B X)

attribute [local instance] fixedRestriction_equivalence
attribute [local irreducible] constantSheaf

set_option backward.isDefEq.respectTransparency false in
private noncomputable def ringUnitLinearize
    {S : Type (u + 1)} [Category.{u} S] (J : GrothendieckTopology S)
    (R : Sheaf J RingCat.{u + 1})
    (α : (Functor.const Sᵒᵖ).obj (RingCat.of B) ⟶ R.obj)
    (Λ : Type (u + 1)) [CommRing Λ] (φ : B →+* Λ) (M : SheafOfModules.{u + 1} R)
    (F : Sheaf J (ModuleCat.{u + 1} Λ))
    (a : M.val.presheaf ⟶ F.obj ⋙ forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
    (ha : ∀ (V : Sᵒᵖ) (b : B) (m : M.val.obj V),
      a.app V ((α.app V b) • m) =
        HSMul.hSMul (β := F.obj.obj V) (φ b) (a.app V m)) :
    (ringUnitRestriction B J R α).obj M ⟶ (Sheaf.restrictScalars J φ).obj F := ⟨
    { app := fun V ↦ ConcreteCategory.ofHom (C := ModuleCat.{u + 1} B)
        { toFun := fun m ↦ a.app V m
          map_add' := fun m n ↦ (a.app V).hom.map_add m n
          map_smul' := fun b m ↦ ha V b m }
      naturality := fun _ _ h ↦ by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro m
        exact ConcreteCategory.congr_hom (a.naturality h) m }⟩

set_option backward.isDefEq.respectTransparency false in
private noncomputable def ringUnitLinearizeIso
    {S : Type (u + 1)} [Category.{u} S] (J : GrothendieckTopology S)
    (R : Sheaf J RingCat.{u + 1})
    (α : (Functor.const Sᵒᵖ).obj (RingCat.of B) ⟶ R.obj)
    {D : Type*} [Category D] (Λ : Type (u + 1)) [CommRing Λ] (φ : B →+* Λ)
    (L : D ⥤ SheafOfModules.{u + 1} R) (Q : D ⥤ Sheaf J (ModuleCat.{u + 1} Λ))
    (a : L ⋙ SheafOfModules.toSheaf R ≅ Q ⋙
      sheafCompose J (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}))
    (ha : ∀ (N : D) (V : Sᵒᵖ) (b : B) (m : (L.obj N).val.obj V),
      (a.hom.app N).hom.app V ((α.app V b) • m) =
        HSMul.hSMul (β := (Q.obj N).obj.obj V) (φ b) ((a.hom.app N).hom.app V m)) :
    L ⋙ ringUnitRestriction B J R α ≅ Q ⋙ Sheaf.restrictScalars J φ := by
  let T := sheafCompose J (forget₂ (ModuleCat.{u + 1} B) AddCommGrpCat.{u + 1})
  let g (N : D) := ringUnitLinearize B J R α Λ φ (L.obj N) (Q.obj N)
    (a.hom.app N).hom (ha N)
  have hg (N : D) : T.map (g N) = a.hom.app N := by
    ext V m
    rfl
  let t : L ⋙ ringUnitRestriction B J R α ⟶ Q ⋙ Sheaf.restrictScalars J φ :=
    { app := g
      naturality := fun {M N} f ↦ by
        ext V m
        change (a.hom.app N).hom.app V ((L.map f).val.app V m) =
          (Q.map f).hom.app V ((a.hom.app M).hom.app V m)
        exact ConcreteCategory.congr_hom (congr_app
          (congrArg (sheafToPresheaf J AddCommGrpCat.{u + 1}).map
            (a.hom.naturality f)) V) m }
  have hi (N : D) : IsIso (t.app N) := by
    have : IsIso (T.map (t.app N)) := by
      change IsIso (T.map (g N))
      rw [hg]
      infer_instance
    exact isIso_of_reflects_iso _ T
  have : IsIso t := NatIso.isIso_of_isIso_app t
  exact asIso t

private theorem fixedRestriction_additive (X : Scheme.{u}) :
    (fixedRestriction B X).Additive where
  map_add := by intros; ext V m; rfl

private noncomputable def cFixed (X : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ) :
    C B X Λ φ ⋙ fixedRestriction B X ≅
      Sheaf.restrictScalars (Scheme.ProEt.topology X) φ :=
  ringUnitLinearizeIso B (Scheme.ProEt.topology X)
    ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (coefficients B X))
    (scalarUnit B X) Λ φ (C B X Λ φ) (𝟭 _) (cUnderlying B X Λ φ)
      (cUnderlying_hom_smul B X Λ φ)

set_option backward.isDefEq.respectTransparency false in
private noncomputable def ringUnitPushforwardIso
    {S T : Type (u + 1)} [Category.{u} S] [Category.{u} T]
    (J : GrothendieckTopology S) (K : GrothendieckTopology T) (F : S ⥤ T)
    [F.IsContinuous J K] (R : Sheaf K RingCat.{u + 1}) (R' : Sheaf J RingCat.{u + 1})
    (α : (Functor.const Tᵒᵖ).obj (RingCat.of B) ⟶ R.obj)
    (α' : (Functor.const Sᵒᵖ).obj (RingCat.of B) ⟶ R'.obj)
    (ψ : R' ⟶ (F.sheafPushforwardContinuous RingCat.{u + 1} J K).obj R)
    (ha : ∀ (M : SheafOfModules.{u + 1} R) (V : Sᵒᵖ) (b : B)
      (m : M.val.obj (F.op.obj V)),
      HSMul.hSMul (β := ((SheafOfModules.pushforward.{u + 1} ψ).obj M).val.obj V)
        (α'.app V b) m = α.app (F.op.obj V) b • m) :
    SheafOfModules.pushforward.{u + 1} ψ ⋙ ringUnitRestriction B J R' α' ≅
      ringUnitRestriction B K R α ⋙ F.sheafPushforwardContinuous (ModuleCat.{u + 1} B) J K :=
by
  let t : SheafOfModules.pushforward.{u + 1} ψ ⋙ ringUnitRestriction B J R' α' ⟶
      ringUnitRestriction B K R α ⋙
        F.sheafPushforwardContinuous (ModuleCat.{u + 1} B) J K :=
    { app := fun M ↦ { hom :=
        { app := fun V ↦ ModuleCat.ofHom
            (X := (ModuleCat.restrictScalars (α'.app V).hom).obj
              ((ModuleCat.restrictScalars (ψ.hom.app V).hom).obj (M.val.obj (F.op.obj V))))
            (Y := (ModuleCat.restrictScalars (α.app (F.op.obj V)).hom).obj
              (M.val.obj (F.op.obj V)))
            { toFun := fun m ↦ m
              map_add' := fun _ _ ↦ rfl
              map_smul' := fun b m ↦ ha M V b m }
          naturality := fun _ _ h ↦ by ext m; rfl } }
      naturality := fun {_ _} h ↦ by ext V m; rfl }
  have (M : SheafOfModules.{u + 1} R) : IsIso (t.app M) := by
    apply (isIso_iff_of_reflects_iso _
      (sheafCompose J (forget₂ (ModuleCat.{u + 1} B) AddCommGrpCat.{u + 1}))).mp
    change IsIso (𝟙 ((sheafCompose J
      (forget₂ (ModuleCat.{u + 1} B) AddCommGrpCat.{u + 1})).obj
        ((SheafOfModules.pushforward.{u + 1} ψ ⋙ ringUnitRestriction B J R' α').obj M)))
    infer_instance
  have : IsIso t := NatIso.isIso_of_isIso_app _
  exact asIso t

private noncomputable def fixedDirect {X Y : Scheme.{u}} (f : X ⟶ Y) :
    moduleDirectImage B f ⋙ fixedRestriction B Y ≅
      fixedRestriction B X ⋙ lowerStar (ModuleCat.{u + 1} B) f :=
  ringUnitPushforwardIso B (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)
    (Scheme.proEtaleBaseChange f)
    ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (coefficients B X))
    ((sheafCompose (Scheme.ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (coefficients B Y))
    (scalarUnit B X) (scalarUnit B Y)
    ⟨Functor.whiskerRight
      (Scheme.proEtaleRingDirectImageMap f (coefficients B Y) (coefficients B X)
        (constantRingIso B f)).hom (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
    (moduleDirectImage_scalarUnit B f)

private theorem cFixed_direct {X Y : Scheme.{u}} (f : X ⟶ Y)
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ) :
    (TwoSquare.vComp
      (TwoSquare.mk (lowerStar (ModuleCat.{u + 1} Λ) f)
        (C B X Λ φ) (C B Y Λ φ) (moduleDirectImage B f) (cDirect B f Λ φ).hom)
      (TwoSquare.mk (moduleDirectImage B f)
        (fixedRestriction B X) (fixedRestriction B Y)
        (lowerStar (ModuleCat.{u + 1} B) f) (fixedDirect B f).hom)) ≫
      Functor.whiskerRight (cFixed B X Λ φ).hom (lowerStar (ModuleCat.{u + 1} B) f) =
    Functor.whiskerLeft (lowerStar (ModuleCat.{u + 1} Λ) f) (cFixed B Y Λ φ).hom := by
  ext M V m
  change ((cUnderlying B X Λ φ).hom.app M).hom.app
      ((Scheme.proEtaleBaseChange f).op.obj V)
      (((cDirect B f Λ φ).hom.app M).val.app V m) =
    ((cUnderlying B Y Λ φ).hom.app ((lowerStar (ModuleCat.{u + 1} Λ) f).obj M)).hom.app V m
  exact (Classical.choose_spec (cDirect_existsUnique B f Λ φ)).1 M V m

attribute [local irreducible] fixedRestriction fixedDirect cFixed

private theorem scalar_direct_mate
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (mateEquiv (upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f)
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
      (TwoSquare.mk _ _ _ _ (upperStarRestrictScalarsIso φ f).hom)) =
        𝟙 (lowerStar (ModuleCat.{u + 1} B) f ⋙
          Sheaf.restrictScalars (Scheme.ProEt.topology Y) φ) := by
  apply (mateEquiv (Sheaf.restrictCoextendScalarsAdj (Scheme.ProEt.topology X) φ)
    (Sheaf.restrictCoextendScalarsAdj (Scheme.ProEt.topology Y) φ)).injective
  rw [iterated_mateEquiv_conjugateEquiv]
  rw [conjugateEquiv_upperStarRestrictScalarsIso_hom]
  ext M ⟨U⟩ x
  exact congrArg (fun t ↦ t.hom x)
    ((ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} φ).right_triangle_components
      (M.obj.obj (Opposite.op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj U)))).symm

private theorem siteDirect_eq {X Y : Scheme.{u}} (f : X ⟶ Y)
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [TopologicalSpace Λ] [DiscreteTopology Λ] :
    (mateEquiv (cbcEtaleComparisonAdjunction (ModuleCat.{u + 1} Λ) f)
      (cbcProEtaleComparisonAdjunction (ModuleCat.{u + 1} Λ) f)
      (cbcComparisonCoefficientPullbackIso (ModuleCat.{u + 1} Λ) f).inv) =
        lowerStarComparisonUpperStarBaseChange f (ModuleCat.{u + 1} Λ) := by
  change mateEquiv _ _ _ = (mateEquiv
    (comparisonAdjunction (ModuleCat.{u + 1} Λ) X)
    (comparisonAdjunction (ModuleCat.{u + 1} Λ) Y)).symm
      (lowerStarCompComparisonLowerStarIso f (ModuleCat.{u + 1} Λ)).inv
  apply (mateEquiv (comparisonAdjunction (ModuleCat.{u + 1} Λ) X)
    (comparisonAdjunction (ModuleCat.{u + 1} Λ) Y)).injective
  rw [Equiv.apply_symm_apply]
  rw [iterated_mateEquiv_conjugateEquiv]
  change conjugateEquiv
    ((cbcEtaleComparisonAdjunction (ModuleCat.{u + 1} Λ) f).comp
      (cbcComparisonCoefficientAdjunction (ModuleCat.{u + 1} Λ) X))
    ((cbcComparisonCoefficientAdjunction (ModuleCat.{u + 1} Λ) Y).comp
      (cbcProEtaleComparisonAdjunction (ModuleCat.{u + 1} Λ) f))
    (cbcComparisonCoefficientPullbackIso (ModuleCat.{u + 1} Λ) f).inv = _
  change conjugateEquiv
    ((cbcEtaleComparisonAdjunction (ModuleCat.{u + 1} Λ) f).comp
      (cbcComparisonCoefficientAdjunction (ModuleCat.{u + 1} Λ) X))
    ((cbcComparisonCoefficientAdjunction (ModuleCat.{u + 1} Λ) Y).comp
      (cbcProEtaleComparisonAdjunction (ModuleCat.{u + 1} Λ) f))
    ((conjugateEquiv _ _).symm
      (cbcComparisonCoefficientDirectImageIso (ModuleCat.{u + 1} Λ) f).inv) = _
  exact (Equiv.apply_symm_apply _ _).trans (by rfl)

private theorem hDirect_isIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ) :
    IsIso (hDirect B f Λ φ) := by
  have : IsIso (mateEquiv
      (cbcEtaleComparisonAdjunction (ModuleCat.{u + 1} Λ) f)
      (cbcProEtaleComparisonAdjunction (ModuleCat.{u + 1} Λ) f)
      (cbcComparisonCoefficientPullbackIso (ModuleCat.{u + 1} Λ) f).inv) := by
    rw [siteDirect_eq]
    exact isIso_lowerStarComparisonUpperStarBaseChange f (ModuleCat.{u + 1} Λ)
  dsimp only [hDirect]
  infer_instance

private theorem cPullback_fixed {X Y : Scheme.{u}} (f : X ⟶ Y)
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ) :
    let a := upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f
    let b := Scheme.proEtaleRingModuleAdjunction f (coefficients B Y)
      (coefficients B X) (constantRingIso B f)
    let c := upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f
    TwoSquare.hComp ((mateEquiv a b).symm (cDirect B f Λ φ).hom)
        ((mateEquiv b c).symm (fixedDirect B f).hom) =
      ((TwoSquare.mk _ _ _ _ (upperStarRestrictScalarsIso φ f).hom).whiskerTop
        (cFixed B Y Λ φ).hom).whiskerBottom (cFixed B X Λ φ).inv := by
  dsimp only
  let a := upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f
  let b := Scheme.proEtaleRingModuleAdjunction f (coefficients B Y)
    (coefficients B X) (constantRingIso B f)
  let c := upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f
  let α := (mateEquiv a b).symm (cDirect B f Λ φ).hom
  let β := (mateEquiv b c).symm (fixedDirect B f).hom
  let d := TwoSquare.vComp
    (TwoSquare.mk _ _ _ _ (cDirect B f Λ φ).hom)
    (TwoSquare.mk _ _ _ _ (fixedDirect B f).hom)
  let t := TwoSquare.hComp α β
  let s := TwoSquare.mk _ _ _ _ (upperStarRestrictScalarsIso φ f).hom
  have hm : mateEquiv a c t = d := by
    simpa only [t, d, α, β, Equiv.apply_symm_apply] using
      mateEquiv_vcomp a b c α β
  have hd : d =
      ((mateEquiv a c s).whiskerRight (cFixed B Y Λ φ).hom).whiskerLeft
        (cFixed B X Λ φ).inv := by
    change d = Functor.whiskerLeft _ (cFixed B Y Λ φ).hom ≫
      (mateEquiv a c s) ≫ Functor.whiskerRight (cFixed B X Λ φ).inv _
    have hs : (mateEquiv a c s) = 𝟙 _ := scalar_direct_mate φ f
    rw [hs, Category.id_comp]
    apply (cancel_mono (Functor.whiskerRight (cFixed B X Λ φ).hom
      (lowerStar (ModuleCat.{u + 1} B) f))).mp
    simp only [Category.assoc, ← Functor.whiskerRight_comp, Iso.inv_hom_id,
      Functor.whiskerRight_id']
    erw [Category.comp_id]
    exact cFixed_direct B f Λ φ
  apply (mateEquiv a c).injective
  exact hm.trans (hd.trans
    (mateEquiv_whiskerTop_whiskerBottom a c s
      (cFixed B Y Λ φ).hom (cFixed B X Λ φ).inv).symm)

private theorem cPullback_isIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ) :
    IsIso ((mateEquiv (cbcProEtaleComparisonAdjunction (ModuleCat.{u + 1} Λ) f)
      (Scheme.proEtaleRingModuleAdjunction f (coefficients B Y)
        (coefficients B X) (constantRingIso B f))).symm (cDirect B f Λ φ).hom) := by
  let a := upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f
  let b := Scheme.proEtaleRingModuleAdjunction f (coefficients B Y)
    (coefficients B X) (constantRingIso B f)
  let c := upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f
  let α := (mateEquiv a b).symm (cDirect B f Λ φ).hom
  let β := (mateEquiv b c).symm (fixedDirect B f).hom
  have : IsIso β := inverseMate_isIso_of_equivalences b c (fixedDirect B f).hom
  have : IsIso (TwoSquare.hComp α β) := by
    rw [show TwoSquare.hComp α β = _ from cPullback_fixed B f Λ φ]
    dsimp only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.mk]
    infer_instance
  exact isIso_of_hComp α β

end FixedCoefficients

/-- The specified coefficient/site pullback comparison is invertible.
Source: Stacks, Tags 03EK and 099R
(blueprint: def-cbc-finite-constant-coefficient-transport).
Proof: separate site inverse image from scalar restriction. The former has the
canonical inverse-image comparison; the latter keeps the inverse-image additive
sheaf and restricts its action. On constant scalars the two actions coincide.
The unit-section normalization identifies their composite with this inverse mate.
No flatness and no preservation of injectives by scalar restriction is used. -/
theorem hPullbackInv_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ) :
    IsIso (hPullbackInv B f Λ φ) := by
  let a := cbcEtaleComparisonAdjunction (ModuleCat.{u + 1} Λ) f
  let b := cbcProEtaleComparisonAdjunction (ModuleCat.{u + 1} Λ) f
  let c := Scheme.proEtaleRingModuleAdjunction f (coefficients B Y)
    (coefficients B X) (constantRingIso B f)
  let α := (cbcComparisonCoefficientPullbackIso (ModuleCat.{u + 1} Λ) f).inv
  let β := ((mateEquiv b c).symm (cDirect B f Λ φ).hom)
  have : IsIso β := cPullback_isIso B f Λ φ
  have h := mateEquiv_vcomp a b c α β
  rw [Equiv.apply_symm_apply] at h
  have he : hPullbackInv B f Λ φ = (TwoSquare.hComp α β) := by
    apply (mateEquiv a c).injective
    change (mateEquiv a c) ((mateEquiv a c).symm (hDirect B f Λ φ)) = _
    rw [Equiv.apply_symm_apply]
    exact h.symm
  rw [he]
  dsimp only [TwoSquare.hComp, TwoSquare.mk]
  infer_instance

section OpenComparison

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] C fixedRestriction fixedDirect cFixed constantSheaf
attribute [local instance] fixedRestriction_equivalence

private noncomputable def scalarRestrictionModel {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (Λ : Type (u + 1)) [CommRing Λ] (φ : B →+* Λ) :
    Sheaf.restrictScalars (Scheme.ProEt.topology X) φ ⋙
      openImmersionRestriction (ModuleCat.{u + 1} B) j ≅
    openImmersionRestriction (ModuleCat.{u + 1} Λ) j ⋙
      Sheaf.restrictScalars (Scheme.ProEt.topology U) φ := Iso.refl _

private noncomputable def scalarPullbackModel {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (Λ : Type (u + 1)) [CommRing Λ] (φ : B →+* Λ) :
    Sheaf.restrictScalars (Scheme.ProEt.topology X) φ ⋙
      upperStar (ModuleCat.{u + 1} B) j ≅
    upperStar (ModuleCat.{u + 1} Λ) j ⋙
      Sheaf.restrictScalars (Scheme.ProEt.topology U) φ :=
  Functor.isoWhiskerLeft (Sheaf.restrictScalars (Scheme.ProEt.topology X) φ)
      (upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} B) j) ≪≫
    (scalarRestrictionModel B j Λ φ) ≪≫
    Functor.isoWhiskerRight
      (upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} Λ) j).symm
      (Sheaf.restrictScalars (Scheme.ProEt.topology U) φ)

private theorem scalarOpenModel_isIso {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (Λ : Type (u + 1)) [CommRing Λ] (φ : B →+* Λ) :
    IsIso ((mateEquiv
      (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j)
      (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j)).symm
        (scalarPullbackModel B j Λ φ).inv) := by
  have he := inverseMate_ofNatIsoRight
    (openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} Λ) j)
    (openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} B) j)
    (upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} Λ) j)
    (upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} B) j)
    (TwoSquare.mk _ _ _ _ (scalarRestrictionModel B j Λ φ).inv)
  change IsIso (((mateEquiv
    ((openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} Λ) j).ofNatIsoRight
      (upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} Λ) j).symm)
    ((openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} B) j).ofNatIsoRight
      (upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} B) j).symm)).symm
      (TwoSquare.mk _ _ _ _
        (Functor.whiskerRight
            (upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} Λ) j).hom _ ≫
          (scalarRestrictionModel B j Λ φ).inv ≫ Functor.whiskerLeft _
            (upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} B) j).inv))))
  rw [he]
  exact scalarMap_isIso φ j

private theorem scalarRestriction_direct_mate {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (Λ : Type (u + 1)) [CommRing Λ] (φ : B →+* Λ) :
    (mateEquiv
      (openImmersionRestrictionLowerStarAdjunction (ModuleCat.{u + 1} Λ) j)
      (openImmersionRestrictionLowerStarAdjunction (ModuleCat.{u + 1} B) j)
      (TwoSquare.mk _ _ _ _ (scalarRestrictionModel B j Λ φ).hom)) =
      𝟙 (lowerStar (ModuleCat.{u + 1} Λ) j ⋙
        Sheaf.restrictScalars (Scheme.ProEt.topology X) φ) := by
  ext M V m
  change ((Sheaf.restrictScalars (Scheme.ProEt.topology X) φ).map
    ((openImmersionRestrictionLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).unit.app
        ((lowerStar (ModuleCat.{u + 1} Λ) j).obj M) ≫
      (lowerStar (ModuleCat.{u + 1} Λ) j).map
        ((openImmersionRestrictionLowerStarAdjunction
          (ModuleCat.{u + 1} Λ) j).counit.app M))).hom.app V m = m
  rw [Adjunction.right_triangle_components]
  rfl

private theorem scalarPullbackModel_direct_mate {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (Λ : Type (u + 1)) [CommRing Λ] (φ : B →+* Λ) :
    (mateEquiv (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j)
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) j)
      (scalarPullbackModel B j Λ φ).hom) =
      𝟙 (lowerStar (ModuleCat.{u + 1} Λ) j ⋙
        Sheaf.restrictScalars (Scheme.ProEt.topology X) φ) := by
  change (mateEquiv (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) j)
    (TwoSquare.mk _ _ _ _
      (Functor.whiskerLeft (Sheaf.restrictScalars (Scheme.ProEt.topology X) φ)
          ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) j).leftAdjointUniq
            (openImmersionRestrictionLowerStarAdjunction (ModuleCat.{u + 1} B) j)).hom ≫
        (scalarRestrictionModel B j Λ φ).hom ≫
        Functor.whiskerRight
          ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).leftAdjointUniq
            (openImmersionRestrictionLowerStarAdjunction (ModuleCat.{u + 1} Λ) j)).inv
          (Sheaf.restrictScalars (Scheme.ProEt.topology U) φ)))) = _
  rw [mateEquiv_leftAdjointUniq]
  exact scalarRestriction_direct_mate B j Λ φ

private theorem siteOpen_isIso {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [TopologicalSpace Λ] [DiscreteTopology Λ] :
    IsIso ((mateEquiv
      (Etale.openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j)
      (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j)).symm
        (cbcComparisonCoefficientPullbackIso (ModuleCat.{u + 1} Λ) j).hom) := by
  let e := Etale.openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} Λ) j
  let p := openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} Λ) j
  let uEt := Etale.upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} Λ) j
  let uPro := upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} Λ) j
  let β := TwoSquare.mk _ _ _ _
    (openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} Λ) j).inv
  let γ := TwoSquare.mk _ _ _ _ (openComparisonRestrictionIso Λ j).hom
  have hm : mateEquiv e p β = γ := by
    apply mateEquiv_eq_of_unit e p β γ
    intro F
    apply (cancel_mono ((openImmersionRestriction (ModuleCat.{u + 1} Λ) j).map
      ((openImmersionLowerShriekComparisonUpperStarIso
        (ModuleCat.{u + 1} Λ) j).hom.app F))).mp
    simp only [β, Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
    exact (openComparison_unit_normalization Λ j).2 F
  have : IsIso ((mateEquiv e p).symm γ) := by
    rw [← hm, Equiv.symm_apply_apply]
    change IsIso (openImmersionLowerShriekComparisonUpperStarIso
      (ModuleCat.{u + 1} Λ) j).inv
    infer_instance
  have hγ : (cbcComparisonCoefficientPullbackIso (ModuleCat.{u + 1} Λ) j).hom =
      Functor.whiskerRight uEt.hom (comparisonUpperStar (ModuleCat.{u + 1} Λ) U) ≫
        γ ≫ Functor.whiskerLeft (comparisonUpperStar (ModuleCat.{u + 1} Λ) X)
          uPro.inv := by
    change (cbcComparisonCoefficientPullbackIso (ModuleCat.{u + 1} Λ) j).hom =
      Functor.whiskerRight uEt.hom (comparisonUpperStar (ModuleCat.{u + 1} Λ) U) ≫
        (Functor.whiskerRight uEt.inv (comparisonUpperStar (ModuleCat.{u + 1} Λ) U) ≫
          (supportSiteComparisonCoefficientPullbackIso (ModuleCat.{u + 1} Λ) j).hom ≫
          Functor.whiskerLeft (comparisonUpperStar (ModuleCat.{u + 1} Λ) X) uPro.hom) ≫
        Functor.whiskerLeft (comparisonUpperStar (ModuleCat.{u + 1} Λ) X) uPro.inv
    simp only [Category.assoc, ← Functor.whiskerRight_comp_assoc, Iso.hom_inv_id,
      Functor.whiskerRight_id', Category.id_comp, ← Functor.whiskerLeft_comp]
    rfl
  change IsIso (((mateEquiv (e.ofNatIsoRight uEt.symm)
    (p.ofNatIsoRight uPro.symm)).symm
      (TwoSquare.mk _ _ _ _
        (cbcComparisonCoefficientPullbackIso (ModuleCat.{u + 1} Λ) j).hom)))
  rw [hγ]
  erw [inverseMate_ofNatIsoRight e p uEt uPro γ]
  infer_instance

private theorem scalarPullbackModel_eq {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (Λ : Type (u + 1)) [CommRing Λ] (φ : B →+* Λ) :
    scalarPullbackModel B j Λ φ = upperStarRestrictScalarsIso φ j := by
  apply Iso.ext
  apply (mateEquiv (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) j)).injective
  exact (scalarPullbackModel_direct_mate B j Λ φ).trans
    (scalar_direct_mate φ j).symm

private theorem cOpen_isIso {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ) :
    let a := upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j
    let b := Scheme.proEtaleRingModuleAdjunction j (coefficients B X)
      (coefficients B U) (constantRingIso B j)
    let α := (mateEquiv a b).symm (cDirect B j Λ φ).hom
    letI : IsIso α := cPullback_isIso B j Λ φ
    IsIso ((mateEquiv
      (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j)
      (moduleJAdj B j)).symm (CategoryTheory.inv α)) := by
  dsimp only
  let a := upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j
  let b := Scheme.proEtaleRingModuleAdjunction j (coefficients B X)
    (coefficients B U) (constantRingIso B j)
  let c := upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) j
  let α := (mateEquiv a b).symm (cDirect B j Λ φ).hom
  let β := (mateEquiv b c).symm (fixedDirect B j).hom
  have : IsIso α := cPullback_isIso B j Λ φ
  have : IsIso β := inverseMate_isIso_of_equivalences b c (fixedDirect B j).hom
  let t := TwoSquare.hComp α β
  have : IsIso t := by
    dsimp only [t, TwoSquare.hComp]
    infer_instance
  let oa := openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j
  let ob := moduleJAdj B j
  let oc := openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j
  let s := TwoSquare.mk _ _ _ _ (upperStarRestrictScalarsIso φ j).inv
  have : IsIso ((mateEquiv oa oc).symm s) := by
    change IsIso ((mateEquiv oa oc).symm
      (upperStarRestrictScalarsIso φ j).inv)
    rw [← scalarPullbackModel_eq B j Λ φ]
    exact scalarOpenModel_isIso B j Λ φ
  let d := (s.whiskerRight (cFixed B U Λ φ).hom).whiskerLeft (cFixed B X Λ φ).inv
  have : IsIso ((mateEquiv oa oc).symm d) :=
    inverseMate_iso_edges oa oc (cFixed B U Λ φ) (cFixed B X Λ φ).symm s
  let z := (Functor.isoWhiskerRight (cFixed B X Λ φ)
      (upperStar (ModuleCat.{u + 1} B) j) ≪≫ upperStarRestrictScalarsIso φ j) ≪≫
    Functor.isoWhiskerLeft (upperStar (ModuleCat.{u + 1} Λ) j) (cFixed B U Λ φ).symm
  have hz : t = z.hom := 
    (cPullback_fixed B j Λ φ)
  have hd : CategoryTheory.inv t = d := by
    calc
      CategoryTheory.inv t = CategoryTheory.inv z.hom := IsIso.inv_eq_inv.mpr hz
      _ = d := by
        simp only [IsIso.Iso.inv_hom, z, Iso.trans_inv, Functor.isoWhiskerLeft_inv,
          Functor.isoWhiskerRight_inv, Iso.symm_inv, d, s, TwoSquare.whiskerRight,
          TwoSquare.whiskerLeft, TwoSquare.mk, Category.assoc]
  have ht : IsIso ((mateEquiv oa oc).symm
      (TwoSquare.mk _ _ _ _ (CategoryTheory.inv t))) := by
    rw [hd]
    infer_instance
  let γ := (mateEquiv oa ob).symm (TwoSquare.mk _ _ _ _ (CategoryTheory.inv α))
  let δ := (mateEquiv ob oc).symm (TwoSquare.mk _ _ _ _ (CategoryTheory.inv β))
  have : IsIso δ := inverseMate_isIso_of_equivalences ob oc _
  have he : (mateEquiv oa oc).symm (TwoSquare.mk _ _ _ _ (CategoryTheory.inv t)) =
      TwoSquare.hComp γ δ := by
    dsimp only [t]
    rw [inv_hComp]
    exact inverseMate_vComp oa ob oc _ _
  rw [he] at ht
  exact isIso_of_hComp γ δ

end OpenComparison

/-- The inverse open comparison is the open-adjunction inverse mate of pullback.
Source: Stacks, Tag 09AF
(blueprint: def-cbc-finite-constant-coefficient-transport). -/
noncomputable def hOpenInv {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ) :
    H B U Λ φ ⋙ moduleJ B j ⟶
      Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j ⋙ H B X Λ φ :=
  ((mateEquiv (Etale.openImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} Λ) j) (moduleJAdj B j)).symm
    (@inv _ _ _ _ (hPullbackInv B j Λ φ) (hPullbackInv_isIso B j Λ φ)))

/-- The specified inverse open comparison is invertible.
Source: Stacks, Tag 09AF
(blueprint: def-cbc-finite-constant-coefficient-transport).
Proof: factor the pullback comparison into its site and coefficient squares.
The site square has an invertible open mate by the recorded open-unit normalization.
Restricting modules over the constant ring sheaf to constant scalars is an equivalence.
After this equivalence, the coefficient square is the standard scalar pullback square:
its direct-image mate acts identically on sections. On an open immersion its open mate
is the scalar extension-by-zero comparison. Both identifications follow by injectivity
of the mate correspondence. Pasting the two invertible open mates gives the specified
inverse open comparison. The argument also covers the empty open and zero ring. -/
theorem hOpenInv_isIso {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ) :
    IsIso (hOpenInv B j Λ φ) := by
  let a := cbcEtaleComparisonAdjunction (ModuleCat.{u + 1} Λ) j
  let b := cbcProEtaleComparisonAdjunction (ModuleCat.{u + 1} Λ) j
  let c := Scheme.proEtaleRingModuleAdjunction j (coefficients B X)
    (coefficients B U) (constantRingIso B j)
  let α := (cbcComparisonCoefficientPullbackIso (ModuleCat.{u + 1} Λ) j).inv
  let β := (mateEquiv b c).symm (cDirect B j Λ φ).hom
  have : IsIso β := cPullback_isIso B j Λ φ
  have : IsIso (TwoSquare.hComp α β) := by
    dsimp only [TwoSquare.hComp]
    infer_instance
  have : IsIso (hPullbackInv B j Λ φ) := hPullbackInv_isIso B j Λ φ
  have hp := mateEquiv_vcomp a b c α β
  rw [Equiv.apply_symm_apply] at hp
  have he : hPullbackInv B j Λ φ = (TwoSquare.hComp α β) := by
    apply (mateEquiv a c).injective
    change (mateEquiv a c) ((mateEquiv a c).symm (hDirect B j Λ φ)) = _
    rw [Equiv.apply_symm_apply]
    exact hp.symm
  let oa := Etale.openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j
  let ob := openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j
  let oc := moduleJAdj B j
  let γ := TwoSquare.mk _ _ _ _ (cbcComparisonCoefficientPullbackIso
    (ModuleCat.{u + 1} Λ) j).hom
  let δ := TwoSquare.mk _ _ _ _ (CategoryTheory.inv β)
  have hi : CategoryTheory.inv (hPullbackInv B j Λ φ) = (TwoSquare.vComp γ δ) := by
    calc
      CategoryTheory.inv (hPullbackInv B j Λ φ) =
          CategoryTheory.inv (TwoSquare.hComp α β) := IsIso.inv_eq_inv.mpr he
      _ = (TwoSquare.vComp γ δ) := by
        simpa only [α, γ, δ, IsIso.Iso.inv_inv] using inv_hComp α β
  have : IsIso ((mateEquiv oa ob).symm γ) := siteOpen_isIso j Λ
  have : IsIso ((mateEquiv ob oc).symm δ) := cOpen_isIso B j Λ φ
  change IsIso ((mateEquiv oa oc).symm (CategoryTheory.inv (hPullbackInv B j Λ φ)))
  rw [hi]
  change IsIso ((mateEquiv oa oc).symm (TwoSquare.vComp γ δ))
  have hu : IsIso (TwoSquare.hComp ((mateEquiv oa ob).symm γ)
      ((mateEquiv ob oc).symm δ)) := by
    dsimp only [TwoSquare.hComp]
    infer_instance
  exact ((inverseMate_vComp oa ob oc γ δ)).symm ▸ hu

/-- The forward open comparison is the inverse of the specified open-adjunction mate.
Source: Stacks, Tag 09AF
(blueprint: def-cbc-finite-constant-coefficient-transport). -/
noncomputable def hOpen {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ) :
    Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j ⋙ H B X Λ φ ⟶
      H B U Λ φ ⋙ moduleJ B j :=
  (@asIso _ _ _ _ (hOpenInv B j Λ φ) (hOpenInv_isIso B j Λ φ)).inv

/-- The normalized forward open comparison is invertible.
Source: Stacks, Tag 09AF
(blueprint: def-cbc-finite-constant-coefficient-transport).
Proof: this is the inverse of the invertible unit-normalized inverse comparison,
so the two inverse identities give invertibility of the forward arrow. -/
theorem hOpen_isIso {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ) :
    IsIso (hOpen B j Λ φ) := by
  dsimp only [hOpen]
  infer_instance

/-- The comparison functor is additive and exact.
Source: Stacks, Tags 03DA and 099R
(blueprint: def-cbc-finite-constant-coefficient-transport).
Proof: comparison inverse image, finite realization and scalar restriction are
additive and exact. Their composite therefore preserves finite limits and colimits. -/
theorem h_exact (X : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ) :
    (H B X Λ φ).Additive ∧ PreservesFiniteLimits (H B X Λ φ) ∧
      PreservesFiniteColimits (H B X Λ φ) := by
  dsimp only [H, C]
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- Additivity of H. Source: Stacks, Tag 099R
(blueprint: def-cbc-finite-constant-coefficient-transport). -/
noncomputable instance h_additive (X : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ) :
    (H B X Λ φ).Additive := (h_exact B X Λ φ).1

/-- Left exactness of H. Source: Stacks, Tag 099R
(blueprint: def-cbc-finite-constant-coefficient-transport). -/
noncomputable instance h_finiteLimits (X : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ) :
    PreservesFiniteLimits (H B X Λ φ) := (h_exact B X Λ φ).2.1

/-- Right exactness of H. Source: Stacks, Tag 099R
(blueprint: def-cbc-finite-constant-coefficient-transport). -/
noncomputable instance h_finiteColimits (X : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ) :
    PreservesFiniteColimits (H B X Λ φ) := (h_exact B X Λ φ).2.2

/-- The bounded-below comparison included into the unbounded target.
Source: Stacks, Tags 099R and 05RU
(blueprint: def-cbc-finite-constant-coefficient-transport). -/
noncomputable def HD (X : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ) :
    DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory (Modules B X) :=
  (H B X Λ φ).mapDerivedCategoryPlus ⋙ DerivedCategory.Plus.ι

/-- Canonical derived direct-image comparison; its unit normalization is built into
rightDerivedFunctorPlusBaseChange. Source: Stacks, Tags 099R and 0B65
(blueprint: def-cbc-finite-constant-coefficient-transport). -/
noncomputable def hR {U X : Scheme.{u}} (f : U ⟶ X) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ) :
    Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) f ⋙ HD B X Λ φ ⟶
      HD B U Λ φ ⋙ (moduleDirectImage B f).rightDerivedFunctor :=
  (Functor.associator _ _ _).inv ≫
  Functor.whiskerRight (Functor.rightDerivedFunctorPlusBaseChange (hDirect B f Λ φ))
    DerivedCategory.Plus.ι ≫
  (Functor.associator _ _ _).hom ≫
  Functor.whiskerLeft (H B U Λ φ).mapDerivedCategoryPlus
    (moduleDirectImage B f).rightDerivedFunctorPlusCompatibility.hom ≫
  (Functor.associator _ _ _).inv

section DerivedHelpers

variable {A A' D D' : Type*} [Category* A] [Category* A']
  [Category* D] [Category* D'] [Abelian A] [Abelian A'] [Abelian D] [Abelian D']
  [HasInjectiveResolutions A] [HasInjectiveResolutions A']
  {F : A ⥤ D} {F' : A' ⥤ D'} {E : A ⥤ A'} {E' : D ⥤ D'}
  [F.Additive] [F'.Additive] [E.Additive] [E'.Additive]
  [PreservesFiniteLimits F'] [E.IsEquivalence] [E'.IsEquivalence]

private theorem rightAcyclic_of_equivalenceSquare (e : F ⋙ E' ≅ E ⋙ F') (M : A)
    (h : F'.rightAcyclic (E.obj M)) : F.rightAcyclic M := by
  intro q
  let e' : E'.obj ((F.rightDerived (q + 1)).obj M) ≅
      (F'.rightDerived (q + 1)).obj (E.obj M) :=
    (Functor.rightDerivedCompObjIso F E' (q + 1) M).symm ≪≫
      Functor.rightDerivedObjIsoOfIso e (q + 1) M ≪≫
      Functor.compRightDerivedObjIso E F'
        (fun I _ ↦ Functor.rightAcyclic_of_injective (E.obj I)) (q + 1) M
  have hz : IsZero (E'.obj ((F.rightDerived (q + 1)).obj M)) := (h q).of_iso e'
  apply (IsZero.iff_id_eq_zero _).mpr
  apply E'.map_injective
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero]
  exact hz.eq_of_src _ _

end DerivedHelpers

section DerivedComparison

attribute [local irreducible] C fixedRestriction fixedDirect cFixed constantSheaf

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] fixedRestriction_equivalence fixedRestriction_additive

private theorem h_rightAcyclic {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ)
    (I : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [Injective I] :
    (moduleDirectImage B f).rightAcyclic ((H B X Λ φ).obj I) := by
  apply rightAcyclic_of_equivalenceSquare (fixedDirect B f)
  let F := (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).obj I
  have hF := rightAcyclic_lowerStar_comparisonUpperStar_obj_of_injective
    (ModuleCat.{u + 1} Λ) f I
  have h : (lowerStar (ModuleCat.{u + 1} B) f).rightAcyclic
      ((Sheaf.restrictScalars (Scheme.ProEt.topology X) φ).obj F) := by
    intro q
    exact (Functor.map_isZero (Sheaf.restrictScalars (Scheme.ProEt.topology Y) φ)
      (hF q)).of_iso ((rightDerivedLowerStarRestrictScalarsIso φ f (q + 1)).app F).symm
  exact (lowerStar (ModuleCat.{u + 1} B) f).rightAcyclic.prop_of_iso
    ((cFixed B X Λ φ).app F).symm h

/-- This particular direct-image comparison is an isomorphism for qcqs maps.
Source: Stacks, Tag 099R
(blueprint: def-cbc-finite-constant-coefficient-transport).
Proof: the underived site mate is invertible for qcqs maps, and the normalized
coefficient comparison is invertible. The image of an injective etale sheaf under
site inverse image is direct-image acyclic. The higher-direct-image scalar comparison
transports this acyclicity through scalar restriction. The equivalence between modules
over the constant ring sheaf and fixed-ring module sheaves reflects acyclicity and
identifies their higher direct images. Thus H sends injective etale sheaves to
module-direct-image acyclic objects. Apply the acyclic-object criterion to the exact
functors H and the specified hDirect; its derived base-change map is invertible.
The associators and compatibility isomorphisms in hR preserve invertibility. -/
theorem hR_isIso {U X : Scheme.{u}} (f : U ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ) :
    IsIso (hR B f Λ φ) := by
  have : (moduleDirectImage B f).IsRightAdjoint :=
    (Scheme.proEtaleRingModuleAdjunction f (coefficients B X)
      (coefficients B U) (constantRingIso B f)).isRightAdjoint
  have : IsIso (hDirect B f Λ φ) := hDirect_isIso B f Λ φ
  have : IsIso (Functor.rightDerivedFunctorPlusBaseChange (hDirect B f Λ φ)) :=
    Functor.isIso_rightDerivedFunctorPlusBaseChange_of_rightAcyclic
      (asIso (hDirect B f Λ φ)) (fun I _ ↦ h_rightAcyclic B f Λ φ I)
  dsimp only [hR]
  infer_instance

end DerivedComparison

/-- Derived open comparison with the same open-unit normalization.
Source: Stacks, Tag 09AF
(blueprint: def-cbc-finite-constant-coefficient-transport). -/
noncomputable def hJ {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ) :
    (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).mapDerivedCategoryPlus ⋙
        HD B X Λ φ ≅ HD B U Λ φ ⋙ (moduleJ B j).mapDerivedCategory :=
  (Functor.associator _ _ _).symm ≪≫
  isoWhiskerRight
    ((Functor.mapDerivedCategoryPlusCompIso _ _).symm ≪≫
      Functor.mapDerivedCategoryPlusNatIso
        (@asIso _ _ _ _ (hOpen B j Λ φ) (hOpen_isIso B j Λ φ)) ≪≫
      Functor.mapDerivedCategoryPlusCompIso _ _) DerivedCategory.Plus.ι ≪≫
  Functor.associator _ _ _ ≪≫
  isoWhiskerLeft (H B U Λ φ).mapDerivedCategoryPlus
    (moduleJ B j).mapDerivedCategoryPlusCompatibility ≪≫
  (Functor.associator _ _ _).symm

/-- The canonical comparison from H of the etale origin to its scalar-restricted
finite-coefficient realization. Source: blueprint finite-origin hypothesis
(blueprint: def-cbc-finite-constant-coefficient-transport). -/
noncomputable def originIso {X : Scheme.{u}} {K : DerivedCategory (Modules B X)}
    (w : ScalarEtaleOrigin B X K) : (HD B X w.Λ w.φ).obj w.origin.L ≅ K :=
  (isoWhiskerRight
    (Functor.mapDerivedCategoryPlusCompIso
      (finiteCoefficientComparison X w.Λ) (finiteRestriction B X w.Λ w.φ))
    DerivedCategory.Plus.ι ≪≫ Functor.associator _ _ _ ≪≫
    isoWhiskerLeft (finiteCoefficientComparison X w.Λ).mapDerivedCategoryPlus
      (finiteRestriction B X w.Λ w.φ).mapDerivedCategoryPlusCompatibility ≪≫
    (Functor.associator _ _ _).symm).app w.origin.L ≪≫
  (finiteRestriction B X w.Λ w.φ).mapDerivedCategory.mapIso
    (DerivedCategory.Plus.ι.mapIso w.origin.alpha) ≪≫ w.iso

end AlgebraicGeometry.ProEtale.StrictTower
