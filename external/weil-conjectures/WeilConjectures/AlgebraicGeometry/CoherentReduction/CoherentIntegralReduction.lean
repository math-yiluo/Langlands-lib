/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SfIntegralReductionTower
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteDiscreteSchemeRingSupplement
public import WeilConjectures.AlgebraicGeometry.Semilinear.ConstantCoefficientSystem
public import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOperations
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.SectionActionInternal
public import WeilConjectures.CategoryTheory.ConstantRingModuleSheaves
public import WeilConjectures.CategoryTheory.Sites.ConstantRingSheafMonObj
public import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
public import WeilConjectures.AlgebraicGeometry.FiniteProperQuotient.FiniteProperExceptionalQuotient
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.Instances.Discrete
public import WeilConjectures.NumberTheory.Padics.IntegersCosetBasis

/-! # The actual coherent integral reduction system

Source: Zheng, Construction 4.1, and the first step of
`lem-sfb-finite-proper-exceptional-coherent-tower`.
(blueprint: def-sfb-coherent-integral-reduction)

Coefficients are continuous condensed rings pulled back from the point. The
reduction is one derived scalar extension on the sequence site. The field of
coefficients may have universe u+1 while the schemes have universe u.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures.SemilinearSections
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CoherentReduction

attribute [local instance] WeilConjectures.instEssentiallySmallProEt_weilConjectures

/-- Continuous functions on profinite tests, with pointwise commutative ring operations.
Source: Bhatt--Scholze, Definition 6.5.1
(blueprint: def-sfb-coherent-integral-reduction). -/
def continuousPresheaf (T : Type (u + 1)) [CommRing T] [TopologicalSpace T]
    [IsTopologicalRing T] : Profinite.{u}ᵒᵖ ⥤ CommRingCat.{u + 1} where
  obj S := CommRingCat.of C(S.unop, T)
  map f := CommRingCat.ofHom
    (ContinuousMap.compRightAlgHom ℤ T f.unop.hom.hom).toRingHom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The continuous condensed coefficient ring, with its actual section construction.
Sheafification is included so the construction does not require a sheaf proof as data.
Source: Bhatt--Scholze, Definition 6.5.1
(blueprint: def-sfb-coherent-integral-reduction). -/
def continuousPoint (T : Type (u + 1)) [CommRing T] [TopologicalSpace T]
    [IsTopologicalRing T] : Sheaf (coherentTopology Profinite.{u}) CommRingCat.{u + 1} :=
  (presheafToSheaf _ CommRingCat.{u + 1}).obj (continuousPresheaf T)

/-- Continuous postcomposition defines the coefficient homomorphisms.
Source: Bhatt--Scholze, Definition 6.5.1
(blueprint: def-sfb-coherent-integral-reduction). -/
def continuousPointMap {T S : Type (u + 1)} [CommRing T] [CommRing S]
    [TopologicalSpace T] [TopologicalSpace S] [IsTopologicalRing T] [IsTopologicalRing S]
    (f : T →+* S) (hf : Continuous f) : continuousPoint T ⟶ continuousPoint S :=
  (presheafToSheaf _ CommRingCat.{u + 1}).map
    { app := fun U ↦ CommRingCat.ofHom (f.compLeftContinuous U.unop hf)
      naturality := fun _ _ _ ↦ rfl }

/-- The sheafified map sending a scalar to its constant continuous function.
Source: Bhatt--Scholze, Definition 6.5.1
(blueprint: def-sfb-coherent-integral-reduction). -/
def pointConstants (T : Type (u + 1)) [CommRing T] [TopologicalSpace T]
    [IsTopologicalRing T] :
    (constantSheaf (coherentTopology Profinite.{u}) CommRingCat.{u + 1}).obj
      (CommRingCat.of T) ⟶ continuousPoint T :=
  (presheafToSheaf _ CommRingCat.{u + 1}).map
    { app := fun U ↦ CommRingCat.ofHom (ContinuousMap.C (α := U.unop))
      naturality := fun _ _ _ ↦ rfl }

/-- Forget commutativity and then multiplication, retaining the canonical internal ring.
Source: the ring-object construction, Stacks 00YV
(blueprint: def-sfb-coherent-integral-reduction). -/
abbrev abelianPoint (T : Type (u + 1)) [CommRing T] [TopologicalSpace T]
    [IsTopologicalRing T] :=
  (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
    ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (continuousPoint T))

/-- The continuous coefficients are commutative internal ring objects.
Source: pointwise multiplication, Stacks 00YV
(blueprint: def-sfb-coherent-integral-reduction). -/
instance abelianPoint_comm (T : Type (u + 1)) [CommRing T] [TopologicalSpace T]
    [IsTopologicalRing T] : IsCommMonObj (abelianPoint T) :=
  Sheaf.isCommMonObj_sheafCompose_obj
    (coherentTopology Profinite.{u})
    ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (continuousPoint T))
    (fun U a b ↦ @mul_comm ((continuousPoint T).obj.obj U) inferInstance a b)

/-- The actual internal coefficient ring p_T^* underline(A).
Source: the blueprint's pulled-back-coefficient convention
(blueprint: def-sfb-coherent-integral-reduction). -/
abbrev internalRing (X : Scheme.{u}) (T : Type (u + 1)) [CommRing T]
    [TopologicalSpace T] [IsTopologicalRing T] :=
  condensedRingObj (abelianPoint T) X

/-- The actual multiplication on the pulled-back continuous ring.
Source: pointwise multiplication, Stacks 00YV
(blueprint: def-sfb-coherent-integral-reduction). -/
instance internalRingMonObj (X : Scheme.{u}) (T : Type (u + 1)) [CommRing T]
    [TopologicalSpace T] [IsTopologicalRing T] : MonObj (internalRing X T) :=
  inferInstanceAs (MonObj (condensedRingObj (abelianPoint T) X))

/-- Commutativity is transported by the original pullback, rather than chosen afresh.
Source: Stacks 00YV (blueprint: def-sfb-coherent-integral-reduction). -/
instance internalRingComm (X : Scheme.{u}) (T : Type (u + 1)) [CommRing T]
    [TopologicalSpace T] [IsTopologicalRing T] : IsCommMonObj (internalRing X T) :=
  inferInstanceAs (IsCommMonObj (condensedRingObj (abelianPoint T) X))

/-- The section-ring presentation of the same internal coefficients.
Source: Stacks 00YV, the recorded section-action equivalence
(blueprint: def-sfb-coherent-integral-reduction). -/
abbrev sectionRing (X : Scheme.{u}) (T : Type (u + 1)) [CommRing T]
    [TopologicalSpace T] [IsTopologicalRing T] :=
  InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
    (Scheme.ProEt.topology X) (internalRing X T)

/-- A morphism of internal rings, reconstructed on their original sections.
Source: Stacks 00YV (blueprint: def-sfb-coherent-integral-reduction). -/
def internalSectionMap (X : Scheme.{u})
    {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (f : R ⟶ S) [IsMonHom f] :
    InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} (Scheme.ProEt.topology X) R ⟶
      InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} (Scheme.ProEt.topology X) S :=
  ⟨Functor.whiskerRight
    ((Monoidal.commMonFunctorCategoryEquivalence X.ProEtᵒᵖ Ab.{u + 1}).functor.map
      ((sheafToPresheaf _ Ab.{u + 1}).mapCommMon.map (CommMon.homMk (Mon.ofHom f))))
    InternalAbelianSheafModule.commMonToRing.{u + 1}⟩

/-- Pull back a continuous scalar homomorphism, then reconstruct the section homomorphism.
Source: the blueprint's coefficient morphisms
(blueprint: def-sfb-coherent-integral-reduction). -/
def sectionMap (X : Scheme.{u}) {T S : Type (u + 1)} [CommRing T] [CommRing S]
    [TopologicalSpace T] [TopologicalSpace S] [IsTopologicalRing T] [IsTopologicalRing S]
    (f : T →+* S) (hf : Continuous f) : sectionRing X T ⟶ sectionRing X S :=
  internalSectionMap X ((upperStarFromPoint X).map
    ((sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
      ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (continuousPointMap f hf))))

/-- The underlying constant-section map on the scheme, using the canonical
constant-sheaf comparison for inverse image from the coefficient point.
Source: the blueprint's pulled-back coefficients
(blueprint: def-sfb-coherent-integral-reduction). -/
def schemeConstants (X : Scheme.{u}) (T : Type (u + 1)) [CommRing T]
    [TopologicalSpace T] [IsTopologicalRing T] :
    (constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).obj (AddCommGrpCat.of T) ⟶
      internalRing X T := by
  letI : HasSheafify (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1} :=
    SheafOfModules.hasSheafify_coefficientUniverse
  letI : (coherentTopology Profinite.{u}).PreservesSheafification
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
        forget₂ RingCat.{u + 1} Ab.{u + 1}) :=
    GrothendieckTopology.instPreservesSheafification _ _
  exact (constantSchemeIso X).hom.app (AddCommGrpCat.of T) ≫
    (upperStarFromPoint X).map
      (((constantCommuteCompose (coherentTopology Profinite.{u})
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
          forget₂ RingCat.{u + 1} Ab.{u + 1})).app (CommRingCat.of T)).inv ≫
        (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
          ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
            (pointConstants T)))

/-- Forgetting a ring sheaf preserves local isomorphisms on the pro-etale site.
Source: Stacks 00WH (blueprint: def-sfb-coherent-integral-reduction). -/
instance coefficientForgetPreserves (X : Scheme.{u}) :
    (Scheme.ProEt.topology X).PreservesSheafification
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
        forget₂ RingCat.{u + 1} Ab.{u + 1}) :=
  GrothendieckTopology.instPreservesSheafification _ _

section ConstantSectionsHelpers

open MonoidalCategory MonObj

/-! ### The constant-section homomorphism -/

set_option backward.isDefEq.respectTransparency false in
/-- The constant-section map from the point to the scheme is a morphism of ring objects.
Source: Stacks 00YV; monoidality of inverse image from the point
(auxiliary; not a blueprint node). -/
theorem schemeConstants_isMonHom (X : Scheme.{u}) (T : Type (u + 1)) [CommRing T]
    [TopologicalSpace T] [IsTopologicalRing T] :
    @IsMonHom _ _ _ _ _ ((constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).monObjObj
      (AddCommGrpCat.of T)) _ (schemeConstants X T) := by
  let : (coherentTopology Profinite.{u}).PreservesSheafification
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙ forget₂ RingCat.{u + 1} Ab.{u + 1}) :=
    GrothendieckTopology.instPreservesSheafification _ _
  have h₁ := isMonHom_constantCommuteCompose_inv_app (coherentTopology Profinite.{u}) T
  have h₂ := Sheaf.isMonHom_sheafCompose_map (coherentTopology Profinite.{u})
    ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (pointConstants T))
  have hi := Functor.isMonHom_compAlgHom
    (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    (upperStarFromPoint X) (constantSchemeIso X).inv (AddCommGrpCat.of T)
  exact IsMonHom.comp_of_monObj _ _ _ _ _
    (IsMonHom.inv_of_hom _ _ ((constantSchemeIso X).app (AddCommGrpCat.of T)).symm hi)
    (Functor.isMonHom_map_of_monObj (upperStarFromPoint X) _ _ _
      (IsMonHom.comp_of_monObj _ _ _ _ _ h₁ h₂))

/-- Constant sections on the scheme, as a morphism of abelian presheaves from the constant
presheaf.
Source: Stacks 03CY (auxiliary; not a blueprint node). -/
def schemeConstantsPresheaf (X : Scheme.{u}) (T : Type (u + 1)) [CommRing T]
    [TopologicalSpace T] [IsTopologicalRing T] :
    (Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of T) ⟶ (internalRing X T).obj :=
  toSheafify (Scheme.ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of T)) ≫
    (schemeConstants X T).hom

/-- The presheaf of constant sections is a morphism of ring objects of abelian presheaves.
Source: Stacks 00YV and 03CY (auxiliary; not a blueprint node). -/
theorem schemeConstantsPresheaf_isMonHom (X : Scheme.{u}) (T : Type (u + 1)) [CommRing T]
    [TopologicalSpace T] [IsTopologicalRing T] :
    @IsMonHom _ _ _ _ _ ((Functor.const X.ProEtᵒᵖ).monObjObj (AddCommGrpCat.of T))
      ((sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1}).monObjObj (internalRing X T))
      (schemeConstantsPresheaf X T) := by
  have hc := IsMonHom.of_eq (schemeConstants X T)
    (Functor.monObjObj_comp (Functor.const X.ProEtᵒᵖ)
      (presheafToSheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (AddCommGrpCat.of T)) rfl
    (hf := schemeConstants_isMonHom X T)
  exact IsMonHom.comp_of_monObj _ _ _ _ _
    ((sheafificationAdjunction (Scheme.ProEt.topology X) Ab.{u + 1}).isMonHom_unitAlgHom
      ((Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of T)))
    (Functor.isMonHom_map_of_monObj (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      _ _ _ hc)

/-- The constant-section homomorphism of commutative ring sheaves: the sheafification adjunct
of the constant sections on the scheme.
Source: Stacks 00YV and 03CY (auxiliary; not a blueprint node). -/
def constantSectionsRingMap (X : Scheme.{u}) (T : Type (u + 1)) [CommRing T]
    [TopologicalSpace T] [IsTopologicalRing T] :
    realizationRing.{u + 1, u} (Scheme.ProEt.topology X) T ⟶ sectionRing X T :=
  ((sheafificationAdjunction (Scheme.ProEt.topology X) CommRingCat.{u + 1}).homEquiv _
    (sectionRing X T)).symm
    (InternalAbelianSheafModule.constantToSectionRings (Scheme.ProEt.topology X) T
      (internalRing X T) (schemeConstantsPresheaf X T) (schemeConstantsPresheaf_isMonHom X T))

/-- The constant-section homomorphism sends the constant section of a scalar to its constant
section in the internal ring.
Source: Stacks 03CY (auxiliary; not a blueprint node). -/
theorem constantSectionsRingMap_toSheafify (X : Scheme.{u}) (T : Type (u + 1)) [CommRing T]
    [TopologicalSpace T] [IsTopologicalRing T] (U : X.ProEtᵒᵖ) (a : T) :
    (constantSectionsRingMap X T).hom.app U
      ((toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of T))).app U a) =
      (schemeConstantsPresheaf X T).app U a :=
  ConcreteCategory.congr_hom (congr_app (((sheafificationAdjunction (Scheme.ProEt.topology X)
    CommRingCat.{u + 1}).homEquiv _ (sectionRing X T)).apply_symm_apply
      (InternalAbelianSheafModule.constantToSectionRings (Scheme.ProEt.topology X) T
        (internalRing X T) (schemeConstantsPresheaf X T)
        (schemeConstantsPresheaf_isMonHom X T))) U) a

set_option backward.isDefEq.respectTransparency false in
/-- The additive map underlying the constant-section homomorphism is the constant-section map,
after the constant-sheaf comparison.
Source: Stacks 03CY (auxiliary; not a blueprint node). -/
theorem constantSectionsRingMap_forget (X : Scheme.{u}) (T : Type (u + 1)) [CommRing T]
    [TopologicalSpace T] [IsTopologicalRing T] :
    ((constantCommuteCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
        forget₂ RingCat.{u + 1} Ab.{u + 1})).app (CommRingCat.of T)).inv ≫
      (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
        forget₂ RingCat.{u + 1} Ab.{u + 1})).map (constantSectionsRingMap X T) =
      schemeConstants X T := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _ (internalRing X T).property
  rw [ObjectProperty.FullSubcategory.comp_hom, ← Category.assoc,
    toSheafify_comp_constantCommuteCompose_inv_app_hom]
  ext U a
  exact constantSectionsRingMap_toSheafify X T U a

/-! ### Finite discrete coefficients -/

/-- Constant functions from the constant presheaf to continuous functions, before
sheafification; `pointConstants` is its sheafification.
Source: Bhatt--Scholze, Definition 6.5.1 (auxiliary; not a blueprint node). -/
def pointConstantsPresheaf (T : Type (u + 1)) [CommRing T] [TopologicalSpace T]
    [IsTopologicalRing T] :
    (Functor.const Profinite.{u}ᵒᵖ).obj (CommRingCat.of T) ⟶ continuousPresheaf T where
  app U := CommRingCat.ofHom (ContinuousMap.C (α := U.unop))
  naturality _ _ _ := rfl

/-- Continuous functions from a profinite set to a finite discrete ring are locally constant:
the constant-function map is locally surjective.
Source: Bhatt--Scholze, Definition 6.5.1 (auxiliary; not a blueprint node). -/
instance pointConstantsPresheaf_isLocallySurjective (T : Type (u + 1)) [CommRing T] [Finite T]
    [TopologicalSpace T] [DiscreteTopology T] :
    Presheaf.IsLocallySurjective (coherentTopology Profinite.{u})
      (pointConstantsPresheaf T) where
  imageSieve_mem {S} s := by
    let f : C(S, T) := s
    have hclosed (a : T) : IsClosed {x : S | f x = a} :=
      isClosed_singleton.preimage f.continuous
    let (a : T) : CompactSpace {x : S // f x = a} :=
      isCompact_iff_compactSpace.mp (hclosed a).isCompact
    let := Fintype.ofFinite T
    let e := (Fintype.equivFin T).symm
    let U (i : Fin (Fintype.card T)) : Profinite.{u} :=
      Profinite.of {x : S // f x = e i}
    let incl (i : Fin (Fintype.card T)) : U i ⟶ S :=
      CompHausLike.ofHom _ ⟨Subtype.val, continuous_subtype_val⟩
    have hι : EffectiveEpiFamily U incl :=
      Profinite.effectiveEpiFamily_of_jointly_surjective U incl
        (fun x ↦ ⟨e.symm (f x), ⟨x, (e.apply_symm_apply (f x)).symm⟩, rfl⟩)
    refine coherentTopology.mem_sieves_of_hasEffectiveEpiFamily _
      ⟨Fin (Fintype.card T), inferInstance, U, incl, hι, fun i ↦ ⟨e i, ?_⟩⟩
    refine ContinuousMap.ext fun x ↦ ?_
    exact x.property.symm

/-- Equality of constant functions is locally detected: the constant-function map is locally
injective, using the empty cover of the empty profinite set.
Source: Bhatt--Scholze, Definition 6.5.1 (auxiliary; not a blueprint node). -/
instance pointConstantsPresheaf_isLocallyInjective (T : Type (u + 1)) [CommRing T]
    [TopologicalSpace T] [IsTopologicalRing T] :
    Presheaf.IsLocallyInjective (coherentTopology Profinite.{u})
      (pointConstantsPresheaf T) where
  equalizerSieve_mem {S} a b h := by
    by_cases hab : a = b
    · subst b
      exact (coherentTopology Profinite).superset_covering
        (fun _ _ _ ↦ rfl) ((coherentTopology Profinite).top_mem _)
    · have : IsEmpty S.unop := ⟨fun x ↦ hab (congrArg (fun t : C(S.unop, T) ↦ t x) h)⟩
      let U : PEmpty → Profinite.{u} := PEmpty.elim
      let incl : ∀ i, U i ⟶ S.unop := fun i ↦ i.elim
      have hι : EffectiveEpiFamily U incl :=
        Profinite.effectiveEpiFamily_of_jointly_surjective U incl (fun x ↦ isEmptyElim x)
      exact coherentTopology.mem_sieves_of_hasEffectiveEpiFamily _
        ⟨PEmpty, inferInstance, U, incl, hι, fun i ↦ i.elim⟩

/-- For a finite discrete ring, constant functions give an isomorphism from the constant
condensed ring to the continuous condensed ring.
Source: Bhatt--Scholze, Definition 6.5.1 (auxiliary; not a blueprint node). -/
instance pointConstants_isIso (T : Type (u + 1)) [CommRing T] [Finite T]
    [TopologicalSpace T] [DiscreteTopology T] : IsIso (pointConstants T) :=
  ((coherentTopology Profinite.{u}).W_iff (pointConstantsPresheaf T)).mp
    ((coherentTopology Profinite.{u}).W_of_isLocallyBijective (pointConstantsPresheaf T))

/-- For a finite discrete ring, the constant-section map on the scheme is an isomorphism.
Source: Bhatt--Scholze, finite coefficient comparison (auxiliary; not a blueprint node). -/
instance schemeConstants_isIso (X : Scheme.{u}) (T : Type (u + 1)) [CommRing T] [Finite T]
    [TopologicalSpace T] [DiscreteTopology T] : IsIso (schemeConstants X T) := by
  let : (coherentTopology Profinite.{u}).PreservesSheafification
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙ forget₂ RingCat.{u + 1} Ab.{u + 1}) :=
    GrothendieckTopology.instPreservesSheafification _ _
  have h : IsIso ((sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
        ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (pointConstants T))) := inferInstance
  have := IsIso.comp_isIso' (inferInstance : IsIso ((constantCommuteCompose
    (coherentTopology Profinite.{u}) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
      forget₂ RingCat.{u + 1} Ab.{u + 1})).app (CommRingCat.of T)).inv) h
  exact IsIso.comp_isIso' inferInstance (Functor.map_isIso (upperStarFromPoint X) _)

end ConstantSectionsHelpers

/-- Constant sections determine the map to the reconstructed continuous coefficient ring.
Source: the constant-ring/section-action comparison, Stacks 00YV
(blueprint: def-sfb-coherent-integral-reduction).

Proof: constant functions preserve addition, multiplication and one before
sheafification. Monoidal pullback from the point preserves those identities.
The section-action equivalence reconstructs this map as a homomorphism of
commutative ring sheaves. Its underlying additive map is exactly the composite
displayed here, because constantSchemeIso is the constant-pullback comparison.
The forgetful functor from commutative rings to abelian groups is faithful;
the prescribed additive map therefore proves uniqueness. Reconstructing the
section rings retains their original carriers and additive restrictions, which
accounts for the heterogeneous equality of the two ring presentations.
-/
theorem constantSections_existsUnique (X : Scheme.{u}) (T : Type (u + 1)) [CommRing T]
    [TopologicalSpace T] [IsTopologicalRing T] :
    ∃! f : realizationRing.{u + 1, u} (Scheme.ProEt.topology X) T ⟶ sectionRing X T,
      HEq ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
          forget₂ RingCat.{u + 1} Ab.{u + 1})).map f)
        (((constantCommuteCompose (Scheme.ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
            forget₂ RingCat.{u + 1} Ab.{u + 1})).app (CommRingCat.of T)).hom ≫
          schemeConstants X T) := by
  refine ⟨constantSectionsRingMap X T, heq_of_eq ?_, fun f hf ↦ ?_⟩
  · set_option backward.isDefEq.respectTransparency false in
    rw [← constantSectionsRingMap_forget, Iso.hom_inv_id_assoc]
  · have h : (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
        forget₂ RingCat.{u + 1} Ab.{u + 1})).map f =
        (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
          forget₂ RingCat.{u + 1} Ab.{u + 1})).map (constantSectionsRingMap X T) := by
      set_option backward.isDefEq.respectTransparency false in
      rw [eq_of_heq hf, ← constantSectionsRingMap_forget, Iso.hom_inv_id_assoc]
    exact (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
      forget₂ RingCat.{u + 1} Ab.{u + 1})).map_injective h

/-- The uniquely specified constant-section homomorphism.
Source: Stacks 00YV (blueprint: def-sfb-coherent-integral-reduction). -/
def constantSections (X : Scheme.{u}) (T : Type (u + 1)) [CommRing T]
    [TopologicalSpace T] [IsTopologicalRing T] :=
  (constantSections_existsUnique X T).exists.choose

/-- For finite discrete coefficients the constant-section homomorphism is an isomorphism.
Source: Bhatt--Scholze, finite coefficient comparison
(blueprint: def-sfb-coherent-integral-reduction).

Proof: continuous functions into a finite discrete ring are locally constant.
On a profinite test each such function is constant on a finite clopen partition.
These partitions are covers for the coherent topology, so pointConstants is
locally surjective. Equality of constant functions is locally detected, giving
local injectivity. Sheafification makes it an isomorphism. Pullback to X and
section-ring reconstruction preserve it. The preceding additive normalization
identifies the resulting map with constantSections by uniqueness. This includes
the zero ring and the empty scheme.
-/
theorem constantSections_isIso (X : Scheme.{u}) (T : Type (u + 1)) [CommRing T]
    [Finite T] [TopologicalSpace T] [DiscreteTopology T] :
    IsIso (constantSections X T) := by
  rw [← isIso_iff_of_reflects_iso _ (sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙ forget₂ RingCat.{u + 1} Ab.{u + 1}))]
  set_option backward.isDefEq.respectTransparency false in
  rw [constantSections, eq_of_heq (constantSections_existsUnique X T).exists.choose_spec]
  infer_instance

/-- The finite constant-coefficient identification, with its original constant-section map.
Source: finite coefficient comparison
(blueprint: def-sfb-coherent-integral-reduction). -/
def finiteConstantIso (X : Scheme.{u}) (T : Type (u + 1)) [CommRing T]
    [Finite T] [TopologicalSpace T] [DiscreteTopology T] :
    realizationRing.{u + 1, u} (Scheme.ProEt.topology X) T ≅ sectionRing X T :=
  letI := constantSections_isIso X T
  asIso (constantSections X T)

variable (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The spectral topology on the ring of integers, with no discrete replacement.
Source: the blueprint's integral coefficient ring
(blueprint: def-sfb-coherent-integral-reduction). -/
instance integersTopology : TopologicalSpace (Padic.coefficientExtensionIntegers l E) :=
  letI := spectralNorm.normedField ℚ_[l] E
  inferInstance

/-- The spectral topology makes O a topological ring.
Source: the blueprint's integral coefficient ring
(blueprint: def-sfb-coherent-integral-reduction). -/
instance integersTopologicalRing : IsTopologicalRing (Padic.coefficientExtensionIntegers l E) :=
  letI := spectralNorm.normedField ℚ_[l] E
  inferInstance

/-- Every finite quotient carries its discrete topology.
Source: the finite torsion levels of the blueprint
(blueprint: def-sfb-coherent-integral-reduction). -/
instance quotientTopology (n : ℕ) : TopologicalSpace (Etale.FiniteProperQuotient.Ring l E n) :=
  ⊥

/-- These specified finite quotient topologies are discrete.
Source: the finite torsion levels of the blueprint
(blueprint: def-sfb-coherent-integral-reduction). -/
instance quotientDiscrete (n : ℕ) : DiscreteTopology (Etale.FiniteProperQuotient.Ring l E n) :=
  ⟨rfl⟩

/-- The quotient homomorphism from O to the positive ell-power quotient.
Source: the finite torsion levels of the blueprint
(blueprint: def-sfb-coherent-integral-reduction). -/
def quotient (n : ℕ) : Padic.coefficientExtensionIntegers l E →+*
    Etale.FiniteProperQuotient.Ring l E n :=
  Ideal.Quotient.mk _

/-- The ideal generated by a power of `ℓ` in the ring of integers is a power of the
maximal ideal. -/
theorem exists_span_pow_eq_coefficientExtensionIdeal (r : ℕ) :
    ∃ k : ℕ, Ideal.span ({(l : Padic.coefficientExtensionIntegers l E) ^ r} :
      Set (Padic.coefficientExtensionIntegers l E)) = Padic.coefficientExtensionIdeal l E k := by
  have h := (Padic.coefficientExtensionIntegers_dvr l E).choose_spec
  have : IsDiscreteValuationRing (Padic.coefficientExtensionIntegers l E) := h.2.2.2.2.2.2.2.1
  have hgen := h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hirr : Irreducible (Padic.coefficientExtensionUniformizer l E) := by
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer,
      ← IsLocalRing.eq_maximalIdeal h.2.2.2.2.1]
    exact hgen.symm
  have hl : ((l : Padic.coefficientExtensionIntegers l E) ^ r) ≠ 0 := by
    refine pow_ne_zero _ fun h0 ↦ ?_
    have h1 := congrArg (fun x : Padic.coefficientExtensionIntegers l E ↦ (x : E)) h0
    simp only [Subring.coe_natCast, ZeroMemClass.coe_zero] at h1
    have h2 : algebraMap ℚ_[l] E (l : ℚ_[l]) = 0 := by simpa using h1
    have h3 := (FaithfulSMul.algebraMap_injective ℚ_[l] E) (h2.trans (map_zero _).symm)
    exact (Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero) h3
  obtain ⟨k, hk⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible
    (s := Ideal.span {(l : Padic.coefficientExtensionIntegers l E) ^ r})
    (by simpa [Ideal.span_singleton_eq_bot] using hl) hirr
  exact ⟨k, by rw [hk, Padic.coefficientExtensionIdeal, Ideal.span_singleton_pow]⟩

/-- Positive ell-power quotients of the ring of integers are finite rings.
Source: the blueprint's finite torsion coefficients
(blueprint: def-sfb-coherent-integral-reduction).

Proof: the integer ring of the finite extension is a DVR with finite residue
field. The nonzero element ell has positive valuation, so ell^(n+1) generates
the same ideal as a positive power of a uniformizer. Filter its quotient by
successive powers of that uniformizer. Each successive quotient is the finite
residue field. Induction on the positive exponent makes the entire quotient
finite. Ramified extensions are included: the exponent is multiplied by their
ramification index, not replaced by n+1.
-/
@[instance] theorem quotient_finite (n : ℕ) : Finite (Etale.FiniteProperQuotient.Ring l E n) := by
  obtain ⟨k, hk⟩ := exists_span_pow_eq_coefficientExtensionIdeal l E (n + 1)
  exact @Finite.of_surjective _ _
    (Padic.finite_coefficientExtensionRing l E (k + 1) (Nat.le_add_left 1 k))
    ((Ideal.quotEquivOfEq hk.symm) ∘
      Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ k)))
    ((Ideal.quotEquivOfEq hk.symm).surjective.comp (Ideal.Quotient.factor_surjective _))

/-- Positive ell-power quotients of the spectral ring of integers are continuous
with their discrete topology.
Source: the finite torsion levels in the blueprint; Zheng, Construction 4.1
(blueprint: def-sfb-coherent-integral-reduction).

Proof: the spectral absolute value restricts to the given l-adic absolute value.
The ideal generated by ell^(n+1) in O is therefore open: a sufficiently small
spectral ball is contained in it, using the discrete valuation of the finite
extension. Every fibre of the quotient map is a translate of this open ideal.
Preimages of arbitrary sets of the discrete quotient are unions of these open
fibres. The quotient homomorphism is continuous. Positivity of n+1 excludes the
zero-exponent convention; ramification changes the valuation of ell but not
openness of its positive powers.
-/
theorem quotient_continuous (n : ℕ) : Continuous (quotient l E n) := by
  obtain ⟨k, hk⟩ := exists_span_pow_eq_coefficientExtensionIdeal l E (n + 1)
  have hle : Padic.coefficientExtensionIdeal l E (k + 1) ≤
      Ideal.span {(l : Padic.coefficientExtensionIntegers l E) ^ (n + 1)} :=
    hk ▸ Ideal.pow_le_pow_right (Nat.le_succ k)
  have hq : IsLocallyConstant
      (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (k + 1))) := by
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro x
    exact (Padic.coefficientExtension_integers_coset_basis l E x).mem_of_mem (i := k) trivial
  have : quotient l E n = (Ideal.Quotient.factor hle).comp
      (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (k + 1))) :=
    (Ideal.Quotient.factor_comp_mk hle).symm
  rw [this]
  exact (hq.comp (Ideal.Quotient.factor hle)).continuous

/-- Finite coefficient sheaves on the pro-etale site, obtained from the point.
Source: the blueprint's quotient coefficient system
(blueprint: def-sfb-coherent-integral-reduction). -/
abbrev coefficients (X : Scheme.{u}) (n : ℕ) :=
  sectionRing X (Etale.FiniteProperQuotient.Ring l E n)

/-- Adjacent quotient maps on the actual pulled-back section rings.
Source: the blueprint's quotient coefficient system
(blueprint: def-sfb-coherent-integral-reduction). -/
def transitions (X : Scheme.{u}) (n : ℕ) :
    coefficients l E X (n + 1) ⟶ coefficients l E X n :=
  sectionMap X (Etale.FiniteProperQuotient.quotient l E (Nat.le_succ n))
    (continuous_of_discreteTopology)

/-- The actual coefficient morphism from continuous integral to finite coefficients.
Source: the blueprint's derived reduction
(blueprint: def-sfb-coherent-integral-reduction). -/
def coefficientMap (X : Scheme.{u}) (n : ℕ) :
    sectionRing X (Padic.coefficientExtensionIntegers l E) ⟶ coefficients l E X n :=
  sectionMap X (quotient l E n) (quotient_continuous l E n)

/-- Postcomposition with continuous ring homomorphisms is functorial. -/
theorem continuousPointMap_comp {T S W : Type (u + 1)} [CommRing T] [CommRing S] [CommRing W]
    [TopologicalSpace T] [TopologicalSpace S] [TopologicalSpace W] [IsTopologicalRing T]
    [IsTopologicalRing S] [IsTopologicalRing W] (f : T →+* S) (hf : Continuous f)
    (g : S →+* W) (hg : Continuous g) :
    continuousPointMap f hf ≫ continuousPointMap g hg =
      continuousPointMap (g.comp f) (hg.comp hf) := by
  unfold continuousPointMap
  rw [← Functor.map_comp]
  rfl

/-- Reconstructing section rings is functorial. -/
theorem internalSectionMap_comp (X : Scheme.{u})
    {R S W : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj S] [MonObj W] [IsCommMonObj R] [IsCommMonObj S] [IsCommMonObj W]
    (f : R ⟶ S) [IsMonHom f] (g : S ⟶ W) [IsMonHom g] :
    internalSectionMap X f ≫ internalSectionMap X g = internalSectionMap X (f ≫ g) :=
  rfl

/-- `sectionMap` is functorial. -/
theorem sectionMap_comp (X : Scheme.{u}) {T S W : Type (u + 1)} [CommRing T] [CommRing S]
    [CommRing W] [TopologicalSpace T] [TopologicalSpace S] [TopologicalSpace W]
    [IsTopologicalRing T] [IsTopologicalRing S] [IsTopologicalRing W]
    (f : T →+* S) (hf : Continuous f) (g : S →+* W) (hg : Continuous g) :
    sectionMap X f hf ≫ sectionMap X g hg = sectionMap X (g.comp f) (hg.comp hf) := by
  unfold sectionMap
  rw [internalSectionMap_comp]
  congr 1
  rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, continuousPointMap_comp]

/-- The integral quotient maps form a morphism of the actual ring systems.
Source: Zheng, Construction 4.1, and the original quotient maps in blueprint step 1
(blueprint: def-sfb-coherent-integral-reduction).

Proof: both ring homomorphisms O to A_n send x to its class modulo ell^(n+1).
Postcomposition on continuous functions preserves composition. So do sheafification,
forgetting to abelian groups, pullback from the point, and section-ring reconstruction.
Their images are the displayed equality of sheaf morphisms. This also proves the
equal-index and composite quotient identities; no coefficient quotient is treated as flat.
-/
theorem coefficientMap_compatible (X : Scheme.{u}) (n : ℕ) :
    coefficientMap l E X (n + 1) ≫ transitions l E X n =
      (𝟙 (sectionRing X (Padic.coefficientExtensionIntegers l E))) ≫
        coefficientMap l E X n := by
  rw [Category.id_comp]
  unfold coefficientMap transitions
  rw [sectionMap_comp]
  congr 1

/-- The normalized simultaneous derived extension of the constant integral system.
Source: Zheng, Construction 4.1; the existing normalized semilinear calculus
(blueprint: def-sfb-coherent-integral-reduction). -/
def reductionScalar (X : Scheme.{u}) :
    ScalarSystems.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
      (constantCoefficients.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
        (sectionRing X (Padic.coefficientExtensionIntegers l E)))
      (constantCoefficientTransitions.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
        (sectionRing X (Padic.coefficientExtensionIntegers l E)))
      (coefficients l E X) (transitions l E X) (coefficientMap l E X)
      (coefficientMap_compatible l E X) :=
  SemilinearDerivedSectionsData.coefficientExtension.{u + 1, u, u + 1}
    (Classical.choice (semilinearDerivedSections.{u + 1, u, u + 1}
    (Scheme.ProEt.topology X)
    (constantCoefficients.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
      (sectionRing X (Padic.coefficientExtensionIntegers l E)))
    (constantCoefficientTransitions.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
      (sectionRing X (Padic.coefficientExtensionIntegers l E)))))
    (coefficients l E X) (transitions l E X) (coefficientMap l E X)
    (coefficientMap_compatible l E X)

/-- The exact section-action equivalence, on the actual continuous integral coefficients.
Source: the recorded internal/sectionwise module equivalence, Stacks 00YV
(blueprint: def-sfb-coherent-integral-reduction). -/
def integralSections (X : Scheme.{u}) :=
  (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u} (Scheme.ProEt.topology X)
    (internalRing X (Padic.coefficientExtensionIntegers l E))).functor

/-- Section-action transport leaves addition of morphisms unchanged.
Source: Stacks 00YV (blueprint: def-sfb-coherent-integral-reduction). -/
instance integralSections_additive (X : Scheme.{u}) : (integralSections l E X).Additive where
  map_add := by intros; rfl

/-- An equivalence preserves kernels.
Source: Stacks 00YV (blueprint: def-sfb-coherent-integral-reduction). -/
instance integralSections_limits (X : Scheme.{u}) :
    PreservesFiniteLimits (integralSections l E X) :=
  inferInstanceAs (PreservesFiniteLimits
    (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u} (Scheme.ProEt.topology X)
      (internalRing X (Padic.coefficientExtensionIntegers l E))).functor)

/-- An equivalence preserves cokernels.
Source: Stacks 00YV (blueprint: def-sfb-coherent-integral-reduction). -/
instance integralSections_colimits (X : Scheme.{u}) :
    PreservesFiniteColimits (integralSections l E X) :=
  inferInstanceAs (PreservesFiniteColimits
    (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u} (Scheme.ProEt.topology X)
      (internalRing X (Padic.coefficientExtensionIntegers l E))).functor)

/-- Bounded constructible integral complexes, with precisely the existing cohomology predicate.
Source: the blueprint's Dbc notation
(blueprint: def-sfb-coherent-integral-reduction). -/
abbrev Bc (X : Scheme.{u}) :=
  BoundedConstructible (internalRing X (Padic.coefficientExtensionIntegers l E))

/-- Actual integral reductions as one object of the ordinary derived category of systems.
This is section-action transport, the exact diagonal, and one simultaneous derived
scalar extension. Its K-flat normalization is part of reductionScalar's model.
Source: Zheng, Construction 4.1; blueprint coherent-tower proof, step 1
(blueprint: def-sfb-coherent-integral-reduction). -/
def reduction (X : Scheme.{u}) :
    DerivedCategory (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (internalRing X (Padic.coefficientExtensionIntegers l E))) ⥤
      DS.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
        (coefficients l E X) (transitions l E X) :=
  (integralSections l E X).mapDerivedCategory ⋙
    derivedConstantSystem.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
      (sectionRing X (Padic.coefficientExtensionIntegers l E)) ⋙
    ScalarData.T.{u + 1, u, u + 1} _ (reductionScalar l E X).scalar

/-- Restrict the canonical reduction functor to the full bounded constructible category.
Source: blueprint coherent-tower statement
(blueprint: def-sfb-coherent-integral-reduction). -/
def reductionBc (X : Scheme.{u}) : Bc l E X ⥤
    DS.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
      (coefficients l E X) (transitions l E X) :=
  (boundedConstructible (internalRing X (Padic.coefficientExtensionIntegers l E))).ι ⋙
    reduction l E X

end AlgebraicGeometry.ProEtale.CoherentReduction
