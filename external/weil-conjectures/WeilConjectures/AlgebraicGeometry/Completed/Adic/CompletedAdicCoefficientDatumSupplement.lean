/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.Complete.CompleteCoefficientDatumSupplement
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import WeilConjectures.Algebra.Homology.ProperBaseChange.KFlatResolutionGeneral
import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import WeilConjectures.AlgebraicGeometry.CompletedAdicCoefficientDatum

/-! # Completed adic coefficient datum

Source: blueprint, sec-proper-base-change/sk-thm-properbasechange, order 1239,
node def-weil-pbc-adic-coefficient-datum; Stacks Tags 099L and 099M
(blueprint: def-weil-pbc-adic-coefficient-datum).

The finite coefficient sheaves are exactly the recorded sheafifications of continuous
functions on connected components. The ambient ring is their inverse limit. In particular,
no identification with the discrete constant coefficient category is used.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe t uC vC r

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped ChangeOfRings

namespace AlgebraicGeometry.Scheme

variable {A : Type t} [CommRing A]

/-- The coordinate projections of the completed coefficient sheaf.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def completedAdicProjection (T : Scheme.{t}) (d : AdicCoefficientDatum A) (n : ℕ) :
    completedAdicRing T d ⟶ completedAdicFiniteRing T d n :=
  limit.π (completedAdicRingSystem T d) (op n)

private theorem finiteRing_comm (T : Scheme.{t}) (d : AdicCoefficientDatum A)
    (n : ℕ) (U : T.ProEtᵒᵖ) (x y : (completedAdicFiniteRing T d n).obj.obj U) :
    x * y = y * x := by
  let J := ProEt.topology T
  let F := ProEtale.finiteCoefficientPresheaf T (completedAdicQuotient d n)
  let R := completedAdicFiniteRing T d n
  let η : F ⟶ R.obj := toSheafify J F
  have hs := (isSheaf_iff_isSheaf_of_type J
      (R.obj ⋙ CategoryTheory.forget RingCat.{t + 1})).1
    ((sheafCompose J (CategoryTheory.forget RingCat.{t + 1})).obj R).property
  apply (hs.isSeparated _ (J.intersection_covering
    (Presheaf.imageSieve_mem J η x) (Presheaf.imageSieve_mem J η y))).ext
  rintro V f ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  change R.obj.map f.op (x * y) = R.obj.map f.op (y * x)
  rw [map_mul, map_mul, ← ha, ← hb, ← map_mul, ← map_mul]
  change C(ConnectedComponents V.left, completedAdicQuotient d n) at a b
  exact congrArg (η.app (op V)) (mul_comm a b)

/-- The category of strict inverse towers of A_T-module sheaves; index n means n+1.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
abbrev CompletedAdicTowers (T : Scheme.{t}) (d : AdicCoefficientDatum A) :=
  ℕᵒᵖ ⥤ CompletedAdicModules T d

/-- Standard localization of the abelian category of strict towers.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
instance completedAdicTowers_hasDerived (T : Scheme.{t}) (d : AdicCoefficientDatum A) :
    HasDerivedCategory (CompletedAdicTowers T d) := HasDerivedCategory.standard _

/-- The coefficient module (P_(n+1))_T restricted along the actual limit projection.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def completedAdicFiniteModule (T : Scheme.{t}) (d : AdicCoefficientDatum A) (n : ℕ) :
    CompletedAdicModules T d :=
  (SheafOfModules.restrictScalars.{t + 1} (completedAdicProjection T d n)).obj
    (SheafOfModules.unit (completedAdicFiniteRing T d n))

/-- The quotient ring map defines a unique A_T-linear map on the restricted unit modules.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: use q on every section. The limit cone identity pi_n=q*pi_(n+1) makes it linear;
its restrictions commute by naturality of q. Equality of all section functions determines
a sheaf morphism uniquely. -/
theorem completedAdicFiniteModuleStep_exists (T : Scheme.{t}) (d : AdicCoefficientDatum A)
    (n : ℕ) : ∃! q : completedAdicFiniteModule T d (n + 1) ⟶ completedAdicFiniteModule T d n,
      ∀ (U : T.ProEtᵒᵖ) (s : (completedAdicFiniteRing T d (n + 1)).obj.obj U),
        q.val.app U s = (completedAdicFiniteStep T d n).hom.app U s := by
  have hw : completedAdicProjection T d (n + 1) ≫ completedAdicFiniteStep T d n =
      completedAdicProjection T d n := by
    simpa only [completedAdicProjection, completedAdicRingSystem,
      Functor.ofOpSequence_map_homOfLE_succ] using
      limit.w (completedAdicRingSystem T d) (homOfLE (Nat.le_succ n)).op
  let q : completedAdicFiniteModule T d (n + 1) ⟶ completedAdicFiniteModule T d n :=
    { val :=
        { app := fun U ↦ ModuleCat.ofHom
            (X := (completedAdicFiniteModule T d (n + 1)).val.obj U)
            (Y := (completedAdicFiniteModule T d n).val.obj U)
            { toFun := (completedAdicFiniteStep T d n).hom.app U
              map_add' := map_add _
              map_smul' := by
                intro r s
                change (completedAdicRing T d).obj.obj U at r
                change (completedAdicFiniteRing T d (n + 1)).obj.obj U at s
                change (completedAdicFiniteStep T d n).hom.app U
                    ((completedAdicProjection T d (n + 1)).hom.app U r * s) =
                  (completedAdicProjection T d n).hom.app U r *
                    (completedAdicFiniteStep T d n).hom.app U s
                rw [map_mul]
                have h := ConcreteCategory.congr_hom
                  (congrArg (fun f ↦ f.hom.app U) hw) r
                exact congrArg (fun z ↦ z * (completedAdicFiniteStep T d n).hom.app U s) h }
          naturality := by
            intro U V f
            ext s
            exact ConcreteCategory.congr_hom
              ((completedAdicFiniteStep T d n).hom.naturality f) s } }
  refine ⟨q, fun _ _ ↦ rfl, ?_⟩
  intro q' hq'
  ext U s
  exact hq' U s

/-- The canonically normalized transition of restricted quotient modules.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def completedAdicFiniteModuleStep (T : Scheme.{t}) (d : AdicCoefficientDatum A) (n : ℕ) :
    completedAdicFiniteModule T d (n + 1) ⟶ completedAdicFiniteModule T d n :=
  (completedAdicFiniteModuleStep_exists T d n).exists.choose

/-- Ordinary tensor reductions as one strict tower-valued functor. Its transitions are
exactly tensor with the quotient maps, not independent choices at each level.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def completedAdicOrdinaryTower (T : Scheme.{t}) (d : AdicCoefficientDatum A) :
    CompletedAdicModules T d ⥤ CompletedAdicTowers T d :=
  (Functor.ofOpSequence
    (X := fun n ↦ (curriedTensor (CompletedAdicModules T d)).flip.obj
      (completedAdicFiniteModule T d n))
    (fun n ↦ (curriedTensor (CompletedAdicModules T d)).flip.map
      (completedAdicFiniteModuleStep T d n))).flip

/-- The strict tensor tower is additive.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: tensor is additive in the original module variable and addition of tower maps is
componentwise, so the assertion follows by evaluating at every level. -/
theorem completedAdicOrdinaryTower_additive (T : Scheme.{t}) (d : AdicCoefficientDatum A) :
    (completedAdicOrdinaryTower T d).Additive := by
  let : MonoidalPreadditive (CompletedAdicModules T d) :=
    SheafOfModules.cochainModulesPreadditive (completedAdicCommRing T d)
  constructor
  intro M N f g
  apply NatTrans.ext
  funext n
  change (tensorRight (completedAdicFiniteModule T d n.unop)).map (f + g) =
    (tensorRight (completedAdicFiniteModule T d n.unop)).map f +
      (tensorRight (completedAdicFiniteModule T d n.unop)).map g
  exact (tensorRight (completedAdicFiniteModule T d n.unop)).map_add

attribute [instance] completedAdicOrdinaryTower_additive

set_option backward.isDefEq.respectTransparency false in
private theorem tensorKFlat_of_acyclic
    {C : Type uC} [Category.{vC} C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
    [BraidedCategory C] [HasColimitsOfSize.{0, 0} C]
    [∀ M : C, PreservesColimitsOfSize.{0, 0} (tensorLeft M)]
    [∀ M : C, PreservesColimitsOfSize.{0, 0} (tensorRight M)]
    (K : CochainComplex C ℤ)
    (hK : ∀ F : CochainComplex C ℤ, F.Acyclic →
      (CochainComplex.mapBifunctor F K (curriedTensor C)).Acyclic) :
    (HomologicalComplex.quasiIso C (.up ℤ)).kFlat K := by
  rw [← HomotopyCategory.kFlat_quotient_obj_iff,
    HomotopyCategory.kFlat_iff_preserves_acyclic]
  intro Z hZ
  obtain ⟨F, rfl⟩ := Z.quotient_obj_surjective
  have hF := (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic F).1 hZ
  have hr := (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic
    (CochainComplex.mapBifunctor F K (curriedTensor C))).2 (hK F hF)
  exact ⟨(HomotopyCategory.subcategoryAcyclic C).prop_of_iso (β_ _ _) hr, hr⟩

set_option backward.isDefEq.respectTransparency false in
private theorem tensorRight_quasiIso_of_models
    {C : Type uC} [Category.{vC} C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
    [BraidedCategory C] [HasColimitsOfSize.{0, 0} C]
    [∀ M : C, PreservesColimitsOfSize.{0, 0} (tensorLeft M)]
    [∀ M : C, PreservesColimitsOfSize.{0, 0} (tensorRight M)]
    (res : ∀ G : CochainComplex C ℤ, ∃ (K : CochainComplex C ℤ) (f : K ⟶ G),
      (HomologicalComplex.quasiIso C (.up ℤ)).kFlat K ∧ QuasiIso f)
    (Q : C) {P₁ P₂ : CochainComplex C ℤ} (f : P₁ ⟶ P₂) (hf : QuasiIso f)
    (h₁ : (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P₁)
    (h₂ : (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P₂) :
    QuasiIso (((tensorRight Q).mapHomologicalComplex (.up ℤ)).map f) := by
  let W := HomologicalComplex.quasiIso C (.up ℤ)
  let Z := (HomologicalComplex.single C (.up ℤ) 0).obj Q
  obtain ⟨Z', g, hZ', hg⟩ := res Z
  have hg' : W g := hg
  have h : W (f ▷ Z) := by
    rw [← W.precomp_iff _ _ (h₁.whiskerLeft hg'), whisker_exchange f g]
    exact W.comp_mem _ _ (hZ'.whiskerRight hf) (h₂.whiskerLeft hg')
  exact (W.arrow_mk_iso_iff
    (Arrow.isoOfNatIso (CochainComplex.map₂HomologicalComplexFlipObjSingleIso (curriedTensor C) Q)
      (Arrow.mk f))).1 h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Existence of the universal left derived reduction-tower pair, computed on K-flat models.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: tensor distributes over the finite cone summands and respects shifts, so the
ordinary tower gives an exact functor on homotopy categories. Resolve every complex by
lem-pc-kflat-resolution. A quasi-isomorphism between K-flat complexes stays a
quasi-isomorphism after tensor with each quotient (lem-pur-derived-change-of-rings).
Tower cohomology is levelwise, so the entire tower map is a quasi-isomorphism. Apply
lem-pur-left-derived-from-kflat-class. Its counit is invertible on K-flat representatives,
which fixes the comparison with the stated strict quotient tower. -/
theorem completedAdicReduction_exists (T : Scheme.{t}) (d : AdicCoefficientDatum A) :
    ∃ (F : DerivedCategory (CompletedAdicModules T d) ⥤
        DerivedCategory (CompletedAdicTowers T d))
      (ε : DerivedCategory.Qh ⋙ F ⟶
        (completedAdicOrdinaryTower T d).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh),
      F.IsLeftDerivedFunctor ε
        (HomotopyCategory.quasiIso (CompletedAdicModules T d) (ComplexShape.up ℤ)) ∧
      ∀ P : CochainComplex (CompletedAdicModules T d) ℤ,
        CochainComplex.IsAcyclicTensorKFlat (R := completedAdicCommRing T d) P →
        IsIso (ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) := by
  let : MonoidalPreadditive (CompletedAdicModules T d) :=
    SheafOfModules.cochainModulesPreadditive (completedAdicCommRing T d)
  let : SymmetricCategory (CompletedAdicModules T d) :=
    SheafOfModules.cochainModulesSymmetric (completedAdicCommRing T d)
  let : ∀ M : CompletedAdicModules T d,
      PreservesColimitsOfSize.{0, 0} (tensorLeft M) :=
    fun M ↦ SheafOfModules.cochainTensorLeftPreservesColimits (completedAdicCommRing T d) M
  let : ∀ M : CompletedAdicModules T d,
      PreservesColimitsOfSize.{0, 0} (tensorRight M) :=
    fun M ↦ SheafOfModules.cochainTensorRightPreservesColimits (completedAdicCommRing T d) M
  have hk (P : CochainComplex (CompletedAdicModules T d) ℤ)
      (hP : CochainComplex.IsAcyclicTensorKFlat (R := completedAdicCommRing T d) P) :
      (HomologicalComplex.quasiIso (CompletedAdicModules T d) (.up ℤ)).kFlat P :=
    tensorKFlat_of_acyclic P hP
  have hmodels (G : CochainComplex (CompletedAdicModules T d) ℤ) :
      ∃ (P : CochainComplex (CompletedAdicModules T d) ℤ) (s : P ⟶ G),
        CochainComplex.IsAcyclicTensorKFlat (R := completedAdicCommRing T d) P ∧
          QuasiIso s := by
    obtain ⟨P, s, hP, _, hs, _⟩ :=
      CochainComplex.exists_isKFlatResolutionGeneral
        (R := completedAdicCommRing T d) G
    exact ⟨P, s, hP, hs⟩
  have hinv {P Q : CochainComplex (CompletedAdicModules T d) ℤ} (a : P ⟶ Q)
      (hP : CochainComplex.IsAcyclicTensorKFlat (R := completedAdicCommRing T d) P)
      (hQ : CochainComplex.IsAcyclicTensorKFlat (R := completedAdicCommRing T d) Q)
      (ha : QuasiIso a) :
      QuasiIso (((completedAdicOrdinaryTower T d).mapHomologicalComplex (.up ℤ)).map a) := by
    apply (HomologicalComplex.quasiIso_iff_evaluation _).2
    intro n
    change QuasiIso
      (((tensorRight (completedAdicFiniteModule T d n.unop)).mapHomologicalComplex
        (.up ℤ)).map a)
    apply tensorRight_quasiIso_of_models _ _ a ha (hk P hP) (hk Q hQ)
    intro G
    obtain ⟨K, s, hK, hs⟩ := hmodels G
    exact ⟨K, s, hk K hK, hs⟩
  let F := (completedAdicOrdinaryTower T d).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh
  let S : Set (HomotopyCategory (CompletedAdicModules T d) (.up ℤ)) :=
    { X | ∃ P : CochainComplex (CompletedAdicModules T d) ℤ,
      CochainComplex.IsAcyclicTensorKFlat (R := completedAdicCommRing T d) P ∧
        (HomotopyCategory.quotient _ (.up ℤ)).obj P = X }
  have hres : ∀ X : HomotopyCategory (CompletedAdicModules T d) (.up ℤ),
      ∃ (X' : HomotopyCategory (CompletedAdicModules T d) (.up ℤ)) (s : X' ⟶ X),
        X' ∈ S ∧ HomotopyCategory.quasiIso _ _ s := by
    intro X
    obtain ⟨G, rfl⟩ := X.quotient_obj_surjective
    obtain ⟨P, s, hP, hs⟩ := hmodels G
    exact ⟨_, (HomotopyCategory.quotient _ _).map s, ⟨P, hP, rfl⟩,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff s).2 hs⟩
  have hinvS : ∀ (X Y : HomotopyCategory (CompletedAdicModules T d) (.up ℤ))
      (s : X ⟶ Y), X ∈ S → Y ∈ S → HomotopyCategory.quasiIso _ _ s →
        IsIso (F.map s) := by
    intro X Y s hX hY hs
    obtain ⟨P, hP, rfl⟩ := hX
    obtain ⟨Q, hQ, rfl⟩ := hY
    obtain ⟨a, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective s
    have ha := (HomotopyCategory.quotient_map_mem_quasiIso_iff a).1 hs
    have hEa := hinv a hP hQ ha
    dsimp only [F, Functor.comp_map, Functor.mapHomotopyCategory_map]
    apply Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso _ _)
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 hEa
  obtain ⟨_, LF, ε, hLF, _, hε⟩ :=
    Functor.leftDerived_from_resolvingClass _ _ F S hres hinvS
  exact ⟨LF, ε, hLF, fun P hP ↦ hε _ ⟨P, hP, rfl⟩⟩

section DerivedReductionModels

variable {B C : Type*} [Category B] [Abelian B] [Category C] [Abelian C]
  [HasDerivedCategory B] [HasDerivedCategory C]
  (F : B ⥤ C) [F.Additive] (P : CochainComplex B ℤ → Prop)

variable {F P}

/-- Computation of the complex comparison on the resolving class.
Source: Stacks Tag 06YY (blueprint: def-weil-pbc-derived-reduction-model-data).
Proof: the homotopy counit is invertible by the computation law, and every other
factor is an image of a localization isomorphism. -/
theorem DerivedReductionModelData.complexCounit_isIso (D : DerivedReductionModelData F P)
    (K : CochainComplex B ℤ) (hK : P K) : IsIso (D.complexCounit K) := by
  have := D.isIso_counit K hK
  unfold DerivedReductionModelData.complexCounit
  infer_instance

/-- The right-derived comparison on a complex, with the localization factors retained.
Source: Stacks Tag 0941 (blueprint: def-weil-pbc-derived-reduction-model-data). -/
def derivedLimitComplexComparison (L : C ⥤ B) [L.Additive]
    (RF : DerivedCategory C ⥤ DerivedCategory B)
    (δ : L.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF)
    (P : CochainComplex C ℤ) :
    DerivedCategory.Q.obj ((L.mapHomologicalComplex (.up ℤ)).obj P) ⟶
      RF.obj (DerivedCategory.Q.obj P) :=
  (DerivedCategory.quotientCompQhIso _).inv.app
      (((L).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
    DerivedCategory.Qh.map
      (((L).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app P) ≫
    δ.app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P) ≫
    (RF).map ((DerivedCategory.quotientCompQhIso _).hom.app P)

/-- The normalized completion unit on a resolving complex.
Source: Stacks Tags 06YY and 0941 (blueprint: def-weil-pbc-derived-reduction-model-data). -/
def derivedCompletionModelUnit (D : DerivedReductionModelData F P)
    (L : C ⥤ B) [L.Additive] (RF : DerivedCategory C ⥤ DerivedCategory B)
    (δ : L.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF)
    (u : 𝟭 B ⟶ F ⋙ L) (K : CochainComplex B ℤ) (hK : P K) :
    DerivedCategory.Q.obj K ⟶ RF.obj (D.reduction.obj (DerivedCategory.Q.obj K)) :=
  DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex u (.up ℤ)).app K) ≫
    derivedLimitComplexComparison L RF δ ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
      RF.map (@inv _ _ _ _ (D.complexCounit K) (D.complexCounit_isIso K hK))

end DerivedReductionModels

/-- The universal strict reduction pair over the completed coefficients.
Source: Stacks Tag 06YY (blueprint: def-weil-pbc-derived-reduction-model-data). -/
abbrev CompletedAdicReductionData (T : Scheme.{t}) (d : AdicCoefficientDatum A) :=
  DerivedReductionModelData (completedAdicOrdinaryTower T d)
    (CochainComplex.IsAcyclicTensorKFlat (R := completedAdicCommRing T d))

/-- Bundle the already chosen universal pair. Its universal property determines it
up to its unique compatible isomorphism.
Source: Stacks Tag 06YY (blueprint: def-weil-pbc-derived-reduction-model-data). -/
def completedAdicReductionData (T : Scheme.{t}) (d : AdicCoefficientDatum A) :
    CompletedAdicReductionData T d :=
  derivedReductionModelDataOfExists (completedAdicOrdinaryTower T d)
    (CochainComplex.IsAcyclicTensorKFlat (R := completedAdicCommRing T d))
    (completedAdicReduction_exists T d)

/-- The reduction tower functor, chosen from its universal derived pair. The universal
property and invertible K-flat counit determine it up to its unique comparison.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def completedAdicReduction (T : Scheme.{t}) (d : AdicCoefficientDatum A) :
    DerivedCategory (CompletedAdicModules T d) ⥤ DerivedCategory (CompletedAdicTowers T d) :=
  (completedAdicReductionData T d).reduction

/-- The finite coefficient sheaf has commutative sections.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: continuous functions into the commutative quotient ring commute pointwise.
The same equation holds locally after sheafification, and the sheaf's separatedness
makes it hold globally on each object. -/
theorem completedAdicFiniteRing_mul_comm (T : Scheme.{t}) (d : AdicCoefficientDatum A)
    (n : ℕ) (U : T.ProEtᵒᵖ) (x y : (completedAdicFiniteRing T d n).obj.obj U) :
    x * y = y * x := by
  exact finiteRing_comm T d n U x y

/-- Commutativity on the finite coefficient sheaf, with unchanged underlying ring data.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
abbrev completedAdicFiniteCommRingStructure (T : Scheme.{t}) (d : AdicCoefficientDatum A)
    (n : ℕ) (U : T.ProEtᵒᵖ) : CommRing ((completedAdicFiniteRing T d n).obj.obj U) :=
  { RingCat.ring _ with mul_comm := completedAdicFiniteRing_mul_comm T d n U }

/-- The existing finite coefficient presheaf with commutativity retained.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def completedAdicFiniteCommPresheaf (T : Scheme.{t}) (d : AdicCoefficientDatum A) (n : ℕ) :
    T.ProEtᵒᵖ ⥤ CommRingCat.{t + 1} where
  obj U := @CommRingCat.of ((completedAdicFiniteRing T d n).obj.obj U)
    (completedAdicFiniteCommRingStructure T d n U)
  map {U V} f :=
    letI := completedAdicFiniteCommRingStructure T d n U
    letI := completedAdicFiniteCommRingStructure T d n V
    CommRingCat.ofHom ((completedAdicFiniteRing T d n).obj.map f).hom
  map_id U := (forget₂ CommRingCat RingCat).map_injective
    ((completedAdicFiniteRing T d n).obj.map_id U)
  map_comp f g := (forget₂ CommRingCat RingCat).map_injective
    ((completedAdicFiniteRing T d n).obj.map_comp f g)

/-- The finite coefficient sheaf, now as commutative rings, with the same ring sheaf.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def completedAdicFiniteCommRing (T : Scheme.{t}) (d : AdicCoefficientDatum A) (n : ℕ) :
    Sheaf (ProEt.topology T) CommRingCat.{t + 1} :=
  ⟨completedAdicFiniteCommPresheaf T d n,
    Presheaf.isSheaf_of_isSheaf_comp _ _ (forget₂ CommRingCat RingCat)
      (completedAdicFiniteRing T d n).property⟩

/-- The limit projection with commutativity retained, without changing its section maps.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def completedAdicCommProjection (T : Scheme.{t}) (d : AdicCoefficientDatum A) (n : ℕ) :
    completedAdicCommRing T d ⟶ completedAdicFiniteCommRing T d n where
  hom :=
    { app := fun U ↦
        letI := completedAdicCommRingStructure T d U
        letI := completedAdicFiniteCommRingStructure T d n U
        CommRingCat.ofHom ((completedAdicProjection T d n).hom.app U).hom
      naturality := fun _ _ f ↦ (forget₂ CommRingCat RingCat).map_injective
        ((completedAdicProjection T d n).hom.naturality f) }

set_option linter.defProp false in
/-- K tensor^L_(A_T) (P_(n+1))_T with its quotient coefficient action retained.
The main reduction functor is its scalar restriction; no constant coefficient category
is identified with the completed category.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def completedAdicQuotientReduction (T : Scheme.{t}) (d : AdicCoefficientDatum A) (n : ℕ) :=
  completedAdicDerivedChange T (completedAdicCommProjection T d n)

namespace CompletedTensorComparisonProof

open SheafOfModules

set_option hygiene false in
local notation "𝓡" R =>
  (sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R

attribute [local instance] isMonoidal_W_independentCoefficients
attribute [local irreducible] monoidalCategory

-- Step 1: the same tensor abelian group, with the two scalar actions identified.
set_option backward.isDefEq.respectTransparency false in
private noncomputable def sectionTensorIso
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{r} C] {J : GrothendieckTopology C}
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
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{r} C] {J : GrothendieckTopology C}
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
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{r} C] {J : GrothendieckTopology C}
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
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{r} C] {J : GrothendieckTopology C}
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

set_option backward.isDefEq.respectTransparency false in
private lemma tensorComparison_naturality
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{r} C] {J : GrothendieckTopology C}
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
  let ε := asIso (PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 O).obj)).counit
  let c (M : SheafOfModules.{r} (𝓡 O)) := ε.app M
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
        have ht := CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom
          (c S).inv (c M).inv (𝟙 (A.obj S.val)) (A.map a.val)
        erw [CategoryTheory.MonoidalCategory.id_tensorHom, Category.comp_id] at ht
        exact ht
      _ = (c S).inv ⊗ₘ (a ≫ (c N).inv) :=
        congrArg (fun f ↦ (c S).inv ⊗ₘ f) hn
      _ = _ := by
        simpa only [Category.id_comp,
          CategoryTheory.MonoidalCategory.id_tensorHom] using
          (CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom
            (𝟙 S) a (c S).inv (c N).inv).symm
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun f ↦ f ≫ Functor.LaxMonoidal.μ A S.val N.val) h) |>.trans
      (Category.assoc _ _ _)

section RestrictionSheafification
variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasWeakSheafify J AddCommGrpCat.{r}]
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  {R₀ B₀ : Sheaf J RingCat.{r}}

private noncomputable def restrictionSheafificationComparison
    (α : R₀ ⟶ B₀) (P : PresheafOfModules.{r} B₀.obj) :
    (PresheafOfModules.sheafification (𝟙 R₀.obj)).obj
      ((PresheafOfModules.restrictScalars α.hom).obj P) ⟶
        (restrictScalars α).obj
          ((PresheafOfModules.sheafification (𝟙 B₀.obj)).obj P) :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 R₀.obj)).symm
    ((PresheafOfModules.restrictScalars α.hom).map
      ((PresheafOfModules.sheafificationAdjunction (𝟙 B₀.obj)).unit.app P))

omit [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})] in
private theorem restrictionSheafificationComparison_isIso
    (α : R₀ ⟶ B₀) (P : PresheafOfModules.{r} B₀.obj) :
    IsIso (restrictionSheafificationComparison α P) := by
  rw [← isIso_iff_of_reflects_iso _ (toSheaf R₀)]
  have he : (toSheaf R₀).map (restrictionSheafificationComparison α P) = 𝟙 _ := by
    unfold restrictionSheafificationComparison
    rw [PresheafOfModules.toSheaf_map_sheafificationHomEquiv_symm]
    apply ((CategoryTheory.sheafificationAdjunction
      J AddCommGrpCat.{r}).homEquiv _ _).injective
    rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
    change (PresheafOfModules.toPresheaf B₀.obj).map
      ((PresheafOfModules.sheafificationAdjunction (𝟙 B₀.obj)).unit.app P) =
        CategoryTheory.toSheafify J P.presheaf
    exact PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app _ _
  rw [he]
  infer_instance

omit [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})] in
set_option backward.isDefEq.respectTransparency false in
private theorem restrictionSheafificationComparison_naturality
    (α : R₀ ⟶ B₀) {P Q : PresheafOfModules.{r} B₀.obj} (f : P ⟶ Q) :
    (PresheafOfModules.sheafification (𝟙 R₀.obj)).map
        ((PresheafOfModules.restrictScalars α.hom).map f) ≫
        restrictionSheafificationComparison α Q =
      restrictionSheafificationComparison α P ≫
        (restrictScalars α).map ((PresheafOfModules.sheafification (𝟙 B₀.obj)).map f) := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 R₀.obj)
  apply (adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  simp only [adj, PresheafOfModules.sheafificationAdjunction_homEquiv_apply,
    restrictionSheafificationComparison, Equiv.apply_symm_apply]
  have h := congrArg (PresheafOfModules.restrictScalars α.hom).map
    ((PresheafOfModules.sheafificationAdjunction (𝟙 B₀.obj)).unit.naturality f)
  simp only [Functor.map_comp] at h
  ext V x
  exact congrArg (fun k ↦ k.app V x) h

end RestrictionSheafification

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem restrictedChangeTensorIso
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{r} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasWeakSheafify J AddCommGrpCat.{r}]
    {R S : Sheaf J CommRingCat.{r}} (φ : R ⟶ S)
    (E : SheafOfModules.{r} (𝓡 R) ⥤ SheafOfModules.{r} (𝓡 S))
    (h : ∀ M, E.obj M = changeOfRings φ M)
    (hm : ∀ {M N} (a : M ⟶ N), E.map a =
      eqToHom (h M) ≫ changeOfRingsHom φ M a ≫ eqToHom (h N).symm) :
    letI := monoidalCategory R
    Nonempty (E ⋙ restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ) ≅
      tensorRight ((restrictScalars
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj (unit (𝓡 S)))) := by
  let := monoidalCategory R
  let := symmetricCategory R
  let α := (sheafCompose J (forget₂ CommRingCat RingCat)).map φ
  let U := restrictScalars α
  let B := U.obj (unit (𝓡 S))
  let A := PresheafOfModules.sheafification (𝟙 (𝓡 R).obj)
  let c (M : SheafOfModules.{r} (𝓡 R)) := by
    have := restrictionSheafificationComparison_isIso α (changeOfRingsPresheaf φ M)
    exact asIso (restrictionSheafificationComparison α (changeOfRingsPresheaf φ M))
  let e (M : SheafOfModules.{r} (𝓡 R)) : U.obj (changeOfRings φ M) ≅ B ⊗ M :=
    (c M).symm ≪≫ A.mapIso (presheafTensorIso φ M) ≪≫
      (tensorObjIsoSheafification B M).symm
  have he {M N : SheafOfModules.{r} (𝓡 R)} (a : M ⟶ N) :
      U.map (changeOfRingsHom φ M a) ≫ (e N).hom = (e M).hom ≫ B ◁ a := by
    have hr := restrictionSheafificationComparison_naturality α (changePresheafHom φ a)
    change A.map ((PresheafOfModules.restrictScalars α.hom).map
      (changePresheafHom φ a)) ≫ (c N).hom =
      (c M).hom ≫ U.map (changeOfRingsHom φ M a) at hr
    have hc : U.map (changeOfRingsHom φ M a) ≫ (c N).inv =
        (c M).inv ≫ A.map ((PresheafOfModules.restrictScalars α.hom).map
          (changePresheafHom φ a)) := by
      apply (cancel_epi (c M).hom).mp
      simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
      rw [← hr]
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    have hp := congrArg A.map (presheafTensorIso_naturality φ a)
    simp only [Functor.map_comp] at hp
    have ht := tensorComparison_naturality B a
    dsimp only [e, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
    rw [← Category.assoc, ← Category.assoc, hc]
    simp only [Category.assoc]
    rw [reassoc_of% hp, ht]
  let e' : E ⋙ U ≅ tensorLeft B := NatIso.ofComponents
    (fun M ↦ U.mapIso (eqToIso (h M)) ≪≫ e M) (by
      intro M N a
      change U.map (E.map a) ≫ _ = _
      rw [hm]
      simp only [Functor.map_comp, Iso.trans_hom, Functor.mapIso_hom, eqToIso.hom,
        Category.assoc]
      simp only [← Functor.map_comp_assoc, eqToHom_trans, eqToHom_refl]
      simp only [Category.comp_id, Functor.map_comp, Category.assoc]
      rw [he]
      rfl)
  exact ⟨e' ≪≫ BraidedCategory.tensorLeftIsoTensorRight B⟩

end CompletedTensorComparisonProof

section FiniteReductionComparison

attribute [local irreducible] SheafOfModules.monoidalCategory

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem completedOrdinaryRestrictionComparison (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S) :
    letI := SheafOfModules.cochainModulesMonoidal R
    Nonempty (completedAdicChange T φ ⋙ SheafOfModules.restrictScalars.{t + 1}
      ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map φ) ≅
      tensorRight ((SheafOfModules.restrictScalars.{t + 1}
        ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map φ)).obj
          (SheafOfModules.unit
            ((sheafCompose (ProEt.topology T)
              (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj S)))) := by
  exact CompletedTensorComparisonProof.restrictedChangeTensorIso φ (completedAdicChange T φ)
    (completedAdicChangeData T φ).choose_spec.choose
    (fun f ↦ (completedAdicChangeData T φ).choose_spec.choose_spec.choose f)

private abbrev completedChangeModels (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S) :=
  let h := (completedAdicChangeData T φ).choose_spec.choose_spec.choose_spec.choose_spec.2.2
  h.choose_spec

end FiniteReductionComparison

private abbrev completedRestriction (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S) :=
  SheafOfModules.restrictScalars.{t + 1}
    ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map φ)

set_option backward.isDefEq.respectTransparency false in
private theorem completedAdjunction (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S) :
    ∃ a : completedAdicChange T φ ⊣ completedRestriction T φ,
      ∀ (M : SheafOfModules.{t + 1}
        ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R))
        (N : SheafOfModules.{t + 1}
        ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj S))
        (f : (completedAdicChange T φ).obj M ⟶ N) (U : T.ProEtᵒᵖ) (x : M.val.obj U),
        (a.homEquiv M N f).val.app U x =
          f.val.app U (completedAdicChangeTensor T φ M U 1 x) := by
  let h := (completedAdicChangeData T φ).choose_spec.choose
  obtain ⟨_, _, ha⟩ := SheafOfModules.sheafRingCoefficientOrdinaryAdjunction φ
  obtain ⟨a, hnorm⟩ := ha (completedAdicChange T φ) h
    (fun f ↦ (completedAdicChangeData T φ).choose_spec.choose_spec.choose f)
  refine ⟨a, ?_⟩
  intro M N f U x
  have he := hnorm M N (eqToHom (h M).symm ≫ f) U x
  have hh : eqToHom (h M) ≫ (eqToHom (h M).symm ≫ f) = f := by simp
  rw [hh] at he
  exact he

set_option backward.isDefEq.respectTransparency false in
private theorem normalizedTensor_smul (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S)
    (M : SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R))
    (N : SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj S))
    (h : N = SheafOfModules.changeOfRings φ M)
    (U : T.ProEtᵒᵖ) (s z : S.obj.obj U) (x : M.val.obj U) :
    (eqToHom h.symm).val.app U
      ((toSheafify (ProEt.topology T)
        (SheafOfModules.changeOfRingsPresheaf φ M).presheaf).app U
          ((s * z) ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x)) =
      s • (eqToHom h.symm).val.app U
        ((toSheafify (ProEt.topology T)
          (SheafOfModules.changeOfRingsPresheaf φ M).presheaf).app U
            (z ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x)) := by
  let η := ((PresheafOfModules.sheafificationAdjunction.{t + 1}
    (R := (sheafCompose (ProEt.topology T)
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj S)
    (𝟙 _)).unit.app (SheafOfModules.changeOfRingsPresheaf.{t, t + 1, t + 1} φ M)).app U
  let e := eqToHom h.symm
  change e.val.app U (η ((s * z) ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x)) =
    s • e.val.app U (η (z ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x))
  clear_value e η
  have ht := ModuleCat.ExtendScalars.smul_tmul (φ.hom.app U).hom s z x
  have hη := η.hom.map_smul s (z ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x)
  have he := (e.val.app U).hom.map_smul s
    (η (z ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x))
  exact (congrArg (fun w ↦ e.val.app U (η w)) ht.symm).trans
    ((congrArg (fun w ↦ e.val.app U w) hη).trans he)

set_option backward.isDefEq.respectTransparency false in
private theorem completedTensor_smul (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S)
    (M : SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R))
    (U : T.ProEtᵒᵖ) (s z : S.obj.obj U) (x : M.val.obj U) :
    completedAdicChangeTensor T φ M U (s * z) x =
      s • completedAdicChangeTensor T φ M U z x := by
  exact normalizedTensor_smul T φ M _
    ((completedAdicChangeData T φ).choose_spec.choose M) U s z x

private def completedRestrictCompIso (T : Scheme.{t})
    {R S V : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ V) :
    completedRestriction T (φ ≫ ψ) ≅ completedRestriction T ψ ⋙ completedRestriction T φ :=
  NatIso.ofComponents (fun N ↦
    { hom.val.app U := (ModuleCat.restrictScalarsComp'App _ _ _ rfl (N.val.obj U)).hom
      hom.val.naturality i := by ext m; rfl
      inv.val.app U := (ModuleCat.restrictScalarsComp'App _ _ _ rfl (N.val.obj U)).inv
      inv.val.naturality i := by ext m; rfl }) (by intro M N f; ext U x; rfl)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem balancing_from_adjunctions (T : Scheme.{t})
    {R S V : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ V)
    (E1 : SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R) ⥤ SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj S))
    [E1.Additive]
    (τ1 : ∀ (M : SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R)) (U : T.ProEtᵒᵖ),
      S.obj.obj U → M.val.obj U → (E1.obj M).val.obj U)
    (a1 : E1 ⊣ completedRestriction T φ)
    (h1 : ∀ (M : SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R)) (N : SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj S))
      (f : E1.obj M ⟶ N) (U : T.ProEtᵒᵖ) (x : M.val.obj U),
      (a1.homEquiv M N f).val.app U x = f.val.app U (τ1 M U 1 x))
    (hs1 : ∀ (M : SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R)) (U : T.ProEtᵒᵖ) (s z : S.obj.obj U)
      (x : M.val.obj U), τ1 M U (s * z) x = s • τ1 M U z x)
    (E2 : SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj S) ⥤ SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj V))
    [E2.Additive]
    (τ2 : ∀ (M : SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj S)) (U : T.ProEtᵒᵖ),
      V.obj.obj U → M.val.obj U → (E2.obj M).val.obj U)
    (a2 : E2 ⊣ completedRestriction T ψ)
    (h2 : ∀ (M : SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj S)) (N : SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj V))
      (f : E2.obj M ⟶ N) (U : T.ProEtᵒᵖ) (x : M.val.obj U),
      (a2.homEquiv M N f).val.app U x = f.val.app U (τ2 M U 1 x))
    (hs2 : ∀ (M : SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj S)) (U : T.ProEtᵒᵖ) (s z : V.obj.obj U)
      (x : M.val.obj U), τ2 M U (s * z) x = s • τ2 M U z x)
    (E3 : SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R) ⥤ SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj V))
    [E3.Additive]
    (τ3 : ∀ (M : SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R)) (U : T.ProEtᵒᵖ),
      V.obj.obj U → M.val.obj U → (E3.obj M).val.obj U)
    (a3 : E3 ⊣ completedRestriction T (φ ≫ ψ))
    (h3 : ∀ (M : SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R)) (N : SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj V))
      (f : E3.obj M ⟶ N) (U : T.ProEtᵒᵖ) (x : M.val.obj U),
      (a3.homEquiv M N f).val.app U x = f.val.app U (τ3 M U 1 x))
    (hs3 : ∀ (M : SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R)) (U : T.ProEtᵒᵖ) (s z : V.obj.obj U)
      (x : M.val.obj U), τ3 M U (s * z) x = s • τ3 M U z x)
    (P : CochainComplex (SheafOfModules.{t + 1}
      (SheafOfModules.derivedChangeRingIndependentCoefficients.{t + 1, t + 1, t}
        (ProEt.topology T) R)) ℤ) :
    ∃! f : ((E2).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((E1).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ⟶
      ((E3).mapHomologicalComplex (ComplexShape.up ℤ)).obj P,
      IsIso f ∧ ∀ (p : ℤ) (U : T.ProEtᵒᵖ) (s : V.obj.obj U) (z : S.obj.obj U)
        (x : (P.X p).val.obj U),
        (f.f p).val.app U
          (τ2 _ U s (τ1 _ U z x)) =
        τ3 _ U (s * (ψ.hom.app U z)) x := by
  let a := (a1.comp a2).ofNatIsoRight (completedRestrictCompIso T φ ψ).symm
  let e := a.leftAdjointUniq a3
  have hcomp (M : SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R))
      (N : SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj V))
      (f : ((E1) ⋙ E2).obj M ⟶ N)
      (U : T.ProEtᵒᵖ) (x : M.val.obj U) :
      (a.homEquiv M N f).val.app U x =
        f.val.app U (τ2 _ U 1
          (τ1 M U 1 x)) := by
    dsimp only [a]
    rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv]
    change (a1.homEquiv M _ (a2.homEquiv _ N f)).val.app U x = _
    exact (h1 M _ (a2.homEquiv _ N f) U x).trans
      (h2 _ N f U (τ1 M U 1 x))
  clear_value a
  have hunit (M : SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R))
      (U : T.ProEtᵒᵖ) (x : M.val.obj U) :
      (e.hom.app M).val.app U (τ2 _ U 1
        (τ1 M U 1 x)) =
      τ3 M U 1 x := by
    have he := congrArg (fun f ↦ f.val.app U x)
      (Adjunction.homEquiv_leftAdjointUniq_hom_app a a3 M)
    rw [hcomp] at he
    rw [← a3.homEquiv_id M, h3] at he
    exact he
  clear_value e
  have hformula (M : SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R))
      (U : T.ProEtᵒᵖ) (s : V.obj.obj U) (z : S.obj.obj U) (x : M.val.obj U) :
      (e.hom.app M).val.app U (τ2 _ U s
        (τ1 M U z x)) =
      τ3 M U (s * ψ.hom.app U z) x := by
    have hz := hs1 M U z 1 x
    rw [mul_one] at hz
    have hs := hs2 ((E1).obj M) U s 1
      (τ1 M U z x)
    rw [mul_one] at hs
    erw [hs, map_smul, ← h2, hz, map_smul]
    change s • (ψ.hom.app U z •
      (show (E3.obj M).val.obj U from
        (a2.homEquiv _ _ (e.hom.app M)).val.app U (τ1 M U 1 x))) = _
    erw [h2, hunit, ← mul_smul]
    have ht := hs3 M U (s * ψ.hom.app U z) 1 x
    simpa only [mul_one] using ht.symm
  let f := ((Functor.mapHomologicalComplexCompIso e (.up ℤ)).hom.app P)
  refine ⟨f, ⟨by dsimp [f]; infer_instance, ?_⟩, ?_⟩
  · intro p U s z x
    exact hformula (P.X p) U s z x
  · intro g hg
    apply HomologicalComplex.Hom.ext
    funext p
    apply (a.homEquiv _ _).injective
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    ext x
    rw [hcomp, hcomp]
    exact (hg.2 p U 1 1 x).trans (hformula (P.X p) U 1 1 x).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Balancing is uniquely fixed on pure tensors, including its inverse.
Source: blueprint order 1239, normalization calculation
(blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: the relation chi=psi*phi makes (s tensor r) tensor x map to
s*psi(r) tensor x a balanced trilinear map. It commutes with restrictions and
with the differentials of P, so sheafification gives a chain map. Its inverse
sends s tensor x to s tensor (1 tensor x). The balanced relations make both
composites identities. The formula on local pure tensors uniquely determines
a sheaf map in each degree and therefore uniquely determines the chain map. -/
theorem completedAdicBalance_exists (T : Scheme.{t})
    {R S V : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ V) (χ : R ⟶ V) (_h : φ ≫ ψ = χ)
    (P : CochainComplex (SheafOfModules.{t + 1}
      (SheafOfModules.derivedChangeRingIndependentCoefficients.{t + 1, t + 1, t}
        (ProEt.topology T) R)) ℤ) :
    ∃! f : ((completedAdicChange T ψ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((completedAdicChange T φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ⟶
      ((completedAdicChange T χ).mapHomologicalComplex (ComplexShape.up ℤ)).obj P,
      IsIso f ∧ ∀ (p : ℤ) (U : T.ProEtᵒᵖ) (s : V.obj.obj U) (z : S.obj.obj U)
        (x : (P.X p).val.obj U),
        (f.f p).val.app U
          (completedAdicChangeTensor T ψ _ U s (completedAdicChangeTensor T φ _ U z x)) =
        completedAdicChangeTensor T χ _ U (s * (ψ.hom.app U z)) x := by
  subst χ
  obtain ⟨a1, h1⟩ := completedAdjunction T φ
  obtain ⟨a2, h2⟩ := completedAdjunction T ψ
  obtain ⟨a3, h3⟩ := completedAdjunction T (φ ≫ ψ)
  exact balancing_from_adjunctions T φ ψ _ (completedAdicChangeTensor T φ) a1 h1
    (completedTensor_smul T φ) _ (completedAdicChangeTensor T ψ) a2 h2
    (completedTensor_smul T ψ) _ (completedAdicChangeTensor T (φ ≫ ψ)) a3 h3
    (completedTensor_smul T (φ ≫ ψ)) P

/-- The canonical balancing chain map; no isomorphism is chosen without its tensor formula.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def completedAdicBalance (T : Scheme.{t})
    {R S V : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ V) (χ : R ⟶ V) (h : φ ≫ ψ = χ)
    (P : CochainComplex (SheafOfModules.{t + 1}
      (SheafOfModules.derivedChangeRingIndependentCoefficients.{t + 1, t + 1, t}
        (ProEt.topology T) R)) ℤ) :=
  (completedAdicBalance_exists T φ ψ χ h P).exists.choose

/-- Invertibility is the first property of the uniquely normalized balancing witness.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
instance completedAdicBalance_isIso (T : Scheme.{t})
    {R S V : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ V) (χ : R ⟶ V) (h : φ ≫ ψ = χ)
    (P : CochainComplex (SheafOfModules.{t + 1}
      (SheafOfModules.derivedChangeRingIndependentCoefficients.{t + 1, t + 1, t}
        (ProEt.topology T) R)) ℤ) : IsIso (completedAdicBalance T φ ψ χ h P) :=
  (completedAdicBalance_exists T φ ψ χ h P).exists.choose_spec.1

/-- The quotient map between any two positive levels, including the identity level.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def completedAdicQuotientCommMap (T : Scheme.{t}) (d : AdicCoefficientDatum A)
    (b a : ℕ) (h : a ≤ b) :
    completedAdicFiniteCommRing T d b ⟶ completedAdicFiniteCommRing T d a where
  hom :=
    { app := fun U ↦
        letI := completedAdicFiniteCommRingStructure T d b U
        letI := completedAdicFiniteCommRingStructure T d a U
        CommRingCat.ofHom
          (((completedAdicRingSystem T d).map (homOfLE h).op).hom.app U).hom
      naturality := fun _ _ f ↦ (forget₂ CommRingCat RingCat).map_injective
        (((completedAdicRingSystem T d).map (homOfLE h).op).hom.naturality f) }

/-- The projections and quotient maps have their actual limit-cone compatibility.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: forget commutativity and apply the naturality identity of the limit cone to
the arrow op b -> op a. The forgetful functor is faithful. -/
theorem completedAdicCommProjection_comp (T : Scheme.{t}) (d : AdicCoefficientDatum A)
    (b a : ℕ) (h : a ≤ b) :
    completedAdicCommProjection T d b ≫ completedAdicQuotientCommMap T d b a h =
      completedAdicCommProjection T d a := by
  apply (sheafCompose (ProEt.topology T)
    (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map_injective
  change completedAdicProjection T d b ≫
    (completedAdicRingSystem T d).map (homOfLE h).op = completedAdicProjection T d a
  exact limit.w _ _

end AlgebraicGeometry.Scheme
