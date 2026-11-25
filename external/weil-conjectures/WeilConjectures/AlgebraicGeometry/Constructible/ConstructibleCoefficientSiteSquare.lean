/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Fixed.ProEtaleFixedModuleConstructible
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import WeilConjectures.SixFunctors.ProEtale.ScalarExtension
public import Mathlib.AlgebraicGeometry.Noetherian

import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModelLocalConstancy
import Mathlib.Algebra.Category.ModuleCat.AB
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CoverLifting
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafEquivalence
import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModelStalks
import WeilConjectures.AlgebraicGeometry.ProEtaleGeometricStalk
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Point.Over
import Mathlib.CategoryTheory.Functor.TypeValuedFlat
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf
import WeilConjectures.SixFunctors.ProEtale.ScalarExtensionConstructible
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.ConstructibleSheaf.KernelCokernel

/-! # Constructibility of the ordinary finite coefficient/site square

Source: Stacks Project, Tags 0GKB and 03RZ, and blueprint main-20261015,
sec-proetale-coefficients/sk-thm-pe-constructible-comparison,
sk-thm-pe-constructible-comparison-equivalence.proof.md, parts (1)-(2).
(blueprint: lem-sp-constructible-coefficient-site-square)

All scalar tensors below are ordinary sheafified tensors, with the target ring acting
on its own factor. No flatness or derived-scalar-extension assertion is present.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

private def identityStratification (T : Scheme.{u}) : Scheme.Stratification T where
  n := 1
  stratum _ := Set.univ
  isLocallyClosed_stratum _ := isOpen_univ.isLocallyClosed
  isConstructible_stratum _ := Topology.IsConstructible.univ
  iUnion_stratum_eq_univ := by
    apply Set.eq_univ_of_forall
    intro x
    exact Set.mem_iUnion.mpr ⟨0, Set.mem_univ x⟩
  pairwise_disjoint_stratum i j hij := (hij (Subsingleton.elim _ _)).elim
  domain _ := T
  immersion _ := 𝟙 T
  range_immersion _ := Set.range_id

private theorem emptyProEtale_isZero (T : Scheme.{u}) [IsEmpty T]
    (R : Type (u + 1)) [CommRing R]
    (F : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} R)) : IsZero F := by
  apply (Limits.IsZero.iff_id_eq_zero F).mpr
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  have : IsEmpty U.unop.left :=
    ⟨fun x ↦ (show IsEmpty T from inferInstance).false (U.unop.hom x)⟩
  exact (Scheme.ProEt.isTerminalSectionsOfIsEmpty F U.unop).hom_ext _ _

private def proEtaleOverIso (T : Scheme.{u}) (U : T.ProEt)
    (R : Type (u + 1)) [CommRing R]
    (F : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} R)) :
    letI := Scheme.ProEt.sliceDense T U
    (((Scheme.ProEt.sliceEquiv T U).sheafCongr
      ((Scheme.ProEt.topology T).over U) (Scheme.ProEt.topology U.left)
      (ModuleCat.{u + 1} R)).functor.obj (F.over U)) ≅
      (ProEtale.upperStar (ModuleCat.{u + 1} R) U.hom).obj F := by
  have : (Scheme.ProEt.sliceEquiv T U).inverse.IsDenseSubsite
      (Scheme.ProEt.topology U.left) ((Scheme.ProEt.topology T).over U) :=
    Scheme.ProEt.sliceDense T U
  exact ObjectProperty.isoMk _ (NatIso.ofComponents (fun _ ↦ Iso.refl _)) ≪≫
    ((ProEtale.upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} R)
      U.hom U.prop).app F).symm

private theorem fixedConstructible_of_models (T : Scheme.{u})
    (R : Type (u + 1)) [CommRing R] [Finite R]
    (F : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} R))
    (h : ProEtale.IsConstructible R F) :
    Scheme.IsConstructibleProEtaleFixedModuleSheaf T R F := by
  obtain ⟨S, hS⟩ := h
  by_cases hn : 0 < S.n
  · refine ⟨S, hn, S.isConstructible_stratum, fun i ↦ ⟨?_, ?_⟩⟩
    · obtain ⟨I, U, f, hf, he⟩ := ProEtale.finiteModels_over R _ (by
        obtain ⟨ι, W, g, hg, hM⟩ := hS i
        exact ⟨ι, W, g, hg, fun j ↦ (hM j).imp fun _ h ↦
          ⟨by have := h.1; exact Module.finite_of_finite R, h.2⟩⟩)
      exact ⟨I, U, f, hf, fun j ↦ ⟨(he j).choose, (he j).choose_spec.2⟩⟩
    · exact ProEtale.finite_geometricStalk_of_finite_models R _ (by
        obtain ⟨ι, W, g, hg, hM⟩ := hS i
        exact ⟨ι, W, g, hg, fun j ↦ (hM j).imp fun _ h ↦
          ⟨by have := h.1; exact Module.finite_of_finite R, h.2⟩⟩)
  · have hz : S.n = 0 := Nat.eq_zero_of_not_pos hn
    have : IsEmpty T := ⟨fun x ↦ by
      have hx : x ∈ ⋃ i, S.stratum i := S.iUnion_stratum_eq_univ.symm ▸ Set.mem_univ x
      obtain ⟨i, _⟩ := Set.mem_iUnion.mp hx
      exact Fin.elim0 (hz ▸ i)⟩
    let S' := identityStratification T
    refine ⟨S', Nat.zero_lt_one, S'.isConstructible_stratum, fun i ↦ ⟨?_, ?_⟩⟩
    · let G := (ProEtale.upperStar (ModuleCat.{u + 1} R) (S'.immersion i)).obj F
      have he : ProEtale.IsFiniteLocallyConstant R G := by
        refine ⟨ULift.{u + 1} Empty, fun i ↦ i.down.elim, fun i ↦ i.down.elim, ?_,
          fun i ↦ i.down.elim⟩
        have hempty : Presieve.ofArrows (fun i : ULift.{u + 1} Empty ↦ i.down.elim)
            (fun i ↦ i.down.elim) = (⊥ : Presieve T) := by
          funext U f
          apply propext
          exact ⟨fun ⟨i⟩ ↦ i.down.elim, False.elim⟩
        rw [hempty]
        exact Scheme.bot_mem_propQCPrecoverage T
      obtain ⟨I, U, f, hf, he⟩ := ProEtale.finiteModels_over R G (by
        obtain ⟨ι, W, g, hg, hM⟩ := he
        exact ⟨ι, W, g, hg, fun j ↦ (hM j).imp fun _ h ↦
          ⟨by have := h.1; exact Module.finite_of_finite R, h.2⟩⟩)
      exact ⟨I, U, f, hf, fun j ↦ ⟨(he j).choose, (he j).choose_spec.2⟩⟩
    · intro Ω _ _ x
      exact isEmptyElim ((show Spec (.of Ω) ⟶ T from x) (IsLocalRing.closedPoint Ω))

/-- Ordinary termwise scalar extension using the published sheaf tensor functor.
Its additive structure is supplied by its actual scalar adjunction.
Source: Stacks 0GKB and 03EK (blueprint: lem-sp-constructible-coefficient-site-square). -/
def constructibleCoefficientComplex {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (X : Scheme.{u}) (φ : A →+* B)
    (C : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) ℤ :=
  have : (ProEtale.etaleSheafExtendScalars φ X).Additive :=
    (ProEtale.etaleSheafExtendScalarsAdjunction φ X).left_adjoint_additive
  ((ProEtale.etaleSheafExtendScalars φ X).mapHomologicalComplex (.up ℤ)).obj C

/-- Each original stratum and each original finite constant model survives ordinary
scalar extension, including on every member of any chosen trivializing cover.
`ModuleCat.extendScalars` uses B tensor M, canonically the same B-module as M tensor B.
Source: Stacks 0GKB (blueprint: lem-sp-constructible-coefficient-site-square).
Proof: (1) Present a finite module by finite free modules, using the lists of its
and its kernel's elements. Exact inverse image and exact module sheafification carry
this presentation to the identical constant presentation (def-sf-site-constant-module-functor,
lem-weil-pbc-site-module-presheaf-sheafification-exact,
situation-conventions).
(2) Apply lem-sf-proetale-sheafification-tensor-comparison to constant presheaves.
The unit is locally bijective by lem-weil-pbc-site-sheafification-iso-locally-bijective.
The pure tensor formula preserves the B-action. Tensors of the finitely many elements
with 1 generate the extension over finite B, so it is a finite set.
(3) Apply lem-weil-pbc-algebraic-inverse-image-tensor-comparison along the stratum
and its cover; its pure-pairing normalization preserves the B-action.
(4) The same strata and the same covers thus give the extended finite constant models.
No flatness is used, and tensoring the zero module still gives zero. -/
theorem constructibleCoefficientSheaf
    (X : Scheme.{u}) [IsNoetherian X]
    (A B : Type (u + 1)) [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
    (_hF : Scheme.IsConstructibleEtaleModuleSheaf F) :
    Scheme.IsConstructibleEtaleModuleSheaf ((ProEtale.etaleSheafExtendScalars φ X).obj F) ∧
    ∀ (S : Scheme.FiniteLocallyClosedStratification X)
      (_hstrata : ∀ k : Fin S.n, Topology.IsConstructible (S.stratum k)) (k : Fin S.n)
      (U : (S.domain k).Etale) (M : ModuleCat.{u + 1} A), Finite M →
      Nonempty
        ((((Etale.upperStar (ModuleCat.{u + 1} A) (S.immersion k)).obj F).over U) ≅
          (constantSheaf ((S.domain k).smallEtaleTopology.over U)
            (ModuleCat.{u + 1} A)).obj M) →
      Finite ((ModuleCat.extendScalars φ).obj M) ∧
      Nonempty
        ((((Etale.upperStar (ModuleCat.{u + 1} B) (S.immersion k)).obj
          ((ProEtale.etaleSheafExtendScalars φ X).obj F)).over U) ≅
          (constantSheaf ((S.domain k).smallEtaleTopology.over U)
            (ModuleCat.{u + 1} B)).obj ((ModuleCat.extendScalars φ).obj M)) := by
  have h := (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf F).mp _hF
  refine ⟨(Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
    (ProEtale.isConstructibleSheaf_etaleSheafExtendScalars_obj φ F), ?_⟩
  intro S _hstrata k U M hM he
  have := hM
  have : Module.Finite A M := Module.Finite.of_finite
  have := ModuleCat.finite_extendScalars_obj' φ M
  refine ⟨Module.finite_of_finite B, ?_⟩
  obtain ⟨e⟩ := he
  let G := (Etale.upperStar (ModuleCat.{u + 1} A) (S.immersion k)).obj F
  let EA := Scheme.Etale.overSheafEquiv U (ModuleCat.{u + 1} A)
  let EB := Scheme.Etale.overSheafEquiv U (ModuleCat.{u + 1} B)
  let ca := ((Scheme.Etale.overEquiv U).constantSheafSheafCongrIso
    ((S.domain k).smallEtaleTopology.over U) U.left.smallEtaleTopology
    (ModuleCat.{u + 1} A) Over.mkIdTerminal).app M
  let cb := ((Scheme.Etale.overEquiv U).constantSheafSheafCongrIso
    ((S.domain k).smallEtaleTopology.over U) U.left.smallEtaleTopology
    (ModuleCat.{u + 1} B) Over.mkIdTerminal).app ((ModuleCat.extendScalars φ).obj M)
  let em := (Scheme.overSheafEquivFunctorObjOverIso (ModuleCat.{u + 1} A) U G).symm ≪≫
    EA.functor.mapIso e ≪≫ ca
  refine ⟨EB.functor.preimageIso (?_ ≪≫ cb.symm)⟩
  exact Scheme.overSheafEquivFunctorObjOverIso (ModuleCat.{u + 1} B) U _ ≪≫
    (Etale.upperStar (ModuleCat.{u + 1} B) U.hom).mapIso
      ((ProEtale.etaleSheafExtendScalarsCompUpperStarIso φ (S.immersion k)).app F) ≪≫
    (ProEtale.etaleSheafExtendScalarsCompUpperStarIso φ U.hom).app G ≪≫
    (ProEtale.etaleSheafExtendScalars φ U.left).mapIso em ≪≫
    (ProEtale.constantSheafCompEtaleSheafExtendScalarsIso φ U.left).app M

/-- Comparison retains every nonempty stratification and its finite constant models.
The last clause explicitly repairs a zero-stratum partition on the empty scheme by
one empty stratum with constant zero value.
Source: blueprint comparison-equivalence proof (1), Stacks 098B and 099R
(blueprint: lem-sp-constructible-coefficient-site-square).
Proof: (1) A finite constant module has the finite free presentation in proof step 1
of the node; lem-sf-comparison-pullback-exact identifies its comparison with the same
constant module by taking the identical cokernel.
(2) Apply proposition-comparison-etale-derived-category--5 to a stratum and then a trivializing map.
The two comparisons identify its restriction with that same finite constant model.
The original etale cover is a pro-etale cover by lem-pur-etale-proetale-cover.
(3) The encoding and constructibility equivalences
lem-weil-pbc-proetale-constant-module-encoding and
lem-weil-pbc-proetale-constant-module-constructibility identify this with the intrinsic
constructibility predicate, retaining the partition when it has positive size.
(4) A partition with no strata forces the underlying scheme to be empty. Its identity
immersion is a one-stratum partition; the identity cover trivializes its unique module
sheaf with zero value. This supplies the positive-size convention without excluding
an empty scheme or an empty input partition. -/
theorem constructibleSiteComparison
    (X : Scheme.{u}) [IsNoetherian X]
    (R : Type (u + 1)) [CommRing R] [Finite R]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))
    (_hF : Scheme.IsConstructibleEtaleModuleSheaf F) :
    Scheme.IsConstructibleProEtaleFixedModuleSheaf X R
      ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} R) X).obj F) ∧
    (∀ (S : Scheme.FiniteLocallyClosedStratification X)
      (_hstrata : ∀ k : Fin S.n, Topology.IsConstructible (S.stratum k))
      (_hS : 0 < S.n) (k : Fin S.n)
      (d : Scheme.LocallyConstantDatum
        ((Etale.upperStar (ModuleCat.{u + 1} R) (S.immersion k)).obj F)),
      Presieve.ofArrows
        (fun i : d.cover.I₀ ↦
          (Scheme.toProEt (S.domain k)).obj (d.cover.etalePrecoverageToEtale i))
        (fun i : d.cover.I₀ ↦ MorphismProperty.Over.homMk
          (B := Scheme.ProEt.mk (𝟙 (S.domain k)))
          (d.cover.f i) (Category.comp_id _) (MorphismProperty.top_apply _)) ∈
            (Scheme.ProEt.precoverage (S.domain k)).coverings (Scheme.ProEt.mk (𝟙 _)) ∧
      ∀ (i : d.cover.I₀) (M : ModuleCat.{u + 1} R), Finite M →
      Nonempty
        ((((Etale.upperStar (ModuleCat.{u + 1} R) (S.immersion k)).obj F).over
          (d.cover.etalePrecoverageToEtale i)) ≅
          (constantSheaf ((S.domain k).smallEtaleTopology.over
            (d.cover.etalePrecoverageToEtale i)) (ModuleCat.{u + 1} R)).obj M) →
      Nonempty
        ((((ProEtale.upperStar (ModuleCat.{u + 1} R) (S.immersion k)).obj
          ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} R) X).obj F)).over
            ((Scheme.toProEt (S.domain k)).obj (d.cover.etalePrecoverageToEtale i))) ≅
          (constantSheaf ((Scheme.ProEt.topology (S.domain k)).over
            ((Scheme.toProEt (S.domain k)).obj (d.cover.etalePrecoverageToEtale i)))
              (ModuleCat.{u + 1} R)).obj M)) ∧
    (∀ S : Scheme.FiniteLocallyClosedStratification X, S.n = 0 →
      IsEmpty X ∧ ∃ S' : Scheme.Stratification X, S'.n = 1 ∧
        ∀ k : Fin S'.n, IsEmpty (S'.domain k) ∧
          Nonempty
            ((ProEtale.upperStar (ModuleCat.{u + 1} R) (S'.immersion k)).obj
              ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} R) X).obj F) ≅
              (constantSheaf (Scheme.ProEt.topology (S'.domain k))
                (ModuleCat.{u + 1} R)).obj (ModuleCat.of R (ULift.{u + 1} PUnit.{1})))) := by
  have h := (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf F).mp _hF
  refine ⟨fixedConstructible_of_models X R _
    (ProEtale.isConstructible_comparisonUpperStar_obj F), ?_, ?_⟩
  · intro S _hstrata _hS k d
    refine ⟨?_, ?_⟩
    · rw [Scheme.ProEt.mem_precoverage_iff, Presieve.map_ofArrows]
      exact Scheme.etalePrecoverage_le_proetalePrecoverage _ d.cover.mem₀
    · intro i M _hM he
      obtain ⟨e⟩ := he
      let G := (Etale.upperStar (ModuleCat.{u + 1} R) (S.immersion k)).obj F
      let U := d.cover.etalePrecoverageToEtale i
      let V := (Scheme.toProEt (S.domain k)).obj U
      have : (Scheme.ProEt.sliceEquiv (S.domain k) V).inverse.IsDenseSubsite
          (Scheme.ProEt.topology U.left) ((Scheme.ProEt.topology (S.domain k)).over V) :=
        Scheme.ProEt.sliceDense (S.domain k) V
      let E := (Scheme.ProEt.sliceEquiv (S.domain k) V).sheafCongr
        ((Scheme.ProEt.topology (S.domain k)).over V)
        (Scheme.ProEt.topology U.left) (ModuleCat.{u + 1} R)
      let ec := ((Scheme.Etale.overEquiv U).constantSheafSheafCongrIso
        ((S.domain k).smallEtaleTopology.over U) U.left.smallEtaleTopology
        (ModuleCat.{u + 1} R) Over.mkIdTerminal).app M
      let ep := ((Scheme.ProEt.sliceEquiv (S.domain k) V).constantSheafSheafCongrIso
        ((Scheme.ProEt.topology (S.domain k)).over V) (Scheme.ProEt.topology U.left)
        (ModuleCat.{u + 1} R) Over.mkIdTerminal).app M
      let em := (Scheme.overSheafEquivFunctorObjOverIso
        (ModuleCat.{u + 1} R) U G).symm ≪≫
        (Scheme.Etale.overSheafEquiv U (ModuleCat.{u + 1} R)).functor.mapIso e ≪≫ ec
      refine ⟨E.functor.preimageIso (?_ ≪≫ ep.symm)⟩
      exact proEtaleOverIso (S.domain k) V R _ ≪≫
        (ProEtale.upperStar (ModuleCat.{u + 1} R) U.hom).mapIso
          ((ProEtale.comparisonUpperStarCompUpperStarIso
            (ModuleCat.{u + 1} R) (S.immersion k)).app F) ≪≫
        (ProEtale.comparisonUpperStarCompUpperStarIso
          (ModuleCat.{u + 1} R) U.hom).app G ≪≫
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} R) U.left).mapIso em ≪≫
        (ProEtale.comparisonUpperStarConstantSheafIso R U.left).app M
  · intro S hz
    have hX : IsEmpty X := ⟨fun x ↦ by
      have hx : x ∈ ⋃ i, S.stratum i := S.iUnion_stratum_eq_univ.symm ▸ Set.mem_univ x
      obtain ⟨i, _⟩ := Set.mem_iUnion.mp hx
      exact Fin.elim0 (hz ▸ i)⟩
    have := hX
    refine ⟨hX, identityStratification X, rfl, fun k ↦ ⟨hX, ?_⟩⟩
    let Z := (constantSheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} R)).obj (ModuleCat.of R (ULift.{u + 1} PUnit.{1}))
    exact ⟨(emptyProEtale_isZero X R _).isoZero ≪≫
      (emptyProEtale_isZero X R Z).isoZero.symm⟩

private theorem etaleHomology_constructible (X : Scheme.{u})
    (R : Type (u + 1)) [CommRing R] [Finite R]
    (C : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) ℤ)
    (hc : ∀ q, Scheme.IsConstructibleEtaleModuleSheaf (C.X q)) (q : ℤ) :
    Scheme.IsConstructibleEtaleModuleSheaf (C.homology q) := by
  have h (i : ℤ) :=
    (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp (hc i)
  let S := C.sc q
  have : Scheme.IsConstructibleSheaf S.X₁ := h _
  have : Scheme.IsConstructibleSheaf S.X₂ := h _
  have : Scheme.IsConstructibleSheaf S.X₃ := h _
  have : Scheme.IsConstructibleSheaf (kernel S.g) :=
    Scheme.IsConstructibleSheaf.kernel S.g
  have : Scheme.IsConstructibleSheaf (cokernel (kernel.lift S.g S.f S.zero)) :=
    Scheme.IsConstructibleSheaf.cokernel _
  exact (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
    (Scheme.IsConstructibleSheaf.of_iso S.homologyIsoCokernelLift.symm)

private theorem fixedConstructible_iso (X : Scheme.{u})
    (R : Type (u + 1)) [CommRing R] [Finite R]
    {F G : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} R)} (e : F ≅ G)
    (h : Scheme.IsConstructibleProEtaleFixedModuleSheaf X R F) :
    Scheme.IsConstructibleProEtaleFixedModuleSheaf X R G := by
  obtain ⟨S, hn, hs, hS⟩ := h
  refine ⟨S, hn, hs, fun i ↦ ?_⟩
  let ei := (ProEtale.upperStar (ModuleCat.{u + 1} R) (S.immersion i)).mapIso e
  obtain ⟨hl, hf⟩ := hS i
  refine ⟨?_, ?_⟩
  · obtain ⟨I, U, f, hcover, he⟩ := hl
    refine ⟨I, U, f, hcover, fun j ↦ ?_⟩
    obtain ⟨M, ⟨em⟩⟩ := he j
    exact ⟨M, ⟨((Scheme.ProEt.topology (S.domain i)).overPullback
      (ModuleCat.{u + 1} R) (U j)).mapIso ei.symm ≪≫ em⟩⟩
  · intro Ω _ _ x
    have hfin := hf Ω x
    let es := HasColimit.isoOfNatIso (Functor.isoWhiskerLeft
      (Scheme.proEtaleGeometricNeighbourhoodForget x).op
      ((sheafToPresheaf _ _).mapIso ei))
    exact @Finite.of_equiv _ _ hfin es.toLinearEquiv.toEquiv

private theorem localizedHomology_isZero
    {D : Type*} [Category D] [Abelian D] [HasDerivedCategory D]
    (C : CochainComplex D ℤ) (q : ℤ) (hz : IsZero (C.X q)) :
    IsZero ((_root_.DerivedCategory.homologyFunctor D q).obj
      (_root_.DerivedCategory.Q.obj C)) :=
  ((C.sc q).isZero_homology_of_isZero_X₂ hz).of_iso
    ((_root_.DerivedCategory.homologyFunctorFactors D q).app C)

/-- The four ordinary localized complexes have constructible cohomology in the original
interval; comparison commutes with each cohomology sheaf.
Source: Stacks 03RZ and blueprint comparison-equivalence proof (2)
(blueprint: lem-sp-constructible-coefficient-site-square).
Proof: (1)-(4) The constant presentation, tensor sheafification and inverse-image tensor
arguments of the node give constructible terms for C_B on the original strata and
covers, with finite values M tensor B. Zero terms remain zero.
(5) The comparison argument just stated gives intrinsic constructibility of each
comparison of a constructible etale sheaf, including the one-empty-stratum convention.
(6) By thm-constructible-serre, first take the kernel of d^q and then the cokernel
of the induced map from C^{q-1} into this kernel. Both are constructible, so H^q is
constructible. A zero middle term gives zero cohomology outside [a,b].
The localization cohomology functor is the same homology by
 def-weil-derived-cohomology-sheaves.
(7) lem-sf-comparison-pullback-exact gives H^q(N C') isomorphic to N H^q(C'), naturally
for C and C_B. Step (5) makes these sheaves intrinsically constructible, and additivity
preserves their vanishing. Thus all four localized objects have exactly the asserted
cohomology bounds, without a flatness hypothesis or a derived-tensor identification. -/
theorem constructibleCoefficientSiteSquare
    (X : Scheme.{u}) [IsNoetherian X]
    (A B : Type (u + 1)) [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (a b : ℤ) (_hab : a ≤ b)
    (C : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (_hzero : ∀ q : ℤ, q < a ∨ b < q → IsZero (C.X q))
    (_hcons : ∀ q : ℤ, Scheme.IsConstructibleEtaleModuleSheaf (C.X q)) :
    (∀ q : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
      ((constructibleCoefficientComplex X φ C).X q)) ∧
    (∀ q : ℤ, q < a ∨ b < q →
      IsZero ((constructibleCoefficientComplex X φ C).X q)) ∧
    Etale.DerivedCategory.isBoundedConstructible A X (_root_.DerivedCategory.Q.obj C) ∧
    Etale.DerivedCategory.isBoundedConstructible B X
      (_root_.DerivedCategory.Q.obj (constructibleCoefficientComplex X φ C)) ∧
    (∀ q : ℤ, q < a ∨ b < q →
      IsZero ((_root_.DerivedCategory.homologyFunctor
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) q).obj
          (_root_.DerivedCategory.Q.obj C)) ∧
      IsZero ((_root_.DerivedCategory.homologyFunctor
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) q).obj
          (_root_.DerivedCategory.Q.obj (constructibleCoefficientComplex X φ C)))) ∧
    (∀ q : ℤ,
      Scheme.IsConstructibleProEtaleFixedModuleSheaf X A
        ((_root_.DerivedCategory.homologyFunctor
          (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) q).obj
          (_root_.DerivedCategory.Q.obj
            (((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapHomologicalComplex
              (.up ℤ)).obj C))) ∧
      Scheme.IsConstructibleProEtaleFixedModuleSheaf X B
        ((_root_.DerivedCategory.homologyFunctor
          (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B)) q).obj
          (_root_.DerivedCategory.Q.obj
            (((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) X).mapHomologicalComplex
              (.up ℤ)).obj (constructibleCoefficientComplex X φ C))))) ∧
    (∀ q : ℤ, q < a ∨ b < q →
      IsZero ((_root_.DerivedCategory.homologyFunctor
        (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) q).obj
          (_root_.DerivedCategory.Q.obj
            (((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapHomologicalComplex
              (.up ℤ)).obj C))) ∧
      IsZero ((_root_.DerivedCategory.homologyFunctor
        (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B)) q).obj
          (_root_.DerivedCategory.Q.obj
            (((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) X).mapHomologicalComplex
              (.up ℤ)).obj (constructibleCoefficientComplex X φ C))))) ∧
    (∀ q : ℤ,
      Nonempty
        ((((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapHomologicalComplex
          (.up ℤ)).obj C).homology q ≅
          (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).obj (C.homology q)) ∧
      Nonempty
        ((((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) X).mapHomologicalComplex
          (.up ℤ)).obj (constructibleCoefficientComplex X φ C)).homology q ≅
          (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) X).obj
            ((constructibleCoefficientComplex X φ C).homology q))) := by
  have hcB (q : ℤ) : Scheme.IsConstructibleEtaleModuleSheaf
      ((constructibleCoefficientComplex X φ C).X q) :=
    (constructibleCoefficientSheaf X A B φ (C.X q) (_hcons q)).1
  have hzB (q : ℤ) (hq : q < a ∨ b < q) :
      IsZero ((constructibleCoefficientComplex X φ C).X q) :=
    (ProEtale.etaleSheafExtendScalars φ X).map_isZero (_hzero q hq)
  have hderived (R : Type (u + 1)) [CommRing R] [Finite R]
      (D : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) ℤ)
      (hc : ∀ q, Scheme.IsConstructibleEtaleModuleSheaf (D.X q))
      (hz : ∀ q, q < a ∨ b < q → IsZero (D.X q)) :
      Etale.DerivedCategory.isBoundedConstructible R X (_root_.DerivedCategory.Q.obj D) := by
    refine ⟨fun q ↦ ?_, a, b, _hab, fun q hq ↦ localizedHomology_isZero D q (hz q hq)⟩
    have h := (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp
      (etaleHomology_constructible X R D hc q)
    have : Scheme.IsConstructibleSheaf
        ((HomologicalComplex.homologyFunctor _ (.up ℤ) q).obj D) := h
    exact (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
      (Scheme.IsConstructibleSheaf.of_iso
        ((_root_.DerivedCategory.homologyFunctorFactors _ q).app D).symm)
  have hpro (R : Type (u + 1)) [CommRing R] [Finite R]
      (D : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) ℤ)
      (hc : ∀ q, Scheme.IsConstructibleEtaleModuleSheaf (D.X q)) (q : ℤ) :
      Scheme.IsConstructibleProEtaleFixedModuleSheaf X R
        ((_root_.DerivedCategory.homologyFunctor
          (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} R)) q).obj
          (_root_.DerivedCategory.Q.obj
            (((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} R) X).mapHomologicalComplex
              (.up ℤ)).obj D))) := by
    let N := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} R) X
    let e := ((_root_.DerivedCategory.homologyFunctorFactors _ q).app
      ((N.mapHomologicalComplex (.up ℤ)).obj D)) ≪≫ (D.sc q).mapHomologyIso N
    exact fixedConstructible_iso X R e.symm
      (constructibleSiteComparison X R (D.homology q)
        (etaleHomology_constructible X R D hc q)).1
  refine ⟨hcB, hzB, hderived A C _hcons _hzero,
    hderived B (constructibleCoefficientComplex X φ C) hcB hzB, ?_, ?_, ?_, ?_⟩
  · intro q hq
    exact ⟨localizedHomology_isZero C q (_hzero q hq),
      localizedHomology_isZero _ q (hzB q hq)⟩
  · intro q
    exact ⟨hpro A C _hcons q, hpro B _ hcB q⟩
  · intro q hq
    exact ⟨localizedHomology_isZero _ q
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).map_isZero (_hzero q hq)),
      localizedHomology_isZero _ q
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) X).map_isZero (hzB q hq))⟩
  · intro q
    exact ⟨⟨(C.sc q).mapHomologyIso
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X)⟩,
      ⟨((constructibleCoefficientComplex X φ C).sc q).mapHomologyIso
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) X)⟩⟩

end AlgebraicGeometry
