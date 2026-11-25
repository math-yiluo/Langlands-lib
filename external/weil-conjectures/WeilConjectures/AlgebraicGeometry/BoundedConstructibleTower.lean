/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum
public import WeilConjectures.AlgebraicGeometry.ProEtaleFixedModuleLocalConstancy
public import WeilConjectures.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
import all WeilConjectures.AlgebraicGeometry.DerivedScalarExtensionRestrictionAdjunction

/-!
# Uniformly bounded constructible adic towers

Source: blueprint sec-proper-base-change/sk-thm-properbasechange,
def-weil-pbc-bounded-constructible-tower, order 1250; Stacks Tags 09AI and 09BT
(blueprint: def-weil-pbc-bounded-constructible-tower).

Positive level n+1 is indexed by n : ℕ. Normalizations are stored for every comparable
pair; their cocycle determines the nonconsecutive ones from the consecutive ones.
Compatibility is expressed on their adjoints M_b→Res(M_a). The tensor-unit normalized
scalar-extension adjunction makes this equivalent to the displayed normalization
identities in the blueprint. This permits restrictions to retain their actual
inverse-image coefficients, without choosing a tensor/pullback comparison.

## Main definitions

* `AdicTower`: a derived strict tower with quotient-linear normalized levels.
* `AdicTowerLocalModel`: one bounded local complex and its compatible reductions.
* `IsUniformlyBoundedConstructibleAdicTower`: common bounds, finite strata and local models.
* `pbcLevelConstantComparison` and `pbcCompletedComparison`: canonical coefficient
  presentation comparisons fixed on constant sections.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct ChangeOfRings

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem normalizedDerivedAdjunction
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (L : A ⥤ B) (R : B ⥤ A) [L.Additive] [R.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R] (adj : L ⊣ R)
    (P : CochainComplex A ℤ → Prop)
    (hres : ∀ G : CochainComplex A ℤ, ∃ (K : CochainComplex A ℤ) (s : K ⟶ G),
      P K ∧ QuasiIso s)
    (LD : DerivedCategory A ⥤ DerivedCategory B)
    (ε : DerivedCategory.Qh ⋙ LD ⟶ L.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (hLD : LD.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso A (.up ℤ)))
    (hε : ∀ K : CochainComplex A ℤ, P K →
      IsIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj K))) :
    ∃! d : LD ⊣ R.mapDerivedCategory,
      ∀ K : CochainComplex A ℤ, P K →
        d.unit.app (DerivedCategory.Q.obj K) ≫
          R.mapDerivedCategory.map
            (LD.map ((DerivedCategory.quotientCompQhIso _).inv.app K) ≫
              ε.app ((HomotopyCategory.quotient _ _).obj K) ≫
              DerivedCategory.Qh.map ((L.mapHomotopyCategoryFactors (.up ℤ)).hom.app K) ≫
              (DerivedCategory.quotientCompQhIso _).hom.app
                ((L.mapHomologicalComplex (.up ℤ)).obj K)) ≫
          R.mapDerivedCategoryFactors.hom.app ((L.mapHomologicalComplex (.up ℤ)).obj K) =
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex adj.unit (.up ℤ)).app K) := by
  have hr (X : HomotopyCategory A (.up ℤ)) :
      ∃ (K : HomotopyCategory A (.up ℤ)) (s : K ⟶ X),
        IsIso (ε.app K) ∧ HomotopyCategory.quasiIso A (.up ℤ) s := by
    obtain ⟨G, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    obtain ⟨K, s, hK, hs⟩ := hres G
    exact ⟨_, (HomotopyCategory.quotient _ _).map s, hε K hK,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff s).2 hs⟩
  obtain ⟨d, hd⟩ := ScalarReductionDerivedProof.derivedAdjunction_of_resolutions
    L R adj LD ε hLD hr
  have hn (K : CochainComplex A ℤ) :
        d.unit.app (DerivedCategory.Q.obj K) ≫
          R.mapDerivedCategory.map
            (LD.map ((DerivedCategory.quotientCompQhIso _).inv.app K) ≫
              ε.app ((HomotopyCategory.quotient _ _).obj K) ≫
              DerivedCategory.Qh.map ((L.mapHomotopyCategoryFactors (.up ℤ)).hom.app K) ≫
              (DerivedCategory.quotientCompQhIso _).hom.app
                ((L.mapHomologicalComplex (.up ℤ)).obj K)) ≫
          R.mapDerivedCategoryFactors.hom.app ((L.mapHomologicalComplex (.up ℤ)).obj K) =
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex adj.unit (.up ℤ)).app K) := by
    have hp := hd ((HomotopyCategory.quotient _ _).obj K)
    change d.unit.app (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient _ _).obj K)) ≫
      R.mapDerivedCategory.map (ε.app ((HomotopyCategory.quotient _ _).obj K)) ≫
      R.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient _ _).obj
        ((L.mapHomologicalComplex (.up ℤ)).obj K)) = _ at hp
    simp only [Functor.mapDerivedCategoryFactorsh_hom_app,
      Adjunction.mapHomotopyCategory_unit_app_quotient] at hp
    simp only [Functor.mapHomotopyCategoryFactors,
      Quotient.lift.isLift_hom, Quotient.lift.isLift_inv] at hp ⊢
    erw [DerivedCategory.Qh.map_id, Category.id_comp]
    erw [DerivedCategory.Qh.map_id, Category.comp_id] at hp
    have hp' := congrArg (fun f ↦ f ≫ (DerivedCategory.quotientCompQhIso A).hom.app
      ((R.mapHomologicalComplex (.up ℤ)).obj ((L.mapHomologicalComplex (.up ℤ)).obj K))) hp
    simp only [Category.assoc, Iso.inv_hom_id_app] at hp'
    erw [Category.comp_id] at hp'
    erw [DerivedCategory.quotientCompQhIso_hom_naturality] at hp'
    apply (cancel_epi ((DerivedCategory.quotientCompQhIso A).hom.app K)).mp
    simp only [Functor.map_comp, Category.assoc]
    have hunit := d.unit.naturality ((DerivedCategory.quotientCompQhIso A).hom.app K)
    simp only [Functor.id_map, Functor.comp_map] at hunit
    rw [reassoc_of% hunit, ← R.mapDerivedCategory.map_comp_assoc, ← LD.map_comp,
      Iso.hom_inv_id_app]
    erw [LD.map_id, R.mapDerivedCategory.map_id, Category.id_comp]
    exact hp'
  refine ⟨d, fun K _ ↦ hn K, ?_⟩
  intro d' hd'
  have hu (K : CochainComplex A ℤ) (hK : P K) :
      d'.unit.app (DerivedCategory.Q.obj K) = d.unit.app (DerivedCategory.Q.obj K) := by
    have : IsIso (ε.app ((HomotopyCategory.quotient _ _).obj K)) := hε K hK
    apply (cancel_mono (R.mapDerivedCategory.map
      (LD.map ((DerivedCategory.quotientCompQhIso _).inv.app K) ≫
        ε.app ((HomotopyCategory.quotient _ _).obj K) ≫
        DerivedCategory.Qh.map ((L.mapHomotopyCategoryFactors (.up ℤ)).hom.app K) ≫
        (DerivedCategory.quotientCompQhIso _).hom.app
          ((L.mapHomologicalComplex (.up ℤ)).obj K)) ≫
      R.mapDerivedCategoryFactors.hom.app
        ((L.mapHomologicalComplex (.up ℤ)).obj K))).mp
    simpa only [Category.assoc] using (hd' K hK).trans (hn K).symm
  apply Adjunction.ext
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso A (.up ℤ))
  intro K
  obtain ⟨K', s, hK', hs⟩ := hres K
  have : QuasiIso s := hs
  apply (cancel_epi (DerivedCategory.Q.map s)).mp
  change (𝟭 _).map (DerivedCategory.Q.map s) ≫ _ =
    (𝟭 _).map (DerivedCategory.Q.map s) ≫ _
  rw [d'.unit.naturality, d.unit.naturality]
  dsimp only [Functor.comp_map, Functor.id_map]
  rw [hu K' hK']

/-- Finite lissity over an inverse-image constant ring. A covering sieve on the final
object trivializes F as a module sheaf; on each member the constant is a finite module.
The coefficient ring is exactly the inverse image, so the module isomorphism is linear
with the restricted coefficient action, including when g is the identity.
Source: Stacks Tags 09AI and 099Y (blueprint: def-weil-pbc-bounded-constructible-tower). -/
def IsRelativelyFiniteLisseModule {X Y : Scheme.{u}} (g : Y ⟶ X)
    (A : Type (u + 1)) [CommRing A]
    (F : ringedSiteModules.{u + 1} ((adicLisseForget Y).obj
      ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj (adicLisseConstantRing X A)))) :
    Prop :=
  ∃ S : Sieve (⊤_ Y.ProEt), S ∈ ProEt.topology Y (⊤_ Y.ProEt) ∧
    ∀ (V : Y.ProEt) (f : V ⟶ ⊤_ Y.ProEt), S f →
      ∃ M : ModuleCat.{u + 1} A, Finite M ∧
        Nonempty ((SheafOfModules.overFunctor _ V).obj F ≅
          (SheafOfModules.overFunctor _ V).obj
            ((proEtaleModuleInverseImage g (adicLisseConstantRing X A)).obj
              ((adicLisseConstantModules X A).obj M)))

variable (X : Scheme.{u})

/-- The module category over a commutative ring sheaf on the small site.
Source: blueprint order 1239 (blueprint: def-weil-pbc-bounded-constructible-tower). -/
abbrev pbcModules (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :=
  ringedSiteModules.{u + 1} ((adicLisseForget X).obj R)

/-- Strict inverse sequences, reindexed by n ↦ n+1.
Source: blueprint order 1239 (blueprint: def-weil-pbc-bounded-constructible-tower). -/
abbrev pbcTowers (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :=
  ℕᵒᵖ ⥤ pbcModules X R

/-- The standard derived localization for strict towers.
Source: blueprint order 1239 (blueprint: def-weil-pbc-bounded-constructible-tower). -/
instance pbcTowers_hasDerivedCategory
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    HasDerivedCategory (pbcTowers X R) := HasDerivedCategory.standard _

variable {X} {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (φ : R ⟶ S)

/-- Restrict scalar actions along the given ring-sheaf map.
Source: Stacks Tag 03CZ (blueprint: def-weil-pbc-bounded-constructible-tower). -/
abbrev pbcRestrict :=
  proEtaleRingRestrictScalars φ

/-- Exact restriction preserves finite limits. Source: Stacks Tag 03DA
(blueprint: def-weil-pbc-bounded-constructible-tower). -/
instance pbcRestrict_limits : PreservesFiniteLimits (pbcRestrict φ) :=
  (proEtaleRingRestrictScalars_properties φ).1

/-- Exact restriction preserves finite colimits. Source: Stacks Tag 03DA
(blueprint: def-weil-pbc-bounded-constructible-tower). -/
instance pbcRestrict_colimits : PreservesFiniteColimits (pbcRestrict φ) :=
  (proEtaleRingRestrictScalars_properties φ).2.1

/-- Restriction of scalars is additive on pro-etale module sheaves.
Source: Stacks Tag 03DA (blueprint: def-weil-pbc-bounded-constructible-tower). -/
instance pbcRestrict_additive : (pbcRestrict φ).Additive := by
  dsimp [pbcRestrict, proEtaleRingRestrictScalars]
  infer_instance

/-- Exact scalar restriction on unbounded derived categories.
Source: blueprint order 1239 (blueprint: def-weil-pbc-bounded-constructible-tower). -/
def pbcDerivedRestrict := (pbcRestrict φ).mapDerivedCategory

set_option linter.defProp false in
/-- The existing universal scalar-extension theorem, including its fixed objects,
fixed maps and K-flat computation. Source: Stacks Tag 06YY
(blueprint: def-weil-pbc-bounded-constructible-tower). -/
abbrev pbcExtensionExistence :=
  completedAdicChangeData X φ

/-- Ordinary sheafified tensor extension, determined on both objects and maps.
Source: Stacks Tag 03EK (blueprint: def-weil-pbc-bounded-constructible-tower). -/
abbrev pbcExtend : pbcModules X R ⥤ pbcModules X S := reductionChange X φ

/-- Tensor extension is additive. Source: Stacks Tag 03EK
(blueprint: def-weil-pbc-bounded-constructible-tower). -/
instance pbcExtend_additive : (pbcExtend φ).Additive :=
  (pbcExtensionExistence φ).choose_spec.choose_spec.choose_spec.choose

set_option linter.defProp false in
/-- The universal derived pair supplied by the existing K-flat scalar-extension theorem.
Source: Stacks Tag 06YY (blueprint: def-weil-pbc-bounded-constructible-tower). -/
@[no_expose] def pbcDerivedExtensionExistence :
    ∃ (LF : DerivedCategory (pbcModules X R) ⥤ DerivedCategory (pbcModules X S))
      (ε : DerivedCategory.Qh ⋙ LF ⟶
        (pbcExtend φ).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh),
      LF.IsLeftDerivedFunctor ε
          (HomotopyCategory.quasiIso (pbcModules X R) (.up ℤ)) ∧
        (∃ (_ : LF.CommShift ℤ), LF.IsTriangulated) ∧
        ∀ P : CochainComplex (pbcModules X R) ℤ,
          CochainComplex.IsKFlatIndependentCoefficients (J := ProEt.topology X) (R := R) P →
          IsIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) :=
  (pbcExtensionExistence φ).choose_spec.choose_spec.choose_spec.choose_spec.2.2

/-- Derived scalar extension, determined up to unique comparison compatible with its
universal counit. Source: Stacks Tag 06YY
(blueprint: def-weil-pbc-bounded-constructible-tower). -/
abbrev pbcDerivedExtend : DerivedCategory (pbcModules X R) ⥤
    DerivedCategory (pbcModules X S) := reductionDerivedChange X φ

/-- The universal comparison, invertible on K-flat complexes.
Source: Stacks Tag 06YY (blueprint: def-weil-pbc-bounded-constructible-tower). -/
def pbcExtensionCounit : DerivedCategory.Qh ⋙ pbcDerivedExtend φ ⟶
    (pbcExtend φ).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh :=
  reductionDerivedCounit X φ

/-- The universal property of the recorded scalar-extension comparison.
Source: Stacks Tag 06YY (blueprint: def-weil-pbc-bounded-constructible-tower). -/
theorem pbcDerivedExtension_universal :
    (pbcDerivedExtend φ).IsLeftDerivedFunctor (pbcExtensionCounit φ)
      (HomotopyCategory.quasiIso (pbcModules X R) (.up ℤ)) :=
  (pbcDerivedExtensionExistence φ).choose_spec.choose_spec.1

/-- The recorded scalar-extension comparison computes tensor on K-flat complexes.
Source: Stacks Tag 06YY (blueprint: def-weil-pbc-bounded-constructible-tower). -/
theorem pbcExtensionCounit_isIso (P : CochainComplex (pbcModules X R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (J := ProEt.topology X) (R := R) P) :
    IsIso ((pbcExtensionCounit φ).app ((HomotopyCategory.quotient _ _).obj P)) :=
  (pbcDerivedExtensionExistence φ).choose_spec.choose_spec.2.2 P hP

/-- A sheafified pure tensor, using the object equality in the scalar-extension witness.
Source: Stacks Tag 03EK (blueprint: def-weil-pbc-bounded-constructible-tower). -/
def pbcTensorSection (M : pbcModules X R) (U : X.ProEtᵒᵖ)
    (s : S.obj.obj U) (x : M.val.obj U) : ((pbcExtend φ).obj M).val.obj U :=
  completedAdicChangeTensor X φ M U s x

/-- The tensor-unit normalized ordinary adjunction is unique.
Source: Stacks Tags 03EK and 06YY (blueprint: def-weil-pbc-bounded-constructible-tower).
Proof: the sheafification universal property and sectionwise tensor adjunction identify
maps out of E(M) with maps M→Res(N), by precomposition with m↦1⊗m. These bijections are
natural. They give the adjunction, and their formula determines it uniquely. -/
theorem pbcScalarAdjunction_exists :
    ∃! adj : pbcExtend φ ⊣ pbcRestrict φ,
      ∀ (M : pbcModules X R) (U : X.ProEtᵒᵖ) (x : M.val.obj U),
        (adj.unit.app M).val.app U x = pbcTensorSection φ M U 1 x := by
  let : HasSheafify (ProEt.topology X) AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbSheafify.{u, 0} X
  let : (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} X
  obtain ⟨adj, hadj⟩ :=
    SheafOfModules.ScalarReductionProof.tensorAdjunction_of_identifications.{u + 1, u, u + 1}
      (K := ProEt.topology X) (A := R) (S := S)
      φ (pbcExtend φ) (pbcExtensionExistence φ).choose_spec.choose
      (pbcExtensionExistence φ).choose_spec.choose_spec.choose
  have hu : ∀ (M : pbcModules X R) (U : X.ProEtᵒᵖ) (x : M.val.obj U),
      (adj.unit.app M).val.app U x = pbcTensorSection φ M U 1 x := by
    intro M U x
    exact hadj M U x
  refine ⟨adj, hu, ?_⟩
  intro adj' hadj'
  apply Adjunction.ext
  ext M U x
  exact (hadj' M U x).trans (hu M U x).symm

/-- The ordinary adjunction with its actual tensor unit.
Source: Stacks Tag 03EK (blueprint: def-weil-pbc-bounded-constructible-tower). -/
def pbcScalarAdjunction : pbcExtend φ ⊣ pbcRestrict φ :=
  (pbcScalarAdjunction_exists φ).exists.choose

/-- The universal derived counit expressed on cochain representatives.
Source: Stacks Tag 06YY (blueprint: def-weil-pbc-bounded-constructible-tower). -/
def pbcComplexCounit (P : CochainComplex (pbcModules X R) ℤ) :
    (pbcDerivedExtend φ).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj (((pbcExtend φ).mapHomologicalComplex (.up ℤ)).obj P) :=
  (pbcDerivedExtend φ).map ((DerivedCategory.quotientCompQhIso _).inv.app P) ≫
    (pbcExtensionCounit φ).app ((HomotopyCategory.quotient _ _).obj P) ≫
    DerivedCategory.Qh.map
      (((pbcExtend φ).mapHomotopyCategoryFactors (.up ℤ)).hom.app P) ≫
    (DerivedCategory.quotientCompQhIso _).hom.app
      (((pbcExtend φ).mapHomologicalComplex (.up ℤ)).obj P)

/-- The derived adjunction is uniquely fixed by its tensor-unit computation on K-flats.
Source: Stacks Tags 06YY and 0DVC (blueprint: def-weil-pbc-bounded-constructible-tower).
Proof: exact restriction has its termwise derived functor. Derive the ordinary adjunction
using K-flat resolutions on the left. Its unit on a K-flat P is the localization of
P→Res(E(P)), transported by the invertible universal counit. Every object has a K-flat
representative; the Hom adjunction and naturality follow from the ordinary bijections
and localization. The formula fixes the unit everywhere and therefore the adjunction. -/
theorem pbcDerivedScalarAdjunction_exists :
    ∃! adj : pbcDerivedExtend φ ⊣ pbcDerivedRestrict φ,
      ∀ (P : CochainComplex (pbcModules X R) ℤ),
        CochainComplex.IsKFlatIndependentCoefficients (J := ProEt.topology X) (R := R) P →
        adj.unit.app (DerivedCategory.Q.obj P) ≫
            (pbcDerivedRestrict φ).map (pbcComplexCounit φ P) ≫
            (pbcRestrict φ).mapDerivedCategoryFactors.hom.app
              (((pbcExtend φ).mapHomologicalComplex (.up ℤ)).obj P) =
          DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex (pbcScalarAdjunction φ).unit (.up ℤ)).app P) := by
  let : HasSheafify (ProEt.topology X) AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbSheafify.{u, 0} X
  let : (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} X
  let : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  exact normalizedDerivedAdjunction (pbcExtend φ) (pbcRestrict φ) (pbcScalarAdjunction φ)
    (CochainComplex.IsKFlatIndependentCoefficients (J := ProEt.topology X) (R := R))
    (ScalarReductionDerivedProof.kFlatResolutions.{u + 1, u, u + 1}
      (J := ProEt.topology X) (O := R))
    (pbcDerivedExtend φ) (pbcExtensionCounit φ)
    (pbcDerivedExtension_universal φ) (pbcExtensionCounit_isIso φ)

/-- Canonical derived scalar extension/restriction adjunction.
Source: Stacks Tag 06YY (blueprint: def-weil-pbc-bounded-constructible-tower). -/
def pbcDerivedScalarAdjunction : pbcDerivedExtend φ ⊣ pbcDerivedRestrict φ :=
  (pbcDerivedScalarAdjunction_exists φ).exists.choose

variable {B : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
  (ψ : S ⟶ B) (χ : R ⟶ B) (h : φ ≫ ψ = χ)

include h in
/-- Composition of ordinary scalar restrictions is identity on underlying sections.
Source: Stacks Tag 03DA (blueprint: def-weil-pbc-bounded-constructible-tower).
Proof: the actions coincide by h; identity on sections is linear and natural, and its
inverse is identity. Sectionwise faithfulness gives uniqueness. -/
theorem pbcRestrictComp_exists :
    ∃! e : pbcRestrict ψ ⋙ pbcRestrict φ ≅ pbcRestrict χ,
      ∀ (M : pbcModules X B) (U : X.ProEtᵒᵖ) (x : M.val.obj U),
        (e.hom.app M).val.app U x = x := by
  have hU (U : X.ProEtᵒᵖ) : (χ.hom.app U).hom =
      (ψ.hom.app U).hom.comp (φ.hom.app U).hom := by
    exact congrArg (fun f : R ⟶ B ↦ (f.hom.app U).hom) h.symm
  let eM (M : pbcModules X B) :
      (pbcRestrict φ).obj ((pbcRestrict ψ).obj M) ≅ (pbcRestrict χ).obj M :=
    (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun U ↦
        (ModuleCat.restrictScalarsComp'App (φ.hom.app U).hom (ψ.hom.app U).hom
          (χ.hom.app U).hom (hU U) (M.val.obj U)).symm)
        (fun {U V} f ↦ by ext x; rfl))
  let e : pbcRestrict ψ ⋙ pbcRestrict φ ≅ pbcRestrict χ :=
    NatIso.ofComponents eM (fun f ↦ by ext U x; rfl)
  refine ⟨e, ?_, ?_⟩
  · intro M U x
    rfl
  · intro e' he'
    apply Iso.ext
    ext M U x
    exact he' M U x

/-- The canonical ordinary restriction comparison.
Source: Stacks Tag 03DA (blueprint: def-weil-pbc-bounded-constructible-tower). -/
def pbcRestrictComp : pbcRestrict ψ ⋙ pbcRestrict φ ≅ pbcRestrict χ :=
  (pbcRestrictComp_exists φ ψ χ h).exists.choose

/-- The already constructed quotient coefficient system; n means positive exponent n+1.
A constant sheaf is canonically also the sheafification of continuous maps from connected
components to the discrete ring: every such function is locally constant on its open
fibres, which form a Zariski, hence pro-etale, cover. Constant sections give the comparison.
Source: blueprint order 1239 (blueprint: def-weil-pbc-bounded-constructible-tower). -/
abbrev pbcAdicRings (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) :=
  AdicCoefficients.ringSystem X d.ideal d.quotientFinite

/-- The completed coefficient sheaf is the actual inverse limit of the quotient sheaves.
Limits of sheaves are sectionwise compatible families, with pointwise operations.
Source: blueprint order 1239 (blueprint: def-weil-pbc-bounded-constructible-tower). -/
abbrev pbcAdicCompletion (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) :=
  AdicCoefficients.completedRing X d.ideal d.quotientFinite

/-- The n-th coordinate of a compatible family in the completed ring.
Source: blueprint order 1239 (blueprint: def-weil-pbc-bounded-constructible-tower). -/
def pbcAdicProjection (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A)
    (n : ℕ) : pbcAdicCompletion X d ⟶ (pbcAdicRings X d).obj (op n) :=
  limit.π (pbcAdicRings X d) (op n)

/-- The quotient continuous-function presheaf with its prescribed discrete topology.
Source: blueprint order 1250 (blueprint: def-weil-pbc-bounded-constructible-tower). -/
def pbcQuotientPresheaf (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (n : ℕ) : X.ProEtᵒᵖ ⥤ CommRingCat.{u + 1} :=
  letI := d.quotientFinite n
  AdicCoefficients.functionPresheaf X (A ⧸ d.ideal ^ (n + 1))

/-- The constant continuous component function used by the coefficient comparison.
Source: blueprint order 1250 (blueprint: def-weil-pbc-bounded-constructible-tower). -/
noncomputable def pbcQuotientConstant (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (n : ℕ)
    (U : X.ProEtᵒᵖ) (b : A ⧸ d.ideal ^ (n + 1))
    (τ : TopologicalSpace (A ⧸ d.ideal ^ (n + 1))) :
    @ContinuousMap (ConnectedComponents U.unop.left) (A ⧸ d.ideal ^ (n + 1))
      inferInstance τ :=
  @ContinuousMap.const (ConnectedComponents U.unop.left) (A ⧸ d.ideal ^ (n + 1))
    inferInstance τ b

/-- The constant-section comparison with the recorded continuous-function coefficient.
Source: blueprint order 1250; Stacks Tags 03CY and 00W1
(blueprint: def-weil-pbc-bounded-constructible-tower).
Proof: send each constant section to the same constant continuous component function.
Its level sets give a Zariski, hence pro-etale, cover. Thus this map is locally bijective
and sheafification makes it an isomorphism. Local constant sections generate, giving
uniqueness even for the empty scheme or zero ring. -/
theorem pbcLevelConstantComparison_exists (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (n : ℕ) :
    ∃! e : adicLisseConstantRing X (A ⧸ d.ideal ^ (n + 1)) ≅
        (pbcAdicRings X d).obj (op n),
      ∀ (U : X.ProEtᵒᵖ) (b : A ⧸ d.ideal ^ (n + 1)),
        e.hom.hom.app U
          ((toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj
            (CommRingCat.of (A ⧸ d.ideal ^ (n + 1))))).app U b) =
          (toSheafify (ProEt.topology X) (pbcQuotientPresheaf X d n)).app U
            (pbcQuotientConstant X d n U b (⊥ : TopologicalSpace (A ⧸ d.ideal ^ (n + 1)))) := by
  let := d.quotientFinite n
  let : TopologicalSpace (A ⧸ d.ideal ^ (n + 1)) := ⊥
  let : DiscreteTopology (A ⧸ d.ideal ^ (n + 1)) := ⟨rfl⟩
  let c := AdicCoefficients.constants X (A ⧸ d.ideal ^ (n + 1))
  let η := toSheafify (ProEt.topology X)
    (AdicCoefficients.functionPresheaf X (A ⧸ d.ideal ^ (n + 1)))
  let cr := Functor.whiskerRight c (forget₂ CommRingCat RingCat)
  let ηr := Functor.whiskerRight η (forget₂ CommRingCat RingCat)
  let eR := AdicCoefficients.finiteRingComparison X (A ⧸ d.ideal ^ (n + 1))
  have hη : ηr ≫ eR.hom.hom = AdicCoefficients.finiteRingUnit X
      (A ⧸ d.ideal ^ (n + 1)) :=
    (AdicCoefficients.finiteRingComparison_exists X
      (A ⧸ d.ideal ^ (n + 1))).choose_spec.1.2
  have hiη : Presheaf.IsLocallyInjective (ProEt.topology X) ηr :=
    (Presheaf.isLocallyInjective_forget_iff (ProEt.topology X) ηr).mp
      ((Presheaf.isLocallyInjective_forget_iff (ProEt.topology X) η).mpr inferInstance)
  have hsη : Presheaf.IsLocallySurjective (ProEt.topology X) ηr :=
    (Presheaf.isLocallySurjective_iff_whisker_forget (ProEt.topology X) ηr).mpr
      ((Presheaf.isLocallySurjective_iff_whisker_forget (ProEt.topology X) η).mp
        inferInstance)
  have hcr : cr ≫ ηr ≫ eR.hom.hom = ProEtale.finiteCoefficientScalarMap X
      (A ⧸ d.ideal ^ (n + 1)) := by
    rw [hη]
    rfl
  have hir : Presheaf.IsLocallyInjective (ProEt.topology X) cr := by
    have hi : Presheaf.IsLocallyInjective (ProEt.topology X) (cr ≫ ηr ≫ eR.hom.hom) := by
      rw [hcr]
      exact (ProEtale.finiteCoefficientScalarMap_locallyBijective X
        (A ⧸ d.ideal ^ (n + 1))).1
    exact Presheaf.isLocallyInjective_of_isLocallyInjective
      (ProEt.topology X) cr (ηr ≫ eR.hom.hom)
  have hsr : Presheaf.IsLocallySurjective (ProEt.topology X) cr := by
    have hs : Presheaf.IsLocallySurjective (ProEt.topology X) (cr ≫ ηr ≫ eR.hom.hom) := by
      rw [hcr]
      exact (ProEtale.finiteCoefficientScalarMap_locallyBijective X
        (A ⧸ d.ideal ^ (n + 1))).2
    exact Presheaf.isLocallySurjective_of_isLocallySurjective_of_isLocallyInjective
      (ProEt.topology X) cr (ηr ≫ eR.hom.hom)
  have hi : Presheaf.IsLocallyInjective (ProEt.topology X) c :=
    (Presheaf.isLocallyInjective_forget_iff (ProEt.topology X) c).mp
      ((Presheaf.isLocallyInjective_forget_iff (ProEt.topology X) cr).mpr hir)
  have hs : Presheaf.IsLocallySurjective (ProEt.topology X) c :=
    (Presheaf.isLocallySurjective_iff_whisker_forget (ProEt.topology X) c).mpr
      ((Presheaf.isLocallySurjective_iff_whisker_forget (ProEt.topology X) cr).mp hsr)
  have hc : IsIso (AdicCoefficients.constantComparison X
      (A ⧸ d.ideal ^ (n + 1))) :=
    ((ProEt.topology X).W_iff c).mp
      (((ProEt.topology X).W_iff_isLocallyBijective c).mpr ⟨hi, hs⟩)
  let e := asIso (AdicCoefficients.constantComparison X (A ⧸ d.ideal ^ (n + 1)))
  have he (U : X.ProEtᵒᵖ) (b : A ⧸ d.ideal ^ (n + 1)) :
      e.hom.hom.app U
        ((toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj
          (CommRingCat.of (A ⧸ d.ideal ^ (n + 1))))).app U b) =
      (toSheafify (ProEt.topology X) (pbcQuotientPresheaf X d n)).app U
        (pbcQuotientConstant X d n U b ⊥) := by
    exact ConcreteCategory.congr_hom (congr_app (toSheafify_naturality
      (ProEt.topology X) c) U) b |>.symm
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Iso.ext
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _ ((pbcAdicRings X d).obj (op n)).property
  ext U b
  exact (he' U b).trans (he U b).symm

/-- The canonical finite coefficient identification, fixed on constant sections.
Source: blueprint order 1250 (blueprint: def-weil-pbc-bounded-constructible-tower). -/
def pbcLevelConstantComparison (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (n : ℕ) :
    adicLisseConstantRing X (A ⧸ d.ideal ^ (n + 1)) ≅ (pbcAdicRings X d).obj (op n) :=
  (pbcLevelConstantComparison_exists X d n).exists.choose

/-- Constant comparisons intertwine the entire recorded quotient diagram.
Source: blueprint order 1250 (blueprint: def-weil-pbc-bounded-constructible-tower).
Proof: on constant sections both routes apply the same quotient homomorphism.
Local generation gives the equality at consecutive indices. Every poset arrow is a
composite of consecutive arrows, so induction gives the result for all indices. -/
theorem pbcConstantSystemComparison_naturality (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A)
    {m n : ℕᵒᵖ} (f : m ⟶ n) :
    (adicLisseRingSystem X d.ideal).map f ≫
        (pbcLevelConstantComparison X d n.unop).hom =
      (pbcLevelConstantComparison X d m.unop).hom ≫
        (pbcAdicRings X d).map f := by
  let := d.quotientFinite
  have he (k : ℕ) : (pbcLevelConstantComparison X d k).hom =
      AdicCoefficients.constantComparison X (A ⧸ d.ideal ^ (k + 1)) := by
    apply Sheaf.hom_ext
    apply sheafify_hom_ext _ _ _ ((pbcAdicRings X d).obj (op k)).property
    change toSheafify _ _ ≫ (pbcLevelConstantComparison X d k).hom.hom =
      toSheafify _ _ ≫ sheafifyMap _ _
    rw [← toSheafify_naturality]
    ext U b
    exact (pbcLevelConstantComparison_exists X d k).exists.choose_spec U b
  let t : adicLisseRingSystem X d.ideal ⟶ pbcAdicRings X d :=
    NatTrans.ofOpSequence (fun k ↦ (pbcLevelConstantComparison X d k).hom) (fun k ↦ by
      simp only [adicLisseRingSystem, pbcAdicRings, AdicCoefficients.ringSystem,
        Functor.ofOpSequence_map_homOfLE_succ]
      rw [he k, he (k + 1)]
      change (presheafToSheaf _ CommRingCat).map _ ≫
          (presheafToSheaf _ CommRingCat).map _ =
        (presheafToSheaf _ CommRingCat).map _ ≫
          (presheafToSheaf _ CommRingCat).map _
      rw [← Functor.map_comp, ← Functor.map_comp]
      congr 1)
  exact t.naturality f

/-- The comparison of constant and continuous-function quotient coefficient diagrams.
Source: blueprint order 1250 (blueprint: def-weil-pbc-bounded-constructible-tower). -/
def pbcConstantSystemComparison (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) :
    adicLisseRingSystem X d.ideal ≅ AdicCoefficients.ringSystem X d.ideal d.quotientFinite :=
  NatIso.ofComponents (fun n ↦ pbcLevelConstantComparison X d n.unop)
    (fun f ↦ pbcConstantSystemComparison_naturality X d f)

/-- The completed-coefficient comparison is induced by the quotient diagram.
No completed coefficient sheaf is identified with a constant sheaf.
Source: blueprint order 1250 (blueprint: def-weil-pbc-bounded-constructible-tower). -/
def pbcCompletedComparison (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) :
    adicLisseCompletedRing X d.ideal ≅ pbcAdicCompletion X d :=
  HasLimit.isoOfNatIso (pbcConstantSystemComparison X d)

variable (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
  (d : AdicCoefficientDatum A)

variable {X} {Y : Scheme.{u}} (g : Y ⟶ X)

/-- Restrict any coefficient sheaf by its actual inverse image along the scheme map.
Source: blueprint order 1250 (blueprint: def-weil-pbc-bounded-constructible-tower). -/
abbrev adicTowerInverseImage := proEtaleSheafInverseImage g CommRingCat.{u + 1}

/-- Exact derived inverse image with exactly the inverse-image coefficient sheaf.
Source: blueprint order 1250 (blueprint: def-weil-pbc-bounded-constructible-tower). -/
abbrev adicTowerPullback (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :=
  proEtaleRingDerivedPullback g R ((adicTowerInverseImage g).obj R) (Iso.refl _)

end AlgebraicGeometry.Scheme
