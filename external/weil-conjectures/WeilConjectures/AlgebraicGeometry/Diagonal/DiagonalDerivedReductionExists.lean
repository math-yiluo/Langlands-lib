/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerSystemInterface
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Homology.Functor
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import all WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
import all WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import all Mathlib.CategoryTheory.Adjunction.Additive
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import all WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.CategoryTheory.Limits.Final
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.CategoryTheory.RingObjects.Ab
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-! # Simultaneous derived reduction of integral sheaves

Source: blueprint diagonal tower proof step 3; Stacks Tags 06XN and 06YY.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u uA vA uB vB a b c d w t v
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite MonoidalCategory
namespace AlgebraicGeometry.ProEtale

private def reductionLevel {B : Type uB} [Category.{vB} B] [Abelian B]
    (ℓ n : ℕ) : B ⥤ B where
  obj M := cokernel (ℓ ^ (n + 1) • 𝟙 M)
  map {M N} f := cokernel.map _ _ f f (by
    simp only [Preadditive.nsmul_comp, Preadditive.comp_nsmul,
      Category.id_comp, Category.comp_id])
  map_id M := by
    apply (cancel_epi (cokernel.π _)).1
    simp [cokernel.map]
  map_comp f g := by
    apply (cancel_epi (cokernel.π _)).1
    simp [cokernel.map]

private def reductionLevelTransition {B : Type uB} [Category.{vB} B] [Abelian B]
    (ℓ n : ℕ) : reductionLevel (B := B) ℓ (n + 1) ⟶ reductionLevel ℓ n where
  app M := cokernel.desc _ (cokernel.π (ℓ ^ (n + 1) • 𝟙 M)) (by
    change (ℓ ^ (n + 1 + 1) • 𝟙 M) ≫
      cokernel.π (ℓ ^ (n + 1) • 𝟙 M) = 0
    have hp : ℓ ^ (n + 1 + 1) • 𝟙 M = ℓ • (ℓ ^ (n + 1) • 𝟙 M) := by
      rw [← mul_nsmul, pow_succ]
    rw [hp, Preadditive.nsmul_comp, cokernel.condition, smul_zero])
  naturality {M N} f := by
    apply (cancel_epi (cokernel.π _)).1
    simp [reductionLevel, cokernel.map, Category.assoc]

private def reductionTower {B : Type uB} [Category.{vB} B] [Abelian B]
    (ℓ : ℕ) : B ⥤ (ℕᵒᵖ ⥤ B) :=
  (Functor.ofOpSequence (X := fun n ↦ reductionLevel (B := B) ℓ n)
    (reductionLevelTransition ℓ)).flip

private theorem reductionTower_additive {B : Type uB} [Category.{vB} B] [Abelian B]
    (ℓ : ℕ) : (reductionTower (B := B) ℓ).Additive where
  map_add {M N} f g := by
    ext n
    apply (cancel_epi (cokernel.π _)).1
    simp only [reductionTower, Functor.flip_map_app, NatTrans.app_add,
      Preadditive.comp_add]
    change cokernel.π _ ≫ (reductionLevel ℓ n.unop).map (f + g) =
      cokernel.π _ ≫ (reductionLevel ℓ n.unop).map f +
        cokernel.π _ ≫ (reductionLevel ℓ n.unop).map g
    simp [reductionLevel, cokernel.map]

private def reductionPresentation {A : Type uA} [Category.{vA} A] [Abelian A]
    {B : Type uB} [Category.{vB} B] [Abelian B]
    (ℓ : ℕ) (L : A ⥤ B) [L.Additive] : DiagonalReductionPresentation ℓ L := by
  let := reductionTower_additive (B := B) ℓ
  refine {
    E := L ⋙ reductionTower ℓ
    π := fun n ↦ {
      app := fun M ↦ cokernel.π (ℓ ^ (n + 1) • 𝟙 (L.obj M))
      naturality := fun _ _ f ↦ by
        change L.map f ≫ cokernel.π _ =
          cokernel.π _ ≫ (reductionLevel ℓ n).map (L.map f)
        simp [reductionLevel, cokernel.map] }
    zero := fun n M ↦ cokernel.condition _
    quotient := fun n M ↦ cokernelIsCokernel _
    transition := ?_ }
  intro n M
  change cokernel.π _ ≫
    ((Functor.ofOpSequence (X := fun n ↦ reductionLevel (B := B) ℓ n)
      (reductionLevelTransition ℓ)).map (homOfLE (Nat.le_succ n)).op).app (L.obj M) = _
  rw [Functor.ofOpSequence_map_homOfLE_succ]
  exact cokernel.π_desc _ _ _

private def reductionComplexSequence
    {A : Type uA} [Category.{vA} A] [Abelian A]
    {B : Type uB} [Category.{vB} B] [Abelian B]
    (ℓ : ℕ) (L : A ⥤ B) [L.Additive]
    (O : DiagonalReductionPresentation ℓ L) (n : ℕ) (P : CochainComplex A ℤ) :
    ShortComplex (CochainComplex B ℤ) :=
  ShortComplex.mk (ℓ ^ (n + 1) • 𝟙 ((L.mapHomologicalComplex (.up ℤ)).obj P))
    ((NatTrans.mapHomologicalComplex (O.π n) (.up ℤ)).app P) (by
      ext i
      exact O.zero n (P.X i))

private theorem reductionComplexSequence_shortExact
    {A : Type uA} [Category.{vA} A] [Abelian A]
    {B : Type uB} [Category.{vB} B] [Abelian B]
    (ℓ : ℕ) (L : A ⥤ B) [L.Additive]
    (O : DiagonalReductionPresentation ℓ L) (n : ℕ) (P : CochainComplex A ℤ)
    (hP : ∀ i : ℤ, Mono (ℓ ^ (n + 1) • 𝟙 (L.obj (P.X i)))) :
    (reductionComplexSequence ℓ L O n P).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  have : Mono (ℓ ^ (n + 1) • 𝟙 (L.obj (P.X i))) := hP i
  have : Epi ((O.π n).app (P.X i)) := Cofork.IsColimit.epi (O.quotient n (P.X i))
  have hs : (ShortComplex.mk (ℓ ^ (n + 1) • 𝟙 (L.obj (P.X i)))
      ((O.π n).app (P.X i)) (O.zero n (P.X i))).ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _ (O.quotient n (P.X i)) }
  convert! hs using 1

private theorem reductionLevel_quasiIso
    {A : Type uA} [Category.{vA} A] [Abelian A]
    {B : Type uB} [Category.{vB} B] [Abelian B]
    (ℓ : ℕ) (L : A ⥤ B) [L.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (O : DiagonalReductionPresentation ℓ L) (n : ℕ)
    {P P' : CochainComplex A ℤ} (f : P ⟶ P') [QuasiIso f]
    (hP : ∀ i : ℤ, Mono (ℓ ^ (n + 1) • 𝟙 (L.obj (P.X i))))
    (hP' : ∀ i : ℤ, Mono (ℓ ^ (n + 1) • 𝟙 (L.obj (P'.X i)))) :
    QuasiIso (((O.E ⋙ (evaluation ℕᵒᵖ B).obj (op n)).mapHomologicalComplex (.up ℤ)).map f) := by
  let φ : reductionComplexSequence ℓ L O n P ⟶
      reductionComplexSequence ℓ L O n P' := {
    τ₁ := (L.mapHomologicalComplex (.up ℤ)).map f
    τ₂ := (L.mapHomologicalComplex (.up ℤ)).map f
    τ₃ := ((O.E ⋙ (evaluation ℕᵒᵖ B).obj (op n)).mapHomologicalComplex (.up ℤ)).map f
    comm₁₂ := by simp [reductionComplexSequence]
    comm₂₃ := (NatTrans.mapHomologicalComplex (O.π n) (.up ℤ)).naturality f }
  exact HomologicalComplex.HomologySequence.quasiIso_τ₃ φ
    (reductionComplexSequence_shortExact ℓ L O n P hP)
    (reductionComplexSequence_shortExact ℓ L O n P' hP') inferInstance inferInstance

private theorem reductionTower_quasiIso
    {A : Type uA} [Category.{vA} A] [Abelian A]
    {B : Type uB} [Category.{vB} B] [Abelian B]
    (ℓ : ℕ) (L : A ⥤ B) [L.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (O : DiagonalReductionPresentation ℓ L)
    {P P' : CochainComplex A ℤ} (f : P ⟶ P') [QuasiIso f]
    (hP : ∀ n : ℕ, ∀ i : ℤ, Mono (ℓ ^ (n + 1) • 𝟙 (L.obj (P.X i))))
    (hP' : ∀ n : ℕ, ∀ i : ℤ, Mono (ℓ ^ (n + 1) • 𝟙 (L.obj (P'.X i)))) :
    QuasiIso ((O.E.mapHomologicalComplex (.up ℤ)).map f) := by
  rw [HomologicalComplex.quasiIso_iff_evaluation]
  intro n
  exact reductionLevel_quasiIso ℓ L O n.unop f (hP n.unop) (hP' n.unop)

open CategoryTheory.Functor in
private theorem cochainDerivedFullExists
    {A : Type a} [Category.{b} A] [Abelian A] [HasDerivedCategory.{w} A]
    {B : Type c} [Category.{d} B] [Abelian B] [HasDerivedCategory.{t} B]
    (E : A ⥤ B) [E.Additive] (good : CochainComplex A ℤ → Prop)
    (res : ∀ K, ∃ (L : CochainComplex A ℤ) (p : L ⟶ K), good L ∧ QuasiIso p)
    (inverts : ∀ {K L : CochainComplex A ℤ} (p : K ⟶ L), QuasiIso p →
      good K → good L → QuasiIso ((E.mapHomologicalComplex (.up ℤ)).map p)) :
    ∃ (T : DerivedCategory A ⥤ DerivedCategory B)
      (β : DerivedCategory.Q ⋙ T ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q),
      T.IsLeftDerivedFunctor β (HomologicalComplex.quasiIso A (.up ℤ)) ∧
      (E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q).HasPointwiseLeftDerivedFunctor
        (HomologicalComplex.quasiIso A (.up ℤ)) ∧
      (∃ (_ : T.CommShift ℤ), T.IsTriangulated) ∧
      ∀ K, good K → IsIso (β.app K) := by
  classical
  let q := HomotopyCategory.quotient A (.up ℤ)
  let F := E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh (C := B)
  let P : Set (HomotopyCategory A (.up ℤ)) := fun X ↦
    ∃ K : CochainComplex A ℤ, good K ∧ q.obj K = X
  have hres : ∀ X : HomotopyCategory A (.up ℤ),
      ∃ (Y : HomotopyCategory A (.up ℤ)) (s : Y ⟶ X),
        Y ∈ P ∧ HomotopyCategory.quasiIso A (.up ℤ) s := by
    intro X
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    obtain ⟨L, p, hL, hp⟩ := res K
    exact ⟨q.obj L, q.map p, ⟨L, hL, rfl⟩,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff p).2 hp⟩
  have hinv : ∀ (X Y : HomotopyCategory A (.up ℤ)) (s : X ⟶ Y),
      X ∈ P → Y ∈ P → HomotopyCategory.quasiIso A (.up ℤ) s → IsIso (F.map s) := by
    rintro X Y s ⟨K, hK, rfl⟩ ⟨L, hL, rfl⟩ hs
    obtain ⟨a, rfl⟩ := q.map_surjective s
    have ha := (HomotopyCategory.quotient_map_mem_quasiIso_iff a).1 hs
    have hg := inverts a ha hK hL
    exact Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso B (.up ℤ)) _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 hg)
  obtain ⟨hpw, T, ε, huniv, htri, hcomp⟩ :=
    Functor.leftDerived_from_resolvingClass A (DerivedCategory B) F P hres hinv
  let : F.HasPointwiseLeftDerivedFunctor (HomotopyCategory.quasiIso A (.up ℤ)) := hpw
  let : T.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso A (.up ℤ)) := huniv
  let α := (Functor.associator q DerivedCategory.Qh T).hom ≫ Functor.whiskerLeft q ε
  have hα := pointwise_precomp_full q DerivedCategory.Qh F T ε
    (Functor.isPointwiseRightKanExtensionOfHasPointwiseLeftDerivedFunctor T ε
      (HomotopyCategory.quasiIso A (.up ℤ)))
  let iq := DerivedCategory.quotientCompQhIso A
  let jq : q ⋙ F ≅ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (E.mapHomotopyCategoryFactors (.up ℤ)) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso B)
  let β : DerivedCategory.Q ⋙ T ⟶
      E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    Functor.whiskerRight iq.inv T ≫ α ≫ jq.hom
  have hβ := pointwise_change_iso T iq jq α hα
  have huni : T.IsLeftDerivedFunctor β (HomologicalComplex.quasiIso A (.up ℤ)) :=
    ⟨hβ.isRightKanExtension⟩
  let := huni
  refine ⟨T, β, huni, ?_, htri, ?_⟩
  · intro X
    exact (Functor.hasPointwiseLeftDerivedFunctorAt_iff
      (E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) DerivedCategory.Q
        (HomologicalComplex.quasiIso A (.up ℤ)) X).2
      ((hβ _).hasPointwiseRightKanExtensionAt)
  · intro K hK
    have := hcomp (q.obj K) ⟨K, hK, rfl⟩
    dsimp [β, α]
    infer_instance

private theorem integerUnit_mono (W : Scheme.{u}) (n : ℕ) (hn : n ≠ 0) :
    Mono (n • 𝟙 (𝟙_ (Sheaf (Scheme.ProEt.topology W) AddCommGrpCat.{u + 1}))) := by
  have hm : Mono (n • 𝟙 (AddCommGrpCat.of (ULift.{u + 1} ℤ))) := by
    rw [AddCommGrpCat.mono_iff_injective]
    intro x y h
    change n • x = n • y at h
    exact ULift.ext (nsmul_right_injective hn (congrArg ULift.down h))
  have hm' : Mono (n • 𝟙 ((constantSheaf (Scheme.ProEt.topology W)
      AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))) := by
    have : Mono ((Functor.const W.ProEtᵒᵖ).map
        (n • 𝟙 (AddCommGrpCat.of (ULift.{u + 1} ℤ)))) := NatTrans.mono_of_mono_app _
    have : Mono ((presheafToSheaf (Scheme.ProEt.topology W) AddCommGrpCat.{u + 1}).map
        ((Functor.const W.ProEtᵒᵖ).map
          (n • 𝟙 (AddCommGrpCat.of (ULift.{u + 1} ℤ))))) := inferInstance
    simpa only [constantSheaf, Functor.comp_obj, CategoryTheory.Functor.map_nsmul,
      CategoryTheory.Functor.map_id]
      using this
  exact hm'

private theorem flat_multiplication_mono
    {A : Type*} [Category A] [Abelian A]
    [MonoidalCategory A] [MonoidalPreadditive A]
    (n : ℕ) (hunit : Mono (n • 𝟙 (𝟙_ A)))
    (M : A) (hM : ObjectProperty.flat M) : Mono (n • 𝟙 M) := by
  let F := tensorRight M
  have : PreservesFiniteLimits F := hM.2.1
  have : Mono (F.map (n • 𝟙 (𝟙_ A))) := inferInstance
  have hm : Mono (n • 𝟙 (F.obj (𝟙_ A))) := by
    simpa only [CategoryTheory.Functor.map_nsmul, CategoryTheory.Functor.map_id] using this
  have he : (n • 𝟙 M) ≫ (leftUnitor M).inv =
      (leftUnitor M).inv ≫ (n • 𝟙 (F.obj (𝟙_ A))) := by
    simp only [Preadditive.nsmul_comp, Preadditive.comp_nsmul,
      Category.id_comp]
    erw [Category.comp_id]
  exact mono_of_mono_fac he

private theorem extendScalars_exact
    {R : Type u} [CommRing R] {S : Type v} [CommRing S]
    (f : R →+* S) (hf : f.Flat) :
    PreservesFiniteLimits (ModuleCat.extendScalars.{u, v, max v w} f) := by
  have : (ModuleCat.extendScalars.{u, v, max v w} f).Additive :=
    (ModuleCat.extendRestrictScalarsAdj f).left_adjoint_additive
  let : Algebra R S := f.toAlgebra
  have : Module.Flat R S := hf
  rw [Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono]
  intro T hT
  have := hT.epi_g
  refine ⟨hT.exact.map_of_epi_of_preservesCokernel _ hT.epi_g inferInstance, ?_⟩
  rw [ModuleCat.mono_iff_injective]
  change Function.Injective (LinearMap.lTensor S T.f.hom)
  exact Module.Flat.lTensor_preserves_injective_linearMap T.f.hom
    ((ModuleCat.mono_iff_injective T.f).1 hT.mono_f)
private theorem padicExtension_exact (ℓ : ℕ) [Fact ℓ.Prime] :
    PreservesFiniteLimits (ModuleCat.extendScalars.{0, u + 1, u + 1}
      (Int.castRingHom (ULift.{u + 1} ℤ_[ℓ]))) := by
  apply extendScalars_exact.{0, u + 1, u + 1}
  change (algebraMap ℤ (ULift.{u + 1} ℤ_[ℓ])).Flat
  rw [RingHom.flat_algebraMap_iff]
  infer_instance

private theorem scalarExtension_exact (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u}) :
    PreservesFiniteLimits (diagonalScalarExtension ℓ W) := by
  have := padicExtension_exact ℓ
  let F := (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).inv ⋙
    ModuleCat.extendScalars (Int.castRingHom (ULift.{u + 1} ℤ_[ℓ]))
  have : PreservesFiniteLimits ((Functor.whiskeringRight W.ProEtᵒᵖ
      AddCommGrpCat.{u + 1} (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[ℓ]))).obj F) :=
    preservesFiniteLimits_of_evaluation _ (fun U ↦
      inferInstanceAs (PreservesFiniteLimits
        ((evaluation W.ProEtᵒᵖ AddCommGrpCat.{u + 1}).obj U ⋙ F)))
  dsimp only [diagonalScalarExtension]
  infer_instance

private theorem scalarExtension_additive (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u}) :
    (diagonalScalarExtension ℓ W).Additive := by
  have := scalarExtension_exact ℓ W
  exact Functor.additive_of_preserves_binary_products _

private theorem derivedReductionForExactExtension
    (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u})
    [HasDerivedCategory.{u + 1} (DiagonalAb W)]
    {B : Type uB} [Category.{vB} B] [Abelian B]
    [HasDerivedCategory.{t} (ℕᵒᵖ ⥤ B)]
    (L : DiagonalAb W ⥤ B) [L.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L] :
    ∃ D : DiagonalDerivedReduction ℓ L,
      ∀ P : CochainComplex (DiagonalAb W) ℤ,
        (∀ (n : ℕ) (i : ℤ), Mono (ℓ ^ (n + 1) • 𝟙 (P.X i))) →
          IsIso (D.ε.app P) := by
  let O := reductionPresentation ℓ L
  let good : CochainComplex (DiagonalAb W) ℤ → Prop := fun P ↦
    ∀ (n : ℕ) (i : ℤ), Mono (ℓ ^ (n + 1) • 𝟙 (P.X i))
  have res : ∀ K : CochainComplex (DiagonalAb W) ℤ,
      ∃ (P : CochainComplex (DiagonalAb W) ℤ) (π : P ⟶ K), good P ∧ QuasiIso π := by
    intro K
    obtain ⟨P, π, hπ, hflat, _⟩ := CochainComplex.exists_quasiIso_flat_kFlat K
    refine ⟨P, π, ?_, hπ⟩
    intro n i
    exact flat_multiplication_mono _
      (integerUnit_mono W _ (pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero)) _ (hflat i)
  have hmono (P : CochainComplex (DiagonalAb W) ℤ) (hP : good P) (n : ℕ) (i : ℤ) :
      Mono (ℓ ^ (n + 1) • 𝟙 (L.obj (P.X i))) := by
    have : Mono (ℓ ^ (n + 1) • 𝟙 (P.X i)) := hP n i
    have hm : Mono (L.map (ℓ ^ (n + 1) • 𝟙 (P.X i))) := inferInstance
    simpa only [CategoryTheory.Functor.map_nsmul, CategoryTheory.Functor.map_id] using hm
  obtain ⟨T, β, hu, hp, ht, hc⟩ := cochainDerivedFullExists O.E good res (by
    intro P P' f hf hP hP'
    let : QuasiIso f := hf
    exact reductionTower_quasiIso ℓ L O f (hmono P hP) (hmono P' hP'))
  refine ⟨{ ordinary := O, T := T, ε := β, universal := hu
            pointwise := hp, triangulated := ht }, hc⟩

/-- The ordinary quotient tower has an everywhere-defined pointwise, triangulated
left derived functor, computed by every complex whose positive prime-power maps
are degreewise monomorphisms. Source: blueprint diagonal tower proof step 3, Stacks 06XN,
06YY (blueprint: lem-sfb-diagonal-derived-reduction-exists).
Proof: construct each level as the cokernel of multiplication by the positive prime
power, with quotient transitions. A complex of flat sheaves has injective scalar
multiplications, including after the exact extension to Z_l. The corresponding short
exact sequences show that reduction preserves quasi-isomorphisms between these
complexes. Flat-term resolutions give the resolving class. The resolving-class theorem
constructs a triangulated pointwise left derived pair; full essential surjectivity of
the homotopy quotient transfers its universal comparison to cochain complexes. -/
theorem exists_diagonalDerivedReduction (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u})
    [HasDerivedCategory.{u + 1} (DiagonalAb W)]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ W)]
    [HasDerivedCategory.{u + 1} (ℕᵒᵖ ⥤ DiagonalAb W)] :
    ∃ (D : DiagonalDerivedReduction ℓ (diagonalScalarExtension ℓ W))
      (I : DiagonalDerivedReduction ℓ (𝟭 (DiagonalAb W))),
      (∀ P : CochainComplex (DiagonalAb W) ℤ,
        (∀ (n : ℕ) (i : ℤ), Mono (ℓ ^ (n + 1) • 𝟙 (P.X i))) →
          IsIso (D.ε.app P)) ∧
      (∀ P : CochainComplex (DiagonalAb W) ℤ,
        (∀ (n : ℕ) (i : ℤ), Mono (ℓ ^ (n + 1) • 𝟙 (P.X i))) →
          IsIso (I.ε.app P)) := by
  have : PreservesFiniteLimits (diagonalScalarExtension ℓ W) := scalarExtension_exact ℓ W
  have : PreservesFiniteColimits (diagonalScalarExtension ℓ W) := by
    have := (diagonalScalarAdjunction ℓ W).leftAdjoint_preservesColimits
    infer_instance
  have : (diagonalScalarExtension ℓ W).Additive := scalarExtension_additive ℓ W
  obtain ⟨D, hD⟩ := derivedReductionForExactExtension ℓ W (diagonalScalarExtension ℓ W)
  obtain ⟨I, hI⟩ := derivedReductionForExactExtension ℓ W (𝟭 (DiagonalAb W))
  exact ⟨D, I, hD, hI⟩

end AlgebraicGeometry.ProEtale
