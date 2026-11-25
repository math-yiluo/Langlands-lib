/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Weil.WeilCompletedKoszulSite
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.AlgebraicGeometry.Weil.WeilCompletedConstantModuleTensor
import WeilConjectures.AlgebraicGeometry.Weil.WeilCompletedModuleTensorTransport
import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement

/-! # Tensor comparison for completed constant realization

Source: Stacks Project, Modules on Sites, Tags 03D8, 03EK and 0GMW.
(blueprint: lem-weil-pbc-completed-realization-tensor).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

private def composeTensorIso
    {B C D : Type*} [Category* B] [Category* C] [Category* D]
    [MonoidalCategory B] [MonoidalCategory C] [MonoidalCategory D]
    (G : B ⥤ C) (F : C ⥤ D)
    (σ : (Functor.postcompose₂.obj G).obj (curriedTensor B) ≅
      (((Functor.whiskeringLeft₂ C).obj G).obj G).obj (curriedTensor C))
    (τ : (Functor.postcompose₂.obj F).obj (curriedTensor C) ≅
      (((Functor.whiskeringLeft₂ D).obj F).obj F).obj (curriedTensor D)) :
    (Functor.postcompose₂.obj (G ⋙ F)).obj (curriedTensor B) ≅
      (((Functor.whiskeringLeft₂ D).obj (G ⋙ F)).obj (G ⋙ F)).obj (curriedTensor D) :=
  NatIso.ofComponents (fun M ↦ NatIso.ofComponents
    (fun N ↦ F.mapIso ((σ.app M).app N) ≪≫ (τ.app (G.obj M)).app (G.obj N)) (by
      intro N N' g
      change F.map (G.map (M ◁ g)) ≫
        (F.map ((σ.hom.app M).app N') ≫ (τ.hom.app (G.obj M)).app (G.obj N')) =
          (F.map ((σ.hom.app M).app N) ≫ (τ.hom.app (G.obj M)).app (G.obj N)) ≫
            F.obj (G.obj M) ◁ F.map (G.map g)
      have hσ := (σ.hom.app M).naturality g
      change G.map (M ◁ g) ≫ (σ.hom.app M).app N' =
        (σ.hom.app M).app N ≫ G.obj M ◁ G.map g at hσ
      have hτ := (τ.hom.app (G.obj M)).naturality (G.map g)
      change F.map (G.obj M ◁ G.map g) ≫ (τ.hom.app (G.obj M)).app (G.obj N') =
        (τ.hom.app (G.obj M)).app (G.obj N) ≫ F.obj (G.obj M) ◁ F.map (G.map g) at hτ
      rw [← F.map_comp_assoc, hσ, F.map_comp, Category.assoc, hτ]
      simp only [Category.assoc])) (by
        intro M M' f
        apply NatTrans.ext
        funext N
        change F.map (G.map (f ▷ N)) ≫
          (F.map ((σ.hom.app M').app N) ≫ (τ.hom.app (G.obj M')).app (G.obj N)) =
            (F.map ((σ.hom.app M).app N) ≫ (τ.hom.app (G.obj M)).app (G.obj N)) ≫
              F.map (G.map f) ▷ F.obj (G.obj N)
        have hσ := congr_app (σ.hom.naturality f) N
        change G.map (f ▷ N) ≫ (σ.hom.app M').app N =
          (σ.hom.app M).app N ≫ G.map f ▷ G.obj N at hσ
        have hτ := congr_app (τ.hom.naturality (G.map f)) (G.obj N)
        change F.map (G.map f ▷ G.obj N) ≫ (τ.hom.app (G.obj M')).app (G.obj N) =
          (τ.hom.app (G.obj M)).app (G.obj N) ≫ F.map (G.map f) ▷ F.obj (G.obj N) at hτ
        rw [← F.map_comp_assoc, hσ, F.map_comp, Category.assoc, hτ]
        simp only [Category.assoc])

private theorem tensorIsoNaturality
    {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D)
    (τ : (Functor.postcompose₂.obj F).obj (curriedTensor C) ≅
      (((Functor.whiskeringLeft₂ D).obj F).obj F).obj (curriedTensor D))
    {M N M' N' : C} (f : M ⟶ M') (g : N ⟶ N') :
    F.map (f ⊗ₘ g) ≫ (τ.hom.app M').app N' =
      (τ.hom.app M).app N ≫ (F.map f ⊗ₘ F.map g) := by
  have h₁ := congr_app (τ.hom.naturality f) N
  change F.map (f ▷ N) ≫ (τ.hom.app M').app N =
    (τ.hom.app M).app N ≫ F.map f ▷ F.obj N at h₁
  have h₂ := (τ.hom.app M').naturality g
  change F.map (M' ◁ g) ≫ (τ.hom.app M').app N' =
    (τ.hom.app M').app N ≫ F.obj M' ◁ F.map g at h₂
  simp only [tensorHom_def, F.map_comp, Category.assoc]
  rw [h₂]
  simpa only [Category.assoc] using
    congrArg (fun k ↦ k ≫ F.obj M' ◁ F.map g) h₁

private theorem regularTensorNormalization
    {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D)
    (τ : (Functor.postcompose₂.obj F).obj (curriedTensor C) ≅
      (((Functor.whiskeringLeft₂ D).obj F).obj F).obj (curriedTensor D))
    (c : 𝟙_ D ⟶ F.obj (𝟙_ C))
    (hτ : ∀ M, F.map (ρ_ M).inv ≫ (τ.hom.app M).app (𝟙_ C) =
      (ρ_ (F.obj M)).inv ≫ F.obj M ◁ c) :
    c ≫ F.map (λ_ (𝟙_ C)).inv ≫ (τ.hom.app (𝟙_ C)).app (𝟙_ C) =
      (λ_ (𝟙_ D)).inv ≫ (c ⊗ₘ c) := by
  rw [unitors_inv_equal, hτ, rightUnitor_inv_naturality_assoc]
  rw [← tensorHom_def, ← unitors_inv_equal]

private theorem totalTensorMap_eq
    {D : Type*} [Category* D] [Preadditive D] [MonoidalCategory D]
    [(curriedTensor D).PreservesZeroMorphisms]
    [∀ M, ((curriedTensor D).obj M).PreservesZeroMorphisms]
    [∀ K L : CochainComplex D ℤ,
      HomologicalComplex.HasMapBifunctor K L (curriedTensor D) (.up ℤ)]
    {K L K' L' : CochainComplex D ℤ} (f : K ⟶ K') (g : L ⟶ L') :
    HomologicalComplex.mapBifunctorMap f g (curriedTensor D) (.up ℤ) =
      (((curriedTensor D).map₂CochainComplex).map f).app L ≫
        (((curriedTensor D).map₂CochainComplex).obj K').map g := by
  apply HomologicalComplex.hom_ext
  intro n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j hij
  change _ = HomologicalComplex.ιMapBifunctor K L (curriedTensor D) _ i j n hij ≫
    (HomologicalComplex.mapBifunctorMap f (𝟙 L) (curriedTensor D) (.up ℤ) ≫
      HomologicalComplex.mapBifunctorMap (𝟙 K') g (curriedTensor D) (.up ℤ)).f n
  simp only [HomologicalComplex.comp_f, HomologicalComplex.ι_mapBifunctorMap_assoc,
    HomologicalComplex.ι_mapBifunctorMap, HomologicalComplex.id_f]
  rw [(curriedTensor D).map_id, ((curriedTensor D).obj _).map_id]
  simp only [NatTrans.id_app, Category.id_comp]

private theorem composeTensorNormalization
    {B C D : Type*} [Category* B] [Category* C] [Category* D]
    [MonoidalCategory B] [MonoidalCategory C] [MonoidalCategory D]
    (G : B ⥤ C) (F : C ⥤ D)
    (σ : (Functor.postcompose₂.obj G).obj (curriedTensor B) ≅
      (((Functor.whiskeringLeft₂ C).obj G).obj G).obj (curriedTensor C))
    (τ : (Functor.postcompose₂.obj F).obj (curriedTensor C) ≅
      (((Functor.whiskeringLeft₂ D).obj F).obj F).obj (curriedTensor D))
    (a : 𝟙_ C ⟶ G.obj (𝟙_ B)) (b : 𝟙_ D ⟶ F.obj (𝟙_ C))
    (hσ : a ≫ G.map (ρ_ (𝟙_ B)).inv ≫ (σ.hom.app (𝟙_ B)).app (𝟙_ B) =
      (λ_ (𝟙_ C)).inv ≫ (a ⊗ₘ a))
    (hτ : ∀ M, F.map (ρ_ M).inv ≫ (τ.hom.app M).app (𝟙_ C) =
      (ρ_ (F.obj M)).inv ≫ F.obj M ◁ b) :
    (b ≫ F.map a) ≫ (G ⋙ F).map (ρ_ (𝟙_ B)).inv ≫
      ((composeTensorIso G F σ τ).hom.app (𝟙_ B)).app (𝟙_ B) =
        (λ_ (𝟙_ D)).inv ≫ ((b ≫ F.map a) ⊗ₘ (b ≫ F.map a)) := by
  change (b ≫ F.map a) ≫ F.map (G.map (ρ_ (𝟙_ B)).inv) ≫
    (F.map ((σ.hom.app (𝟙_ B)).app (𝟙_ B)) ≫
      (τ.hom.app (G.obj (𝟙_ B))).app (G.obj (𝟙_ B))) = _
  simp only [Category.assoc]
  rw [← F.map_comp_assoc, ← F.map_comp_assoc, Category.assoc a, hσ, F.map_comp]
  simp only [Category.assoc]
  rw [tensorIsoNaturality F τ a a]
  rw [reassoc_of% (regularTensorNormalization F τ b hτ)]
  simp only [tensorHom_comp_tensorHom]

private theorem totalTensorComparison
    {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
    [HasZeroObject C] [MonoidalCategory C] [MonoidalCategory D]
    [MonoidalPreadditive C] [MonoidalPreadditive D]
    [HasColimitsOfSize.{0, 0} C] [HasColimitsOfSize.{0, 0} D]
    (F : C ⥤ D) [F.Additive] [PreservesColimitsOfSize.{0, 0} F]
    (τ : (Functor.postcompose₂.obj F).obj (curriedTensor C) ≅
      (((Functor.whiskeringLeft₂ D).obj F).obj F).obj (curriedTensor D))
    (c : 𝟙_ D ⟶ F.obj (𝟙_ C))
    (hc : c ≫ F.map (ρ_ (𝟙_ C)).inv ≫ (τ.hom.app (𝟙_ C)).app (𝟙_ C) =
      (λ_ (𝟙_ D)).inv ≫ (c ⊗ₘ c)) :
    let H := F.mapHomologicalComplex (.up ℤ)
    let T := (curriedTensor D).map₂CochainComplex
    ∃ t : ∀ K L : CochainComplex C ℤ,
        H.obj (HomologicalComplex.tensorObj K L) ≅ (T.obj (H.obj K)).obj (H.obj L),
      (∀ (K L K' L' : CochainComplex C ℤ) (f : K ⟶ K') (g : L ⟶ L'),
        H.map (HomologicalComplex.tensorHom f g) ≫ (t K' L').hom =
          (t K L).hom ≫ (T.map (H.map f)).app (H.obj L) ≫
            (T.obj (H.obj K')).map (H.map g)) ∧
      (∀ (K L : CochainComplex C ℤ) (v : 𝟙_ C ⟶ K.X 0) (w : 𝟙_ C ⟶ L.X 0),
        c ≫ F.map ((ρ_ (𝟙_ C)).inv ≫ (v ⊗ₘ w) ≫
          HomologicalComplex.ιTensorObj K L 0 0 0 (by omega)) ≫ (t K L).hom.f 0 =
            (λ_ (𝟙_ D)).inv ≫ ((c ≫ F.map v) ⊗ₘ (c ≫ F.map w)) ≫
              CochainComplex.ιMapBifunctor (H.obj K) (H.obj L)
                (curriedTensor D) 0 0 0 (by omega)) := by
  let H := F.mapHomologicalComplex (.up ℤ)
  let t (K L : CochainComplex C ℤ) :=
    asIso (HomologicalComplex.mapBifunctorComparison τ.hom (.up ℤ) K L)
  refine ⟨t, ?_, ?_⟩
  · intro K L K' L' f g
    have hn := HomologicalComplex.mapBifunctorComparison_naturality τ.hom (.up ℤ) f g
    rw [totalTensorMap_eq (H.map f) (H.map g)] at hn
    exact hn
  · intro K L v w
    let j : F.obj (K.X 0) ⊗ F.obj (L.X 0) ⟶ _ :=
      CochainComplex.ιMapBifunctor (H.obj K) (H.obj L)
        (curriedTensor D) 0 0 0 (by omega)
    have hs := HomologicalComplex.map_ιMapBifunctor_mapBifunctorComparisonX
      τ.hom (.up ℤ) K L 0 0 0 (by rfl)
    change F.map (HomologicalComplex.ιTensorObj K L 0 0 0 (by omega)) ≫
      (HomologicalComplex.mapBifunctorComparison τ.hom (.up ℤ) K L).f 0 = _ at hs
    change c ≫ F.map ((ρ_ (𝟙_ C)).inv ≫ (v ⊗ₘ w) ≫
      HomologicalComplex.ιTensorObj K L 0 0 0 (by omega)) ≫
        (HomologicalComplex.mapBifunctorComparison τ.hom (.up ℤ) K L).f 0 = _
    simp only [F.map_comp, Category.assoc]
    rw [hs]
    dsimp only [HomologicalComplex.mapBifunctorComparisonApp]
    rw [reassoc_of% (tensorIsoNaturality F τ v w), reassoc_of% hc]
    change (λ_ (𝟙_ D)).inv ≫ (c ⊗ₘ c) ≫ (F.map v ⊗ₘ F.map w) ≫ j =
      (λ_ (𝟙_ D)).inv ≫ ((c ≫ F.map v) ⊗ₘ (c ≫ F.map w)) ≫ j
    rw [tensorHom_comp_tensorHom_assoc]

namespace AlgebraicGeometry.Scheme

attribute [local irreducible] completedCechModulesEquiv pbcCompletedComparison
  completedKoszulConstant completedKoszulOne completedCechCoefficientUnit

/-- Completed constant realization commutes with total tensor products, naturally
and with the specified normalization on the (0,0) pure tensor summand.

Source: Stacks Project, Modules on Sites, Tags 03D8, 03EK and 0GMW;
algebraization.tex, Tag 0A0E, the finite free coefficient realization.
(blueprint: lem-weil-pbc-completed-realization-tensor).

Proof: on modules, the balanced tensor universal property identifies extension of
a tensor product with the tensor product of extensions. Constant sheafification
has the same comparison, by the sheaf tensor universal property. Restriction
along the coefficient ring isomorphism and reindexing along the site equivalence
are monoidal equivalences. Compose these comparisons. All four functors preserve
the coproducts in totalization: sheafification and extension are left adjoints,
restriction along a ring isomorphism and site reindexing are equivalences. Apply
the module comparison on each summand of each total degree and its inverse on
the same summands. These are inverse because total inclusions are jointly epic.
The two parts of the total differential commute with the comparison by
naturality; additivity preserves its Koszul sign. This constructs t. Applying
the same argument to two chain maps proves naturality. On the (0,0) summand the
module comparison sends 1 tensor (u(1) tensor v(1)) to
(1 tensor u(1)) tensor (1 tensor v(1)); both prescribed coefficient units send
1 to 1. This proves the displayed normalization, with the inverse unitors and
total inclusion in exactly the displayed order. No flatness, boundedness, or
nonzero-ring assumption is needed; coproduct preservation also covers unbounded
complexes and the empty site. -/
theorem completedRealizationTensor
    (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    let F := intrinsicPresentationModulesBack X d ⋙ (completedCechModulesEquiv X d).functor
    let G := completedKoszulConstant X (intrinsicPresentationDatum d)
    let Q := G ⋙ F
    let H := Q.mapHomologicalComplex (.up ℤ)
    let O := completedCechRing X d
    let c := completedCechCoefficientUnit X d ≫
      F.map (completedKoszulOne X (intrinsicPresentationDatum d))
    letI := SheafOfModules.monoidalCategory O
    letI := SheafOfModules.symmetricCategory O
    letI := Classical.choice (SheafOfModules.tensorClosed O).1
    letI := Classical.choice (SheafOfModules.tensorClosed O).2.1
    ∃ t : ∀ K L : CochainComplex (ModuleCat.{u + 1} A) ℤ,
        H.obj (HomologicalComplex.tensorObj K L) ≅
          ((ringedKoszulTensor O).obj (H.obj K)).obj (H.obj L),
      (∀ (K L K' L' : CochainComplex (ModuleCat.{u + 1} A) ℤ)
          (f : K ⟶ K') (g : L ⟶ L'),
        H.map (HomologicalComplex.tensorHom f g) ≫ (t K' L').hom =
          (t K L).hom ≫ ((ringedKoszulTensor O).map (H.map f)).app (H.obj L) ≫
            ((ringedKoszulTensor O).obj (H.obj K')).map (H.map g)) ∧
      (∀ (K L : CochainComplex (ModuleCat.{u + 1} A) ℤ)
          (v : ModuleCat.of A A ⟶ K.X 0) (w : ModuleCat.of A A ⟶ L.X 0),
        c ≫ Q.map ((ρ_ (ModuleCat.of A A)).inv ≫ (v ⊗ₘ w) ≫
          HomologicalComplex.ιTensorObj K L 0 0 0 (by omega)) ≫ (t K L).hom.f 0 =
        (λ_ (SheafOfModules.unit ((sheafCompose (completedCechTopology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O))).inv ≫
          ((c ≫ Q.map v) ⊗ₘ (c ≫ Q.map w)) ≫
            CochainComplex.ιMapBifunctor (H.obj K) (H.obj L)
              (curriedTensor _) 0 0 0 (by omega)) := by
  let O₀ := adicDatumRing X (intrinsicPresentationDatum d)
  let := SheafOfModules.isMonoidal_W_independentCoefficients O₀
  let := SheafOfModules.monoidalCategory O₀
  let O := completedCechRing X d
  let := SheafOfModules.monoidalCategory O
  let := SheafOfModules.symmetricCategory O
  let := Classical.choice (SheafOfModules.tensorClosed O).1
  let := Classical.choice (SheafOfModules.tensorClosed O).2.1
  let G := completedKoszulConstant X (intrinsicPresentationDatum d)
  let F := intrinsicPresentationModulesBack X d ⋙ (completedCechModulesEquiv X d).functor
  let Q := G ⋙ F
  let a := completedKoszulOne X (intrinsicPresentationDatum d)
  let b := completedCechCoefficientUnit X d
  let c := b ≫ F.map a
  have : (intrinsicPresentationModulesBack X d).IsEquivalence :=
    inferInstanceAs (proEtaleScalarEquivalence X
      ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso
        (pbcCompletedComparison X d).symm)).functor.IsEquivalence
  have : F.IsEquivalence := by dsimp [F]; infer_instance
  let P : ModuleCat.{u + 1} A ⥤
      _root_.PresheafOfModules.{u + 1} ((Functor.const X.ProEtᵒᵖ).obj (RingCat.of A)) :=
    siteConstantModulePresheaf (C := Discrete (ULift.{u + 1} Unit)) A ⋙
      PresheafOfModules.pushforward₀
        ((Functor.const X.ProEt).obj (Discrete.mk (ULift.up ())))
        ((Functor.const (Discrete (ULift.{u + 1} Unit))ᵒᵖ).obj (RingCat.of A))
  have : PreservesColimitsOfSize.{0, 0} P := by
    constructor
    intro J _
    constructor
    intro K
    constructor
    intro z hz
    exact ⟨PresheafOfModules.evaluationJointlyReflectsColimits _ _ (fun U ↦ hz)⟩
  have : PreservesColimitsOfSize.{0, 0} (adicLisseConstantModules X A) :=
    inferInstanceAs (PreservesColimitsOfSize.{0, 0}
      (P ⋙ PresheafOfModules.sheafification (adicLisseConstantUnit X A)))
  have : (completedConstantExtension X
      (adicDatumScalar X (intrinsicPresentationDatum d))).IsLeftAdjoint := by
    rw [adicDatumOrdinaryExtension_eq]
    exact (adicDatumOrdinaryAdjunction X _).isLeftAdjoint
  have : PreservesColimitsOfSize.{0, 0} G := by
    unfold G completedKoszulConstant
    infer_instance
  have : PreservesColimitsOfSize.{0, 0} Q := by dsimp [Q]; infer_instance
  obtain ⟨σ, hσ⟩ := completedConstantModuleTensor X (intrinsicPresentationDatum d)
  obtain ⟨τ, hτ⟩ := completedCechModuleTensorTransport X d
  let γ := composeTensorIso G F σ τ
  have hc := composeTensorNormalization G F σ τ a b hσ hτ
  exact totalTensorComparison Q γ c hc

end AlgebraicGeometry.Scheme
