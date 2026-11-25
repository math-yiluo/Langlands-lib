/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CoefficientTorFlatModel
public import WeilConjectures.AlgebraicGeometry.ConstructibleProEtaleComparison
import WeilConjectures.AlgebraicGeometry.ConstructibleComparisonModuleExact
import WeilConjectures.AlgebraicGeometry.RingedTopoiTensorComparisonConstruction
import WeilConjectures.CategoryTheory.ContinuousRingedToposModuleDirectImage
import all WeilConjectures.CategoryTheory.RingedToposKFlatPullback
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle

/-! # Reflection of one coefficient-model tensor test
Source: Stacks Project, Tag 07A4, and blueprint finite-Tor comparison.
-/

@[expose] public section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

-- The universe-polymorphic `hasSheafify_of_essentiallySmall` gets stuck on the universe of
-- `ModuleCat.{max v (u + 1)}`; Mathlib's concrete-category instance applies instead.
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
open SheafOfModules
namespace AlgebraicGeometry.ProEtale

private theorem comparisonTensorIso (X : Scheme.{u}) (A : Type (max v (u + 1))) [CommRing A] :
    let R := ConstantCompletion.constant
      (Scheme.smallModelComparisonEtaleTopology.{u, v} X) A
    let S := ConstantCompletion.constant (Scheme.coefficientProEtaleModelTopology.{u, v} X) A
    let F := constructibleComparisonPullback X A
    ∃ μ : ∀ M N, F.obj ((monoidalCategory R).tensorObj M N) ≅
        (monoidalCategory S).tensorObj (F.obj M) (F.obj N),
      ∀ {M M' N N'} (f : M ⟶ M') (g : N ⟶ N'),
        F.map ((monoidalCategory R).tensorHom f g) ≫ (μ M' N').hom =
          (μ M N).hom ≫ (monoidalCategory S).tensorHom (F.map f) (F.map g) := by
  classical
  let J := Scheme.smallModelComparisonEtaleTopology.{u, v} X
  let K := Scheme.coefficientProEtaleModelTopology.{u, v} X
  let R := ConstantCompletion.constant J A
  let S := ConstantCompletion.constant K A
  let F := Scheme.smallModelComparisonInclusion.{u, v} X
  let φ : R ⟶ (F.sheafPushforwardContinuous CommRingCat.{max v (u + 1)} J K).obj S :=
    ((sheafificationAdjunction J CommRingCat.{max v (u + 1)}).homEquiv
      ((Functor.const _).obj (CommRingCat.of A))
      ((F.sheafPushforwardContinuous CommRingCat.{max v (u + 1)} J K).obj S)).symm
        (Functor.whiskerLeft F.op (toSheafify K ((Functor.const _).obj (CommRingCat.of A))))
  obtain ⟨p, hp⟩ := continuousRingedToposModuleDirectImage_exists F
    (Scheme.smallModelComparisonPullback.{u, v} X)
    (Scheme.smallModelProEtaleComparison.{u, v} X) S R φ
  let _ := p.leftExact
  obtain ⟨RI, ⟨I⟩⟩ := algebraic_image J K p.inverse p.direct p.adj R
  obtain ⟨c, hc⟩ := structural_map K J S R p RI I
  obtain ⟨adj⟩ := supplied_adjunction p RI I c hc
  let G := I.modules ⋙ tensorFunctor c
  have hobj (M : ConstantCompletion.Mod R) :
      G.obj M = changeOfRings c (I.modules.obj M) := rfl
  have hmap {M N : ConstantCompletion.Mod R} (f : M ⟶ N) :
      G.map f = eqToHom (hobj M) ≫
        changeOfRingsHom c (I.modules.obj M) (I.modules.map f) ≫ eqToHom (hobj N).symm := by
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  obtain ⟨k⟩ := canonicalRingedTensorComparison_nonempty R S RI p.inverse I c G hobj
    p.direct p.adj hmap
  let adjF := SheafOfModules.pullbackPushforwardAdjunction
    (F := F) (constructibleComparisonRingMap X A)
  have adj' : G ⊣ SheafOfModules.pushforward
      (F := F) (constructibleComparisonRingMap X A) := by
    simpa only [hp, φ, R, S, J, K, F, constructibleComparisonRingMap] using adj
  let e : G ≅ constructibleComparisonPullback X A := adj'.leftAdjointUniq adjF
  let _ := monoidalCategory R
  let _ := monoidalCategory S
  let eG : tensor _ ⋙ G ≅ G.prod G ⋙ tensor _ :=
    NatIso.ofComponents (fun MN ↦ k.mu MN.1 MN.2) (fun f ↦ k.naturality f.1 f.2)
  let eF : tensor _ ⋙ constructibleComparisonPullback X A ≅
      (constructibleComparisonPullback X A).prod (constructibleComparisonPullback X A) ⋙
        tensor _ :=
    Functor.isoWhiskerLeft (tensor _) e.symm ≪≫ eG ≪≫
      Functor.isoWhiskerRight (NatIso.prod e e) (tensor _)
  refine ⟨fun M N ↦ eF.app (M, N), ?_⟩
  intro M M' N N' f g
  exact eF.hom.naturality (show (M, N) ⟶ (M', N') from (f, g))

private theorem tensorTestReflectsZero {C E : Type w} [SmallCategory C] [SmallCategory E]
    {J : GrothendieckTopology C} {K : GrothendieckTopology E}
    (R : Sheaf J CommRingCat.{w}) (S : Sheaf K CommRingCat.{w})
    (F : ConstantCompletion.Mod R ⥤ ConstantCompletion.Mod S)
    [F.PreservesZeroMorphisms] [F.PreservesHomology] [F.Faithful]
    (P : ConstantCompletion.Cx R) (M : ConstantCompletion.Mod R) (q : ℤ)
    (μ : ∀ N, F.obj ((SheafOfModules.monoidalCategory R).tensorObj N M) ≅
      (SheafOfModules.monoidalCategory S).tensorObj (F.obj N) (F.obj M))
    (hμ : ∀ {N N'} (f : N ⟶ N'),
      F.map ((SheafOfModules.monoidalCategory R).tensorHom f (𝟙 M)) ≫ (μ N').hom =
      (μ N).hom ≫ (SheafOfModules.monoidalCategory S).tensorHom (F.map f) (𝟙 _))
    (hz : IsZero (HomologicalComplex.homology
      (((ringedKoszulTensor S).obj ((F.mapHomologicalComplex (.up ℤ)).obj P)).obj
        ((HomologicalComplex.single (ConstantCompletion.Mod S) (.up ℤ) 0).obj
          (F.obj M))) q)) :
    IsZero (HomologicalComplex.homology (((ringedKoszulTensor R).obj P).obj
      ((HomologicalComplex.single (ConstantCompletion.Mod R) (.up ℤ) 0).obj M)) q) := by
  let _ := SheafOfModules.monoidalCategory R
  let _ := SheafOfModules.monoidalCategory S
  let _ : MonoidalPreadditive (ConstantCompletion.Mod R) :=
    Classical.choice (SheafOfModules.tensorClosed R).1
  let _ : MonoidalPreadditive (ConstantCompletion.Mod S) :=
    Classical.choice (SheafOfModules.tensorClosed S).1
  let T := ((tensorRight M).mapHomologicalComplex (.up ℤ)).obj P
  let U := ((tensorRight (F.obj M)).mapHomologicalComplex (.up ℤ)).obj
    ((F.mapHomologicalComplex (.up ℤ)).obj P)
  let e : (F.mapHomologicalComplex (.up ℤ)).obj T ≅ U :=
    HomologicalComplex.Hom.isoOfComponents (fun i ↦ μ (P.X i)) (by
      intro i j hij
      change (μ (P.X i)).hom ≫ (F.map (P.d i j)) ▷ (F.obj M) =
        F.map ((P.d i j) ▷ M) ≫ (μ (P.X j)).hom
      simpa only [MonoidalCategory.tensorHom_def, whiskerLeft_id, Category.comp_id]
        using (hμ (P.d i j)).symm)
  let eR := CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _) M P
  let eS := CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _) (F.obj M)
    ((F.mapHomologicalComplex (.up ℤ)).obj P)
  let H := HomologicalComplex.homologyFunctor (ConstantCompletion.Mod S) (.up ℤ) q
  have hu : IsZero (U.homology q) := hz.of_iso (H.mapIso eS).symm
  have ht : IsZero (((F.mapHomologicalComplex (.up ℤ)).obj T).homology q) :=
    hu.of_iso (H.mapIso e)
  have hf : IsZero (F.obj (T.homology q)) :=
    ht.of_iso ((F.mapHomologicalComplexHomologyIso (.up ℤ) q).app T).symm
  have he : 𝟙 (T.homology q) = 0 := by
    apply F.map_injective
    simpa only [F.map_id, F.map_zero] using hf.eq_of_src (𝟙 _) 0
  have ht' : IsZero (T.homology q) := (IsZero.iff_id_eq_zero _).mpr he
  exact ht'.of_iso
    ((HomologicalComplex.homologyFunctor (ConstantCompletion.Mod R) (.up ℤ) q).mapIso eR)

/-- Vanishing of a pulled-back tensor test detects vanishing of the etale tensor test.
Source: Stacks Project, Tag 07A4, lemma-pullback-tensor-product; blueprint finite-Tor
comparison, paragraphs Tor amplitude is detected and The equivalence
(auxiliary; not a blueprint node).

Proof: use constructibleComparisonPullback_exact_faithful for the intrinsic-module
comparison. Its left adjoint preserves finite colimits, so it commutes with homology.
Construct its ordinary tensor comparison by the continuous ringed-topos interface
and uniqueness of left adjoints. The ordinary
symmetric monoidal inverse image preserves the tensor of P with M[0], termwise and
with its signed total differential; since the second factor is concentrated in
degree zero, each total degree has only one nonzero summand. Thus the pro-etale
homology object in the hypothesis is isomorphic to the inverse image of the etale
homology object in the conclusion. Faithfulness reflects zero objects: apply it
to id = 0. No K-flatness, derived localization, Tor interval, constructibility or
boundedness hypothesis is needed. -/
theorem constructibleComparisonTensorTest_reflects_zero (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A]
    (P : ConstantCompletion.Cx (ConstantCompletion.constant
      (Scheme.smallModelComparisonEtaleTopology.{u, v} X) A))
    (M : ConstantCompletion.Mod (ConstantCompletion.constant
      (Scheme.smallModelComparisonEtaleTopology.{u, v} X) A)) (q : ℤ)
    (hzero : IsZero (coefficientModelTensorTest (ConstantCompletion.constant
      (Scheme.coefficientProEtaleModelTopology.{u, v} X) A)
        ((constructibleComparisonComplexPullback X A).obj P)
        ((constructibleComparisonPullback X A).obj M) q)) :
    IsZero (coefficientModelTensorTest (ConstantCompletion.constant
      (Scheme.smallModelComparisonEtaleTopology.{u, v} X) A) P M q) := by
  let F := constructibleComparisonPullback X A
  obtain ⟨hlim, hfaith⟩ := constructibleComparisonPullback_exact_faithful X A
  let _ : PreservesFiniteLimits F := hlim
  let _ : F.Faithful := hfaith
  let adj := SheafOfModules.pullbackPushforwardAdjunction
    (F := Scheme.smallModelComparisonInclusion.{u, v} X)
    (constructibleComparisonRingMap X A)
  let _ : F.IsLeftAdjoint := adj.isLeftAdjoint
  let _ : F.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_isLeftAdjoint F
  let _ : PreservesFiniteColimits F := inferInstance
  let _ : F.PreservesHomology := inferInstance
  obtain ⟨μ, hμ⟩ := comparisonTensorIso X A
  exact tensorTestReflectsZero _ _ F P M q (fun N ↦ μ N M)
    (fun f ↦ by
      have h := hμ f (𝟙 M)
      rw [(constructibleComparisonPullback X A).map_id M] at h
      exact h) hzero

end AlgebraicGeometry.ProEtale
