/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleModelTypePartition
import WeilConjectures.AlgebraicGeometry.ProEtaleUniformModelEtaleCover
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs

/-! # Descent of finite pro-etale models to an etale trivializing cover

Source: Stacks Project, Tag 099Y, proof steps selecting module types and their Isom torsors.
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.Scheme

private noncomputable def emptySheafIso
    {X : Scheme.{u}} [IsEmpty X] (Λ : Type (u + 1)) [CommRing Λ]
    (F G : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)) : F ≅ G := by
  have (T : X.ProEt) : IsEmpty T.left := ⟨fun t ↦ isEmptyElim (show X from T.hom t)⟩
  exact ObjectProperty.isoMk _ (NatIso.ofComponents
    (fun T ↦ (ProEt.isTerminalSectionsOfIsEmpty F T.unop).uniqueUpToIso
      (ProEt.isTerminalSectionsOfIsEmpty G T.unop))
    (fun {_ _} _ ↦ (ProEt.isTerminalSectionsOfIsEmpty G _).hom_ext _ _))

private noncomputable def constantPullbackIso
    {X Y : Scheme.{u}} (Λ : Type (u + 1)) [CommRing Λ] (g : Y ⟶ X)
    [WeaklyEtale g] (M : ModuleCat.{u + 1} Λ) :
    (AlgebraicGeometry.ProEtale.upperStar (ModuleCat.{u + 1} Λ) g).obj
      ((constantSheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)).obj M) ≅
        (constantSheaf (ProEt.topology Y) (ModuleCat.{u + 1} Λ)).obj M :=
  (AlgebraicGeometry.ProEtale.upperStarIsoLocalizationRestriction
    (ModuleCat.{u + 1} Λ) g inferInstance).app _ ≪≫
    (Functor.pushforwardContinuousSheafificationCompatibility
      (MorphismProperty.Over.map (P := @WeaklyEtale) ⊤ (inferInstance : WeaklyEtale g))
        (ModuleCat.{u + 1} Λ) (ProEt.topology Y) (ProEt.topology X)).symm.app
          ((Functor.const X.ProEtᵒᵖ).obj M)

/-- A finite-model pro-etale covering admits an etale trivializing covering.
Source: Stacks Project, Tag 099Y, proof of lemma-compare-locally-constant.
Partition the base by the isomorphism types of the finite constant models, descending
these open subsets by fpqc descent. On each open the module-Isom sheaf from its model
to F is locally the constant automorphism sheaf. Its local sections therefore descend
to an etale cover by the locally-classical etale-section comparison. Combining the
open subsets and etale covers gives the claimed finite module trivializations.
(auxiliary; not a blueprint node) -/
theorem etale_cover_of_proetale_finite_models
    (X : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (F : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ))
    (hF : ∃ (ι : Type (u + 1)) (W : ι → Scheme.{u}) (g : ∀ i, W i ⟶ X),
      Presieve.ofArrows W g ∈ Scheme.proetalePrecoverage X ∧
        ∀ i, ∃ M : ModuleCat.{u + 1} Λ, Finite M ∧
          Nonempty ((AlgebraicGeometry.ProEtale.upperStar
            (ModuleCat.{u + 1} Λ) (g i)).obj F ≅
              (constantSheaf (ProEt.topology (W i)) (ModuleCat.{u + 1} Λ)).obj M)) :
    ∃ 𝒰 : Cover.{u} etalePrecoverage X, ∀ i : 𝒰.I₀,
      ∃ M : ModuleCat.{u + 1} Λ, Finite M ∧
        Nonempty ((AlgebraicGeometry.ProEtale.upperStar
          (ModuleCat.{u + 1} Λ) (𝒰.f i)).obj F ≅
            (constantSheaf (ProEt.topology (𝒰.X i)) (ModuleCat.{u + 1} Λ)).obj M) := by
  classical
  obtain ⟨I, W, g, hg, hmodels⟩ := hF
  choose M hM e using hmodels
  obtain ⟨O, hO, hcover⟩ := proEtale_model_type_opens Λ F W g hg M (fun i ↦ (e i).some)
  have (i : I) : WeaklyEtale (g i) :=
    proetalePrecoverage_le_precoverage_weaklyEtale _ hg (.mk i)
  have huniform (i : I) : ∃ 𝒰 : Cover.{u} etalePrecoverage (O i).toScheme,
      ∀ a : 𝒰.I₀, Nonempty
        ((AlgebraicGeometry.ProEtale.upperStar (ModuleCat.{u + 1} Λ) (𝒰.f a)).obj
          ((AlgebraicGeometry.ProEtale.upperStar (ModuleCat.{u + 1} Λ) (O i).ι).obj F) ≅
            (constantSheaf (ProEt.topology (𝒰.X a)) (ModuleCat.{u + 1} Λ)).obj (M i)) := by
    have : Finite (M i) := hM i
    apply etale_cover_of_proetale_uniform_model (O i).toScheme Λ _ (M i)
    refine ⟨I, (fun j ↦ pullback (g j) (O i).ι),
      (fun j ↦ pullback.snd (g j) (O i).ι), ?_, ?_⟩
    · exact Precoverage.mem_coverings_of_isPullback g hg (O i).ι _ _
        (fun j ↦ (IsPullback.of_hasPullback (g j) (O i).ι).flip)
    · intro j
      by_cases h : Nonempty (pullback (g j) (O i).ι : Scheme.{u})
      · obtain ⟨z⟩ := h
        have hz : g j ((pullback.fst (g j) (O i).ι) z) ∈ O i := by
          rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
          exact (pullback.snd (g j) (O i).ι z).property
        obtain ⟨a⟩ := (hO i j _).1 hz
        let p := pullback.fst (g j) (O i).ι
        let q := pullback.snd (g j) (O i).ι
        let A := ModuleCat.{u + 1} Λ
        exact ⟨((AlgebraicGeometry.ProEtale.upperStarComp A q (O i).ι).app F).symm ≪≫
          (eqToIso (congrArg (fun k ↦ (AlgebraicGeometry.ProEtale.upperStar A k).obj F)
            (pullback.condition (f := g j) (g := (O i).ι)).symm)) ≪≫
          (AlgebraicGeometry.ProEtale.upperStarComp A p (g j)).app F ≪≫
          (AlgebraicGeometry.ProEtale.upperStar A p).mapIso (e j).some ≪≫
          constantPullbackIso Λ p (M j) ≪≫
          (constantSheaf (ProEt.topology (pullback (g j) (O i).ι)) A).mapIso a⟩
      · have : IsEmpty (pullback (g j) (O i).ι : Scheme.{u}) := not_nonempty_iff.mp h
        exact ⟨emptySheafIso Λ _ _⟩
  choose 𝒰 h𝒰 using huniform
  have hpoint (x : X) : ∃ i, x ∈ O i := by
    have hx : x ∈ ⋃ i, (O i : Set X) := by rw [hcover]; trivial
    exact Set.mem_iUnion.mp hx
  choose index hindex using hpoint
  let P (a : Σ x : X, (𝒰 (index x)).I₀) : Scheme.{u} := (𝒰 (index a.1)).X a.2
  let f (a : Σ x : X, (𝒰 (index x)).I₀) : P a ⟶ X :=
    (𝒰 (index a.1)).f a.2 ≫ (O (index a.1)).ι
  have (a : Σ x : X, (𝒰 (index x)).I₀) : Etale (f a) := by
    dsimp [f]
    infer_instance
  have hf : ∀ x : X, ∃ a, ∃ y : P a, f a y = x := by
    intro x
    let y : (O (index x)).toScheme := ⟨x, hindex x⟩
    obtain ⟨a, z, hz⟩ := ((Scheme.ofArrows_mem_precoverage_iff _).1
      (𝒰 (index x)).mem₀).1 y
    refine ⟨⟨x, a⟩, z, ?_⟩
    change ((𝒰 (index x)).f a ≫ (O (index x)).ι) z = x
    rw [Scheme.Hom.comp_apply, hz]
    rfl
  let 𝒱 : Cover.{u} etalePrecoverage X :=
    Cover.mkOfCovers (Σ x : X, (𝒰 (index x)).I₀) P f
      (fun x ↦ by obtain ⟨a, y, hy⟩ := hf x; exact ⟨a, y, hy⟩)
      inferInstance
  refine ⟨𝒱, ?_⟩
  rintro ⟨x, a⟩
  exact ⟨M (index x), hM (index x),
    ⟨(AlgebraicGeometry.ProEtale.upperStarComp (ModuleCat.{u + 1} Λ)
      ((𝒰 (index x)).f a) (O (index x)).ι).app F ≪≫ (h𝒰 (index x) a).some⟩⟩

end AlgebraicGeometry.Scheme
