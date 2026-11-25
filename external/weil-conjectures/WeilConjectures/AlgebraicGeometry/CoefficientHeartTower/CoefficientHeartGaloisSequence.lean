/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Galois.Decomposition
public import Mathlib.CategoryTheory.Functor.OfSequence

/-! # Nested pointed Galois representatives of a countable family

Source: coefficient-heart proof (1), the connected finite etale trivializing tower.
(blueprint: lem-sfb-coefficient-heart-galois-sequence)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory Opposite
namespace AlgebraicGeometry.ProEtale.CoefficientHeartTower
variable {C : Type u} [Category.{v} C] [GaloisCategory C]
variable (F : C ⥤ FintypeCat.{w}) [FiberFunctor F]

/-- A single pointed Galois representative can represent two nonempty fibres at once.
Source: coefficient-heart proof (1), intersections of finite monodromy kernels.
(blueprint: lem-sfb-coefficient-heart-galois-sequence)
Proof: represent the product. Fix a point in the other factor to obtain surjectivity
of evaluation on each factor. Evaluation from a connected object is already injective. -/
theorem exists_pair_representative (P Q : C) (p : F.obj P) (q : F.obj Q) :
    ∃ (B : C) (b : F.obj B), IsGalois B ∧
      Function.Bijective (fun f : B ⟶ P ↦ F.map f b) ∧
      Function.Bijective (fun f : B ⟶ Q ↦ F.map f b) := by
  obtain ⟨B, b, hB, h⟩ := exists_galois_representative F (P ⨯ Q)
  have := hB
  refine ⟨B, b, hB, ⟨evaluation_injective_of_isConnected F B P b, ?_⟩,
    ⟨evaluation_injective_of_isConnected F B Q b, ?_⟩⟩
  · intro x
    obtain ⟨f, hf⟩ := h.surjective ((fiberBinaryProductEquiv F P Q).symm (x, q))
    refine ⟨f ≫ prod.fst, ?_⟩
    simp only [Functor.map_comp, FintypeCat.comp_apply, hf,
      fiberBinaryProductEquiv_symm_fst_apply]
  · intro y
    obtain ⟨f, hf⟩ := h.surjective ((fiberBinaryProductEquiv F P Q).symm (p, y))
    refine ⟨f ≫ prod.snd, ?_⟩
    simp only [Functor.map_comp, FintypeCat.comp_apply, hf,
      fiberBinaryProductEquiv_symm_snd_apply]

/-- Evaluation on a represented product gives evaluation on either nonempty factor.
Source: coefficient-heart proof (1), simultaneous finite trivializations.
(blueprint: lem-sfb-coefficient-heart-galois-sequence)
Proof: fix a point in the other factor and lift the pair. Evaluation from the connected
source is injective. This applies to the already chosen stages of the tower. -/
theorem evaluation_factors (B P Q : C) [IsConnected B]
    (b : F.obj B) (p : F.obj P) (q : F.obj Q)
    (h : Function.Bijective (fun f : B ⟶ P ⨯ Q ↦ F.map f b)) :
    Function.Bijective (fun f : B ⟶ P ↦ F.map f b) ∧
      Function.Bijective (fun f : B ⟶ Q ↦ F.map f b) := by
  constructor
  · refine ⟨evaluation_injective_of_isConnected F B P b, ?_⟩
    intro x
    obtain ⟨f, hf⟩ := h.surjective ((fiberBinaryProductEquiv F P Q).symm (x, q))
    refine ⟨f ≫ prod.fst, ?_⟩
    simp only [Functor.map_comp, FintypeCat.comp_apply, hf,
      fiberBinaryProductEquiv_symm_fst_apply]
  · refine ⟨evaluation_injective_of_isConnected F B Q b, ?_⟩
    intro y
    obtain ⟨f, hf⟩ := h.surjective ((fiberBinaryProductEquiv F P Q).symm (p, y))
    refine ⟨f ≫ prod.snd, ?_⟩
    simp only [Functor.map_comp, FintypeCat.comp_apply, hf,
      fiberBinaryProductEquiv_symm_snd_apply]

/-- A pointed Galois object representing all members through one finite level.
Source: coefficient-heart proof (1), finite intersections of monodromy kernels.
(blueprint: lem-sfb-coefficient-heart-galois-sequence). -/
structure GaloisStage (E : ℕ → C) (n : ℕ) where
  obj : C
  point : F.obj obj
  galois : IsGalois obj
  evaluation : ∀ (m : ℕ), m ≤ n →
    Function.Bijective (fun f : obj ⟶ E m ↦ F.map f point)

/-- The pointed stages and their adjacent refinements, before forming a scheme limit.
Source: coefficient-heart proof (1), nested pointed finite covers.
(blueprint: lem-sfb-coefficient-heart-galois-sequence). -/
structure GaloisSequence (E : ℕ → C) where
  stage : ∀ n : ℕ, GaloisStage F E n
  arrow : ∀ n : ℕ, (stage (n + 1)).obj ⟶ (stage n).obj
  point_arrow : ∀ n : ℕ, F.map (arrow n) (stage (n + 1)).point = (stage n).point

/-- A countable family with nonempty fibres admits a compatible sequence of pointed
Galois representatives, each representing all preceding fibres.
Source: coefficient-heart proof (1), choose nested finite monodromy kernels.
(blueprint: lem-sfb-coefficient-heart-galois-sequence)
Proof: represent E_0. Given a stage, represent its product with E_(n+1). Evaluation
on the old stage supplies a transition carrying the new marked point to the old one.
For any earlier E_m, precompose its representing maps with that transition to get
surjectivity of evaluation; connectedness gives injectivity. Dependent recursion yields
the sequence and its coherent marked points. This constructs only finite stages. -/
theorem exists_galoisSequence (E : ℕ → C) (hE : ∀ n : ℕ, Nonempty (F.obj (E n))) :
    Nonempty (GaloisSequence F E) := by
  classical
  have h0 : Nonempty (GaloisStage F E 0) := by
    obtain ⟨B, b, hB, h⟩ := exists_galois_representative F (E 0)
    refine ⟨⟨B, b, hB, ?_⟩⟩
    intro m hm
    obtain rfl : m = 0 := Nat.eq_zero_of_le_zero hm
    exact h
  have hnext (n : ℕ) (s : GaloisStage F E n) :
      ∃ (t : GaloisStage F E (n + 1)) (f : t.obj ⟶ s.obj),
        F.map f t.point = s.point := by
    obtain ⟨B, b, hB, hprev, hnew⟩ :=
      exists_pair_representative F s.obj (E (n + 1)) s.point (hE (n + 1)).some
    obtain ⟨f, hf⟩ := hprev.surjective s.point
    have := hB
    let t : GaloisStage F E (n + 1) :=
      { obj := B
        point := b
        galois := hB
        evaluation m hm := by
          by_cases hmn : m ≤ n
          · refine ⟨evaluation_injective_of_isConnected F B (E m) b, ?_⟩
            intro x
            obtain ⟨g, hg⟩ := (s.evaluation m hmn).surjective x
            refine ⟨f ≫ g, ?_⟩
            simp only [Functor.map_comp, FintypeCat.comp_apply, hf, hg]
          · have heq : m = n + 1 := by omega
            subst m
            exact hnew }
    exact ⟨t, f, hf⟩
  choose next arrow hpoint using hnext
  let stage : ∀ n : ℕ, GaloisStage F E n := Nat.rec h0.some (fun n s ↦ next n s)
  exact ⟨{
    stage := stage
    arrow := fun n ↦ arrow n (stage n)
    point_arrow := fun n ↦ hpoint n (stage n) }⟩

end AlgebraicGeometry.ProEtale.CoefficientHeartTower
