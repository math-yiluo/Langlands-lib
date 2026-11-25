/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Galois.GaloisObjects
public import Mathlib.CategoryTheory.Limits.FintypeCat

/-!
# Consequences of the axioms of a Galois category

Let `C` be a pre-Galois category with a fibre functor `F : C ⥤ FintypeCat`. This file records
the elementary consequences of the axioms (blueprint `lem-galois-axioms`), most of which are in
Mathlib:

- `F` is faithful;
- a morphism is a monomorphism (resp. an epimorphism) if and only if it is injective
  (resp. surjective) on fibres;
- an object is initial (resp. terminal) if and only if its fibre is empty (resp. a singleton);
- every morphism between connected objects is an epimorphism;
- two morphisms out of a connected object agreeing at one point of the fibre are equal;
- for connected `X` and `x ∈ F(X)`, the evaluation `Aut X → F(X)` is injective, and `X` is
  Galois if and only if `Aut X` acts transitively on `F(X)`;
- every morphism out of a coproduct of connected objects into a coproduct of connected objects is
  given by a map of index sets and morphisms between the summands.
-/

@[expose] public section

universe u₁ u₂ w

open CategoryTheory Limits Functor

namespace CategoryTheory.PreGaloisCategory

section Pre

variable {C : Type u₁} [Category.{u₂} C] [PreGaloisCategory C] (F : C ⥤ FintypeCat.{w})
  [FiberFunctor F]

/-- A fibre functor is faithful. (blueprint: `lem-galois-axioms`) -/
theorem faithful_of_fiberFunctor : F.Faithful :=
  inferInstance

/-- A morphism is a monomorphism if and only if it is injective on fibres.
(blueprint: `lem-galois-axioms`) -/
theorem mono_iff_injective_map {X Y : C} (f : X ⟶ Y) : Mono f ↔ Function.Injective (F.map f) := by
  rw [← ConcreteCategory.mono_iff_injective_of_preservesPullback]
  exact ⟨fun _ ↦ inferInstance, fun _ ↦ F.mono_of_mono_map ‹_›⟩

/-- A morphism is an epimorphism if and only if it is surjective on fibres.
(blueprint: `lem-galois-axioms`) -/
theorem epi_iff_surjective_map {X Y : C} (f : X ⟶ Y) : Epi f ↔ Function.Surjective (F.map f) := by
  refine ⟨fun _ ↦ surjective_on_fiber_of_epi F f, fun h ↦ ?_⟩
  have : Epi (F.map f) := ConcreteCategory.epi_of_surjective _ h
  exact F.epi_of_epi_map this

/-- An object is initial if and only if its fibre is empty. (blueprint: `lem-galois-axioms`) -/
theorem nonempty_isInitial_iff_isEmpty (X : C) : Nonempty (IsInitial X) ↔ IsEmpty (F.obj X) :=
  initial_iff_fiber_empty F X

/-- An object is terminal if and only if its fibre is a singleton.
(blueprint: `lem-galois-axioms`) -/
theorem nonempty_isTerminal_iff_card_eq_one (X : C) :
    Nonempty (IsTerminal X) ↔ Nat.card (F.obj X) = 1 := by
  have hT : Nat.card (F.obj (⊤_ C)) = 1 := by
    have h : IsTerminal (F.obj (⊤_ C)) := terminalIsTerminal.isTerminalObj F _
    rw [Nat.card_eq_one_iff_unique]
    let P : FintypeCat.{w} := FintypeCat.of PUnit.{w + 1}
    refine ⟨⟨fun x y ↦ ?_⟩, ⟨h.from P PUnit.unit⟩⟩
    exact congr_arg (fun g : P ⟶ F.obj (⊤_ C) ↦ g PUnit.unit)
      (h.hom_ext (FintypeCat.homMk fun _ ↦ x) (FintypeCat.homMk fun _ ↦ y))
  constructor
  · rintro ⟨h⟩
    rw [Nat.card_congr (FintypeCat.equivEquivIso.symm (F.mapIso (h.uniqueUpToIso
      terminalIsTerminal))), hT]
  · intro h
    have hb : Function.Bijective (F.map (terminal.from X)) := by
      rw [Nat.bijective_iff_injective_and_card]
      refine ⟨fun a b _ ↦ ?_, h.trans hT.symm⟩
      have : Subsingleton (F.obj X) := (Nat.card_eq_one_iff_unique.1 h).1
      exact Subsingleton.elim a b
    have : IsIso (F.map (terminal.from X)) := (ConcreteCategory.isIso_iff_bijective _).2 hb
    have : IsIso (terminal.from X) := isIso_of_reflects_iso _ F
    exact ⟨terminalIsTerminal.ofIso (asIso (terminal.from X)).symm⟩

include F in
/-- Every morphism between connected objects is an epimorphism.
(blueprint: `lem-galois-axioms`) -/
theorem epi_of_isConnected {X A : C} [IsConnected X] [IsConnected A] (f : X ⟶ A) : Epi f :=
  epi_of_nonempty_of_isConnected F f

/-- Two morphisms out of a connected object which agree at one point of the fibre are equal.
(blueprint: `lem-galois-axioms`) -/
theorem eq_of_map_apply_eq {X Y : C} [IsConnected X] {a b : X ⟶ Y} (x : F.obj X)
    (h : F.map a x = F.map b x) : a = b :=
  evaluation_injective_of_isConnected F X Y x h

/-- For a connected object `X` and `x ∈ F(X)`, the evaluation `Aut X → F(X)`, `g ↦ F(g)(x)` is
injective, so `#Aut X ≤ #F(X)`. (blueprint: `lem-galois-axioms`) -/
theorem injective_evaluation_aut_and_card_le (X : C) [IsConnected X] (x : F.obj X) :
    Function.Injective (fun g : Aut X ↦ F.map g.asIso.hom x) ∧
      Nat.card (Aut X) ≤ Nat.card (F.obj X) :=
  ⟨evaluation_aut_injective_of_isConnected F X x, card_aut_le_card_fiber_of_connected F X⟩

/-- A connected object `X` is Galois if and only if `Aut X` acts transitively on `F(X)`, if and
only if `#Aut X = #F(X)`. (blueprint: `lem-galois-axioms`) -/
theorem isGalois_iff_pretransitive_and_card {C : Type u₁} [Category.{u₂} C] [GaloisCategory C]
    (F : C ⥤ FintypeCat.{w}) [FiberFunctor F] (X : C) [IsConnected X] :
    (IsGalois X ↔ MulAction.IsPretransitive (Aut X) (F.obj X)) ∧
      (IsGalois X ↔ Nat.card (Aut X) = Nat.card (F.obj X)) := by
  refine ⟨isGalois_iff_pretransitive F X, ?_⟩
  rw [isGalois_iff_pretransitive F X]
  obtain ⟨x⟩ := nonempty_fiber_of_isConnected F X
  have hinj := evaluation_aut_injective_of_isConnected F X x
  constructor
  · intro h
    have hsurj : Function.Surjective (fun g : Aut X ↦ F.map g.asIso.hom x) := fun y ↦
      MulAction.exists_smul_eq (Aut X) x y
    exact Nat.card_eq_of_bijective _ ⟨hinj, hsurj⟩
  · intro h
    have hb : Function.Bijective (fun g : Aut X ↦ F.map g.asIso.hom x) := by
      rw [Nat.bijective_iff_injective_and_card]
      exact ⟨hinj, h⟩
    refine ⟨fun y z ↦ ?_⟩
    obtain ⟨g, hg⟩ := hb.2 y
    obtain ⟨g', hg'⟩ := hb.2 z
    refine ⟨g' * g⁻¹, ?_⟩
    change F.map (g' * g⁻¹).asIso.hom y = z
    rw [← hg, ← hg', ← FintypeCat.comp_apply, ← F.map_comp]
    change F.map (g.asIso.hom ≫ (g' * g⁻¹).asIso.hom) x = F.map g'.asIso.hom x
    congr 2
    simp [Aut.mul_asIso, Aut.inv_asIso]

end Pre

section Galois

variable {C : Type u₁} [Category.{u₂} C] [GaloisCategory C] (F : C ⥤ FintypeCat.{w})
  [FiberFunctor F]

include F in
/-- A morphism from a connected object into a coproduct factors through one of the summands.
(blueprint: `lem-galois-axioms`) -/
theorem exists_comp_sigmaι_of_isConnected {ι : Type*} [Finite ι] {X : C} [IsConnected X]
    (Y : ι → C) (f : X ⟶ ∐ Y) : ∃ (j : ι) (g : X ⟶ Y j), g ≫ Sigma.ι Y j = f := by
  obtain ⟨x⟩ := nonempty_fiber_of_isConnected F X
  have : PreservesColimitsOfShape (Discrete ι) F := by
    have := (FiberFunctor.preservesFiniteCoproducts (F := F)).preserves
    exact preservesColimitsOfShape_of_equiv (Discrete.equivalence (Finite.equivFin ι).symm) F
  have hc : IsColimit (F.mapCocone (colimit.cocone (Discrete.functor Y))) :=
    isColimitOfPreserves F (colimit.isColimit _)
  have := Fintype.ofFinite ι
  obtain ⟨⟨j⟩, y, hy⟩ := FintypeCat.jointly_surjective _ _ hc (F.map f x)
  have hm : Mono (pullback.fst f (Sigma.ι Y j)) := inferInstance
  let e := fiberPullbackEquiv F f (Sigma.ι Y j)
  let z : F.obj (pullback f (Sigma.ι Y j)) := e.symm ⟨(x, y), hy.symm⟩
  have : IsIso (pullback.fst f (Sigma.ι Y j)) :=
    IsConnected.noTrivialComponent _ _ (not_initial_of_inhabited F z)
  exact ⟨j, inv (pullback.fst f (Sigma.ι Y j)) ≫ pullback.snd f (Sigma.ι Y j), by
    simp [pullback.condition]⟩

include F in
/-- If `X = ∐ᵢ Xᵢ` and `Y = ∐ⱼ Yⱼ` are finite coproducts of connected objects, every morphism
`X ⟶ Y` is given by a map of index sets `α` and morphisms `Xᵢ ⟶ Y_{α(i)}`.
(blueprint: `lem-galois-axioms`) -/
theorem exists_sigma_desc_eq {ι κ : Type*} [Finite ι] [Finite κ] (X : ι → C) (Y : κ → C)
    [∀ i, IsConnected (X i)] (f : ∐ X ⟶ ∐ Y) :
    ∃ (α : ι → κ) (g : ∀ i, X i ⟶ Y (α i)), ∀ i, Sigma.ι X i ≫ f = g i ≫ Sigma.ι Y (α i) := by
  choose α g hg using fun i ↦ exists_comp_sigmaι_of_isConnected F Y (Sigma.ι X i ≫ f)
  exact ⟨α, g, fun i ↦ (hg i).symm⟩

end Galois

end CategoryTheory.PreGaloisCategory
