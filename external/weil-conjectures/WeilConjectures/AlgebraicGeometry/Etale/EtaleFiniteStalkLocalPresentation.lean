/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ConstructibleSheaf.Defs
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits

/-! # Lifting a finite geometric stalk to neighbourhood sections

Source: Stacks Project, Tag 0GKC, the finite-presentation paragraph.
(blueprint: lem-weil-pbc-etale-finite-stalk-local-presentation).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

private theorem finite_germ_representatives
    {S : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ]
    (G : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    {I : Type (u + 1)} [Finite I]
    (z : I → (↑(((pointSmallEtale s).sheafFiber
      (A := ModuleCat.{u + 1} Λ)).obj G) : Type (u + 1))) :
    ∃ (U : S.Etale) (a : (pointSmallEtale s).fiber.obj U)
      (σ : I → G.obj.obj (op U)),
      ∀ i, (pointSmallEtale s).toPresheafFiber U a G.obj (σ i) = z i := by
  classical
  have : PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  let Φ := pointSmallEtale s
  choose U a σ hσ using fun i ↦ Φ.toPresheafFiber_jointly_surjective (z i)
  let X : I → Φ.fiber.Elements := fun i ↦ Φ.fiber.elementsMk (U i) (a i)
  let O : Finset Φ.fiber.Elements := (Set.finite_range X).toFinset
  obtain ⟨W, hW⟩ := IsCofiltered.inf_objs_exists O
  let f : ∀ i, W ⟶ X i := fun i ↦ (hW (by simp [O])).some
  refine ⟨W.1, W.2, fun i ↦ G.obj.map (f i).1.op (σ i), fun i ↦ ?_⟩
  exact (ConcreteCategory.congr_hom (Φ.toPresheafFiber_w (f i).1 W.2 G.obj) (σ i)).trans
    ((congrArg (fun a ↦ Φ.toPresheafFiber (U i) a G.obj (σ i)) (f i).2).trans (hσ i))

private theorem finite_germ_relations
    {S : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ]
    (G : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    {I : Type (u + 1)} (T : Finset I)
    (U : S.Etale) (a : (pointSmallEtale s).fiber.obj U)
    (x y : I → G.obj.obj (op U))
    (h : ∀ i ∈ T, (pointSmallEtale s).toPresheafFiber U a G.obj (x i) =
      (pointSmallEtale s).toPresheafFiber U a G.obj (y i)) :
    ∃ (V : S.Etale) (f : V ⟶ U) (b : (pointSmallEtale s).fiber.obj V),
      (pointSmallEtale s).fiber.map f b = a ∧
      ∀ i ∈ T, G.obj.map f.op (x i) = G.obj.map f.op (y i) := by
  classical
  have : PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  let Φ := pointSmallEtale s
  induction T using Finset.induction_on with
  | empty => exact ⟨U, 𝟙 U, a, by simp, by simp⟩
  | @insert i T hi ih =>
    obtain ⟨V, f, b, hb, hT⟩ := ih (fun j hj ↦ h j (Finset.mem_insert_of_mem hj))
    have heq : Φ.toPresheafFiber V b G.obj (G.obj.map f.op (x i)) =
        Φ.toPresheafFiber V b G.obj (G.obj.map f.op (y i)) := by
      simp only [← ConcreteCategory.comp_apply, Φ.toPresheafFiber_w]
      change Φ.fiber.map f b = a at hb
      rw [hb]
      exact h i (Finset.mem_insert_self _ _)
    obtain ⟨W, g, c, hc, heq⟩ := (Φ.toPresheafFiber_eq_iff' V b _ _).mp heq
    refine ⟨W, g ≫ f, c, ?_, ?_⟩
    · change Φ.fiber.map (g ≫ f) c = a
      rw [Functor.map_comp]
      change Φ.fiber.map f (Φ.fiber.map g c) = a
      rw [hc]
      exact hb
    · intro j hj
      rw [op_comp, G.obj.map_comp]
      change G.obj.map g.op (G.obj.map f.op (x j)) =
        G.obj.map g.op (G.obj.map f.op (y j))
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact heq
      · exact congrArg (G.obj.map g.op) (hT j hj)

/-- The identity of a finite geometric stalk lifts to a linear map into the sections
on one pointed etale neighbourhood.

Source: Stacks Project, Tag 0GKC, finite-presentation paragraph, expanded using the finite
operation table (blueprint: lem-weil-pbc-etale-finite-stalk-local-presentation).

Proof: Represent every element of the finite stalk by a section. Cofilteredness puts
these representatives on one pointed neighbourhood. Equality in the stalk is eventual
equality, so refine for all addition and scalar-multiplication relations; there are only
finitely many because both the stalk and coefficient ring are finite. The resulting
representatives define a linear map. Its composite with the germ map is the identity
because each chosen representative has its prescribed germ. This also handles the zero
ring and the zero stalk. -/
theorem exists_etale_finite_stalk_section
    {S : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    (G : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    [Finite (↑((pointSmallEtale s).sheafFiber.obj G) : Type (u + 1))] :
    ∃ (U : S.Etale) (a : (pointSmallEtale s).fiber.obj U)
      (f : (pointSmallEtale s).sheafFiber.obj G ⟶ G.obj.obj (op U)),
      f ≫ (pointSmallEtale s).toPresheafFiber U a G.obj = 𝟙 _ := by
  classical
  let M := (pointSmallEtale s).sheafFiber.obj G
  obtain ⟨U, a, σ, hσ⟩ := finite_germ_representatives G s (id : M → M)
  let I := (M × M) ⊕ (Λ × M)
  let : Fintype I := Fintype.ofFinite I
  let x : I → G.obj.obj (op U)
    | .inl p => σ (p.1 + p.2)
    | .inr p => σ (p.1 • p.2)
  let y : I → G.obj.obj (op U)
    | .inl p => σ p.1 + σ p.2
    | .inr p => p.1 • σ p.2
  have hrel (i : I) : (pointSmallEtale s).toPresheafFiber U a G.obj (x i) =
      (pointSmallEtale s).toPresheafFiber U a G.obj (y i) := by
    rcases i with ⟨m, n⟩ | ⟨r, m⟩
    · simp [x, y, hσ]
    · simp [x, y, hσ]
  obtain ⟨V, g, b, hb, hg⟩ := finite_germ_relations G s Finset.univ U a x y
    (fun i _ ↦ hrel i)
  let f : M ⟶ G.obj.obj (op V) := ModuleCat.ofHom
    { toFun := fun m ↦ G.obj.map g.op (σ m)
      map_add' := fun m n ↦ by
        simpa [x, y] using hg (.inl (m, n)) (Finset.mem_univ _)
      map_smul' := fun r m ↦ by
        simpa [x, y] using hg (.inr (r, m)) (Finset.mem_univ _) }
  refine ⟨V, b, f, ?_⟩
  ext m
  change (pointSmallEtale s).toPresheafFiber V b G.obj
    (G.obj.map g.op (σ m)) = m
  rw [← ConcreteCategory.comp_apply, (pointSmallEtale s).toPresheafFiber_w, hb]
  exact hσ m

end AlgebraicGeometry.Scheme
