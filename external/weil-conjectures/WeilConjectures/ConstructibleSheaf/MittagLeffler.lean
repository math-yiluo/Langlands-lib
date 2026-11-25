/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.KernelCokernel
public import WeilConjectures.ConstructibleSheaf.StalkCardinality
public import WeilConjectures.ConstructibleSheaf.Pullback
public import Mathlib.Topology.NoetherianSpace

/-!
# Towers of finite locally constant sheaves are Mittag-Leffler

Let `X` be a scheme whose underlying space is noetherian and let `(Hₙ)ₙ` be a tower of finite
locally constant étale sheaves of `Λ`-modules on `X` with finite stalks (e.g. the higher direct
images `(Rᵠf_* Fₙ)ₙ` of an `ℓ`-adic tower along a smooth proper morphism). Then the tower is
Mittag-Leffler: for every `n` the images of the transition maps `H_k ⟶ Hₙ`, `k ≥ n`, stabilise
(`AlgebraicGeometry.Etale.mittagLeffler_imageSubobject_of_isFiniteLocallyConstantSheaf`).

Indeed, the images `Iₖ ⊆ Hₙ` form a decreasing chain of locally constant subsheaves
(`AlgebraicGeometry.Etale.isLocallyConstantSheaf_imageSubobject`, from the closure of locally
constant sheaves under kernels and cokernels). The cardinality of the stalk of `Iₖ` is a locally
constant function on `X`, hence constant on each of the finitely many irreducible components of
`X`; so these finitely many decreasing sequences of natural numbers stabilise simultaneously. Once
the stalk cardinalities of `I_{k} ⊆ I_N` agree everywhere, the inclusion is an isomorphism on all
geometric stalks, hence an isomorphism
(`AlgebraicGeometry.Etale.isIso_of_mono_of_natCard_sheafFiber_eq`).

This is the Mittag-Leffler input for the vanishing of `R¹lim` in the Milnor sequence of the
higher direct images of an `ℓ`-adic tower (Stacks 0CQD).
-/

@[expose] public section

universe w u

open CategoryTheory Limits Opposite

/-- On a noetherian topological space, finitely many points detect the values of all locally
constant functions: one point in each irreducible component. -/
lemma TopologicalSpace.NoetherianSpace.exists_finite_forall_isLocallyConstant
    (X : Type w) [TopologicalSpace X] [TopologicalSpace.NoetherianSpace X] :
    ∃ (ι : Type w) (_ : Finite ι) (p : ι → X), ∀ x : X, ∃ i : ι,
      ∀ {β : Type*} (f : X → β), IsLocallyConstant f → f x = f (p i) := by
  have hfin := TopologicalSpace.NoetherianSpace.finite_irreducibleComponents (α := X)
  refine ⟨irreducibleComponents X, hfin.to_subtype,
    fun Z ↦ Z.2.1.nonempty.some,
    fun x ↦ ⟨⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩,
      fun f hf ↦ ?_⟩⟩
  exact hf.apply_eq_of_isPreconnected
    (isIrreducible_irreducibleComponent (x := x)).isPreirreducible.isPreconnected
    mem_irreducibleComponent (Set.Nonempty.some_mem _)

/-- Finitely many antitone sequences of natural numbers stabilise simultaneously. -/
lemma Nat.exists_forall_ge_eq_of_antitone {ι : Type*} [Finite ι] (a : ι → ℕ → ℕ)
    (ha : ∀ i, Antitone (a i)) : ∃ N : ℕ, ∀ k ≥ N, ∀ i, a i k = a i N := by
  have h (i : ι) : ∀ᶠ k in Filter.atTop, a i k = sInf (Set.range (a i)) := by
    obtain ⟨M, hM⟩ := Nat.sInf_mem (Set.range_nonempty (a i))
    refine Filter.eventually_atTop.2 ⟨M, fun k hk ↦ le_antisymm ?_ (Nat.sInf_le ⟨k, rfl⟩)⟩
    rw [← hM]
    exact ha i hk
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (Filter.eventually_all.2 h)
  exact ⟨N, fun k hk i ↦ (hN k hk i).trans (hN N le_rfl i).symm⟩

namespace AlgebraicGeometry.Etale

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ] {X : Scheme.{u}}

/-- A monomorphism `ι : A ⟶ B` of étale sheaves of `Λ`-modules such that, at every geometric
point `X.algClosurePoint x`, the stalk of `B` is finite with as many elements as the stalk of `A`,
is an isomorphism: it is bijective on all these stalks, which form a conservative family. -/
lemma isIso_of_mono_of_natCard_sheafFiber_eq
    {A B : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (ι : A ⟶ B) [Mono ι]
    (hfin : ∀ x : X, Finite ((pointSmallEtale (X.algClosurePoint x)).sheafFiber
      (A := ModuleCat.{u + 1} Λ) |>.obj B))
    (hcard : ∀ x : X,
      Nat.card ((pointSmallEtale (X.algClosurePoint x)).sheafFiber
        (A := ModuleCat.{u + 1} Λ) |>.obj A) =
      Nat.card ((pointSmallEtale (X.algClosurePoint x)).sheafFiber
        (A := ModuleCat.{u + 1} Λ) |>.obj B)) :
    IsIso ι := by
  refine Scheme.isIso_of_isIso_sheafFiber_map _ fun x ↦ ?_
  let Φ := (pointSmallEtale (X.algClosurePoint x)).sheafFiber (A := ModuleCat.{u + 1} Λ)
  have hinj : Function.Injective (Φ.map ι) := (ModuleCat.mono_iff_injective _).1 (Φ.map_mono _)
  have := hfin x
  have h : IsIso (Φ.map ι) := (ConcreteCategory.isIso_iff_bijective _).2
    (hinj.bijective_of_nat_card_le (hcard x).ge)
  exact (NatIso.isIso_map_iff (GrothendieckTopology.Point.uliftSheafFiberIso.{u + 1}
    (pointSmallEtale (X.algClosurePoint x)) (ModuleCat.{u + 1} Λ)) ι).2 h

/-- **The image of a morphism between finite locally constant sheaves is locally constant**: it is
the kernel of the cokernel map, and locally constant sheaves are closed under kernels and
cokernels of morphisms out of finite locally constant sheaves. -/
lemma isLocallyConstantSheaf_imageSubobject
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (φ : F ⟶ G)
    [IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) F]
    [IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) G] :
    IsLocallyConstantSheaf
      ((imageSubobject φ : Subobject G) : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) := by
  have := (IsLocallyConstantSheaf.kernel_and_cokernel φ).2
  have := (IsLocallyConstantSheaf.kernel_and_cokernel (cokernel.π φ)).1
  exact IsLocallyConstantSheaf.of_iso ((imageSubobjectIso φ) ≪≫ (Abelian.imageIsoImage φ).symm).symm

/-- **Towers of finite locally constant sheaves with finite stalks on a noetherian scheme are
Mittag-Leffler.** Let `X` be a scheme with noetherian underlying space and `H` a tower of finite
locally constant étale sheaves of `Λ`-modules whose stalks at the geometric points
`X.algClosurePoint x` are finite. Then for every `n` there is `N ≥ n` such that the image of
`H_N ⟶ Hₙ` is contained in the image of `H_k ⟶ Hₙ` for every `k ≥ n`. -/
theorem mittagLeffler_imageSubobject_of_isFiniteLocallyConstantSheaf
    [TopologicalSpace.NoetherianSpace X]
    (H : ℕᵒᵖ ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [∀ n : ℕ, IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) (H.obj (op n))]
    (hfin : ∀ (n : ℕ) (x : X), Finite ((pointSmallEtale (X.algClosurePoint x)).sheafFiber
      (A := ModuleCat.{u + 1} Λ) |>.obj (H.obj (op n)))) (n : ℕ) :
    ∃ N : ℕ, ∃ hN : n ≤ N, ∀ (k : ℕ) (hk : n ≤ k),
      imageSubobject (H.map (homOfLE hN).op) ≤ imageSubobject (H.map (homOfLE hk).op) := by
  let Φ (x : X) := (pointSmallEtale (X.algClosurePoint x)).sheafFiber (A := ModuleCat.{u + 1} Λ)
  -- the images `S j ⊆ Hₙ` of the transition maps `H_{n + j} ⟶ Hₙ`
  let S (j : ℕ) : Subobject (H.obj (op n)) :=
    imageSubobject (H.map (homOfLE (Nat.le_add_right n j)).op)
  have hS : Antitone S := fun j j' hjj' ↦ by
    have : H.map (homOfLE (Nat.le_add_right n j')).op =
        H.map (homOfLE (Nat.add_le_add_left hjj' n)).op ≫
          H.map (homOfLE (Nat.le_add_right n j)).op := by
      rw [← H.map_comp]
      rfl
    dsimp only [S]
    rw [this]
    exact imageSubobject_comp_le _ _
  have hinj (j : ℕ) (x : X) : Function.Injective ((Φ x).map (S j).arrow) :=
    (ModuleCat.mono_iff_injective _).1 ((Φ x).map_mono _)
  have hfinS (j : ℕ) (x : X) : Finite ((Φ x).obj (S j)) :=
    have := hfin n x
    Finite.of_injective _ (hinj j x)
  -- the stalk cardinalities of the `S j`
  let c (j : ℕ) (x : X) : ℕ := Nat.card ((Φ x).obj (S j))
  have hc (j : ℕ) : IsLocallyConstant (c j) := by
    have := isLocallyConstantSheaf_imageSubobject (H.map (homOfLE (Nat.le_add_right n j)).op)
    exact (IsLocallyConstant.iff_isOpen_fiber).2 fun m ↦
      isOpen_setOf_natCard_sheafFiber (S j : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) m
  have hc_anti (x : X) : Antitone fun j ↦ c j x := fun j j' hjj' ↦ by
    have := hfinS j x
    refine Nat.card_le_card_of_injective _ (?_ : Function.Injective
      ((Φ x).map (Subobject.ofLE _ _ (hS hjj'))))
    exact (ModuleCat.mono_iff_injective _).1 ((Φ x).map_mono _)
  obtain ⟨ι, _, p, hp⟩ := TopologicalSpace.NoetherianSpace.exists_finite_forall_isLocallyConstant X
  obtain ⟨N, hN⟩ := Nat.exists_forall_ge_eq_of_antitone (fun i j ↦ c j (p i))
    fun i ↦ hc_anti (p i)
  refine ⟨n + N, Nat.le_add_right n N, fun k hk ↦ ?_⟩
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  rcases le_total j N with hjN | hNj
  · exact (hS hjN : S N ≤ S j)
  · have : IsIso (Subobject.ofLE _ _ (hS hNj)) :=
      isIso_of_mono_of_natCard_sheafFiber_eq _ (hfinS N) fun x ↦ by
        obtain ⟨i, hi⟩ := hp x
        exact ((hi (c j) (hc j)).trans (hN j hNj i)).trans (hi (c N) (hc N)).symm
    exact ((Subobject.eq_of_comm (asIso (Subobject.ofLE _ _ (hS hNj)))
      (Subobject.ofLE_arrow _)).symm.le : S N ≤ S j)

end AlgebraicGeometry.Etale
