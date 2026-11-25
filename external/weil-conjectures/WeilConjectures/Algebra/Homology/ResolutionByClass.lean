/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.Algebra.Homology.QuasiIso
public import WeilConjectures.Mathlib.Algebra.Homology.Embedding.Extend
public import WeilConjectures.Mathlib.Algebra.Homology.Embedding.HomEquiv
public import Mathlib.Algebra.Homology.Refinements
public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.CategoryTheory.Abelian.Refinements

/-!
# Resolutions by a class of objects lifting along epimorphisms

Let `C` be an abelian category, `T` a property of objects closed under kernels and `S` a
property of objects contained in `T` and closed under binary biproducts. Assume that `S`
*lifts along epimorphisms onto `T`* (`ChainComplex.LiftsAlongEpi`): for every epimorphism
`p : A ⟶ B` and every morphism `g : G ⟶ B` from an object `G` of `T`, there are an object `E`
of `S`, an epimorphism `e : E ⟶ G` and a morphism `h : E ⟶ A` with `h ≫ p = e ≫ g`.

Then every chain complex `M` indexed by `ℕ` whose homology objects belong to `T` admits a
quasi-isomorphism `Q ⟶ M` from a complex `Q` whose terms belong to `S`
(`ChainComplex.exists_quasiIso_of_liftsAlongEpi`). This is the usual construction of a
resolution degree by degree [SGA 4½, Rapport, 4.6–4.8]: in degree `k + 1`, one covers the
cycles of `Q` in degree `k` which become boundaries in `M` (making the homology map in degree
`k` injective) and the homology of `M` in degree `k + 1` (making the next homology map
surjective). The class `T` is needed because the objects to be covered are not themselves
terms of `M`: the kernel of `Z_k(Q) ⟶ H_k(M)` belongs to `T` as `Z_k(Q)` and `H_k(M)` do.

The typical example is that of constructible sheaves `T` on a Noetherian scheme and finite sums
of extensions by zero `j_{V!} Λ_V` for `S`.

## Main definitions and results

- `ChainComplex.LiftsAlongEpi S T`: the lifting property.
- `ChainComplex.exists_quasiIso_of_liftsAlongEpi`: the resolution.
- `CochainComplex.exists_quasiIso_of_liftsAlongEpi`: the resolution of a cochain complex
  indexed by `ℤ` and vanishing above some degree `b`, by a complex vanishing above `b`.
-/

@[expose] public section

open CategoryTheory Limits ZeroObject

namespace ChainComplex

variable {C : Type*} [Category* C] [Abelian C] (S T : ObjectProperty C)

/-- The property `S` *lifts along epimorphisms onto `T`*: for every epimorphism `p : A ⟶ B`
and every morphism `g : G ⟶ B` from an object `G` satisfying `T`, there are an object `E`
satisfying `S`, an epimorphism `e : E ⟶ G` and a morphism `h : E ⟶ A` with
`h ≫ p = e ≫ g`. -/
def LiftsAlongEpi : Prop :=
  ∀ ⦃A B G : C⦄ (p : A ⟶ B) [Epi p] (g : G ⟶ B), T G →
    ∃ (E : C) (e : E ⟶ G) (h : E ⟶ A), S E ∧ Epi e ∧ h ≫ p = e ≫ g

namespace ResolutionOfLiftsAlongEpi

variable {S T} (M : ChainComplex C ℕ)

lemma next_eq (k : ℕ) : (ComplexShape.down ℕ).next k = k - 1 := by
  cases k <;> simp

variable (S T) in
/-- The data of the resolution in degree `k`: the term `X` in degree `k`, the differential
`d : X ⟶ Y` to the term in degree `k - 1` and the map `φ : X ⟶ M_k`, together with the
property that the homology map in degree `k` is surjective. -/
structure Stage (k : ℕ) where
  /-- The term in degree `k`. -/
  X : C
  /-- The term in degree `k - 1` (zero for `k = 0`). -/
  Y : C
  /-- The differential in degree `k`. -/
  d : X ⟶ Y
  /-- The component of the resolution map in degree `k`. -/
  φ : X ⟶ M.X k
  hX : S X
  hY : T Y
  w : kernel.ι d ≫ φ ≫ M.d k (k - 1) = 0
  hepi : ∀ ⦃A : C⦄ (z : A ⟶ M.cycles k), ∃ (A' : C) (π : A' ⟶ A) (_ : Epi π) (x : A' ⟶ X)
    (_ : x ≫ d = 0) (y : A' ⟶ M.X (k + 1)), π ≫ z ≫ M.iCycles k = x ≫ φ + y ≫ M.d (k + 1) k

variable {M}

/-- An object of `S` covering the homology of `M` in degree `k`, with a lift to the cycles. -/
lemma exists_cover_homology (hlift : LiftsAlongEpi S T) (hM : ∀ k, T (M.homology k)) (k : ℕ) :
    ∃ (E : C) (h : E ⟶ M.cycles k), S E ∧ ∀ ⦃A : C⦄ (z : A ⟶ M.cycles k),
      ∃ (A' : C) (π : A' ⟶ A) (_ : Epi π) (x : A' ⟶ E) (y : A' ⟶ M.X (k + 1)),
        π ≫ z = x ≫ h + y ≫ M.toCycles (k + 1) k := by
  obtain ⟨E, e, h, hE, _, he⟩ := hlift (M.homologyπ k) (𝟙 _) (hM k)
  refine ⟨E, h, hE, fun A z ↦ ?_⟩
  obtain ⟨A₁, π₁, _, x, hx⟩ := surjective_up_to_refinements_of_epi e (z ≫ M.homologyπ k)
  have : (π₁ ≫ z - x ≫ h) ≫ M.homologyπ k = 0 := by
    rw [Preadditive.sub_comp, Category.assoc, hx, Category.assoc, he, Category.comp_id,
      sub_self]
  obtain ⟨A₂, π₂, _, y, hy⟩ :=
    (M.comp_homologyπ_eq_zero_iff_up_to_refinements (k + 1) k (by simp) _).1 this
  refine ⟨A₂, π₂ ≫ π₁, inferInstance, π₂ ≫ x, y, ?_⟩
  rw [Preadditive.comp_sub, sub_eq_iff_eq_add] at hy
  rw [Category.assoc, Category.assoc, hy, add_comm]

/-- The stage in degree `0`. -/
noncomputable def stageZero [T.ContainsZero] [T.IsClosedUnderIsomorphisms]
    (hlift : LiftsAlongEpi S T)
    (hM : ∀ k, T (M.homology k)) : Stage S T M 0 :=
  have h := exists_cover_homology hlift hM 0
  { X := h.choose
    Y := 0
    d := 0
    φ := h.choose_spec.choose ≫ M.iCycles 0
    hX := h.choose_spec.choose_spec.1
    hY := T.prop_of_isZero (isZero_zero C)
    w := by simp
    hepi := fun A z ↦ by
      obtain ⟨A', π, _, x, y, hxy⟩ := h.choose_spec.choose_spec.2 z
      exact ⟨A', π, inferInstance, x, by simp, y, by simp [reassoc_of% hxy]⟩ }

variable (S T M) in
/-- The data of one step of the construction: the next term `X'` with its differential
`d' : X' ⟶ s.X` and map `φ' : X' ⟶ M_{k+1}`, making the homology map in degree `k` injective
and the one in degree `k + 1` surjective. -/
def StepData {k : ℕ} (s : Stage S T M k) (X' : C) (d' : X' ⟶ s.X) (φ' : X' ⟶ M.X (k + 1)) :
    Prop :=
  S X' ∧ d' ≫ s.d = 0 ∧ d' ≫ s.φ = φ' ≫ M.d (k + 1) k ∧
    (∀ ⦃A : C⦄ (x₂ : A ⟶ s.X) (_ : x₂ ≫ s.d = 0) (y₁ : A ⟶ M.X (k + 1))
      (_ : x₂ ≫ s.φ = y₁ ≫ M.d (k + 1) k),
      ∃ (A' : C) (π : A' ⟶ A) (_ : Epi π) (x₁ : A' ⟶ X'), π ≫ x₂ = x₁ ≫ d') ∧
    ∀ ⦃A : C⦄ (z : A ⟶ M.cycles (k + 1)), ∃ (A' : C) (π : A' ⟶ A) (_ : Epi π) (x : A' ⟶ X')
      (_ : x ≫ d' = 0) (y : A' ⟶ M.X (k + 1 + 1)),
      π ≫ z ≫ M.iCycles (k + 1) = x ≫ φ' + y ≫ M.d (k + 1 + 1) (k + 1)

lemma exists_stepData [T.IsClosedUnderKernels] (hST : S ≤ T)
    (hS : ∀ X Y, S X → S Y → S (X ⊞ Y)) (hlift : LiftsAlongEpi S T)
    (hM : ∀ k, T (M.homology k)) {k : ℕ} (s : Stage S T M k) :
    ∃ (X' : C) (d' : X' ⟶ s.X) (φ' : X' ⟶ M.X (k + 1)), StepData S T M s X' d' φ' := by
  -- the cycles of the resolution in degree `k`, and their map to the cycles of `M`
  have hZ : T (kernel s.d) := T.prop_kernel _ (hST _ s.hX) s.hY
  let ζ : kernel s.d ⟶ M.cycles k := M.liftCycles (kernel.ι s.d ≫ s.φ) (k - 1) (next_eq k)
    (by simpa using s.w)
  -- those which become boundaries in `M`
  let ι := kernel.ι (ζ ≫ M.homologyπ k)
  have hW : T (kernel (ζ ≫ M.homologyπ k)) := T.prop_kernel _ hZ (hM k)
  let p := pullback.fst (ι ≫ ζ ≫ M.iCycles k) (M.d (k + 1) k)
  have : Epi p := by
    rw [epi_iff_surjective_up_to_refinements]
    intro A w
    have : (w ≫ ι ≫ ζ) ≫ M.homologyπ k = 0 := by simp [ι]
    obtain ⟨A', π, _, y, hy⟩ :=
      (M.comp_homologyπ_eq_zero_iff_up_to_refinements (k + 1) k (by simp) _).1 this
    refine ⟨A', π, inferInstance, pullback.lift (π ≫ w) y ?_, (pullback.lift_fst _ _ _).symm⟩
    simpa using hy =≫ M.iCycles k
  obtain ⟨E₁, e₁, h₁, hE₁, _, he₁⟩ := hlift p (𝟙 _) hW
  obtain ⟨E₂, h₂, hE₂, hcov⟩ := exists_cover_homology hlift hM (k + 1)
  rw [Category.comp_id] at he₁
  refine ⟨E₁ ⊞ E₂, biprod.desc (e₁ ≫ ι ≫ kernel.ι s.d) 0,
    biprod.desc (h₁ ≫ pullback.snd _ _) (h₂ ≫ M.iCycles (k + 1)),
    hS _ _ hE₁ hE₂, by ext <;> simp, ?_, ?_, ?_⟩
  · ext
    · have := h₁ ≫= pullback.condition (f := ι ≫ ζ ≫ M.iCycles k) (g := M.d (k + 1) k)
      rw [← Category.assoc h₁, he₁] at this
      simpa [ζ] using this
    · simp
  · intro A x₂ hx₂ y₁ hy₁
    -- `x₂` is a cycle which becomes a boundary in `M`
    let z := kernel.lift s.d x₂ hx₂
    have hz : (z ≫ ζ) ≫ M.homologyπ k = 0 := by
      have : z ≫ ζ = y₁ ≫ M.toCycles (k + 1) k := by
        rw [← cancel_mono (M.iCycles k)]
        simpa [z, ζ] using hy₁
      rw [this, Category.assoc, M.toCycles_comp_homologyπ, Limits.comp_zero]
    obtain ⟨A', π, _, x, hx⟩ :=
      surjective_up_to_refinements_of_epi e₁ (kernel.lift _ z (by simpa using hz))
    refine ⟨A', π, inferInstance, x ≫ biprod.inl, ?_⟩
    have := hx =≫ (ι ≫ kernel.ι s.d)
    simpa [ι, z] using this
  · intro A z
    obtain ⟨A', π, _, x, y, hxy⟩ := hcov z
    exact ⟨A', π, inferInstance, x ≫ biprod.inr, by simp, y, by simp [reassoc_of% hxy]⟩

/-- One step of the construction: the stage in degree `k + 1` from the stage in degree `k`. -/
noncomputable def step [T.IsClosedUnderKernels] (hST : S ≤ T)
    (hS : ∀ X Y, S X → S Y → S (X ⊞ Y)) (hlift : LiftsAlongEpi S T)
    (hM : ∀ k, T (M.homology k)) {k : ℕ} (s : Stage S T M k) : Stage S T M (k + 1) :=
  have h := exists_stepData hST hS hlift hM s
  have hd := h.choose_spec.choose_spec.choose_spec
  { X := h.choose
    Y := s.X
    d := h.choose_spec.choose
    φ := h.choose_spec.choose_spec.choose
    hX := hd.1
    hY := hST _ s.hX
    w := by
      have := kernel.condition h.choose_spec.choose =≫ s.φ
      rw [Category.assoc, hd.2.2.1, zero_comp] at this
      simpa using this
    hepi := hd.2.2.2.2 }

lemma step_stepData [T.IsClosedUnderKernels] (hST : S ≤ T)
    (hS : ∀ X Y, S X → S Y → S (X ⊞ Y)) (hlift : LiftsAlongEpi S T)
    (hM : ∀ k, T (M.homology k)) {k : ℕ} (s : Stage S T M k) :
    StepData S T M s (step hST hS hlift hM s).X (step hST hS hlift hM s).d
      (step hST hS hlift hM s).φ :=
  (exists_stepData hST hS hlift hM s).choose_spec.choose_spec.choose_spec

/-- The stages of the construction. -/
noncomputable def stage [T.IsClosedUnderKernels] [T.ContainsZero]
    [T.IsClosedUnderIsomorphisms] (hST : S ≤ T)
    (hS : ∀ X Y, S X → S Y → S (X ⊞ Y)) (hlift : LiftsAlongEpi S T)
    (hM : ∀ k, T (M.homology k)) : (k : ℕ) → Stage S T M k
  | 0 => stageZero hlift hM
  | k + 1 => step hST hS hlift hM (stage hST hS hlift hM k)

end ResolutionOfLiftsAlongEpi

open ResolutionOfLiftsAlongEpi in
/-- **Resolutions by a class lifting along epimorphisms.** Let `T` be closed under kernels and
contain the zero objects, and let `S ≤ T` be closed under binary biproducts and lift along
epimorphisms onto `T`. Then a chain complex `M` indexed by `ℕ` whose homology objects belong to
`T` has a quasi-isomorphism `Q ⟶ M` from a complex whose terms belong to `S`. -/
theorem exists_quasiIso_of_liftsAlongEpi [T.IsClosedUnderKernels] [T.ContainsZero]
    [T.IsClosedUnderIsomorphisms]
    (hST : S ≤ T) (hS : ∀ X Y, S X → S Y → S (X ⊞ Y)) (hlift : LiftsAlongEpi S T)
    (M : ChainComplex C ℕ) (hM : ∀ k, T (M.homology k)) :
    ∃ (Q : ChainComplex C ℕ) (φ : Q ⟶ M), QuasiIso φ ∧ ∀ k, S (Q.X k) := by
  let s := stage hST hS hlift hM
  have hs (k : ℕ) := step_stepData hST hS hlift hM (s k)
  let Q : ChainComplex C ℕ :=
    ChainComplex.of (fun k ↦ (s k).X) (fun k ↦ ((s (k + 1)).d : (s (k + 1)).X ⟶ (s k).X))
      (fun k ↦ (hs (k + 1)).2.1)
  have hd (k : ℕ) : Q.d (k + 1) k = (s (k + 1)).d :=
    ChainComplex.of_d (fun k ↦ (s k).X) (fun k ↦ ((s (k + 1)).d : (s (k + 1)).X ⟶ (s k).X)) k
  let φ : Q ⟶ M := ChainComplex.ofHom (fun k ↦ (s k).φ) (fun k ↦ by
    rw [hd]
    exact ((hs k).2.2.1).symm)
  -- the differential of `Q` out of degree `k`
  have hQd (k : ℕ) {A : C} (x : A ⟶ Q.X k) : x ≫ Q.d k (k - 1) = 0 ↔ x ≫ (s k).d = 0 := by
    cases k with
    | zero =>
      have h₁ : Q.d 0 (0 - 1) = 0 := Q.shape _ _ (by simp)
      have h₂ : (s 0).d = 0 := rfl
      simp only [h₁, h₂, Limits.comp_zero]
    | succ k => rw [show k + 1 - 1 = k from rfl, hd]
  refine ⟨Q, φ, ?_, fun k ↦ (s k).hX⟩
  rw [quasiIso_iff]
  intro k
  rw [quasiIsoAt_iff_isIso_homologyMap, isIso_iff_mono_and_epi]
  constructor
  · rw [HomologicalComplex.mono_homologyMap_iff_up_to_refinements φ (k + 1) k (k - 1)
      (by simp) (next_eq k)]
    intro A x₂ hx₂ y₁ hy₁
    obtain ⟨A', π, _, x₁, hx₁⟩ := (hs k).2.2.2.1 x₂ ((hQd k x₂).1 hx₂) y₁ hy₁
    exact ⟨A', π, inferInstance, x₁, by rw [hd]; exact hx₁⟩
  · rw [HomologicalComplex.epi_homologyMap_iff_up_to_refinements φ (k + 1) k (k - 1)
      (by simp) (next_eq k)]
    intro A y₂ hy₂
    obtain ⟨A', π, _, x, hx, y, hxy⟩ := (s k).hepi (M.liftCycles y₂ (k - 1) (next_eq k) hy₂)
    exact ⟨A', π, inferInstance, x, (hQd k x).2 hx, y, by simpa using hxy⟩

end ChainComplex

namespace CochainComplex

variable {C : Type*} [Category* C] [Abelian C] {S T : ObjectProperty C}

/-- **Resolutions by a class lifting along epimorphisms**, for cochain complexes indexed by `ℤ`.
Let `T` be closed under kernels and isomorphisms and contain the zero objects, and let `S ≤ T`
be closed under binary biproducts and isomorphisms, contain the zero objects and lift along
epimorphisms onto `T`. Then a cochain complex `L` vanishing above degree `b` whose cohomology
objects belong to `T` has a quasi-isomorphism `P ⟶ L` from a complex vanishing above `b` whose
terms belong to `S`. -/
theorem exists_quasiIso_of_liftsAlongEpi [T.IsClosedUnderKernels] [T.ContainsZero]
    [T.IsClosedUnderIsomorphisms] [S.ContainsZero] [S.IsClosedUnderIsomorphisms]
    (hST : S ≤ T) (hS : ∀ X Y, S X → S Y → S (X ⊞ Y)) (hlift : ChainComplex.LiftsAlongEpi S T)
    (L : CochainComplex C ℤ) (b : ℤ) [L.IsStrictlyLE b] (hL : ∀ n, T (L.homology n)) :
    ∃ (P : CochainComplex C ℤ) (_ : P.IsStrictlyLE b) (π : P ⟶ L), QuasiIso π ∧
      ∀ n, S (P.X n) := by
  let e := ComplexShape.embeddingUpIntLE b
  let M := L.restriction e
  have hM (k : ℕ) : T (M.homology k) :=
    T.prop_of_iso ((HomologicalComplex.homologyMapIso (L.isoRestrictionExtend e) _) ≪≫
      M.extendHomologyIso e rfl) (hL (e.f k))
  obtain ⟨Q, φ, _, hQ⟩ := ChainComplex.exists_quasiIso_of_liftsAlongEpi S T hST hS hlift M hM
  exact ⟨Q.extend e, inferInstanceAs ((Q.extend e).IsStrictlySupported e),
    HomologicalComplex.extendMap φ e ≫ (L.isoRestrictionExtend e).inv, inferInstance,
    HomologicalComplex.prop_extend_X S e hQ⟩

end CochainComplex
