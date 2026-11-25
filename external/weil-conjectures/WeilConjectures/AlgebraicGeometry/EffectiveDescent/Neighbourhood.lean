/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.EffectiveDescent.Invariant
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiniteFlatNorm
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Invariant affine neighbourhoods for descent data along finite locally free morphisms

Let `p : X ⟶ Y` be finite, flat and locally of finite presentation, and let `D` be a descent
datum on a scheme `V` over `X` relative to `p`. Write `P = V ×_Y X`, with first projection
`fst : P ⟶ V` and universal transport `φ = D.univ : P ⟶ V`. Two points `w, w'` of `V` are in the
same *orbit* if `w = fst z` and `w' = φ z` for some point `z` of `P`.

If every finite set of points of `V` lying over one point of `Y` lies in an affine open, then
every point of `V` has an affine open neighbourhood which is invariant under `D` (Stacks 03JE,
0H8K). The proof:

1. For an open `T` of `V`, the set `S(T)` of points whose whole orbit lies in `T` is open (as
   `fst` is a closed map) and invariant (the orbit relation is transitive, by the cocycle
   condition).
2. Around the image of `v` in `Y` choose an affine open `W` over which `p` is free. The orbit
   of `v` is finite and lies over `W`, hence in an affine open `A`, and by prime avoidance in a
   basic open `D(f) ⊆ A ∩ S(A ∩ q⁻¹ W)`.
3. The norm `g` of `φ^* f` along the finite free map `fst⁻¹ D(f) ⟶ D(f)` cuts out
   `D(g) = S(D(f))`, an invariant affine neighbourhood of `v`.

## Main statements

- `CategoryTheory.Over.DescentDatum.exists_isInvariant_isAffineOpen_of_fibre`,
  `CategoryTheory.Over.DescentDatum.exists_isInvariant_isAffineOpen`: invariant affine
  neighbourhoods.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace CategoryTheory.Over.DescentDatum

open AlgebraicGeometry

variable {X Y : Scheme.{u}} {p : X ⟶ Y} {V : Over X} (D : DescentDatum p V)

/-- The universal transport and the first projection `V ×_Y X ⟶ V` agree after mapping to `Y`.
-/
@[reassoc]
lemma univ_comp_hom_comp : D.univ ≫ V.hom ≫ p = pullback.fst (V.hom ≫ p) p ≫ V.hom ≫ p := by
  rw [univ_hom_assoc, pullback.condition]

lemma univ_apply_hom_comp (z : ↥(Limits.pullback (V.hom ≫ p) p)) :
    (V.hom ≫ p) (D.univ z) = (V.hom ≫ p) (pullback.fst (V.hom ≫ p) p z) := by
  rw [← Scheme.Hom.comp_apply, D.univ_comp_hom_comp, Scheme.Hom.comp_apply]

/-- **Reflexivity of the orbit relation.** Every point `w` of `V` is the first projection and the
universal transport of a point of `V ×_Y X` (the diagonal point). -/
lemma exists_fst_eq_univ_eq (w : V.left) :
    ∃ z, pullback.fst (V.hom ≫ p) p z = w ∧ D.univ z = w := by
  refine ⟨pullback.lift (𝟙 V.left) V.hom (by simp) w, ?_, ?_⟩
  · rw [← Scheme.Hom.comp_apply, pullback.lift_fst]
    rfl
  · rw [← Scheme.Hom.comp_apply, lift_univ]
    rfl

/-- The pair `(fst ∘ a, snd ∘ b)` of `T`-points defines a `T`-point of `V ×_Y X` when
`φ ∘ a = fst ∘ b`. -/
lemma lift_fst_snd_condition {T : Scheme.{u}} (a b : T ⟶ Limits.pullback (V.hom ≫ p) p)
    (hab : a ≫ D.univ = b ≫ pullback.fst (V.hom ≫ p) p) :
    (a ≫ pullback.fst (V.hom ≫ p) p) ≫ V.hom ≫ p = (b ≫ pullback.snd (V.hom ≫ p) p) ≫ p := by
  rw [Category.assoc, ← D.univ_comp_hom_comp, reassoc_of% hab, pullback.condition,
    Category.assoc]

/-- **The cocycle condition for the universal transport.** For `T`-points `a, b` of `V ×_Y X`
with `φ ∘ a = fst ∘ b`, the point `(fst ∘ a, snd ∘ b)` is transported to `φ ∘ b`. -/
lemma lift_fst_snd_univ {T : Scheme.{u}} (a b : T ⟶ Limits.pullback (V.hom ≫ p) p)
    (hab : a ≫ D.univ = b ≫ pullback.fst (V.hom ≫ p) p) :
    pullback.lift (a ≫ pullback.fst (V.hom ≫ p) p) (b ≫ pullback.snd (V.hom ≫ p) p)
      (D.lift_fst_snd_condition a b hab) ≫ D.univ = b ≫ D.univ := by
  have h₁₂ : (a ≫ pullback.fst (V.hom ≫ p) p ≫ V.hom) ≫ p =
      (a ≫ pullback.snd (V.hom ≫ p) p) ≫ p := by
    simp only [Category.assoc, pullback.condition]
  have h₂₃ : (a ≫ pullback.snd (V.hom ≫ p) p) ≫ p = (b ≫ pullback.snd (V.hom ≫ p) p) ≫ p := by
    simp only [Category.assoc, ← pullback.condition, ← reassoc_of% hab, D.univ_comp_hom_comp]
  let α : Over.mk (a ≫ pullback.fst (V.hom ≫ p) p ≫ V.hom) ⟶ V :=
    Over.homMk (a ≫ pullback.fst (V.hom ≫ p) p) (by simp)
  let β : Over.mk (a ≫ pullback.snd (V.hom ≫ p) p) ⟶ V :=
    Over.homMk (b ≫ pullback.fst (V.hom ≫ p) p) (by
      rw [← hab, Category.assoc, univ_hom]
      rfl)
  have e₂ : (D.transport _ _ h₁₂ α).left = β.left := by
    rw [D.transport_left_eq]
    refine (congrArg (· ≫ D.univ) ?_).trans hab
    ext <;> simp [α]
  have e₃ := D.transport_left_eq _ _ (h₁₂.trans h₂₃) α
  rw [← D.transport_transport _ _ _ h₁₂ h₂₃, D.transport_left_congr' h₂₃ h₂₃ rfl rfl β _ e₂,
    D.transport_left_eq] at e₃
  refine e₃.symm.trans ?_
  congr 1
  ext <;> simp [β]

/-- **Transitivity of the orbit relation.** If `φ z₁ = fst z₂`, some point `z₃` has
`fst z₃ = fst z₁` and `φ z₃ = φ z₂`. -/
lemma exists_fst_eq_univ_eq_of_univ_eq_fst (z₁ z₂ : ↥(Limits.pullback (V.hom ≫ p) p))
    (h : D.univ z₁ = pullback.fst (V.hom ≫ p) p z₂) :
    ∃ z₃, pullback.fst (V.hom ≫ p) p z₃ = pullback.fst (V.hom ≫ p) p z₁ ∧
      D.univ z₃ = D.univ z₂ := by
  obtain ⟨t, ht₁, ht₂⟩ := Scheme.Pullback.exists_preimage_pullback z₁ z₂ h
  refine ⟨pullback.lift _ _ (D.lift_fst_snd_condition _ _ pullback.condition) t, ?_, ?_⟩
  · rw [← Scheme.Hom.comp_apply, pullback.lift_fst, Scheme.Hom.comp_apply, ht₁]
  · rw [← Scheme.Hom.comp_apply, D.lift_fst_snd_univ _ _ pullback.condition,
      Scheme.Hom.comp_apply, ht₂]

/-- An open `U` of `V` cut out as the set of points whose whole orbit lies in a set `T` is
invariant. -/
lemma isInvariant_of_forall_mem_iff (U : V.left.Opens) (T : Set V.left)
    (hU : ∀ w, w ∈ U ↔ ∀ z, pullback.fst (V.hom ≫ p) p z = w → D.univ z ∈ T) :
    D.IsInvariant U := by
  refine (D.isInvariant_iff U).mpr fun z hz ↦ (hU _).mpr fun z' hz' ↦ ?_
  obtain ⟨z₃, h₁, h₂⟩ := D.exists_fst_eq_univ_eq_of_univ_eq_fst z z' hz'.symm
  exact h₂ ▸ (hU _).mp hz z₃ h₁

/-- The set of points of `V` whose whole orbit lies in an open `T` is open: its complement is the
image of the closed set `φ⁻¹(V ∖ T)` under the finite, hence closed, projection `fst`. -/
lemma isOpen_setOf_forall_univ_mem [IsFinite p] {T : Set V.left} (hT : IsOpen T) :
    IsOpen {w | ∀ z, pullback.fst (V.hom ≫ p) p z = w → D.univ z ∈ T} := by
  have e : {w | ∀ z, pullback.fst (V.hom ≫ p) p z = w → D.univ z ∈ T} =
      (pullback.fst (V.hom ≫ p) p '' (D.univ ⁻¹' Tᶜ))ᶜ := by
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_image, Set.mem_preimage,
      not_exists, not_and]
    exact forall_congr' fun z ↦ ⟨fun h hz hw ↦ hz (h hw), fun h hw ↦ by_contra (h · hw)⟩
  rw [e, isOpen_compl_iff]
  exact (pullback.fst (V.hom ≫ p) p).isClosedMap _
    (hT.isClosed_compl.preimage D.univ.continuous)

/-- **Invariant affine neighbourhoods** (Stacks 03JE, 0H8K). Let `p : X ⟶ Y` be finite, flat and
locally of finite presentation and `D` a descent datum on `V` relative to `p`. If every finite set
of points of `V` lying over one point of `Y` lies in an affine open (the hypothesis of Stacks
0CCI), then every point `v` of `V` has an affine open neighbourhood `U` which is invariant under
`D` and lies over an affine open of `Y`.

(blueprint: `proposition-jacobian-over-ground-field--1`, a step of the proof) -/
theorem exists_isInvariant_isAffineOpen_of_fibre [IsFinite p] [Flat p]
    [LocallyOfFinitePresentation p] (D : DescentDatum p V)
    (hV : ∀ (y : Y) (s : Set V.left), s.Finite → (∀ x ∈ s, (V.hom ≫ p) x = y) →
      ∃ U : V.left.Opens, IsAffineOpen U ∧ s ⊆ U)
    (v : V.left) :
    ∃ U : V.left.Opens, v ∈ U ∧ D.IsInvariant U ∧ IsAffineOpen U ∧
      ∃ W : Y.Opens, IsAffineOpen W ∧ U ≤ (V.hom ≫ p) ⁻¹ᵁ W := by
  obtain ⟨W, hW, hvW, hfree⟩ := p.exists_isAffineOpen_mem_free_app ((V.hom ≫ p) v)
  -- the orbit of `v`
  let O := D.univ '' (pullback.fst (V.hom ≫ p) p ⁻¹' {v})
  have hOfin : O.Finite :=
    ((pullback.fst (V.hom ≫ p) p).finite_preimage_singleton v).image _
  obtain ⟨A, hA, hOA⟩ := hV ((V.hom ≫ p) v) O hOfin (by
    rintro _ ⟨z, hz, rfl⟩
    rw [D.univ_apply_hom_comp, Set.mem_singleton_iff.mp hz])
  let G : V.left.Opens := ⟨_, D.isOpen_setOf_forall_univ_mem (A ⊓ (V.hom ≫ p) ⁻¹ᵁ W).isOpen⟩
  have hGle : G ≤ A ⊓ (V.hom ≫ p) ⁻¹ᵁ W := fun w hw ↦ by
    obtain ⟨z, hz₁, hz₂⟩ := D.exists_fst_eq_univ_eq w
    exact hz₂ ▸ hw z hz₁
  have hOG : O ⊆ G := by
    rintro _ ⟨z₀, hz₀, rfl⟩ z hz
    obtain ⟨z₃, h₁, h₂⟩ := D.exists_fst_eq_univ_eq_of_univ_eq_fst z₀ z hz.symm
    have hz₃ : D.univ z ∈ O := ⟨z₃, h₁.trans hz₀, h₂⟩
    refine ⟨hOA hz₃, ?_⟩
    rw [SetLike.mem_coe, Scheme.Hom.mem_preimage, ← h₂, D.univ_apply_hom_comp, h₁,
      Set.mem_singleton_iff.mp hz₀]
    exact hvW
  -- a basic open `D(f)` of `A` containing the orbit of `v`, inside `G`
  obtain ⟨f, hOf, hfG⟩ := hA.exists_basicOpen_le_of_finite (O := G ⊓ A) inf_le_right hOfin
    (Set.subset_inter hOG hOA)
  have hfW : V.left.basicOpen f ≤ (V.hom ≫ p) ⁻¹ᵁ W :=
    hfG.trans (inf_le_left.trans (hGle.trans inf_le_right))
  have hfree' := free_app_of_isPullback (IsPullback.of_hasPullback (V.hom ≫ p) p) hW
    (hW.preimage p) (hA.basicOpen f) hfW hfree
  have hle : pullback.fst (V.hom ≫ p) p ⁻¹ᵁ V.left.basicOpen f ≤ D.univ ⁻¹ᵁ A :=
    fun z hz ↦ ((inf_le_left : G ⊓ A ≤ G) (hfG hz) z rfl).1
  -- the norm of `φ^* f` along `fst⁻¹ D(f) ⟶ D(f)`
  let h := D.univ.appLE A (pullback.fst (V.hom ≫ p) p ⁻¹ᵁ V.left.basicOpen f) hle f
  let g := (pullback.fst (V.hom ≫ p) p).normAt (V.left.basicOpen f) h
  have key (w : V.left) : w ∈ V.left.basicOpen g ↔
      ∀ z, pullback.fst (V.hom ≫ p) p z = w → D.univ z ∈ V.left.basicOpen f := by
    have hiff (hw : w ∈ V.left.basicOpen f) :=
      mem_basicOpen_normAt_of_free _ (hA.basicOpen f) hfree' h hw
    refine ⟨fun hw z hz ↦ ?_, fun hw ↦ ?_⟩
    · have := (hiff (V.left.basicOpen_le g hw)).mp hw z hz
      rw [Scheme.basicOpen_appLE] at this
      exact this.2
    · obtain ⟨z, hz₁, hz₂⟩ := D.exists_fst_eq_univ_eq w
      have hwf : w ∈ V.left.basicOpen f := hz₂ ▸ hw z hz₁
      refine (hiff hwf).mpr fun z hz ↦ ?_
      rw [Scheme.basicOpen_appLE]
      refine ⟨?_, hw z hz⟩
      rw [SetLike.mem_coe, Scheme.Hom.mem_preimage, hz]
      exact hwf
  exact ⟨V.left.basicOpen g, (key v).mpr fun z hz ↦ hOf ⟨z, hz, rfl⟩,
    D.isInvariant_of_forall_mem_iff _ _ key, (hA.basicOpen f).basicOpen g, W, hW,
    (V.left.basicOpen_le g).trans hfW⟩

/-- **Invariant affine neighbourhoods** (Stacks 03JE, 0H8K). Let `p : X ⟶ Y` be finite, flat and
locally of finite presentation and `D` a descent datum on `V` relative to `p`. If every finite set
of points of `V` lies in an affine open, then every point `v` of `V` has an affine open
neighbourhood `U` which is invariant under `D` and lies over an affine open of `Y`.

(blueprint: `proposition-jacobian-over-ground-field--1`, a step of the proof) -/
theorem exists_isInvariant_isAffineOpen [IsFinite p] [Flat p] [LocallyOfFinitePresentation p]
    (D : DescentDatum p V)
    (hV : ∀ s : Set V.left, s.Finite → ∃ U : V.left.Opens, IsAffineOpen U ∧ s ⊆ U)
    (v : V.left) :
    ∃ U : V.left.Opens, v ∈ U ∧ D.IsInvariant U ∧ IsAffineOpen U ∧
      ∃ W : Y.Opens, IsAffineOpen W ∧ U ≤ (V.hom ≫ p) ⁻¹ᵁ W :=
  D.exists_isInvariant_isAffineOpen_of_fibre (fun _ s hs _ ↦ hV s hs) v

end CategoryTheory.Over.DescentDatum
