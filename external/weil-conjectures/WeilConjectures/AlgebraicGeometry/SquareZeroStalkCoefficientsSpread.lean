/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.Module.ULift
import Mathlib.Data.Int.Interval

/-! # Spreading finite square-zero coefficient data

Source: Stacks Project, Tags 0BCD, 0BC7 and 00CR, finite-matrix spreading.
-/

@[expose] public section
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

private def coordMatrix {R : Type u} [CommRing R] {n m : ℕ}
    (f : ModuleCat.of R (ULift.{0} (Fin n → R)) ⟶
      ModuleCat.of R (ULift.{0} (Fin m → R))) : Matrix (Fin m) (Fin n) R :=
  LinearMap.toMatrix' ((ULift.moduleEquiv : ULift.{0} (Fin m → R) ≃ₗ[R] _).toLinearMap
    ∘ₗ f.hom ∘ₗ (ULift.moduleEquiv : ULift.{0} (Fin n → R) ≃ₗ[R] _).symm.toLinearMap)

private noncomputable def coordMap {R : Type u} [CommRing R] {n m : ℕ}
    (A : Matrix (Fin m) (Fin n) R) :
    ModuleCat.of R (ULift.{0} (Fin n → R)) ⟶
      ModuleCat.of R (ULift.{0} (Fin m → R)) :=
  ModuleCat.ofHom
    ((ULift.moduleEquiv : ULift.{0} (Fin m → R) ≃ₗ[R] _).symm.toLinearMap
      ∘ₗ Matrix.toLin' A ∘ₗ
        (ULift.moduleEquiv : ULift.{0} (Fin n → R) ≃ₗ[R] _).toLinearMap)

private lemma coordMatrix_apply {R : Type u} [CommRing R] {n m : ℕ}
    (f : ModuleCat.of R (ULift.{0} (Fin n → R)) ⟶
      ModuleCat.of R (ULift.{0} (Fin m → R))) (p : Fin n) (q : Fin m) :
    coordMatrix f q p = (f (ULift.up (Pi.single p 1))).down q := rfl

private lemma coordMatrix_comp {R : Type u} [CommRing R] {n m k : ℕ}
    (f : ModuleCat.of R (ULift.{0} (Fin n → R)) ⟶
      ModuleCat.of R (ULift.{0} (Fin m → R)))
    (g : ModuleCat.of R (ULift.{0} (Fin m → R)) ⟶
      ModuleCat.of R (ULift.{0} (Fin k → R))) :
    coordMatrix (f ≫ g) = coordMatrix g * coordMatrix f := by
  unfold coordMatrix
  rw [← LinearMap.toMatrix'_comp]
  congr 1

private lemma coordMatrix_zero {R : Type u} [CommRing R] {n m : ℕ} :
    coordMatrix (0 : ModuleCat.of R (ULift.{0} (Fin n → R)) ⟶
      ModuleCat.of R (ULift.{0} (Fin m → R))) = 0 := by
  ext q p
  rfl

private lemma coordMatrix_injective {R : Type u} [CommRing R] {n m : ℕ} :
    Function.Injective (coordMatrix (R := R) (n := n) (m := m)) := by
  intro f g h
  have h' := LinearMap.toMatrix'.injective h
  ext w q
  exact congrFun (LinearMap.congr_fun h' w.down) q

private lemma coordMatrix_coordMap {R : Type u} [CommRing R] {n m : ℕ}
    (A : Matrix (Fin m) (Fin n) R) : coordMatrix (coordMap A) = A := by
  exact LinearMap.toMatrix'_toLin' A

private lemma finite_scalar_lift {X : Scheme.{u}} {κ : Type} [Finite κ]
    (x : X) (V : X.Opens) (hxV : x ∈ V) (a : κ → X.presheaf.stalk x) :
    ∃ (U : X.Opens) (_ : U ≤ V) (hxU : x ∈ U) (b : κ → Γ(X, U)),
      ∀ k, X.presheaf.germ U x hxU (b k) = a k := by
  classical
  let := Fintype.ofFinite κ
  choose W hWV hxW b hb using
    fun k ↦ X.presheaf.exists_le_germ_eq (a k) hxV
  let U := V ⊓ ⨅ k, W k
  have hUW (k : κ) : U ≤ W k := inf_le_right.trans (iInf_le _ k)
  have hxU : x ∈ U := ⟨hxV, by
    change x ∈ ((⨅ k, W k : X.Opens) : Set X)
    rw [TopologicalSpace.Opens.coe_iInf]
    exact Set.mem_iInter.mpr hxW⟩
  refine ⟨U, inf_le_left, hxU,
    fun k ↦ X.presheaf.map (homOfLE (hUW k)).op (b k), ?_⟩
  intro k
  exact (X.presheaf.germ_res_apply (homOfLE (hUW k)) x hxU (b k)).trans (hb k)

private lemma finite_scalar_zero {X : Scheme.{u}} {κ : Type} [Finite κ]
    (x : X) (V : X.Opens) (hxV : x ∈ V) (a : κ → Γ(X, V))
    (ha : ∀ k, X.presheaf.germ V x hxV (a k) = 0) :
    ∃ (U : X.Opens) (hUV : U ≤ V) (_ : x ∈ U),
      ∀ k, X.presheaf.map (homOfLE hUV).op (a k) = 0 := by
  classical
  let := Fintype.ofFinite κ
  have hz (k : κ) : X.presheaf.germ V x hxV (a k) =
      X.presheaf.germ V x hxV 0 := by simpa using ha k
  choose W hxW iW jW hW using fun k ↦ X.presheaf.germ_eq x hxV hxV (a k) 0 (hz k)
  let U := V ⊓ ⨅ k, W k
  have hUW (k : κ) : U ≤ W k := inf_le_right.trans (iInf_le _ k)
  have hxU : x ∈ U := ⟨hxV, by
    change x ∈ ((⨅ k, W k : X.Opens) : Set X)
    rw [TopologicalSpace.Opens.coe_iInf]
    exact Set.mem_iInter.mpr hxW⟩
  refine ⟨U, inf_le_left, hxU, ?_⟩
  intro k
  have h := congrArg (X.presheaf.map (homOfLE (hUW k)).op) (hW k)
  have hm : (iW k).op ≫ (homOfLE (hUW k)).op =
      (homOfLE (show U ≤ V from inf_le_left)).op := Subsingleton.elim _ _
  simpa only [map_zero, ← ConcreteCategory.comp_apply, ← Functor.map_comp, hm] using h

/-- Finite-support square-zero maps of coordinate modules spread to section modules.

Source: Stacks Project, Tags 0BCD and 0BC7, spreading finite presentation matrices;
Tag 00CR, localization as a filtered colimit.
(blueprint: lem-sc-square-zero-stalk-coefficients-spread).

Proof: Only the entries indexed by i in [a,b] can occur. Represent each entry of
δ i on a common open neighbourhood of x, by the elementwise description of a stalk.
The matrix product entries have zero germ by hδ. Represent the finitely many
zero-germ witnesses and intersect their neighbourhoods. Restrict further to an
affine open containing x. Define D by the lifted matrices on the standard bases;
the now-zero product entries give hD. In degrees with zero source or target there
is just the zero map. The germ equations on basis vectors are the chosen entry
representations. Empty support and rank zero require no entries or equations. -/
theorem exists_squareZero_stalk_coefficients_spread
    (X : Scheme.{u}) (x : X) (d : ℤ → ℕ) (a b : ℤ)
    (hd : ∀ i : ℤ, i < a ∨ b < i → d i = 0)
    (δ : ∀ i : ℤ, ModuleCat.of (X.presheaf.stalk x)
      (ULift.{0} (Fin (d i) → X.presheaf.stalk x)) ⟶
      ModuleCat.of (X.presheaf.stalk x)
        (ULift.{0} (Fin (d (i + 1)) → X.presheaf.stalk x)))
    (hδ : ∀ i, δ i ≫ δ (i + 1) = 0) :
    ∃ (U : X.Opens) (hxU : x ∈ U), IsAffineOpen U ∧
      ∃ D : ∀ i : ℤ, ModuleCat.of Γ(X, U) (ULift.{0} (Fin (d i) → Γ(X, U))) ⟶
          ModuleCat.of Γ(X, U) (ULift.{0} (Fin (d (i + 1)) → Γ(X, U))),
        (∀ i, D i ≫ D (i + 1) = 0) ∧
        ∀ i (p : Fin (d i)) (q : Fin (d (i + 1))),
          X.presheaf.germ U x hxU ((D i (ULift.up (Pi.single p 1))).down q) =
            ((δ i (ULift.up (Pi.single p 1))).down q)  := by
  classical
  let ι := {i : ℤ // i ∈ Finset.Icc a b}
  let κ := Σ i : ι, Fin (d (i.1 + 1)) × Fin (d i.1)
  let c : κ → X.presheaf.stalk x :=
    fun k ↦ coordMatrix (δ k.1.1) k.2.1 k.2.2
  obtain ⟨V, _, hxV, t, ht⟩ := finite_scalar_lift x ⊤ (by trivial) c
  let A (i : ℤ) : Matrix (Fin (d (i + 1))) (Fin (d i)) Γ(X, V) :=
    if hi : i ∈ Finset.Icc a b then fun q p ↦ t ⟨⟨i, hi⟩, q, p⟩ else 0
  have hg (i : ℤ) : (A i).map (X.presheaf.germ V x hxV) = coordMatrix (δ i) := by
    ext q p
    by_cases hi : i ∈ Finset.Icc a b
    · exact (by simpa only [A, dite_eq_left hi, Matrix.map_apply, c] using ht ⟨⟨i, hi⟩, q, p⟩)
    · have hz : d i = 0 := hd i (by simpa only [Finset.mem_Icc, not_and_or, not_le] using hi)
      exact Fin.elim0 (hz ▸ p)
  let τ := Σ i : ι, Fin (d (i.1 + 1 + 1)) × Fin (d i.1)
  let z : τ → Γ(X, V) := fun k ↦ (A (k.1.1 + 1) * A k.1.1) k.2.1 k.2.2
  have hz (k : τ) : X.presheaf.germ V x hxV (z k) = 0 := by
    have hh : (A (k.1.1 + 1) * A k.1.1).map (X.presheaf.germ V x hxV) = 0 := by
      rw [Matrix.map_mul, hg, hg, ← coordMatrix_comp, hδ, coordMatrix_zero]
    exact congrFun (congrFun hh k.2.1) k.2.2
  obtain ⟨W, hWV, hxW, hW⟩ := finite_scalar_zero x V hxV z hz
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUW⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxW W.2
  let ρ := X.presheaf.map (homOfLE (hUW.trans hWV)).op
  let B (i : ℤ) := (A i).map ρ
  have hB (i : ℤ) : B (i + 1) * B i = 0 := by
    ext q p
    by_cases hi : i ∈ Finset.Icc a b
    · have hh := congrArg (X.presheaf.map (homOfLE hUW).op) (hW ⟨⟨i, hi⟩, q, p⟩)
      have hm : (homOfLE hWV).op ≫ (homOfLE hUW).op =
          (homOfLE (hUW.trans hWV)).op := Subsingleton.elim _ _
      simpa only [B, ρ, ← Matrix.map_mul, z, map_zero, ← ConcreteCategory.comp_apply,
        ← Functor.map_comp, hm, Matrix.map_apply, Matrix.zero_apply] using hh
    · have hz : d i = 0 := hd i (by simpa only [Finset.mem_Icc, not_and_or, not_le] using hi)
      exact Fin.elim0 (hz ▸ p)
  refine ⟨U, hxU, hU, fun i ↦ coordMap (B i), ?_, ?_⟩
  · intro i
    apply coordMatrix_injective
    rw [coordMatrix_comp, coordMatrix_coordMap, coordMatrix_coordMap, hB, coordMatrix_zero]
  · intro i p q
    rw [← coordMatrix_apply, coordMatrix_coordMap]
    change X.presheaf.germ U x hxU (ρ (A i q p)) = _
    exact (X.presheaf.germ_res_apply (homOfLE (hUW.trans hWV)) x hxU (A i q p)).trans
      (congrFun (congrFun (hg i) q) p)


end AlgebraicGeometry.Scheme
