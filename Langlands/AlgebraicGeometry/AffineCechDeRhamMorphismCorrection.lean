import Langlands.AlgebraicGeometry.AffineCechDeRhamIdealPrimitives
import Mathlib.LinearAlgebra.Basis.Defs

/-! # Correcting affine pullbacks from their degree-one Hodge classes -/

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeq (inter inter_le_comp)

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.AffineCechDeRham

section Algebra

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] {I : Ideal R}

private lemma mul_zero_of_mem_extendedIdeal (hI : I * I = ⊥) {x y : B}
    (hx : x ∈ I.map (algebraMap R B)) (hy : y ∈ I.map (algebraMap R B)) : x * y = 0 := by
  have h := Ideal.mul_mem_mul hx hy
  rwa [← Ideal.map_mul, hI, Ideal.map_bot, Ideal.mem_bot] at h

private def subtractDerivation (s : A →ₐ[R] B) (hI : I * I = ⊥)
    (C : Ω[A⁄R] →ₛₗ[s.toRingHom] B)
    (hC : ∀ ω, C ω ∈ I.map (algebraMap R B)) : A →ₐ[R] B where
  toFun a := s a - C (KaehlerDifferential.D R A a)
  map_zero' := by simp
  map_one' := by simp
  map_add' a b := by simp only [map_add]; abel
  map_mul' a b := by
    simp only [map_mul, (KaehlerDifferential.D R A).leibniz, map_add, C.map_smulₛₗ]
    change s a * s b - (s a * C (KaehlerDifferential.D R A b) +
      s b * C (KaehlerDifferential.D R A a)) =
      (s a - C (KaehlerDifferential.D R A a)) * (s b - C (KaehlerDifferential.D R A b))
    have h := mul_zero_of_mem_extendedIdeal hI (hC (KaehlerDifferential.D R A a))
      (hC (KaehlerDifferential.D R A b))
    linear_combination -h
  commutes' a := by rw [Derivation.map_algebraMap, map_zero, sub_zero, s.commutes]

@[simp]
private lemma subtractDerivation_apply (s : A →ₐ[R] B) (hI : I * I = ⊥)
    (C : Ω[A⁄R] →ₛₗ[s.toRingHom] B) (hC : ∀ ω, C ω ∈ I.map (algebraMap R B)) (a : A) :
    subtractDerivation s hI C hC a = s a - C (KaehlerDifferential.D R A a) := rfl

variable {κ : Type u}

private def contractionOfBasis (s : A →ₐ[R] B) (e : Module.Basis κ A Ω[A⁄R])
    (v : κ → B) : Ω[A⁄R] →ₛₗ[s.toRingHom] B := by
  letI : Module A B := Module.compHom B s.toRingHom
  let C := e.constr ℕ v
  exact { C.toAddMonoidHom with map_smul' := C.map_smul }

@[simp]
private lemma contractionOfBasis_basis (s : A →ₐ[R] B) (e : Module.Basis κ A Ω[A⁄R])
    (v : κ → B) (k : κ) : contractionOfBasis s e v (e k) = v k := by
  let : Module A B := Module.compHom B s.toRingHom
  exact e.constr_basis ℕ v k

variable [Fintype κ]

private lemma contraction_sum (s : A →ₐ[R] B) (e : Module.Basis κ A Ω[A⁄R])
    (C : Ω[A⁄R] →ₛₗ[s.toRingHom] B) (w : Ω[A⁄R]) :
    C w = ∑ k, s (e.repr w k) * C (e k) := by
  conv_lhs => rw [← e.sum_repr w, map_sum]
  exact Finset.sum_congr rfl fun k _ => C.map_smulₛₗ _ _

private lemma contractionOfBasis_mem (s : A →ₐ[R] B) (e : Module.Basis κ A Ω[A⁄R])
    (v : κ → B) (hv : ∀ k, v k ∈ I.map (algebraMap R B)) (w : Ω[A⁄R]) :
    contractionOfBasis s e v w ∈ I.map (algebraMap R B) := by
  rw [contraction_sum s e]
  exact Ideal.sum_mem _ fun k _ => by
    rw [contractionOfBasis_basis]
    exact Ideal.mul_mem_left _ _ (hv k)

end Algebra

variable {R : Type u} [CommRing R] {X Y : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of R)} {g : Y ⟶ Spec (CommRingCat.of R)}
  {U : Scheme.AffineOpenCover.{u} X} {V : Scheme.AffineOpenCover.{u} Y}
  {κ : Type u}

open RelativeForms

/-- Compatible closed forms whose restrictions are bases over the coordinate
rings of every tuple intersection. -/
structure ClosedFormBasis (g : Y ⟶ Spec (CommRingCat.of R)) (V : Scheme.AffineOpenCover.{u} Y)
    (κ : Type u) where
  forms : κ → closedForms g V
  basis : ∀ {p : ℕ} (τ : Fin (p + 1) → V.I₀), Module.Basis κ (tupleSections g V τ)
    Ω[(tupleSections g V τ)⁄R]
  basis_apply : ∀ {p : ℕ} (τ : Fin (p + 1) → V.I₀) (i : Fin (p + 1)) (k : κ),
    basis τ k = restrictCochain (oneForms g) (forms k).val τ (fun _ => i)

namespace LocalPullbacks

variable {I : Ideal R} {β : U.I₀ → V.I₀} [Fintype κ]
  (L : LocalPullbacks (f := f) (g := g) I β) (hI : I * I = ⊥)
  (e : ClosedFormBasis g V κ)
  (a : κ → C0 f U)
  (ha : ∀ (k : κ) (σ : Fin 1 → U.I₀), a k σ ∈ I.map (algebraMap R (tupleSections f U σ)))

private def correction {p : ℕ} (τ : Fin (p + 1) → U.I₀) (i : Fin (p + 1)) :=
  contractionOfBasis (L.sections τ i) (e.basis (β ∘ τ))
    (fun k => restrictCochain (functions f) (a k) τ (fun _ => i))

include ha in
private lemma correction_mem {p : ℕ} (τ : Fin (p + 1) → U.I₀) (i : Fin (p + 1))
    (ω : Ω[(tupleSections g V (β ∘ τ))⁄R]) :
    L.correction e a τ i ω ∈ I.map (algebraMap R (tupleSections f U τ)) :=
  contractionOfBasis_mem _ _ _
    (fun k => map_mem_extendedIdeal (restrictSections f U τ (fun _ : Fin 1 => i)) (ha k _)) ω

omit [Fintype κ] in
private lemma correction_basis {p : ℕ} (τ : Fin (p + 1) → U.I₀) (i : Fin (p + 1)) (k : κ) :
    L.correction e a τ i (e.basis (β ∘ τ) k) =
      restrictCochain (functions f) (a k) τ (fun _ => i) :=
  contractionOfBasis_basis _ _ _ _

/-- Subtract the derivations whose values on the basis of closed forms are
the local function primitives. -/
def correctedSections {p : ℕ} (τ : Fin (p + 1) → U.I₀) (i : Fin (p + 1)) :
    tupleSections g V (β ∘ τ) →ₐ[R] tupleSections f U τ :=
  subtractDerivation (L.sections τ i) hI (L.correction e a τ i) (L.correction_mem e a ha τ i)

/-- The corrections retain the original maps on reduction. -/
lemma sections_sub_correctedSections_mem {p : ℕ} (τ : Fin (p + 1) → U.I₀) (i : Fin (p + 1))
    (x : tupleSections g V (β ∘ τ)) :
    L.sections τ i x - L.correctedSections hI e a ha τ i x ∈
      I.map (algebraMap R (tupleSections f U τ)) := by
  rw [correctedSections, subtractDerivation_apply, sub_sub_cancel]
  exact L.correction_mem e a ha τ i _

omit [Fintype κ] in
private lemma restrict_basis {p q : ℕ} (τ : Fin (q + 1) → U.I₀)
    (θ : Fin (p + 1) → Fin (q + 1)) (i : Fin (p + 1)) (k : κ) :
    mapOne (restrictSections g V (β ∘ τ) θ) (e.basis (β ∘ (τ ∘ θ)) k) =
      e.basis (β ∘ τ) k := by
  rw [e.basis_apply (β ∘ (τ ∘ θ)) i, e.basis_apply (β ∘ τ) (θ i)]
  let P := oneForms g
  change P.map (homOfLE (inter_le_comp (β ∘ τ) θ)).op
      (P.map (homOfLE (inter_le_comp (β ∘ τ ∘ θ) (fun _ : Fin 1 => i))).op
        ((e.forms k).val (β ∘ τ ∘ θ ∘ fun _ => i))) = _
  change (P.map (homOfLE (inter_le_comp (β ∘ τ ∘ θ) (fun _ : Fin 1 => i))).op ≫
    P.map (homOfLE (inter_le_comp (β ∘ τ) θ)).op)
      ((e.forms k).val (β ∘ τ ∘ θ ∘ fun _ => i)) = _
  rw [← Functor.map_comp]
  rfl

private lemma restrict_correction {p q : ℕ} (τ : Fin (q + 1) → U.I₀)
    (θ : Fin (p + 1) → Fin (q + 1)) (i : Fin (p + 1))
    (ω : Ω[(tupleSections g V (β ∘ (τ ∘ θ)))⁄R]) :
    restrictSections f U τ θ (L.correction e a (τ ∘ θ) i ω) =
      L.correction e a τ (θ i) (mapOne (restrictSections g V (β ∘ τ) θ) ω) := by
  conv_lhs => rw [contraction_sum (L.sections (τ ∘ θ) i) (e.basis (β ∘ (τ ∘ θ))), map_sum]
  conv_rhs =>
    rw [← (e.basis (β ∘ (τ ∘ θ))).sum_repr ω, map_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, (mapOne _).map_smulₛₗ, (L.correction e a τ (θ i)).map_smulₛₗ,
    restrict_basis e τ θ i k, L.correction_basis, L.correction_basis]
  have hs := DFunLike.congr_fun (L.restrict_sections τ θ i) ((e.basis (β ∘ (τ ∘ θ))).repr ω k)
  let P := functions f
  have hr :
      P.map (homOfLE (inter_le_comp τ θ)).op
          (restrictCochain P (a k) (τ ∘ θ) (fun _ : Fin 1 => i)) =
        restrictCochain P (a k) τ (fun _ : Fin 1 => θ i) := by
    change (P.map (homOfLE (inter_le_comp (τ ∘ θ) (fun _ : Fin 1 => i))).op ≫
      P.map (homOfLE (inter_le_comp τ θ)).op) (a k (τ ∘ θ ∘ fun _ => i)) = _
    rw [← Functor.map_comp]
    rfl
  exact congrArg₂ (· * ·) hs hr

/-- Correcting pullback maps commutes with restriction at a fixed vertex. -/
lemma restrict_correctedSections {p q : ℕ} (τ : Fin (q + 1) → U.I₀)
    (θ : Fin (p + 1) → Fin (q + 1)) (i : Fin (p + 1)) :
    (restrictSections f U τ θ).comp (L.correctedSections hI e a ha (τ ∘ θ) i) =
      (L.correctedSections hI e a ha τ (θ i)).comp (restrictSections g V (β ∘ τ) θ) := by
  ext x
  simp only [AlgHom.comp_apply, correctedSections, subtractDerivation_apply, map_sub]
  rw [← mapOne_d]
  exact congrArg₂ (· - ·) (DFunLike.congr_fun (L.restrict_sections τ θ i) x)
    (L.restrict_correction e a τ θ i (KaehlerDifferential.D R _ x))

/-- If the chosen ideal-valued primitives are the contractions of the differences,
the corrected maps from the two vertices coincide on every pair intersection. -/
theorem correctedSections_eq_of_primitives
    (h : ∀ (k : κ) (τ : Fin 2 → U.I₀), cechD U (functions f) 0 (a k) τ =
      L.contraction hI τ 1 0 (e.basis (β ∘ τ) k)) (τ : Fin 2 → U.I₀) :
    L.correctedSections hI e a ha τ 1 = L.correctedSections hI e a ha τ 0 := by
  let s₀ := L.sections τ 0
  let s₁ := L.sections τ 1
  let c₀ := L.correction e a τ 0
  let c₁ := L.correction e a τ 1
  let b := e.basis (β ∘ τ)
  have hc (ω : Ω[(tupleSections g V (β ∘ τ))⁄R]) :
      L.contraction hI τ 1 0 ω = c₁ ω - c₀ ω := by
    rw [contraction_sum s₁ b (L.contraction hI τ 1 0), contraction_sum s₁ b c₁,
      contraction_sum s₀ b c₀, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hω := (h k τ).symm
    rw [cechD_zero_eq_sub_restrict, ← L.correction_basis e a τ 1 k,
      ← L.correction_basis e a τ 0 k] at hω
    change L.contraction hI τ 1 0 (b k) = c₁ (b k) - c₀ (b k) at hω
    rw [hω, mul_sub]
    have hz : (s₁ (b.repr ω k) - s₀ (b.repr ω k)) * c₀ (b k) = 0 :=
      mul_zero_of_mem_extendedIdeal hI (L.congruent τ 1 0 _) (L.correction_mem e a ha τ 0 _)
    rw [sub_mul, sub_eq_zero] at hz
    rw [hz]
  ext x
  simp only [correctedSections, subtractDerivation_apply]
  have hx := hc (KaehlerDifferential.D R _ x)
  change contractDifferenceOne s₁ s₀ hI (L.congruent τ 1 0) (KaehlerDifferential.D R _ x) = _ at hx
  rw [contractDifferenceOne_d] at hx
  exact sub_eq_sub_iff_sub_eq_sub.mpr hx

end LocalPullbacks
end Langlands.AlgebraicGeometry.AffineCechDeRham
