import Langlands.AlgebraicGeometry.CommonOpenGluing
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-!
# Countably many affine lines glued along the line with `p` inverted

Let `R` be a commutative ring and `p ∈ R`. For every `j : ℕ` take an affine line `Spec R[u_j]`,
and glue them all along the common open `Spec R[t][1/p]`, embedded in the `j`-th line by
`u_j = (t - p^j)/p^(j+1)`, that is `t = p^j + p^(j+1) u_j`. Over a valuation ring `R = O` with
`0 < ‖p‖ < 1`, the `O`-points of the `j`-th line are the disc `|t - p^j| ≤ |p|^(j+1)` of the
generic fibre, and these discs accumulate at `t = 0`. This is the separated, locally finite
type counterexample to the closedness assertion of Conrad's Corollary 5.7.

This module constructs the open immersions of the common open into the lines, the glued scheme
and its morphism to `Spec R`.
-/

noncomputable section

universe u

open CategoryTheory Polynomial
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

namespace DilatedLineChain

variable (R : Type u) [CommRing R] (p : R)

/-- The coordinate ring `R[t][1/p]` of the common open. -/
abbrev L : Type u := Localization.Away (C p : R[X])

/-- The image of `p` in `L`. -/
abbrev P : L R p := algebraMap R[X] (L R p) (C p)

/-- The coordinate `t` in `L`. -/
abbrev T : L R p := algebraMap R[X] (L R p) X

/-- The inverse of `p` in `L`. -/
abbrev e : L R p := IsLocalization.Away.invSelf (C p : R[X])

theorem P_mul_e : P R p * e R p = 1 := IsLocalization.Away.mul_invSelf _

theorem isUnit_P : IsUnit (P R p) := IsLocalization.Away.algebraMap_isUnit _

theorem algebraMap_R_L (a : R) : algebraMap R (L R p) a = algebraMap R[X] (L R p) (C a) := by
  rw [IsScalarTower.algebraMap_apply R R[X] (L R p), Polynomial.algebraMap_apply,
    Algebra.algebraMap_self, RingHom.id_apply]

/-- The coordinate `u_j = (t - p^j)/p^(j+1)` of the `j`-th line on the common open. -/
def σ (j : ℕ) : R[X] →+* L R p :=
  eval₂RingHom (algebraMap R (L R p)) ((T R p - P R p ^ j) * e R p ^ (j + 1))

/-- The coordinate `t = p^j + p^(j+1) u` on the `j`-th line with `p` inverted. -/
def τ (j : ℕ) : R[X] →+* L R p :=
  eval₂RingHom (algebraMap R (L R p)) (P R p ^ j + P R p ^ (j + 1) * T R p)

theorem σ_C (j : ℕ) (a : R) : σ R p j (C a) = algebraMap R[X] (L R p) (C a) := by
  rw [σ, coe_eval₂RingHom, eval₂_C, algebraMap_R_L]

theorem τ_C (j : ℕ) (a : R) : τ R p j (C a) = algebraMap R[X] (L R p) (C a) := by
  rw [τ, coe_eval₂RingHom, eval₂_C, algebraMap_R_L]

theorem σ_X (j : ℕ) : σ R p j X = (T R p - P R p ^ j) * e R p ^ (j + 1) := by
  rw [σ, coe_eval₂RingHom, eval₂_X]

theorem τ_X (j : ℕ) : τ R p j X = P R p ^ j + P R p ^ (j + 1) * T R p := by
  rw [τ, coe_eval₂RingHom, eval₂_X]

/-- `σ` extended to the localization. -/
def σ' (j : ℕ) : L R p →+* L R p :=
  IsLocalization.Away.lift (C p) (g := σ R p j) (by rw [σ_C]; exact isUnit_P R p)

/-- `τ` extended to the localization. -/
def τ' (j : ℕ) : L R p →+* L R p :=
  IsLocalization.Away.lift (C p) (g := τ R p j) (by rw [τ_C]; exact isUnit_P R p)

theorem σ'_algebraMap (j : ℕ) (a : R[X]) : σ' R p j (algebraMap R[X] (L R p) a) = σ R p j a :=
  IsLocalization.Away.lift_eq _ _ a

theorem τ'_algebraMap (j : ℕ) (a : R[X]) : τ' R p j (algebraMap R[X] (L R p) a) = τ R p j a :=
  IsLocalization.Away.lift_eq _ _ a

theorem σ'_comp (j : ℕ) : (σ' R p j).comp (algebraMap R[X] (L R p)) = σ R p j :=
  IsLocalization.Away.lift_comp _ _

theorem σ'_P (j : ℕ) : σ' R p j (P R p) = P R p := by
  rw [σ'_algebraMap, σ_C]

theorem τ'_P (j : ℕ) : τ' R p j (P R p) = P R p := by
  rw [τ'_algebraMap, τ_C]

theorem τ'_e (j : ℕ) : τ' R p j (e R p) = e R p := by
  have h : P R p * τ' R p j (e R p) = 1 := by
    rw [← τ'_P R p j, ← map_mul, P_mul_e, map_one]
  calc τ' R p j (e R p) = (P R p * e R p) * τ' R p j (e R p) := by rw [P_mul_e, one_mul]
    _ = e R p * (P R p * τ' R p j (e R p)) := by ring
    _ = e R p := by rw [h, mul_one]

theorem pow_P_mul_e (n : ℕ) : P R p ^ n * e R p ^ n = 1 := by
  rw [← mul_pow, P_mul_e, one_pow]

theorem σ'_τ' (j : ℕ) : (σ' R p j).comp (τ' R p j) = RingHom.id _ := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (C p : R[X]))
  apply Polynomial.ringHom_ext
  · intro a
    simp only [RingHom.comp_apply, τ'_algebraMap, τ_C, σ'_algebraMap, σ_C, RingHom.id_apply]
  · simp only [RingHom.comp_apply, τ'_algebraMap, τ_X, RingHom.id_apply]
    rw [map_add, map_mul, map_pow, map_pow, σ'_P, σ'_algebraMap, σ_X]
    linear_combination (T R p - P R p ^ j) * pow_P_mul_e R p (j + 1)

theorem τ'_σ' (j : ℕ) : (τ' R p j).comp (σ' R p j) = RingHom.id _ := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (C p : R[X]))
  apply Polynomial.ringHom_ext
  · intro a
    simp only [RingHom.comp_apply, σ'_algebraMap, σ_C, τ'_algebraMap, τ_C, RingHom.id_apply]
  · simp only [RingHom.comp_apply, σ'_algebraMap, σ_X, RingHom.id_apply]
    rw [map_mul, map_sub, map_pow, map_pow, τ'_P, τ'_e, τ'_algebraMap, τ_X]
    linear_combination T R p * pow_P_mul_e R p (j + 1)

/-- `σ'` is a ring automorphism of `L`. -/
def σEquiv (j : ℕ) : L R p ≃+* L R p :=
  RingEquiv.ofRingHom (σ' R p j) (τ' R p j) (σ'_τ' R p j) (τ'_σ' R p j)

/-- The inclusion of the common open into the `j`-th line. -/
def g (j : ULift.{u} ℕ) : Spec (CommRingCat.of (L R p)) ⟶ Spec (CommRingCat.of R[X]) :=
  Spec.map (CommRingCat.ofHom (σ R p j.down))

theorem g_eq (j : ULift.{u} ℕ) : g R p j =
    Spec.map (CommRingCat.ofHom (σ' R p j.down)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R[X] (L R p))) := by
  rw [g, ← Spec.map_comp, ← CommRingCat.ofHom_comp, σ'_comp]

instance (j : ULift.{u} ℕ) : IsOpenImmersion (g R p j) := by
  have : IsIso (CommRingCat.ofHom (σ' R p j.down)) :=
    (σEquiv R p j.down).toCommRingCatIso.isIso_hom
  rw [g_eq]
  infer_instance

/-- The glued scheme. -/
abbrev glued : Scheme.{u} :=
  CommonOpenGluing.glued (fun _ : ULift.{u} ℕ => Spec (CommRingCat.of R[X]))
    (Spec (CommRingCat.of (L R p))) (g R p)

/-- The `j`-th line in the glued scheme. -/
abbrev ι (j : ULift.{u} ℕ) : Spec (CommRingCat.of R[X]) ⟶ glued R p :=
  CommonOpenGluing.ι (fun _ : ULift.{u} ℕ => Spec (CommRingCat.of R[X]))
    (Spec (CommRingCat.of (L R p))) (g R p) j

theorem σ_comp_algebraMap (j : ℕ) :
    (σ R p j).comp (algebraMap R R[X]) = algebraMap R (L R p) := by
  ext a
  rw [RingHom.comp_apply, Polynomial.algebraMap_apply, Algebra.algebraMap_self,
    RingHom.id_apply, σ_C, algebraMap_R_L]

/-- All lines have the same structure morphism on the common open. -/
theorem g_comp_structure (i j : ULift.{u} ℕ) :
    g R p i ≫ Spec.map (CommRingCat.ofHom (algebraMap R R[X])) =
      g R p j ≫ Spec.map (CommRingCat.ofHom (algebraMap R R[X])) := by
  have h : ∀ j : ULift.{u} ℕ, g R p j ≫ Spec.map (CommRingCat.ofHom (algebraMap R R[X])) =
      Spec.map (CommRingCat.ofHom (algebraMap R (L R p))) := by
    intro j
    rw [g, ← Spec.map_comp, ← CommRingCat.ofHom_comp, σ_comp_algebraMap]
  rw [h, h]

/-- The structure morphism of the glued scheme. -/
def toBase : glued R p ⟶ Spec (CommRingCat.of R) :=
  CommonOpenGluing.desc (fun _ => Spec.map (CommRingCat.ofHom (algebraMap R R[X])))
    (g_comp_structure R p)

@[reassoc (attr := simp)]
theorem ι_toBase (j : ULift.{u} ℕ) :
    ι R p j ≫ toBase R p = Spec.map (CommRingCat.ofHom (algebraMap R R[X])) :=
  CommonOpenGluing.ι_desc _ _ j

end DilatedLineChain

end Langlands.AlgebraicGeometry.AlgebraicSpace
