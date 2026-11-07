import Langlands.AlgebraicGeometry.CommonOpenGluing
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-!
# Two affine lines over a ring glued along a translate of a punctured line

Let `R` be a commutative ring and `p ∈ R`. Glue two copies of the affine line `Spec R[t]` and
`Spec R[s]` along the opens `D(p t)` and `D(p (p s - 1))`, identified by `t = p s - 1`. Over a
valuation ring `R = O` with `0 < ‖p‖ < 1`, the generic fibre is the affine line with the point
`t = 0` doubled by the point `s = 1/p`; this is the quasi-separated finite type counterexample to
the closedness assertion of Conrad's Corollary 5.7.

This module constructs the ring isomorphism `R[t][1/(p t)] ≃ R[s][1/(p (p s - 1))]`, so that
both inclusions of the common open are open immersions, and the glued scheme with its morphism to
`Spec R`.
-/

noncomputable section

universe u

open CategoryTheory Polynomial
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

namespace DoubledPointLine

variable (R : Type u) [CommRing R] (p : R)

/-- The function `p t` on the first chart. -/
def f₁ : R[X] := C p * X

/-- The function `p (p s - 1)` on the second chart. -/
def f₂ : R[X] := C p * (C p * X - 1)

/-- The coordinate ring of the common open, as a localization of the first chart. -/
abbrev B₁ : Type u := Localization.Away (f₁ R p)

/-- The coordinate ring of the common open, as a localization of the second chart. -/
abbrev B₂ : Type u := Localization.Away (f₂ R p)

theorem algebraMap_f₁ : algebraMap R[X] (B₁ R p) (f₁ R p) =
    algebraMap R[X] (B₁ R p) (C p) * algebraMap R[X] (B₁ R p) X :=
  map_mul _ _ _

theorem algebraMap_f₂ : algebraMap R[X] (B₂ R p) (f₂ R p) =
    algebraMap R[X] (B₂ R p) (C p) * algebraMap R[X] (B₂ R p) (C p * X - 1) :=
  map_mul _ _ _

theorem isUnit_p₁ : IsUnit (algebraMap R[X] (B₁ R p) (C p)) := by
  have h := IsLocalization.Away.algebraMap_isUnit (S := B₁ R p) (f₁ R p)
  rw [algebraMap_f₁] at h
  exact isUnit_of_mul_isUnit_left h

theorem isUnit_t₁ : IsUnit (algebraMap R[X] (B₁ R p) X) := by
  have h := IsLocalization.Away.algebraMap_isUnit (S := B₁ R p) (f₁ R p)
  rw [algebraMap_f₁] at h
  exact isUnit_of_mul_isUnit_right h

theorem isUnit_p₂ : IsUnit (algebraMap R[X] (B₂ R p) (C p)) := by
  have h := IsLocalization.Away.algebraMap_isUnit (S := B₂ R p) (f₂ R p)
  rw [algebraMap_f₂] at h
  exact isUnit_of_mul_isUnit_left h

/-- The first chart coordinate on the common open of the second chart: `t = p s - 1`. -/
def α : R[X] →+* B₂ R p :=
  eval₂RingHom (algebraMap R (B₂ R p)) (algebraMap R[X] (B₂ R p) (C p * X - 1))

/-- The second chart coordinate on the common open of the first chart: `s = (1 + t) / p`. -/
def β : R[X] →+* B₁ R p :=
  eval₂RingHom (algebraMap R (B₁ R p))
    ((1 + algebraMap R[X] (B₁ R p) X) * ↑(isUnit_p₁ R p).unit⁻¹)

theorem α_C (a : R) : α R p (C a) = algebraMap R[X] (B₂ R p) (C a) := by
  rw [α, coe_eval₂RingHom, eval₂_C, IsScalarTower.algebraMap_apply R R[X] (B₂ R p),
    Polynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]

theorem β_C (a : R) : β R p (C a) = algebraMap R[X] (B₁ R p) (C a) := by
  rw [β, coe_eval₂RingHom, eval₂_C, IsScalarTower.algebraMap_apply R R[X] (B₁ R p),
    Polynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]

theorem α_f₁ : α R p (f₁ R p) = algebraMap R[X] (B₂ R p) (f₂ R p) := by
  have e : α R p (f₁ R p) = α R p (C p) * α R p X := map_mul _ _ _
  rw [e, α_C, algebraMap_f₂, α, coe_eval₂RingHom, eval₂_X]

theorem β_f₂ : β R p (f₂ R p) = algebraMap R[X] (B₁ R p) (f₁ R p) := by
  have hu := (isUnit_p₁ R p).mul_val_inv
  have e : β R p (f₂ R p) = β R p (C p) * (β R p (C p) * β R p X - 1) := by
    change β R p (C p * (C p * X - 1)) = _
    rw [map_mul, map_sub, map_mul, map_one]
  rw [e, β_C, algebraMap_f₁, β, coe_eval₂RingHom, eval₂_X]
  calc algebraMap R[X] (B₁ R p) (C p) *
        (algebraMap R[X] (B₁ R p) (C p) *
          ((1 + algebraMap R[X] (B₁ R p) X) * ↑(isUnit_p₁ R p).unit⁻¹) - 1) =
      algebraMap R[X] (B₁ R p) (C p) *
        ((1 + algebraMap R[X] (B₁ R p) X) *
          (algebraMap R[X] (B₁ R p) (C p) * ↑(isUnit_p₁ R p).unit⁻¹) - 1) := by ring
    _ = algebraMap R[X] (B₁ R p) (C p) * algebraMap R[X] (B₁ R p) X := by
        rw [hu]
        ring

/-- The map `R[t][1/(p t)] → R[s][1/(p (p s - 1))]`. -/
def ψ : B₁ R p →+* B₂ R p :=
  IsLocalization.Away.lift (f₁ R p) (g := α R p) (by
    rw [α_f₁]
    exact IsLocalization.Away.algebraMap_isUnit _)

/-- The map `R[s][1/(p (p s - 1))] → R[t][1/(p t)]`. -/
def χ : B₂ R p →+* B₁ R p :=
  IsLocalization.Away.lift (f₂ R p) (g := β R p) (by
    rw [β_f₂]
    exact IsLocalization.Away.algebraMap_isUnit _)

theorem ψ_algebraMap (a : R[X]) : ψ R p (algebraMap R[X] (B₁ R p) a) = α R p a :=
  IsLocalization.Away.lift_eq _ _ a

theorem χ_algebraMap (a : R[X]) : χ R p (algebraMap R[X] (B₂ R p) a) = β R p a :=
  IsLocalization.Away.lift_eq _ _ a

theorem χ_ψ : (χ R p).comp (ψ R p) = RingHom.id _ := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (f₁ R p))
  apply Polynomial.ringHom_ext
  · intro a
    simp only [RingHom.comp_apply, ψ_algebraMap, α_C, χ_algebraMap, β_C, RingHom.id_apply]
  · simp only [RingHom.comp_apply, ψ_algebraMap, RingHom.id_apply]
    rw [α, coe_eval₂RingHom, eval₂_X, χ_algebraMap, map_sub, map_mul, map_one, β_C, β,
      coe_eval₂RingHom, eval₂_X]
    have hu := (isUnit_p₁ R p).mul_val_inv
    calc algebraMap R[X] (B₁ R p) (C p) *
          ((1 + algebraMap R[X] (B₁ R p) X) * ↑(isUnit_p₁ R p).unit⁻¹) - 1 =
        (1 + algebraMap R[X] (B₁ R p) X) *
          (algebraMap R[X] (B₁ R p) (C p) * ↑(isUnit_p₁ R p).unit⁻¹) - 1 := by ring
      _ = algebraMap R[X] (B₁ R p) X := by
          rw [hu]
          ring

theorem ψ_χ : (ψ R p).comp (χ R p) = RingHom.id _ := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (f₂ R p))
  apply Polynomial.ringHom_ext
  · intro a
    simp only [RingHom.comp_apply, χ_algebraMap, β_C, ψ_algebraMap, α_C, RingHom.id_apply]
  · simp only [RingHom.comp_apply, χ_algebraMap, RingHom.id_apply]
    rw [β, coe_eval₂RingHom, eval₂_X, map_mul, map_add, map_one, ψ_algebraMap, α,
      coe_eval₂RingHom, eval₂_X]
    have hp : ψ R p (algebraMap R[X] (B₁ R p) (C p)) = algebraMap R[X] (B₂ R p) (C p) := by
      rw [ψ_algebraMap, α_C]
    have hinv : ψ R p ↑(isUnit_p₁ R p).unit⁻¹ * algebraMap R[X] (B₂ R p) (C p) = 1 := by
      rw [← hp, ← map_mul, (isUnit_p₁ R p).val_inv_mul, map_one]
    calc (1 + algebraMap R[X] (B₂ R p) (C p * X - 1)) * ψ R p ↑(isUnit_p₁ R p).unit⁻¹ =
        algebraMap R[X] (B₂ R p) X *
          (ψ R p ↑(isUnit_p₁ R p).unit⁻¹ * algebraMap R[X] (B₂ R p) (C p)) := by
          rw [map_sub, map_mul, map_one]
          ring
      _ = algebraMap R[X] (B₂ R p) X := by rw [hinv, mul_one]

/-- The ring isomorphism between the two descriptions of the common open. -/
def ringEquiv : B₁ R p ≃+* B₂ R p :=
  RingEquiv.ofRingHom (ψ R p) (χ R p) (ψ_χ R p) (χ_ψ R p)

/-- With the algebra structure given by `t ↦ p s - 1`, the common open is a localization of the
first chart away from `p t`. -/
theorem isLocalization_α :
    letI := (α R p).toAlgebra
    IsLocalization.Away (f₁ R p) (B₂ R p) := by
  let := (α R p).toAlgebra
  let e : B₁ R p ≃ₐ[R[X]] B₂ R p :=
    { ringEquiv R p with
      commutes' := fun a => ψ_algebraMap R p a }
  exact IsLocalization.isLocalization_of_algEquiv (Submonoid.powers (f₁ R p)) e

/-- The inclusion of the common open into the first chart. -/
def g₁ : Spec (CommRingCat.of (B₂ R p)) ⟶ Spec (CommRingCat.of R[X]) :=
  Spec.map (CommRingCat.ofHom (α R p))

/-- The inclusion of the common open into the second chart. -/
def g₂ : Spec (CommRingCat.of (B₂ R p)) ⟶ Spec (CommRingCat.of R[X]) :=
  Spec.map (CommRingCat.ofHom (algebraMap R[X] (B₂ R p)))

instance : IsOpenImmersion (g₁ R p) := by
  let := (α R p).toAlgebra
  have := isLocalization_α R p
  exact IsOpenImmersion.of_isLocalization (f₁ R p) (S := B₂ R p)

instance : IsOpenImmersion (g₂ R p) := by
  unfold g₂
  infer_instance

/-- The two inclusions of the common open, indexed by the two charts (`true` for the chart with
coordinate `t`, `false` for the chart with coordinate `s`). -/
def g : ULift.{u} Bool → (Spec (CommRingCat.of (B₂ R p)) ⟶ Spec (CommRingCat.of R[X]))
  | ⟨true⟩ => g₁ R p
  | ⟨false⟩ => g₂ R p

instance (b : ULift.{u} Bool) : IsOpenImmersion (g R p b) := by
  obtain ⟨b⟩ := b
  cases b
  · exact inferInstanceAs (IsOpenImmersion (g₂ R p))
  · exact inferInstanceAs (IsOpenImmersion (g₁ R p))

/-- The glued scheme. -/
abbrev glued : Scheme.{u} :=
  CommonOpenGluing.glued (fun _ : ULift.{u} Bool => Spec (CommRingCat.of R[X]))
    (Spec (CommRingCat.of (B₂ R p))) (g R p)

/-- The chart with coordinate `t` (`true`) or `s` (`false`). -/
abbrev ι (b : ULift.{u} Bool) : Spec (CommRingCat.of R[X]) ⟶ glued R p :=
  CommonOpenGluing.ι (fun _ : ULift.{u} Bool => Spec (CommRingCat.of R[X]))
    (Spec (CommRingCat.of (B₂ R p))) (g R p) b

theorem α_comp_algebraMap : (α R p).comp (algebraMap R R[X]) = algebraMap R (B₂ R p) := by
  ext a
  rw [RingHom.comp_apply, Polynomial.algebraMap_apply, Algebra.algebraMap_self,
    RingHom.id_apply, α, coe_eval₂RingHom, eval₂_C]

/-- The two charts have the same structure morphism on the common open. -/
theorem g_comp_structure (b b' : ULift.{u} Bool) :
    g R p b ≫ Spec.map (CommRingCat.ofHom (algebraMap R R[X])) =
      g R p b' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R[X])) := by
  have h : ∀ b, g R p b ≫ Spec.map (CommRingCat.ofHom (algebraMap R R[X])) =
      Spec.map (CommRingCat.ofHom (algebraMap R (B₂ R p))) := by
    intro b
    obtain ⟨b⟩ := b
    cases b
    · change Spec.map _ ≫ Spec.map _ = _
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
    · change Spec.map _ ≫ Spec.map _ = _
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, α_comp_algebraMap]
  rw [h, h]

/-- The structure morphism of the glued scheme. -/
def toBase : glued R p ⟶ Spec (CommRingCat.of R) :=
  CommonOpenGluing.desc (fun _ => Spec.map (CommRingCat.ofHom (algebraMap R R[X])))
    (g_comp_structure R p)

@[reassoc (attr := simp)]
theorem ι_toBase (b : ULift.{u} Bool) :
    ι R p b ≫ toBase R p = Spec.map (CommRingCat.ofHom (algebraMap R R[X])) :=
  CommonOpenGluing.ι_desc _ _ b

end DoubledPointLine

end Langlands.AlgebraicGeometry.AlgebraicSpace
