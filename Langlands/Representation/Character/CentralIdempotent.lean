import Mathlib.RepresentationTheory.Character
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Basic.Complex.Basic

/-! # The regular representation cut out by a central idempotent -/

noncomputable section

namespace Langlands.Representation.Character

open scoped MonoidAlgebra

universe u

/-- The character of the part of the left regular representation cut out by a
central idempotent is its coefficient function at inverses, scaled by the group order. -/
def CentralIdempotentCharacterStatement (G : Type u) [Group G] [Fintype G] : Prop :=
  ∀ e : ℂ[G], e ∈ Subring.center ℂ[G] → IsIdempotentElem e →
    ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module ℂ W) (_ : FiniteDimensional ℂ W)
      (ρ : Representation ℂ G W),
      ∀ g, ρ.character g = (Fintype.card G : ℂ) * e.coeff g⁻¹

private theorem trace_mulLeft_groupAlgebra {G : Type u} [Group G] [Fintype G] (a : ℂ[G]) :
    LinearMap.trace ℂ ℂ[G] (LinearMap.mulLeft ℂ a) = (Fintype.card G : ℂ) * a.coeff 1 := by
  classical
  rw [LinearMap.trace_eq_matrix_trace _ (MonoidAlgebra.basis G ℂ), Matrix.trace]
  change (∑ g : G,
    LinearMap.toMatrix (MonoidAlgebra.basis G ℂ) (MonoidAlgebra.basis G ℂ)
      (LinearMap.mulLeft ℂ a) g g) = _
  simp only [LinearMap.toMatrix_apply, LinearMap.mulLeft_apply, MonoidAlgebra.basis_apply]
  change (∑ g : G, (a * MonoidAlgebra.single g 1).coeff g) = _
  simp [MonoidAlgebra.coeff_mul_single_apply, nsmul_eq_mul]

theorem centralIdempotentCharacter (G : Type u) [Group G] [Fintype G] :
    CentralIdempotentCharacterStatement G := by
  intro e he hE
  let P := LinearMap.mulLeft ℂ e
  let I := P.range
  let R := Representation.ofMulAction ℂ G G
  have hR (g : G) (x : ℂ[G]) : R g x = MonoidAlgebra.single g 1 * x := by
    rw [← Representation.asAlgebraHom_single_one R,
      Representation.asAlgebraHom_ofMulAction_smul_eq_mul]
  have hcomm (g : G) : Commute (MonoidAlgebra.single g 1 : ℂ[G]) e :=
    Subring.mem_center_iff.mp he _
  let ρ : Representation ℂ G I := R.subrepresentation I (fun g x hx => by
    obtain ⟨y, rfl⟩ := hx
    refine ⟨R g y, ?_⟩
    change e * R g y = R g (e * y)
    rw [hR, hR, ← mul_assoc, ← mul_assoc, (hcomm g).eq])
  have hP (x : I) : P x.val = x.val := by
    obtain ⟨y, hy⟩ := x.property
    change e * x.val = x.val
    rw [← hy]
    change e * (e * y) = e * y
    rw [← mul_assoc, hE.eq]
  let p : ℂ[G] →ₗ[ℂ] I := P.codRestrict I (fun x => ⟨x, rfl⟩)
  refine ⟨I, inferInstance, inferInstance, inferInstance, ρ, fun g => ?_⟩
  have hRestrict : p ∘ₗ (R g ∘ₗ I.subtype) = ρ g := by
    ext v : 1
    apply Subtype.ext
    change e * R g v.val = R g v.val
    exact hP (ρ g v)
  have hExtend : (R g ∘ₗ I.subtype) ∘ₗ p = LinearMap.mulLeft ℂ (MonoidAlgebra.single g 1 * e) := by
    apply LinearMap.ext
    intro x
    change R g (e * x) = (MonoidAlgebra.single g 1 * e) * x
    rw [hR, mul_assoc]
  change LinearMap.trace ℂ I (ρ g) = _
  rw [← hRestrict, LinearMap.trace_comp_comm', hExtend, trace_mulLeft_groupAlgebra,
    MonoidAlgebra.coeff_single_mul_apply, mul_one, one_mul]

end Langlands.Representation.Character
