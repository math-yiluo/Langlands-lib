/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.FunctionFieldCohomology
public import WeilConjectures.AlgebraicGeometry.Sites.FieldCohomologyTorsion
public import WeilConjectures.AlgebraicGeometry.Sites.Hilbert90
public import WeilConjectures.AlgebraicGeometry.Sites.TorsionSheaf

/-!
# Cohomology of the units of algebraic extensions of function fields of curves

Let `k` be an algebraically closed field, `C` an integral curve over `k` and `L` an algebraic
extension of the function field `k(C)`. Then `Hᵠ(Spec L_ét, 𝔾ₘ) = 0` for every `q ≥ 1`.

In degree one this is Hilbert 90, in degree two it is the vanishing of the Brauer group of the
`C₁` field `L` (Tsen's theorem). In degrees `q ≥ 3` the group `Hᵠ(Spec L_ét, 𝔾ₘ)` is torsion,
and multiplication by every prime `ℓ` is injective on it: the kernel and the cokernel of
`ℓ : 𝔾ₘ → 𝔾ₘ` are torsion sheaves, whose cohomology vanishes in degrees `≥ 2` because `L` has
cohomological dimension at most one
(`AlgebraicGeometry.Scheme.subsingleton_sheafH_of_isQuasiAlgClosed`).

The torsion property is `AlgebraicGeometry.Scheme.isOfFinAddOrder_sheafH_of_field`.

## Main statements

- `CategoryTheory.Sheaf.H.map_injective_of_subsingleton_kernel_cokernel`: a morphism of
  abelian sheaves induces an injection on `Hⁿ⁺¹` as soon as `Hⁿ⁺¹` of its kernel and `Hⁿ` of its
  cokernel vanish.
- `AlgebraicGeometry.Scheme.subsingleton_sheafH_gmSheaf_of_isQuasiAlgClosed`: the
  vanishing for a `C₁` field containing an algebraically closed field.
- `AlgebraicGeometry.IsCurve.subsingleton_sheafH_gmSheaf_of_isAlgebraic_functionField`:
  the vanishing for algebraic extensions of function fields of curves.
-/

@[expose] public section

universe w' w v u

open CategoryTheory Limits

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]

/-- A morphism `φ : F ⟶ G` of abelian sheaves induces an injection `Hⁿ⁺¹(F) → Hⁿ⁺¹(G)` as soon
as `Hⁿ⁺¹(ker φ) = 0` and `Hⁿ(coker φ) = 0`: factor `φ` through its image `I` and use the long
exact cohomology sequences of `0 → ker φ → F → I → 0` and `0 → I → G → coker φ → 0`. -/
theorem H.map_injective_of_subsingleton_kernel_cokernel {F G : Sheaf J AddCommGrpCat.{w}}
    (φ : F ⟶ G) (n : ℕ) [Subsingleton (H (kernel φ) (n + 1))]
    [Subsingleton (H (cokernel φ) n)] : Function.Injective (H.map φ (n + 1)) := by
  let S₁ := ShortComplex.mk (kernel.ι φ) (Abelian.factorThruImage φ)
    (by simp [← cancel_mono (Abelian.image.ι φ)])
  let S₂ := ShortComplex.mk (Abelian.image.ι φ) (cokernel.π φ) (kernel.condition _)
  have hS₁ : S₁.ShortExact := by
    refine ShortComplex.ShortExact.mk' ?_ inferInstance inferInstance
    let S' := ShortComplex.mk (kernel.ι φ) φ (kernel.condition φ)
    let ψ : S₁ ⟶ S' := { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := Abelian.image.ι φ }
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono ψ).2 (ShortComplex.exact_kernel φ)
  have hS₂ : S₂.ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_kernel _) inferInstance inferInstance
  have h₁ : Function.Injective (H.map S₁.g (n + 1)) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, rfl⟩ := ((H.exact_map_map hS₁ (n + 1)) x).1 hx
    rw [Subsingleton.elim y 0, map_zero]
  have h₂ : Function.Injective (H.map S₂.f (n + 1)) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, rfl⟩ := ((H.exact_δSucc_map hS₂ n) x).1 hx
    rw [Subsingleton.elim y 0, map_zero]
  have hφ : φ = S₁.g ≫ S₂.f := (Abelian.image.fac φ).symm
  intro x y hxy
  rw [hφ, H.map_comp_apply, H.map_comp_apply] at hxy
  exact h₁ (h₂ hxy)

end CategoryTheory.Sheaf

namespace AlgebraicGeometry

namespace Scheme

/-- Multiplication by a positive integer `ℓ` on `Hⁿ⁺³(Spec L_ét, 𝔾ₘ)` is injective for a `C₁`
field `L` containing an algebraically closed field: the kernel and the cokernel of
`ℓ : 𝔾ₘ → 𝔾ₘ` are torsion sheaves, so their cohomology vanishes in degrees `≥ 2`. -/
lemma nsmul_injective_sheafH_gmSheaf_of_isQuasiAlgClosed (k L : Type u) [Field k]
    [IsAlgClosed k] [Field L] [Algebra k L] [IsQuasiAlgClosed L] {ℓ : ℕ} (hℓ : 0 < ℓ)
    (n : ℕ) : Function.Injective (fun x : Sheaf.H (Spec (.of L)).gmSheaf (n + 3) ↦ ℓ • x) := by
  set F := (Spec (.of L)).gmSheaf
  let φ : F ⟶ F := ℓ • 𝟙 F
  have hK : (kernel φ).IsTorsion := by
    refine isTorsion_of_nsmul_id_eq_zero hℓ ((cancel_mono (kernel.ι φ)).1 ?_)
    rw [Preadditive.nsmul_comp, Category.id_comp, zero_comp, ← Category.comp_id (kernel.ι φ),
      ← Preadditive.comp_nsmul, kernel.condition]
  have hQ : (cokernel φ).IsTorsion := by
    refine isTorsion_of_nsmul_id_eq_zero hℓ ((cancel_epi (cokernel.π φ)).1 ?_)
    rw [Preadditive.comp_nsmul, Category.comp_id, comp_zero, ← Category.id_comp (cokernel.π φ),
      ← Preadditive.nsmul_comp, cokernel.condition]
  have := subsingleton_sheafH_of_isQuasiAlgClosed k L _ hK (q := n + 3) (by omega)
  have := subsingleton_sheafH_of_isQuasiAlgClosed k L _ hQ (q := n + 2) (by omega)
  have hinj := Sheaf.H.map_injective_of_subsingleton_kernel_cokernel φ (n + 2)
  intro x y hxy
  apply hinj
  simp only [φ, Sheaf.H.map_nsmul_apply, Sheaf.H.map_id_apply]
  exact hxy

/-- **Cohomology of the units of a `C₁` field.** Let `L` be a quasi-algebraically closed field
containing an algebraically closed field `k`. Then `Hᵠ(Spec L_ét, 𝔾ₘ) = 0` for every `q ≥ 1`:
for `q = 1` by Hilbert 90, for `q = 2` since the Brauer group of a `C₁` field vanishes, and for
`q ≥ 3` since multiplication by every prime is injective on `Hᵠ`, which is torsion
(`AlgebraicGeometry.Scheme.isOfFinAddOrder_sheafH_of_field`). -/
theorem subsingleton_sheafH_gmSheaf_of_isQuasiAlgClosed (k L : Type u) [Field k]
    [IsAlgClosed k] [Field L] [Algebra k L] [IsQuasiAlgClosed L]
    (q : ℕ) (hq : 1 ≤ q) : Subsingleton (Sheaf.H (Spec (.of L)).gmSheaf q) := by
  obtain _ | _ | _ | n := q
  · omega
  · exact subsingleton_cohomologicalPicardGroup_of_field L
  · exact IsQuasiAlgClosed.subsingleton_cohomologicalBrauerGroup L
  · refine ⟨fun x y ↦ ?_⟩
    suffices h : ∀ z : Sheaf.H (Spec (.of L)).gmSheaf (n + 3), z = 0 by rw [h x, h y]
    intro z
    by_contra hz
    have hpos := (isOfFinAddOrder_sheafH_of_field L _ (n + 2) z).addOrderOf_pos
    have hne : addOrderOf z ≠ 1 := fun h ↦ hz (AddMonoid.addOrderOf_eq_one_iff.1 h)
    obtain ⟨ℓ, hℓ, m, hm⟩ := Nat.exists_prime_and_dvd hne
    have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; omega)
    have hmz : m • z ≠ 0 := by
      intro h
      have := Nat.le_of_dvd hm0 (addOrderOf_dvd_of_nsmul_eq_zero h)
      have := hℓ.two_le
      nlinarith
    apply hmz
    apply nsmul_injective_sheafH_gmSheaf_of_isQuasiAlgClosed k L hℓ.pos n
    simp only [smul_zero, smul_smul]
    rw [← hm, addOrderOf_nsmul_eq_zero]

end Scheme

namespace IsCurve

/-- **Cohomology of the units of an algebraic extension of a curve function field.** Let `k` be
an algebraically closed field, `C` an integral curve over `k` and `L` an algebraic extension of
its function field `k(C)`. Then `Hᵠ(Spec L_ét, 𝔾ₘ) = 0` for every `q ≥ 1`: the field `L` is
`C₁` by Tsen's theorem (`AlgebraicGeometry.IsCurve.isQuasiAlgClosed_functionField`), and
`AlgebraicGeometry.Scheme.subsingleton_sheafH_gmSheaf_of_isQuasiAlgClosed` applies.
(blueprint: `lemma-cohomology-multiplicative-group`) -/
theorem subsingleton_sheafH_gmSheaf_of_isAlgebraic_functionField {k : Type u}
    [Field k] [IsAlgClosed k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve f]
    [IsIntegral C] (L : Type u) [Field L] [Algebra C.functionField L]
    [Algebra.IsAlgebraic C.functionField L]
    (q : ℕ) (hq : 1 ≤ q) : Subsingleton (Sheaf.H (Spec (.of L)).gmSheaf q) := by
  have := isQuasiAlgClosed_functionField f
  have : IsQuasiAlgClosed L := IsQuasiAlgClosed.of_isAlgebraic C.functionField L
  obtain ⟨x⟩ := (inferInstance : Nonempty C)
  have : Nonempty (⊤ : C.Opens) := ⟨⟨x, trivial⟩⟩
  let : Algebra k L := ((algebraMap C.functionField L).comp ((C.germToFunctionField ⊤).hom.comp
    (f.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom))).toAlgebra
  exact Scheme.subsingleton_sheafH_gmSheaf_of_isQuasiAlgClosed k L q hq

end IsCurve

end AlgebraicGeometry
