/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Final
public import WeilConjectures.AlgebraicGeometry.Picard.Jacobian
public import WeilConjectures.Mathlib.Algebra.Module.Torsion.Basic

/-!
# The Picard group of a smooth proper curve over an algebraically closed field

Let `C` be a smooth proper connected curve of genus `g` over an algebraically closed field `k`.
The degree splits `Pic(C) = ℤ × Pic⁰(C)`, and `Pic⁰(C)` is the group of `k`-points of the
Jacobian `J` of `C`, an abelian variety of dimension `g`. Hence `Pic(C)[n] ≅ (ℤ/n)^{2g}` and
`Pic(C)/n ≅ ℤ/n` for `n` prime to `char k`.

## Main statements

- `AlgebraicGeometry.Scheme.exists_jacobian_addEquiv_prod`: the Jacobian `J` and an isomorphism
  `Pic(C) ≅ ℤ × J(k)` whose first coordinate is the degree.
- `AlgebraicGeometry.Scheme.nonempty_addEquiv_torsionBy_pic_and_quotient`:
  `Pic(C)[n] ≅ (ℤ/n)^{2g}`, `Pic(C)/n ≅ ℤ/n`, and `Pic⁰(C)` is `n`-divisible.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj

namespace AlgebraicGeometry

variable {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}} [C.Over (Spec (.of k))]
  [SmoothOfRelativeDimension 1 (C ↘ Spec (.of k))] [IsProper (C ↘ Spec (.of k))]
  [ConnectedSpace C]

variable (k C) in
/-- **`Pic(C) ≅ ℤ × J(k)`.** A smooth proper connected curve `C` of genus `g` over an
algebraically closed field `k` has a Jacobian `J`: an abelian variety of dimension `g` with a
commutative group scheme structure, representing the degree zero part `Pic⁰_{C/k}` of the Picard
functor compatibly with the group laws (`AlgebraicGeometry.exists_jacobian`). The degree and the
identification `Pic⁰(C) ≅ J(k)` give an isomorphism `Pic(C) ≅ ℤ × J(k)` whose first coordinate
is the degree (`AlgebraicGeometry.Scheme.exists_mulEquiv_prod_ker_picDegreeHom`). -/
theorem Scheme.exists_jacobian_addEquiv_prod :
    ∃ (J : Over (Spec (.of k))) (_ : CommGrpObj J)
      (e : (picardFunctorDegree (C ↘ Spec (.of k)) 0).obj.RepresentableBy J)
      (_ : IsAbelianVariety J),
      IsPicardZeroMul (C ↘ Spec (.of k)) e ∧
        IsAbelianVariety.dim J = (C ↘ Spec (.of k)).genus ∧
        Nonempty (picardZero k C ≃* (𝟙_ (Over (Spec (.of k))) ⟶ J)) ∧
        ∃ E : Additive C.Pic ≃+ ℤ × Additive (𝟙_ (Over (Spec (.of k))) ⟶ J),
          ∀ L, (E L).1 = Multiplicative.toAdd (Scheme.picDegreeHom k C L.toMul) := by
  have : Smooth (C ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth 1 _
  have : GeometricallyConnected (C ↘ Spec (.of k)) :=
    GeometricallyConnected.of_connectedSpace_of_isSepClosed _
  have : GeometricallyIrreducible (C ↘ Spec (.of k)) :=
    GeometricallyIrreducible.of_smooth_of_geometricallyConnected _
  have : GeometricallyReduced (C ↘ Spec (.of k)) := Smooth.geometricallyReduced _
  have : GeometricallyIntegral (C ↘ Spec (.of k)) :=
    GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible _
  obtain ⟨J, _, e, hP, hS, hG, he, ⟨ψ⟩⟩ := exists_jacobian (k := k) (X := C)
  have : Smooth J.hom := SmoothOfRelativeDimension.smooth (arithmeticGenus k C) J.hom
  have : IsIntegral J.left := GeometricallyIntegral.isIntegral_of_subsingleton J.hom
  have : IsAbelianVariety J := { }
  have hdim : IsAbelianVariety.dim J = (C ↘ Spec (.of k)).genus := by
    rw [Scheme.genus_eq_arithmeticGenus]
    have h := (IsAbelianVariety.topologicalKrullDim_eq J).symm.trans
      (topologicalKrullDim_eq_of_smoothOfRelativeDimension J.hom (arithmeticGenus k C))
    exact_mod_cast h
  obtain ⟨eProd, heProd⟩ := Scheme.exists_mulEquiv_prod_ker_picDegreeHom (k := k) (C := C)
  refine ⟨J, inferInstance, e, inferInstance, he, hdim, ⟨ψ⟩,
    { toFun := fun x ↦ ((eProd x.toMul).1.toAdd, .ofMul (ψ (eProd x.toMul).2))
      invFun := fun y ↦ .ofMul (eProd.symm (.ofAdd y.1, ψ.symm y.2.toMul))
      left_inv := fun x ↦ by simp
      right_inv := fun y ↦ by simp
      map_add' := fun x y ↦ by
        simp only [toMul_add, map_mul, Prod.fst_mul, toAdd_mul, Prod.snd_mul]
        rfl }, fun L ↦ ?_⟩
  change Multiplicative.toAdd (eProd L.toMul).1 = _
  rw [heProd]

/-- **The Picard group of a proper curve.** Let `C` be a smooth proper connected curve of genus
`g` over an algebraically closed field `k`, and let `n ≥ 1` be prime to `char k`. Then

`Pic(C)[n] ≅ (ℤ/n)^{2g}`, `Pic(C) / n Pic(C) ≅ ℤ/n`,

and `Pic⁰(C)` is `n`-divisible.

By `AlgebraicGeometry.Scheme.exists_jacobian_addEquiv_prod`, `Pic(C) ≅ ℤ × J(k)` for the Jacobian
`J` of `C`, an abelian variety of dimension `g`, whose group of `k`-points is divisible with
`n`-torsion `(ℤ/n)^{2g}` (`AlgebraicGeometry.abelianVariety_estimate_of_isAlgClosed`).
(blueprint: `corollary-torsion-jacobian-field-extension`) -/
theorem Scheme.nonempty_addEquiv_torsionBy_pic_and_quotient {n : ℕ} (hn : (n : k) ≠ 0) :
    Nonempty (AddSubgroup.torsionBy (Additive C.Pic) n ≃+
        (Fin (2 * (C ↘ Spec (.of k)).genus) → ZMod n)) ∧
      Nonempty (Additive C.Pic ⧸ (zsmulAddGroupHom (α := Additive C.Pic) n).range ≃+
        ZMod n) ∧
      Function.Surjective fun L : picardZero k C ↦ L ^ n := by
  have hn0 : n ≠ 0 := by rintro rfl; exact hn Nat.cast_zero
  have hp : ¬ ringChar k ∣ n := fun h ↦ hn ((ringChar.spec k n).2 h)
  obtain ⟨J, _, -, _, -, hdim, ⟨ψ⟩, E, -⟩ := Scheme.exists_jacobian_addEquiv_prod k C
  set G := Additive (𝟙_ (Over (Spec (.of k))) ⟶ J)
  obtain ⟨hfin, -, hdiv, -, -⟩ := abelianVariety_estimate_of_isAlgClosed (ringChar k) J
  have hG' : Function.Surjective (zsmulAddGroupHom (α := G) n) := by
    intro x
    obtain ⟨a, ha⟩ := hdiv n (Nat.pos_of_ne_zero hn0) x.toMul
    refine ⟨.ofMul a, ?_⟩
    rw [zsmulAddGroupHom_apply, natCast_zsmul, ← ofMul_pow, show a ^ n = x.toMul from ha]
    rfl
  obtain ⟨eJ⟩ := hfin n (Nat.pos_of_ne_zero hn0) hp
  obtain ⟨eT⟩ := AddSubgroup.nonempty_addEquiv_torsionBy_int_prod G (n := n)
    (by exact_mod_cast hn0)
  obtain ⟨eQ⟩ := AddSubgroup.nonempty_addEquiv_quotient_range_zsmul_int_prod G hG'
  refine ⟨⟨(AddSubgroup.torsionByCongr E n).trans (eT.trans (hdim ▸ eJ))⟩,
    ⟨(AddSubgroup.quotientRangeZsmulCongr E n).trans eQ⟩, fun L ↦ ?_⟩
  obtain ⟨a, ha⟩ := hdiv n (Nat.pos_of_ne_zero hn0) (ψ L)
  refine ⟨ψ.symm a, ψ.injective ?_⟩
  simpa using ha

end AlgebraicGeometry
