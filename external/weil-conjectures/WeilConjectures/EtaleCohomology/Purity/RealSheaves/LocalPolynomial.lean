/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafRepresentation
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Weights

/-!
# Local Frobenius polynomials of lisse Weil sheaves

Let `ℱ` be a lisse Weil sheaf on a curve `C₀` over a finite field, with Weil fundamental
representation `(V, ρ)` under the lisse sheaf–representation equivalence
(`AlgebraicGeometry.WeilGroup.exists_equivalence_isLisse`). The local characteristic factor
`P_x(ℱ, T) = det (1 - T F_x ∣ ℱ_x̄)` at a closed point `x` is `det (1 - T ρ(g) ∣ V)` for every
member `g` of the Frobenius conjugacy class of `x` in the Weil group (blueprint
`situation-weil`).

## Main statements

- `AlgebraicGeometry.WeilGroup.exists_equivalence_localPolynomial_stalk`: the local polynomials
  of a lisse Weil sheaf are those of its Weil fundamental representation.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace WeilGroup

variable {K : Type u} [Field K] [Finite K] {C : Scheme.{u}} [C.Over (Spec (.of K))]
  [IsCurve (C ↘ Spec (.of K))] [SmoothOfRelativeDimension 1 (C ↘ Spec (.of K))]
  [GeometricallyConnected (C ↘ Spec (.of K))] (W : WeilGroup (C ↘ Spec (.of K))) (l : ℕ)
  [Fact l.Prime] [Fact (ringChar K ≠ l)]

/-- Blueprint `situation-weil`: Local Frobenius polynomials.

Under the lisse sheaf–representation equivalence `ℱ ↦ (V, ρ)` of
`AlgebraicGeometry.WeilGroup.exists_equivalence_isLisse`, the local characteristic factor
`P_x(ℱ, T) = det (1 - T F_x ∣ ℱ_x̄)` of a lisse Weil sheaf `ℱ` at a closed point `x` is
`det (1 - T ρ(g) ∣ V)` for every `g ∈ W(C₀)` conjugate to the local Frobenius element at `x`:
the stalk `ℱ_x̄` with `F_x` is `V` with `ρ (Frob_x)`, and a characteristic polynomial is invariant
under conjugation (`AlgebraicGeometry.WeilGroup.localPolynomial_eq_charpolyRev_of_isConj`).
The operations on lisse Weil sheaves are transported along this equivalence. -/
theorem exists_equivalence_localPolynomial_stalk :
    ∃ e : ObjectProperty.FullSubcategory (fun F : WeilSheaf K l C ↦ F.IsLisse) ≌
        ObjectProperty.FullSubcategory (W.isLisseRep l),
      ∀ (F : ObjectProperty.FullSubcategory (fun F : WeilSheaf K l C ↦ F.IsLisse))
        (x : C.finitePoints) (g : W.carrier), IsConj (W.frobenius x) g →
        haveI := (e.functor.obj F).property.1
        (F.obj.stalk x).localPolynomial = ((e.functor.obj F).obj.ρ g).charpolyRev := by
  obtain ⟨e, hst, -, -, -⟩ := W.exists_equivalence_isLisse l
  refine ⟨e, fun F x g hg ↦ ?_⟩
  have := (e.functor.obj F).property.1
  obtain ⟨f, hf⟩ := hst F x
  rw [← localPolynomial_eq_charpolyRev_of_isConj hg, localPolynomial,
    FrobeniusModule.localPolynomial, LinearMap.charpolyRev_def, LinearMap.charpolyRev_def]
  exact congrArg Polynomial.reverse
    (LinearMap.charpoly_eq_of_comp_eq f (LinearMap.ext fun v ↦ hf v))

variable {W l}

omit [SmoothOfRelativeDimension 1 (C ↘ Spec (.of K))]
  [GeometricallyConnected (C ↘ Spec (.of K))] in
/-- If an equivalence `e` identifies the stalks of lisse Weil sheaves with their Weil
fundamental representations, then the local polynomial `P_x(ℱ, T)` of a lisse Weil sheaf is
`det (1 - T σ(g) ∣ V')` for every representation `σ` equivalent to the representation of `ℱ` and
every `g` conjugate to the Frobenius element at `x`. -/
theorem localPolynomial_stalk_eq_charpolyRev_of_equiv
    (e : ObjectProperty.FullSubcategory (fun F : WeilSheaf K l C ↦ F.IsLisse) ≌
        ObjectProperty.FullSubcategory (W.isLisseRep l))
    (hst : ∀ (F : ObjectProperty.FullSubcategory (fun F : WeilSheaf K l C ↦ F.IsLisse))
          (x : C.finitePoints),
        ∃ f : (F.obj.stalk x).carrier ≃ₗ[PadicAlgCl l] (e.functor.obj F).obj.V,
          ∀ v, f ((F.obj.stalk x).frobenius v) = (e.functor.obj F).obj.ρ (W.frobenius x) (f v))
    (F : ObjectProperty.FullSubcategory (fun F : WeilSheaf K l C ↦ F.IsLisse))
    {x : C.finitePoints} {g : W.carrier} (hg : IsConj (W.frobenius x) g) {V' : Type*}
    [AddCommGroup V'] [Module (PadicAlgCl l) V'] [FiniteDimensional (PadicAlgCl l) V']
    {σ : Representation (PadicAlgCl l) W.carrier V'} (b : (e.functor.obj F).obj.ρ.Equiv σ) :
    (F.obj.stalk x).localPolynomial = (σ g).charpolyRev := by
  have := (e.functor.obj F).property.1
  obtain ⟨f, hf⟩ := hst F x
  have h : (F.obj.stalk x).localPolynomial =
      W.localPolynomial l (e.functor.obj F).obj.ρ x := by
    rw [localPolynomial, FrobeniusModule.localPolynomial, LinearMap.charpolyRev_def,
      LinearMap.charpolyRev_def]
    exact congrArg Polynomial.reverse
      (LinearMap.charpoly_eq_of_comp_eq f (LinearMap.ext fun v ↦ hf v))
  rw [h, localPolynomial_eq_charpolyRev_of_isConj hg, LinearMap.charpolyRev_def,
    LinearMap.charpolyRev_def, b.charpoly_apply]

variable (W l)

/-- Blueprint `situation-weil` (subsection `situation-weil`): Local Frobenius polynomials
of the operations.

Under the lisse sheaf–representation equivalence `ℱ ↦ (V, ρ)` of
`AlgebraicGeometry.WeilGroup.exists_equivalence_isLisse`, which is compatible with duals, tensor
products and direct sums, the local characteristic factors of the operations on lisse Weil
sheaves are computed by the corresponding operations on representations: for every closed point
`x` and every `g ∈ W(C₀)` conjugate to the local Frobenius element at `x`,

* `P_x(ℱ, T) = det (1 - T ρ_ℱ(g) ∣ V_ℱ)`;
* `P_x(ℱ^∨, T) = det (1 - T ρ_ℱ^∨(g) ∣ V_ℱ^∨)`;
* `P_x(ℱ ⊗ 𝒢, T) = det (1 - T (ρ_ℱ ⊗ ρ_𝒢)(g) ∣ V_ℱ ⊗ V_𝒢)`;
* `P_x(ℱ ⊕ 𝒢, T) = P_x(ℱ, T) P_x(𝒢, T)`.

Exterior powers and determinants of lisse Weil sheaves are defined by transport along the
equivalence: the lisse Weil sheaf with representation `∧ʳρ` or `det ρ` and its local polynomials
are given by `AlgebraicGeometry.WeilGroup.exists_weilSheaf_of_isLisse` applied to
`ρ.exteriorPower r` (`AlgebraicGeometry.WeilGroup.IsLisse.exteriorPower`) or to
`Representation.ofCharacter ρ.detCharacter`
(`AlgebraicGeometry.WeilGroup.IsLisse.ofCharacter_detCharacter`). -/
theorem exists_equivalence_localPolynomial_operations :
    ∃ e : ObjectProperty.FullSubcategory (fun F : WeilSheaf K l C ↦ F.IsLisse) ≌
        ObjectProperty.FullSubcategory (W.isLisseRep l),
      (∀ (F : ObjectProperty.FullSubcategory (fun F : WeilSheaf K l C ↦ F.IsLisse))
        (x : C.finitePoints) (g : W.carrier), IsConj (W.frobenius x) g →
        haveI := (e.functor.obj F).property.1
        (F.obj.stalk x).localPolynomial = ((e.functor.obj F).obj.ρ g).charpolyRev) ∧
      (∀ (F : ObjectProperty.FullSubcategory (fun F : WeilSheaf K l C ↦ F.IsLisse))
        (x : C.finitePoints) (g : W.carrier), IsConj (W.frobenius x) g →
        haveI := (e.functor.obj F).property.1
        ((F.obj.dual F.property).stalk x).localPolynomial =
          ((e.functor.obj F).obj.ρ.dual g).charpolyRev) ∧
      (∀ (F G : ObjectProperty.FullSubcategory (fun F : WeilSheaf K l C ↦ F.IsLisse))
        (x : C.finitePoints) (g : W.carrier), IsConj (W.frobenius x) g →
        haveI := (e.functor.obj F).property.1
        haveI := (e.functor.obj G).property.1
        ((F.obj.tensorObj G.obj F.property).stalk x).localPolynomial =
          (((e.functor.obj F).obj.ρ.tprod (e.functor.obj G).obj.ρ) g).charpolyRev) ∧
      (∀ (F G : ObjectProperty.FullSubcategory (fun F : WeilSheaf K l C ↦ F.IsLisse))
        (x : C.finitePoints) (g : W.carrier), IsConj (W.frobenius x) g →
        haveI := (e.functor.obj F).property.1
        haveI := (e.functor.obj G).property.1
        ((F.obj ⊞ G.obj).stalk x).localPolynomial =
          ((e.functor.obj F).obj.ρ g).charpolyRev * ((e.functor.obj G).obj.ρ g).charpolyRev) := by
  obtain ⟨e, hst, hdu, -, hte⟩ := W.exists_equivalence_isLisse l
  have hP (F : ObjectProperty.FullSubcategory (fun F : WeilSheaf K l C ↦ F.IsLisse))
      (x : C.finitePoints) (g : W.carrier) (hg : IsConj (W.frobenius x) g) :
      haveI := (e.functor.obj F).property.1
      (F.obj.stalk x).localPolynomial = ((e.functor.obj F).obj.ρ g).charpolyRev :=
    have := (e.functor.obj F).property.1
    localPolynomial_stalk_eq_charpolyRev_of_equiv e hst F hg (.refl _)
  refine ⟨e, hP, fun F x g hg ↦ ?_, fun F G x g hg ↦ ?_, fun F G x g hg ↦ ?_⟩
  · have := (e.functor.obj F).property.1
    obtain ⟨b⟩ := hdu F
    exact localPolynomial_stalk_eq_charpolyRev_of_equiv e hst
      ⟨F.obj.dual F.property, F.property.dual⟩ hg b
  · have := (e.functor.obj F).property.1
    have := (e.functor.obj G).property.1
    obtain ⟨b⟩ := hte F G
    exact localPolynomial_stalk_eq_charpolyRev_of_equiv e hst
      ⟨F.obj.tensorObj G.obj F.property, F.property.tensorObj G.property⟩ hg b
  · obtain ⟨b⟩ := WeilSheaf.nonempty_equiv_stalk_biprod F.obj G.obj x
    rw [b.localPolynomial_eq, FrobeniusModule.localPolynomial_prod, hP F x g hg, hP G x g hg]

end WeilGroup

end AlgebraicGeometry
