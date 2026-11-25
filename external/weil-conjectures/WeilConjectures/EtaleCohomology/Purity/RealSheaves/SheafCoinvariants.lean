/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin
import WeilConjectures.WeilSheaf.CurveTopCohomology

/-!
# Geometric coinvariants and `H_c²` of a lisse Weil sheaf

Let `C₀` be a smooth geometrically connected curve over the finite field `K` with Weil group
`W = W(C₀)`, and let `ℱ` be a lisse Weil sheaf on `C₀` with Weil fundamental representation
`(V, ρ)` (`AlgebraicGeometry.WeilGroup.exists_equivalence_isLisse`). The geometric coinvariants
`Γ(C̄, ℱ^∨)^∨` of `ℱ` (`AlgebraicGeometry.WeilSheaf.geometricCoinvariants`) are the coinvariants
`V_{π₁(C)}`, with the Frobenius induced by the degree-one lift `γ`
(`AlgebraicGeometry.WeilGroup.exists_equivalence_isLisse_geometricCoinvariants`). Hence, for an
affine curve, `H_c² (C, ℱ) ≅ V_{π₁(C)} (-1)` Frobenius-equivariantly
(`AlgebraicGeometry.WeilGroup.exists_equivalence_isLisse_compactlySupportedCohomology_two`,
blueprint `lemma-degree-zero-top-cohomology--2`), and the eigenvalues `α` of the geometric Frobenius
on `H_c² (C, ℱ)` give determinant weights `wt (α q⁻¹)` of `ℱ`
(blueprint `proposition-bound-largest-determinant-weight`).

## Main statements

- `AlgebraicGeometry.WeilGroup.exists_equivalence_isLisse_geometricCoinvariants`
- `AlgebraicGeometry.WeilGroup.exists_equivalence_isLisse_compactlySupportedCohomology_two`
- `AlgebraicGeometry.WeilGroup.exists_equivalence_isLisse_hasDetWeight`
- `AlgebraicGeometry.WeilGroup.exists_weilSheaf_hasDetWeight_of_isLisse`
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace WeilGroup

variable {k G : Type*} [Field k] [Group G]

/-- Linear algebra behind the geometric coinvariants: let `ρ` be a finite-dimensional
representation of `G` on `V`, `H ≤ G` a subgroup and `γ ∈ G` an element normalising `H`, and let
`M` be a Frobenius module identified with the `H`-invariants of a representation `ρ'`
isomorphic to the contragredient `ρ^∨`, the Frobenius of `M` becoming `ρ' γ`. Then the dual
`M^∨` is the coinvariant space `V_H`, with Frobenius induced by `ρ γ`. -/
theorem exists_linearEquiv_coinvariants_of_dual {V V' : Type*} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] [AddCommGroup V'] [Module k V'] (ρ : Representation k G V)
    (ρ' : Representation k G V') (H : Subgroup G) [H.Normal] (γ : G)
    (b : ρ'.Equiv ρ.dual) (M : FrobeniusModule k)
    (a : M.carrier ≃ₗ[k] Representation.invariants (ρ'.comp H.subtype))
    (ha : ∀ v, (a (M.frobenius v) : V') = ρ' γ (a v)) :
    ∃ f : M.dual.carrier ≃ₗ[k] Representation.Coinvariants (ρ.comp H.subtype),
      ∀ v, f (M.dual.frobenius v) = ρ.toCoinvariants H γ (f v) := by
  let bL := b.toLinearEquiv
  have hb (g : G) (u) : bL (ρ' g u) = ρ.dual g (bL u) :=
    Representation.IntertwiningMap.isIntertwining _ _ b.toIntertwiningMap g u
  have hdual (g : G) (φ : Module.Dual k V) (w) : ρ.dual g φ w = φ (ρ g⁻¹ w) := by
    rw [Representation.dual_apply]
    rfl
  -- the linear forms coming from invariants of `ρ'` are invariant
  have hinv (u : Representation.invariants (ρ'.comp H.subtype)) (h : H) (w) :
      bL u.1 (ρ h w) = bL u.1 w := by
    have h1 : ρ' ((h⁻¹ : H) : G) u.1 = u.1 := u.2 h⁻¹
    have h2 := congrArg (fun z ↦ bL z w) h1
    rw [hb, hdual, Subgroup.coe_inv, inv_inv] at h2
    exact h2
  have hmk (h : H) (v : V) : Representation.Coinvariants.mk (ρ.comp H.subtype) (ρ h v) =
      Representation.Coinvariants.mk (ρ.comp H.subtype) v :=
    Representation.Coinvariants.mk_self_apply _ h v
  -- invariant linear forms on `V` are the linear forms on the coinvariants
  let toF : Representation.invariants (ρ'.comp H.subtype) →ₗ[k]
      Module.Dual k (Representation.Coinvariants (ρ.comp H.subtype)) :=
    { toFun u := Representation.Coinvariants.lift (ρ.comp H.subtype) (bL u.1)
        (fun h ↦ LinearMap.ext fun v ↦ by
          simp only [LinearMap.comp_apply, MonoidHom.comp_apply, Subgroup.coe_subtype]
          rw [hinv u h])
      map_add' u u' := Representation.Coinvariants.hom_ext (LinearMap.ext fun v ↦ by
        simp [Representation.Coinvariants.lift_mk])
      map_smul' r u := Representation.Coinvariants.hom_ext (LinearMap.ext fun v ↦ by
        simp [Representation.Coinvariants.lift_mk]) }
  have htoF (u) (v : V) : toF u (Representation.Coinvariants.mk _ v) = bL u.1 v :=
    rfl
  let invF : Module.Dual k (Representation.Coinvariants (ρ.comp H.subtype)) →ₗ[k]
      Representation.invariants (ρ'.comp H.subtype) :=
    { toFun φ := ⟨bL.symm (φ ∘ₗ Representation.Coinvariants.mk _), fun h ↦ by
        change ρ' (h : G) _ = _
        apply bL.injective
        rw [hb, LinearEquiv.apply_symm_apply]
        refine LinearMap.ext fun w ↦ ?_
        rw [hdual]
        simp only [LinearMap.comp_apply]
        rw [← Subgroup.coe_inv, hmk]⟩
      map_add' φ φ' := Subtype.ext (by simp [LinearMap.add_comp])
      map_smul' r φ := Subtype.ext (by simp [LinearMap.smul_comp]) }
  let d : Representation.invariants (ρ'.comp H.subtype) ≃ₗ[k]
      Module.Dual k (Representation.Coinvariants (ρ.comp H.subtype)) :=
    LinearEquiv.ofLinearMap toF invF
    (LinearMap.ext fun φ ↦ Representation.Coinvariants.hom_ext (LinearMap.ext fun v ↦ by
      change bL (bL.symm _) v = _
      rw [LinearEquiv.apply_symm_apply]
      simp))
    (LinearMap.ext fun u ↦ Subtype.ext (by
      change bL.symm (toF u ∘ₗ Representation.Coinvariants.mk _) = u.1
      rw [LinearEquiv.symm_apply_eq]
      refine LinearMap.ext fun v ↦ ?_
      simp only [LinearMap.comp_apply, htoF]))
  -- the Frobenius `ρ (γ)` on the coinvariants
  let Q := ρ.toCoinvariants H
  let T : Representation.Coinvariants (ρ.comp H.subtype) ≃ₗ[k]
      Representation.Coinvariants (ρ.comp H.subtype) :=
    LinearEquiv.ofLinearMap (Q γ) (Q γ⁻¹)
      (LinearMap.ext fun n ↦ by
        rw [LinearMap.comp_apply, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
          Module.End.one_apply, LinearMap.id_apply])
      (LinearMap.ext fun n ↦ by
        rw [LinearMap.comp_apply, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
          Module.End.one_apply, LinearMap.id_apply])
  have hc (m : M.carrier) (n : Representation.Coinvariants (ρ.comp H.subtype)) :
      (a.trans d) (M.frobenius m) (T n) = (a.trans d) m n := by
    refine Representation.Coinvariants.induction_on n fun v ↦ ?_
    change toF (a _) (Q γ (Representation.Coinvariants.mk _ v)) =
      toF (a m) (Representation.Coinvariants.mk _ v)
    rw [Representation.toCoinvariants_mk, htoF, htoF, ha, hb, hdual,
      ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  exact FrobeniusModule.exists_linearEquiv_dual_of_linearEquiv_dual M T (a.trans d) hc

section Sheaf

variable {K : Type u} [Field K] [Finite K] {C : Scheme.{u}} [C.Over (Spec (.of K))]
  [IsCurve (C ↘ Spec (.of K))] [SmoothOfRelativeDimension 1 (C ↘ Spec (.of K))]
  [GeometricallyConnected (C ↘ Spec (.of K))] (W : WeilGroup (C ↘ Spec (.of K))) (l : ℕ)
  [Fact l.Prime] [Fact (ringChar K ≠ l)]

/-- Blueprint `definition-weil-representation--1`, with the geometric coinvariants:
the lisse sheaf–representation equivalence `ℱ ↦ (V, ρ)` of
`AlgebraicGeometry.WeilGroup.exists_equivalence_isLisse` (stalks, duals and global sections
being as there) identifies the geometric coinvariants `Γ(C̄, ℱ^∨)^∨` of `ℱ`
(`AlgebraicGeometry.WeilSheaf.geometricCoinvariants`) with the coinvariants `V_{π₁(C)}`,
the Frobenius becoming the endomorphism induced by the degree-one lift `γ`.

Indeed `Γ(C̄, ℱ^∨)` is the space of invariants of the representation of `ℱ^∨`, the
contragredient `ρ^∨`, and the `π₁(C)`-invariant linear forms on `V` are the linear forms on
`V_{π₁(C)}` (`AlgebraicGeometry.WeilGroup.exists_linearEquiv_coinvariants_of_dual`). -/
theorem exists_equivalence_isLisse_geometricCoinvariants :
    ∃ e : ObjectProperty.FullSubcategory (fun F : WeilSheaf K l C ↦ F.IsLisse) ≌
        ObjectProperty.FullSubcategory (W.isLisseRep l),
      (∀ (F : ObjectProperty.FullSubcategory (fun F : WeilSheaf K l C ↦ F.IsLisse))
          (x : C.finitePoints),
        ∃ f : (F.obj.stalk x).carrier ≃ₗ[PadicAlgCl l] (e.functor.obj F).obj.V,
          ∀ v, f ((F.obj.stalk x).frobenius v) =
            (e.functor.obj F).obj.ρ (W.frobenius x) (f v)) ∧
      (∀ F : ObjectProperty.FullSubcategory (fun F : WeilSheaf K l C ↦ F.IsLisse),
        Nonempty ((e.functor.obj ⟨F.obj.dual F.property, F.property.dual⟩).obj.ρ.Equiv
          (e.functor.obj F).obj.ρ.dual)) ∧
      (∀ F : ObjectProperty.FullSubcategory (fun F : WeilSheaf K l C ↦ F.IsLisse),
        ∃ f : F.obj.globalSections.carrier ≃ₗ[PadicAlgCl l]
            Representation.invariants ((e.functor.obj F).obj.ρ.comp W.geometric.subtype),
          ∀ v, (f (F.obj.globalSections.frobenius v) : (e.functor.obj F).obj.V) =
            (e.functor.obj F).obj.ρ W.frobeniusLift (f v)) ∧
      (∀ F : ObjectProperty.FullSubcategory (fun F : WeilSheaf K l C ↦ F.IsLisse),
        ∃ f : (F.obj.geometricCoinvariants F.property).carrier ≃ₗ[PadicAlgCl l]
            Representation.Coinvariants ((e.functor.obj F).obj.ρ.comp W.geometric.subtype),
          ∀ v, f ((F.obj.geometricCoinvariants F.property).frobenius v) =
            (e.functor.obj F).obj.ρ.toCoinvariants W.geometric W.frobeniusLift (f v)) := by
  obtain ⟨e, hst, hdu, hse, -⟩ := W.exists_equivalence_isLisse l
  refine ⟨e, hst, hdu, hse, fun F ↦ ?_⟩
  obtain ⟨a, ha⟩ := hse ⟨F.obj.dual F.property, F.property.dual⟩
  obtain ⟨b⟩ := hdu F
  have : FiniteDimensional (PadicAlgCl l) (e.functor.obj F).obj.V := (e.functor.obj F).property.1
  exact exists_linearEquiv_coinvariants_of_dual _ _ W.geometric W.frobeniusLift b _ a ha

/-- An eigenvalue of the Frobenius of a Frobenius module `M` identified with `(V, T)` is an
eigenvalue of `T`. -/
theorem _root_.FrobeniusModule.hasEigenvalue_of_linearEquiv {k : Type*} [Field k]
    (M : FrobeniusModule k) {V : Type*} [AddCommGroup V] [Module k V] {T : Module.End k V}
    (f : M.carrier ≃ₗ[k] V) (hf : ∀ v, f (M.frobenius v) = T (f v)) {α : k}
    (hα : M.frobeniusEnd.HasEigenvalue α) : T.HasEigenvalue α := by
  obtain ⟨v, hv⟩ := hα.exists_hasEigenvector
  refine Module.End.hasEigenvalue_of_hasEigenvector (x := f v) ⟨?_, ?_⟩
  · rw [Module.End.mem_eigenspace_iff, ← hf, ← map_smul, ← hv.apply_eq_smul]
    rfl
  · rw [ne_eq, map_eq_zero_iff _ f.injective]
    exact hv.2

/-- If `N ≅ M (-1)` and `M` is identified with `(V, T)`, then `N` is identified with
`(V, q T)`. -/
theorem _root_.FrobeniusModule.exists_linearEquiv_of_equiv_tateTwist_neg_one {k : Type*}
    [Field k] {M N : FrobeniusModule k} {q : ℕ} (hq : (q : k) ≠ 0)
    (e : N.Equiv (M.tateTwist q (-1))) {V : Type*} [AddCommGroup V] [Module k V]
    {T : Module.End k V} (f : M.carrier ≃ₗ[k] V) (hf : ∀ v, f (M.frobenius v) = T (f v)) :
    ∃ g : N.carrier ≃ₗ[k] V, ∀ v, g (N.frobenius v) = (q : k) • T (g v) := by
  have hq' : ((q : k) ^ (-(-1 : ℤ))) ≠ 0 := zpow_ne_zero _ hq
  refine ⟨e.toLinearEquiv.trans f, fun v ↦ ?_⟩
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, e.map_frobenius]
  have key := FrobeniusModule.frobeniusEnd_rescale_apply (M := M) hq' (e.toLinearEquiv v)
  refine (congrArg f key).trans ?_
  rw [map_smul, FrobeniusModule.frobeniusEnd_apply, hf, neg_neg, zpow_one]
  rfl

variable [IsAffine C]

/-- Blueprint `lemma-degree-zero-top-cohomology--2`: Description of `H_c²` on an affine curve.

Let `C₀` be a smooth geometrically connected affine curve and `ℱ` a lisse Weil sheaf on `C₀` with
Weil fundamental representation `(V, ρ)` (the lisse sheaf–representation equivalence
`AlgebraicGeometry.WeilGroup.exists_equivalence_isLisse`). Then
`H_c² (C, ℱ) ≅ V_{π₁(C)} (-1)` Frobenius-equivariantly: the geometric Frobenius on `H_c²`
becomes `q` times the endomorphism of the coinvariants induced by the degree-one lift `γ`, that
is `AlgebraicGeometry.WeilGroup.compactTopFrobenius`.

This is `AlgebraicGeometry.WeilSheaf.nonempty_equiv_compactlySupportedCohomology_two`, which
identifies `H_c²` with the Tate twist `(-1)` of the geometric coinvariants, combined with the
description of the geometric coinvariants as `V_{π₁(C)}`
(`AlgebraicGeometry.WeilGroup.exists_equivalence_isLisse_geometricCoinvariants`). -/
theorem exists_equivalence_isLisse_compactlySupportedCohomology_two :
    ∃ e : ObjectProperty.FullSubcategory (fun F : WeilSheaf K l C ↦ F.IsLisse) ≌
        ObjectProperty.FullSubcategory (W.isLisseRep l),
      (∀ (F : ObjectProperty.FullSubcategory (fun F : WeilSheaf K l C ↦ F.IsLisse))
          (x : C.finitePoints),
        ∃ f : (F.obj.stalk x).carrier ≃ₗ[PadicAlgCl l] (e.functor.obj F).obj.V,
          ∀ v, f ((F.obj.stalk x).frobenius v) =
            (e.functor.obj F).obj.ρ (W.frobenius x) (f v)) ∧
      (∀ F : ObjectProperty.FullSubcategory (fun F : WeilSheaf K l C ↦ F.IsLisse),
        ∃ f : (F.obj.compactlySupportedCohomology 2).carrier ≃ₗ[PadicAlgCl l]
            Representation.Coinvariants ((e.functor.obj F).obj.ρ.comp W.geometric.subtype),
          ∀ v, f ((F.obj.compactlySupportedCohomology 2).frobenius v) =
            W.compactTopFrobenius l (e.functor.obj F).obj.ρ (f v)) := by
  obtain ⟨e, hst, -, -, hco⟩ := W.exists_equivalence_isLisse_geometricCoinvariants l
  refine ⟨e, hst, fun F ↦ ?_⟩
  obtain ⟨f, hf⟩ := hco F
  obtain ⟨e₂⟩ := WeilSheaf.nonempty_equiv_compactlySupportedCohomology_two F.obj F.property
  exact FrobeniusModule.exists_linearEquiv_of_equiv_tateTwist_neg_one
    (Nat.cast_ne_zero.2 Nat.card_pos.ne') e₂ f hf

/-- Blueprint `proposition-bound-largest-determinant-weight`: Eigenvalues of `H_c²` are determinant
weights.

Let `C₀` be a smooth geometrically connected affine curve and `ℱ` a lisse Weil sheaf on `C₀` with
Weil fundamental representation `(V, ρ)`. If `α` is an eigenvalue of the geometric Frobenius on
`H_c² (C, ℱ)`, then `wt_{ι, q} (α q⁻¹)` is a determinant weight of `ℱ`: the determinant weight of
an irreducible constituent `M ⧸ N` of `ρ`.

By `lemma-degree-zero-top-cohomology--2`
(`AlgebraicGeometry.WeilGroup.exists_equivalence_isLisse_compactlySupportedCohomology_two`),
`α` is an eigenvalue of `AlgebraicGeometry.WeilGroup.compactTopFrobenius`, and this is
`AlgebraicGeometry.WeilGroup.exists_isConstituent_hasDetWeight_of_hasEigenvalue`. -/
theorem exists_equivalence_isLisse_hasDetWeight (ι : PadicAlgCl l →+* ℂ) :
    ∃ e : ObjectProperty.FullSubcategory (fun F : WeilSheaf K l C ↦ F.IsLisse) ≌
        ObjectProperty.FullSubcategory (W.isLisseRep l),
      (∀ (F : ObjectProperty.FullSubcategory (fun F : WeilSheaf K l C ↦ F.IsLisse))
          (x : C.finitePoints),
        ∃ f : (F.obj.stalk x).carrier ≃ₗ[PadicAlgCl l] (e.functor.obj F).obj.V,
          ∀ v, f ((F.obj.stalk x).frobenius v) =
            (e.functor.obj F).obj.ρ (W.frobenius x) (f v)) ∧
      ∀ (F : ObjectProperty.FullSubcategory (fun F : WeilSheaf K l C ↦ F.IsLisse))
        {α : PadicAlgCl l}, (F.obj.compactlySupportedCohomology 2).frobeniusEnd.HasEigenvalue α →
        ∃ N M : Subrepresentation (e.functor.obj F).obj.ρ, N ≤ M ∧
          (M.subquotient N).IsConstituent (e.functor.obj F).obj.ρ ∧
          W.HasDetWeight l (M.subquotient N) ι
            (frobeniusWeight ι (Nat.card K) (α / Nat.card K)) := by
  obtain ⟨e, hst, h₂⟩ := W.exists_equivalence_isLisse_compactlySupportedCohomology_two l
  refine ⟨e, hst, fun F α hα ↦ ?_⟩
  obtain ⟨f, hf⟩ := h₂ F
  have : FiniteDimensional (PadicAlgCl l) (e.functor.obj F).obj.V := (e.functor.obj F).property.1
  exact exists_isConstituent_hasDetWeight_of_hasEigenvalue (e.functor.obj F).obj.ρ ι
    ((F.obj.compactlySupportedCohomology 2).hasEigenvalue_of_linearEquiv f hf hα)

variable {W l} in
/-- Blueprint `proposition-bound-largest-determinant-weight`, for the lisse Weil sheaf `ℱ` attached
to a lisse representation `ρ` of `W(C₀)` (`AlgebraicGeometry.WeilGroup.exists_weilSheaf_of_isLisse`,
whose local Frobenius at `x` has the characteristic polynomial of `ρ (Frob_x)`): every eigenvalue
`α` of the geometric Frobenius on `H_c² (C, ℱ)` gives the determinant weight `wt_{ι, q} (α q⁻¹)`
of an irreducible constituent of `ρ`. -/
theorem exists_weilSheaf_hasDetWeight_of_isLisse (ι : PadicAlgCl l →+* ℂ) {V : Type u}
    [AddCommGroup V] [Module (PadicAlgCl l) V] [FiniteDimensional (PadicAlgCl l) V]
    {ρ : Representation (PadicAlgCl l) W.carrier V} (hρ : W.IsLisse l ρ) :
    ∃ (F : WeilSheaf K l C) (_ : F.IsLisse),
      (∀ x : C.finitePoints, (F.stalk x).frobeniusEnd.charpoly = (ρ (W.frobenius x)).charpoly) ∧
      ∀ {α : PadicAlgCl l}, (F.compactlySupportedCohomology 2).frobeniusEnd.HasEigenvalue α →
        ∃ N M : Subrepresentation ρ, N ≤ M ∧ (M.subquotient N).IsConstituent ρ ∧
          W.HasDetWeight l (M.subquotient N) ι
            (frobeniusWeight ι (Nat.card K) (α / Nat.card K)) := by
  obtain ⟨F, hF, hst, f, hf⟩ := exists_weilSheaf_of_isLisse (W := W) hρ
  refine ⟨F, hF, hst, fun {α} hα ↦ ?_⟩
  obtain ⟨e₂⟩ := WeilSheaf.nonempty_equiv_compactlySupportedCohomology_two F hF
  obtain ⟨g, hg⟩ := FrobeniusModule.exists_linearEquiv_of_equiv_tateTwist_neg_one
    (Nat.cast_ne_zero.2 Nat.card_pos.ne') e₂ f hf
  exact exists_isConstituent_hasDetWeight_of_hasEigenvalue ρ ι
    ((F.compactlySupportedCohomology 2).hasEigenvalue_of_linearEquiv g hg hα)

end Sheaf

end WeilGroup

end AlgebraicGeometry
