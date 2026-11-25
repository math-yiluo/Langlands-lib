/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.Divisor
public import WeilConjectures.AlgebraicGeometry.Curve.SerreDuality
public import WeilConjectures.AlgebraicGeometry.Hilbert.Curve
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree

/-!
# Pullback of divisors along finite flat morphisms of curves

Let `π : X ⟶ Y` be a finite flat morphism of proper smooth integral curves over an algebraically
closed field `k`. We define the pullback `π^* D` of a divisor `D = ∑_y n_y [y]` on `Y` as
`∑_x n_{π(x)} e_x [x]`, where the ramification index `e_x = v_x(π^♯ t)` is the order at `x` of the
pullback of a uniformizer `t` of `𝒪_{Y, π(x)}`, and prove `deg π^* D = d · deg D`, where
`d = [k(X) : k(Y)]` is the degree of `π`.

## Main definitions and results

- `AlgebraicGeometry.Scheme.Hom.ramificationIndex`: the ramification index `e_x` of `π` at `x`.
- `AlgebraicGeometry.Scheme.Divisor.pullback`: the pullback of divisors along a finite morphism.
- `AlgebraicGeometry.Scheme.Divisor.degree_pullback`: `deg π^* D = d · deg D`.
- `AlgebraicGeometry.Scheme.Hom.finrank_genericPoint_eq_finrank_functionField`: the rank `d` of
  `π` is the degree `[k(X) : k(Y)]` of the extension of function fields.
-/

@[expose] public section

universe u

open CategoryTheory Limits IsLocalRing

/-- The residue map of a local ring which is a field is bijective. -/
theorem IsLocalRing.residue_bijective_of_isField {R : Type*} [CommRing R] [IsLocalRing R]
    (hR : IsField R) : Function.Bijective (IsLocalRing.residue R) := by
  refine ⟨?_, IsLocalRing.residue_surjective⟩
  rw [injective_iff_map_eq_zero]
  intro a ha
  rwa [IsLocalRing.residue_eq_zero_iff,
    (IsLocalRing.isField_iff_maximalIdeal_eq).mp hR, Ideal.mem_bot] at ha

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}}

section Degree

/-- A flat morphism of integral schemes maps the generic point to the generic point: the generic
point of the target generalizes the image of the generic point of the source, and generizations
lift along flat morphisms. -/
theorem Hom.apply_genericPoint_of_flat [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [Flat f] :
    f (genericPoint X) = genericPoint Y := by
  obtain ⟨x, hx, hfx⟩ := Flat.generalizingMap f (genericPoint_specializes (f (genericPoint X)))
  obtain rfl : x = genericPoint X := (hx.antisymm (genericPoint_specializes x)).eq
  exact hfx

/-- The map of function fields `k(Y) → k(X)` induced by a morphism `f : X ⟶ Y` of integral
schemes mapping the generic point to the generic point, e.g. a flat morphism: the map of stalks
at the generic point. -/
noncomputable def Hom.functionFieldMap [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y)
    (hf : f (genericPoint X) = genericPoint Y) : Y.functionField ⟶ X.functionField :=
  Y.presheaf.stalkSpecializes (specializes_of_eq hf) ≫ f.stalkMap (genericPoint X)

/-- If the stalks at `x` and at `z = f x` are fields, the degree of the extension of stalks
equals the degree of the extension of residue fields. -/
theorem Hom.finrank_stalk_eq_finrank_residueField (f : X ⟶ Y) (x : X) (z : Y) (hz : f x = z)
    (hY : IsField (Y.presheaf.stalk z)) (hX : IsField (X.presheaf.stalk x)) :
    letI := (Y.presheaf.stalkSpecializes (specializes_of_eq hz) ≫ f.stalkMap x).hom.toAlgebra
    letI := (f.residueFieldMap x).hom.toAlgebra
    Module.finrank (Y.presheaf.stalk z) (X.presheaf.stalk x) =
      Module.finrank (Y.residueField (f x)) (X.residueField x) := by
  subst hz
  let _ := (Y.presheaf.stalkSpecializes (specializes_of_eq (rfl : f x = f x)) ≫
    f.stalkMap x).hom.toAlgebra
  let _ := (f.residueFieldMap x).hom.toAlgebra
  refine Algebra.finrank_eq_of_equiv_equiv
    (RingEquiv.ofBijective _ (residue_bijective_of_isField hY))
    (RingEquiv.ofBijective _ (residue_bijective_of_isField hX)) ?_
  ext a
  have h := congr($(residue_residueFieldMap f x) a)
  simp only [CommRingCat.comp_apply] at h
  simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingHom.coe_coe, RingEquiv.ofBijective_apply, RingHom.algebraMap_toAlgebra,
    CommRingCat.hom_comp, TopCat.Presheaf.stalkSpecializes_refl]
  exact h

/-- **The degree of a finite flat morphism of integral schemes is the degree of the extension of
function fields.** For a finite flat morphism `f : X ⟶ Y` of integral schemes, the rank
`d = f.finrank (genericPoint Y)` of `f_* 𝒪_X` is `[k(X) : k(Y)]`.

(blueprint: `theorem-riemann-roch-coherent-serre-duality`) -/
theorem Hom.finrank_genericPoint_eq_finrank_functionField [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [Flat f] [IsFinite f] :
    letI := (f.functionFieldMap f.apply_genericPoint_of_flat).hom.toAlgebra
    f.finrank (genericPoint Y) = Module.finrank Y.functionField X.functionField := by
  have h := f.finrank_stalk_eq_finrank_residueField (genericPoint X) (genericPoint Y)
    f.apply_genericPoint_of_flat (Field.toIsField Y.functionField)
    (Field.toIsField X.functionField)
  refine Eq.trans ?_ h.symm
  rw [f.finrank_eq_fiberDegree, ← f.apply_genericPoint_of_flat, f.fiberDegree_genericPoint]

end Degree

section Pullback

/-- A finite morphism maps closed points to closed points. -/
theorem Hom.isClosed_singleton_apply (f : X ⟶ Y) [IsFinite f] {x : X} (hx : IsClosed {x}) :
    IsClosed {f x} := by
  simpa using f.isClosedMap _ hx

/-- The points in the fibre of a locally quasi-finite morphism over a closed point are closed. -/
theorem Hom.isClosed_singleton_of_apply (f : X ⟶ Y) [LocallyQuasiFinite f] {x : X}
    (hx : IsClosed {f x}) : IsClosed {x} := by
  have := (f.isDiscrete_preimage_singleton (f x)).to_subtype
  have hc := (isClosed_discrete ({⟨x, rfl⟩} : Set (f ⁻¹' {f x}))).trans
    (hx.preimage f.continuous)
  simpa using hc

variable [IsIntegral X] [IsLocallyNoetherian X]

/-- The **ramification index** `e_x = v_x(π^♯ t)` of a morphism `π : X ⟶ Y` at a point `x`: the
order of vanishing at `x` of the image of a chosen generator `t` of the maximal ideal of
`𝒪_{Y, π(x)}` (a uniformizer, when `𝒪_{Y, π(x)}` is a discrete valuation ring). -/
noncomputable def Hom.ramificationIndex (π : X ⟶ Y) (x : X) : ℤ :=
  X.ord (algebraMap (X.presheaf.stalk x) X.functionField (π.stalkMap x
    (Classical.epsilon fun t ↦ maximalIdeal (Y.presheaf.stalk (π x)) = Ideal.span {t}))) x

/-- The ramification index can be computed with any section `t` whose germ at `π x` is the
chosen generator of the maximal ideal. -/
lemma Hom.ramificationIndex_eq (π : X ⟶ Y) (x : X) {V : Y.Opens} (hxV : π x ∈ V) (t : Γ(Y, V))
    (ht : Y.presheaf.germ V (π x) hxV t =
      Classical.epsilon fun t ↦ maximalIdeal (Y.presheaf.stalk (π x)) = Ideal.span {t}) :
    π.ramificationIndex x = X.ord (algebraMap (X.presheaf.stalk x) X.functionField
      (X.presheaf.germ (π ⁻¹ᵁ V) x hxV (π.app V t))) x := by
  rw [Hom.ramificationIndex, ← ht, Scheme.Hom.germ_stalkMap_apply]

variable (π : X ⟶ Y) [IsFinite π]

/-- The pullback `π^* D = ∑_x n_{π(x)} e_x [x]` of a divisor `D = ∑_y n_y [y]` along a finite
morphism `π`, where `e_x` is the ramification index
(`AlgebraicGeometry.Scheme.Hom.ramificationIndex`).
It has finite support since the fibres of `π` are finite.

(blueprint: `theorem-riemann-roch-coherent-serre-duality`) -/
noncomputable def Divisor.pullback : Y.Divisor →+ X.Divisor where
  toFun D := Finsupp.ofSupportFinite
    (fun P ↦ D ⟨π P.1, π.isClosed_singleton_apply P.2⟩ * π.ramificationIndex P.1) <| by
      refine ((π.finite_preimage (D.support.finite_toSet.image Subtype.val)).preimage
        Subtype.val_injective.injOn).subset fun P hP ↦ ?_
      exact ⟨_, Finsupp.mem_support_iff.mpr (left_ne_zero_of_mul hP), rfl⟩
  map_zero' := by
    ext P
    simp [Finsupp.ofSupportFinite_coe]
  map_add' D D' := by
    ext P
    simp [Finsupp.ofSupportFinite_coe, add_mul]

lemma Divisor.pullback_apply (D : Y.Divisor) (P : closedPoints X) :
    Divisor.pullback π D P =
      D ⟨π P.1, π.isClosed_singleton_apply P.2⟩ * π.ramificationIndex P.1 := by
  simp [Divisor.pullback, Finsupp.ofSupportFinite_coe]

end Pullback

section Curve

variable {k : Type u} [Field k] [IsAlgClosed k] [IsIntegral X] [IsLocallyNoetherian X]
  [IsIntegral Y] (π : X ⟶ Y) [IsFinite π] [Flat π]

/-- **Degree of the pullback of a point.** `deg π^*[y] = d` for every closed point `y`, where
`d = π.finrank (genericPoint Y)` is the degree of `π`.

(blueprint: `theorem-riemann-roch-coherent-serre-duality`) -/
theorem Divisor.degree_pullback_single
    [X.Over (Spec (.of k))] [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))] [Y.Over (Spec (.of k))]
    [SmoothOfRelativeDimension 1 (Y ↘ Spec (.of k))] [IsProper (Y ↘ Spec (.of k))]
    [π.IsOver (Spec (.of k))] (y : closedPoints Y) (n : ℤ) :
    Divisor.degree X (Divisor.pullback π (Finsupp.single y n)) =
      π.finrank (genericPoint Y) * n := by
  classical
  obtain ⟨y, hy⟩ := y
  have hyc : IsClosed {y} := hy
  have := SmoothOfRelativeDimension.smooth 1 (Y ↘ Spec (.of k))
  -- a uniformizer at `y`, as a section `t` on an open `V ∋ y`
  obtain ⟨_, hdvr⟩ := isDiscreteValuationRing_stalk_of_isClosed (Y ↘ Spec (.of k)) hyc
  have hε : maximalIdeal (Y.presheaf.stalk y) = Ideal.span
      {Classical.epsilon fun t ↦ maximalIdeal (Y.presheaf.stalk y) = Ideal.span {t}} := by
    refine Classical.epsilon_spec (p := fun t ↦ maximalIdeal (Y.presheaf.stalk y) =
      Ideal.span {t}) ?_
    obtain ⟨t, ht⟩ := (IsPrincipalIdealRing.principal (maximalIdeal (Y.presheaf.stalk y))).1
    exact ⟨t, ht⟩
  obtain ⟨V, hyV, t, hgerm⟩ := TopCat.Presheaf.exists_germ_eq Y.presheaf
    (Classical.epsilon fun t ↦ maximalIdeal (Y.presheaf.stalk y) = Ideal.span {t})
  have hsum := finsum_ord_eq_finrank (k := k) π hyc hyV t (hgerm ▸ hε)
  -- the summand of the degree at a closed point `P` of `X`
  set F : X → ℤ := fun x ↦ ∑ᶠ (hx : π.base x = y), X.ord (algebraMap (X.presheaf.stalk x)
    X.functionField (X.presheaf.germ (π ⁻¹ᵁ V) x (show π.base x ∈ V from hx ▸ hyV)
      (π.app V t))) x with hF
  have hP (P : closedPoints X) :
      Divisor.pullback π (Finsupp.single ⟨y, hy⟩ n) P = n * F P.1 := by
    rw [Divisor.pullback_apply, Finsupp.single_apply]
    by_cases h : π P.1 = y
    · have hF : F P.1 = π.ramificationIndex P.1 := by
        rw [hF]
        dsimp only
        rw [finsum_eq_dif, dite_eq_left h]
        obtain ⟨P, hP⟩ := P
        subst h
        exact (π.ramificationIndex_eq P hyV t hgerm).symm
      rw [ite_eq_left (Subtype.ext h.symm), hF]
    · have hF : F P.1 = 0 := by
        rw [hF]
        dsimp only
        rw [finsum_eq_dif, dite_eq_right h]
      rw [ite_eq_right fun h' ↦ h (congrArg Subtype.val h').symm, hF, zero_mul, mul_zero]
  have hFc (x : X) (hx : F x ≠ 0) : x ∈ closedPoints X := by
    by_contra hxc
    refine hx ?_
    rw [hF]
    dsimp only
    rw [finsum_eq_dif,
      dite_eq_right fun (h : π x = y) ↦ hxc (π.isClosed_singleton_of_apply (h ▸ hyc))]
  have hC : ∑ᶠ x ∈ closedPoints X, F x = ∑ᶠ x, F x := finsum_congr fun x ↦ by
    by_cases hx : x ∈ closedPoints X
    · rw [finsum_eq_if, ite_eq_left hx]
    · rw [finsum_eq_if, ite_eq_right hx]
      exact (not_not.mp (mt (hFc x) hx)).symm
  rw [Divisor.degree_apply, Finsupp.sum, ← finsum_eq_sum_of_support_subset _
    (s := (Divisor.pullback π (Finsupp.single ⟨y, hy⟩ n)).support) (by simp)]
  simp_rw [hP]
  rw [← mul_finsum, finsum_set_coe_eq_finsum_mem (f := F), hC, hsum, mul_comm]

/-- **Degree of pullbacks of divisors.** For a finite flat morphism `π : X ⟶ Y` of proper smooth
integral curves over an algebraically closed field `k`, of degree `d = π.finrank (genericPoint Y)`,
`deg π^* D = d · deg D` for every divisor `D` on `Y`.

(blueprint: `theorem-riemann-roch-coherent-serre-duality`) -/
theorem Divisor.degree_pullback
    [X.Over (Spec (.of k))] [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))] [Y.Over (Spec (.of k))]
    [SmoothOfRelativeDimension 1 (Y ↘ Spec (.of k))] [IsProper (Y ↘ Spec (.of k))]
    [π.IsOver (Spec (.of k))] (D : Y.Divisor) :
    Divisor.degree X (Divisor.pullback π D) =
      π.finrank (genericPoint Y) * Divisor.degree Y D := by
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add D D' hD hD' => rw [map_add, map_add, hD, hD', map_add, mul_add]
  | single y n => rw [Divisor.degree_pullback_single (k := k), Divisor.degree_single]

/-- **Degree of pullbacks of divisors.** For a finite flat morphism `π : X ⟶ Y` of proper smooth
integral curves over an algebraically closed field `k`, `deg π^* D = [k(X) : k(Y)] · deg D` for
every divisor `D` on `Y`.

(blueprint: `theorem-riemann-roch-coherent-serre-duality`) -/
theorem Divisor.degree_pullback_eq_finrank_functionField_mul
    [X.Over (Spec (.of k))] [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))] [Y.Over (Spec (.of k))]
    [SmoothOfRelativeDimension 1 (Y ↘ Spec (.of k))] [IsProper (Y ↘ Spec (.of k))]
    [π.IsOver (Spec (.of k))] (D : Y.Divisor) :
    letI := (π.functionFieldMap π.apply_genericPoint_of_flat).hom.toAlgebra
    Divisor.degree X (Divisor.pullback π D) =
      Module.finrank Y.functionField X.functionField * Divisor.degree Y D := by
  rw [Divisor.degree_pullback (k := k), π.finrank_genericPoint_eq_finrank_functionField]

end Curve

end AlgebraicGeometry.Scheme
