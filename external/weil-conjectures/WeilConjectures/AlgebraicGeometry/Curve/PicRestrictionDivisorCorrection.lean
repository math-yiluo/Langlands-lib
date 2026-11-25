/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.Compactification
public import WeilConjectures.AlgebraicGeometry.Curve.Picard
import WeilConjectures.AlgebraicGeometry.Curve.DivisorRestrictionPicard
import WeilConjectures.AlgebraicGeometry.Curve.PrincipalDivisorOpenExtension

/-!
# Principal correction gives a boundary-supported representative

Source: blueprint, sec-curve-estimates/lem-sc-arbitrary-curve-cd/lem-sc-pic-affine,
first paragraph, restriction and boundary divisors
(blueprint: lem-sc-pic-restriction-divisor-correction).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A divisor whose class restricts trivially has a boundary-supported representative.
Source: blueprint, sec-curve-estimates/lem-sc-arbitrary-curve-cd/lem-sc-pic-affine, first paragraph;
restriction and boundary divisors, steps 2--4 of lem-sc-pic-restriction-exact
(blueprint: lem-sc-pic-restriction-divisor-correction).

Proof: Restrict D by retaining its coefficients at the points of C. The divisor-class
comparison identifies its class with the pullback of O(D), since the open immersion
identifies local rings and valuation bounds. The assumed triviality means that this
restricted divisor is principal, div_C(a), by injectivity of the divisor-class comparison.
The dense open immersion identifies the two function fields. Regard the same nonzero
rational function a as a function on c.Z. Its orders at points of C agree with those of a
on C, since their local rings are identified. Set E = D - div_Z(a). Its coefficients at
all points in the image vanish, and its Picard class equals that of D because principal
divisors have trivial class. Both divisors have finite support on the Noetherian curves.
If the boundary is empty this construction forces E = 0, as required. The conclusion is
only a divisor normal form; generation of the Picard kernel is proved separately. -/
theorem Scheme.Hom.pic_restriction_divisor_correction
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f] [IsAffine C]
    (c : Compactification f) [IsConnectedCurve c.g]
    [hsm : SmoothOfRelativeDimension 1 c.g]
    (D : c.Z.Divisor)
    (hD : Scheme.Pic.mapHom c.i
      (@Scheme.Divisor.toPic k _ c.Z ⟨c.g⟩ hsm D).toMul = 1) :
    ∃ E : c.Z.Divisor,
      @Scheme.Divisor.toPic k _ c.Z ⟨c.g⟩ hsm E =
        @Scheme.Divisor.toPic k _ c.Z ⟨c.g⟩ hsm D ∧
      ∀ P : closedPoints c.Z, P.val ∈ Set.range c.i.base → E P = 0 := by
  classical
  let : C.Over (Spec (.of k)) := ⟨f⟩
  let : c.Z.Over (Spec (.of k)) := ⟨c.g⟩
  have : Smooth c.g := SmoothOfRelativeDimension.smooth 1 c.g
  let : IsNoetherian C := isNoetherian_of_locallyOfFiniteType f
  let : IsNoetherian c.Z := isNoetherian_of_locallyOfFiniteType c.g
  have : ConnectedSpace C := IsConnectedCurve.connectedSpace (f := f)
  have : ConnectedSpace c.Z := IsConnectedCurve.connectedSpace (f := c.g)
  have : IsRegular C := IsRegular.of_smooth f
  have : IsRegular c.Z := IsRegular.of_smooth c.g
  have : IrreducibleSpace C := IsRegular.irreducibleSpace C
  have : IrreducibleSpace c.Z := IsRegular.irreducibleSpace c.Z
  have : IsReduced C := isReduced_of_isReduced_stalk C
  have : IsReduced c.Z := isReduced_of_isReduced_stalk c.Z
  have : IsIntegral C := isIntegral_of_irreducibleSpace_of_isReduced C
  have : IsIntegral c.Z := isIntegral_of_irreducibleSpace_of_isReduced c.Z
  let : SmoothOfRelativeDimension 1 f :=
    (smoothOfRelativeDimension_iff_topologicalKrullDim_eq f 1).mpr
      (IsConnectedCurve.krullDim_eq_one (f := f))
  let : SmoothOfRelativeDimension 1 (C ↘ Spec (.of k)) := by
    change SmoothOfRelativeDimension 1 f
    infer_instance
  let : SmoothOfRelativeDimension 1 (c.Z ↘ Spec (.of k)) := by
    change SmoothOfRelativeDimension 1 c.g
    exact hsm
  let : IsCurve (C ↘ Spec (.of k)) := by change IsCurve f; infer_instance
  let : IsCurve (c.Z ↘ Spec (.of k)) := by change IsCurve c.g; infer_instance
  obtain ⟨R, hR, hcoeff⟩ := f.exists_divisor_restriction_picard c D
  have hRzero : Scheme.Divisor.toPic k C R = 0 := by
    apply Additive.toMul.injective
    exact hR.trans hD
  obtain ⟨eC, heC⟩ := Scheme.exists_divisorClassGroup_addEquiv_pic (k := k) (C := C)
  have hRclass : (QuotientAddGroup.mk R : C.DivisorClassGroup) = 0 := by
    apply eC.injective
    rw [heC, hRzero, map_zero]
  have hprincipal : R ∈ C.principalDivisors := (QuotientAddGroup.eq_zero_iff R).mp hRclass
  obtain ⟨a, ha⟩ := hprincipal
  obtain ⟨b, hb⟩ := f.exists_principal_divisor_open_extension c a
  obtain ⟨eZ, heZ⟩ := Scheme.exists_divisorClassGroup_addEquiv_pic (k := k) (C := c.Z)
  have hbclass : (QuotientAddGroup.mk (c.Z.div b) : c.Z.DivisorClassGroup) = 0 :=
    (QuotientAddGroup.eq_zero_iff _).mpr ⟨b, rfl⟩
  have hbzero : Scheme.Divisor.toPic k c.Z (c.Z.div b) = 0 := by
    rw [← heZ, hbclass, map_zero]
  refine ⟨D - c.Z.div b, ?_, ?_⟩
  · rw [map_sub, hbzero, sub_zero]
  · intro P hP
    obtain ⟨Q, hQ, hPQ⟩ := hcoeff P hP
    simp only [Finsupp.sub_apply]
    rw [hb P Q hQ, ha, hPQ, sub_self]

end AlgebraicGeometry
