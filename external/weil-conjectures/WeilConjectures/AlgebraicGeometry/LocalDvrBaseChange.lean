/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DivisorModule
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
import WeilConjectures.AlgebraicGeometry.RationalPointBaseChangeStalk
import WeilConjectures.AlgebraicGeometry.BaseChangeCurve
import WeilConjectures.AlgebraicGeometry.Curve.ClosedPoint
import WeilConjectures.AlgebraicGeometry.DensePoints

/-!
# Local orders at rational points after extension of algebraically closed fields

Source: blueprint sec-curve-estimates/sbc-thm-algebraically-closed-invariance,
proposition-cohomology-smooth-affine-curve, affine-case unit quotient paragraph
(blueprint: lem-sc-local-dvr-base-change).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

private theorem ord_eq_of_stalk_uniformizer
    (X Y : Scheme.{u}) [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (a : X) (b : Y)
    [IsDiscreteValuationRing (X.presheaf.stalk a)]
    [IsDiscreteValuationRing (Y.presheaf.stalk b)]
    (φ : X.presheaf.stalk a →+* Y.presheaf.stalk b)
    (hφ : ∀ t, Irreducible t → Irreducible (φ t))
    (ρ : X.functionField →+* Y.functionField)
    (hρ : ∀ r, ρ (algebraMap _ X.functionField r) =
      algebraMap _ Y.functionField (φ r)) (f : X.functionField) :
    Y.ord (ρ f) b = X.ord f a := by
  have ha : Order.coheight a = 1 := by
    have h := IsDiscreteValuationRing.ringKrullDim_eq_one (X.presheaf.stalk a)
    rw [ringKrullDim_stalk_eq_coheight] at h
    exact_mod_cast h
  have hb : Order.coheight b = 1 := by
    have h := IsDiscreteValuationRing.ringKrullDim_eq_one (Y.presheaf.stalk b)
    rw [ringKrullDim_stalk_eq_coheight] at h
    exact_mod_cast h
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible (X.presheaf.stalk a)
  have hr (r : X.presheaf.stalk a) (hr : r ≠ 0) :
      Ring.ordFrac (Y.presheaf.stalk b) (ρ (algebraMap _ X.functionField r)) =
        Ring.ordFrac (X.presheaf.stalk a) (algebraMap _ X.functionField r) := by
    obtain ⟨n, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr ht
    rw [hv]
    simp only [map_mul, map_pow, hρ]
    rw [Ring.ordFrac_of_isUnit (v.isUnit.map φ), Ring.ordFrac_of_isUnit v.isUnit,
      Ring.ordFrac_irreducible (hφ t ht), Ring.ordFrac_irreducible ht]
  have hfrac : Ring.ordFrac (Y.presheaf.stalk b) (ρ f) =
      Ring.ordFrac (X.presheaf.stalk a) f := by
    obtain ⟨r, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := X.presheaf.stalk a) f
    by_cases hr0 : r = 0
    · simp [hr0]
    · rw [map_div₀, map_div₀, map_div₀, hr r hr0, hr q (mem_nonZeroDivisors_iff_ne_zero.mp hq)]
  simpa only [Scheme.ord_eq_ordHom_of_coheight_eq_one ha,
    Scheme.ord_eq_ordHom_of_coheight_eq_one hb, Scheme.ordHom] using
    congrArg (fun z : WithZero (Multiplicative ℤ) ↦
      Multiplicative.toAdd (z.unzeroD 1)) hfrac

/-- The unique point over a rational closed point has a DVR stalk, and pullback preserves
normalized orders. Source: blueprint proposition-cohomology-smooth-affine-curve, affine-case unit
quotient paragraph (blueprint: lem-sc-local-dvr-base-change).

Proof:
1. Choose an affine neighbourhood Spec A of P. Its residue field is k because P is closed,
   A is of finite type over the algebraically closed field k. By
   theorem-finite-etale-covers-proper-henselian--2, points over P correspond to primes of
   (A/m) tensor_k k' = k'. This field has exactly one prime, giving the unique point P'.
2. Localize A tensor_k k' at m(A tensor_k k'). This is the corresponding localization of
   O_{X,P} tensor_k k'. The original stalk is a DVR by
   lem-sc-smooth-connected-curve-local-rings. Apply lem-sc-dvr-field-extension-order:
   the new stalk is a DVR, and a uniformizer stays a uniformizer.
3. The stalk fraction fields are the scheme function fields. Extend the stalk map to
   their fraction fields; the displayed compatibility specifies exactly the rational
   pullback. Unit-times-uniformizer factorizations then have the same integer exponent
   on both sides, giving the equality of Scheme.ord, as used in def-sc-divisor.

The existential integral and locally Noetherian instances only make the function fields
and Scheme.ord well typed; they follow from the smooth connected finite-type curve
hypotheses and their base changes. No such hypothesis is imposed on the input.
Closed points of this finite-type scheme over algebraically closed k are k-rational.
The pullback ring homomorphism is specified on the entire stalk, whose fraction field is
X.functionField, so this condition determines the canonical rational pullback uniquely. -/
theorem Scheme.local_dvr_base_change
    (k k' : Type u) [Field k] [IsAlgClosed k] [Field k'] [IsAlgClosed k']
    [Algebra k k'] (X : Scheme.{u}) (s : X ⟶ Spec (.of k))
    [IsConnectedCurve s] [Smooth s] [IsProper s] (P : X)
    (hP : P ∈ closedPoints X) :
    ∃ (_ : IsIntegral X)
      (_ : IsIntegral (pullback s (Spec.map (CommRingCat.ofHom (algebraMap k k')))))
      (_ : IsLocallyNoetherian X)
      (_ : IsLocallyNoetherian
        (pullback s (Spec.map (CommRingCat.ofHom (algebraMap k k'))))),
    ∃ P' : (pullback s (Spec.map (CommRingCat.ofHom (algebraMap k k'))) : Scheme.{u}),
      pullback.fst s (Spec.map (CommRingCat.ofHom (algebraMap k k'))) P' = P ∧
      (∀ Q : (pullback s (Spec.map (CommRingCat.ofHom (algebraMap k k'))) : Scheme.{u}),
        pullback.fst s (Spec.map (CommRingCat.ofHom (algebraMap k k'))) Q = P → Q = P') ∧
      IsDiscreteValuationRing (X.presheaf.stalk P) ∧
      IsDiscreteValuationRing
        ((pullback s (Spec.map (CommRingCat.ofHom (algebraMap k k')))).presheaf.stalk P') ∧
      ∃ ρ : X.functionField →+*
          (pullback s (Spec.map (CommRingCat.ofHom (algebraMap k k')))).functionField,
        (∀ r : X.presheaf.stalk
            (pullback.fst s (Spec.map (CommRingCat.ofHom (algebraMap k k'))) P'),
          ρ (algebraMap _ X.functionField r) =
            algebraMap _
              (pullback s (Spec.map (CommRingCat.ofHom (algebraMap k k')))).functionField
              ((pullback.fst s
                (Spec.map (CommRingCat.ofHom (algebraMap k k')))).stalkMap P' r)) ∧
        ∀ f : X.functionFieldˣ,
          (pullback s (Spec.map (CommRingCat.ofHom (algebraMap k k')))).ord (ρ f) P' =
            X.ord (f : X.functionField) P := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap k k'))
  let X' := pullback s g
  let s' : X' ⟶ Spec (.of k') := pullback.snd s g
  have hbase := baseChange_curve (k' := k') s
  let : IsConnectedCurve s' := hbase.2.2.2.2.2 inferInstance
  let : Smooth s' := hbase.2.2.1 inferInstance
  let : IsNoetherian X := isNoetherian_of_locallyOfFiniteType s
  let : IsNoetherian X' := isNoetherian_of_locallyOfFiniteType s'
  let : ConnectedSpace X := IsConnectedCurve.connectedSpace (f := s)
  let : ConnectedSpace X' := IsConnectedCurve.connectedSpace (f := s')
  let : IsRegular X := IsRegular.of_smooth s
  let : IsRegular X' := IsRegular.of_smooth s'
  let : IsIntegral X := IsRegular.isIntegral X
  let : IsIntegral X' := IsRegular.isIntegral X'
  let := (s.residueFieldAlgebraMap P).toAlgebra
  have := s.finite_residueField_of_isClosed P hP
  let e := RingEquiv.ofBijective (algebraMap k (X.residueField P))
    (IsSepClosed.algebraMap_bijective k (X.residueField P))
  obtain ⟨p, hp⟩ := (s.exists_fieldPoints_base_eq_iff k P).mpr
    ⟨CommRingCat.ofHom e.symm.toRingHom, by
      ext c
      exact e.symm_apply_apply c⟩
  let p' := s.baseChangeFieldPoint k' p
  let P' : X' := p'.1.base default
  have hP' : (pullback.fst s g) P' = P := by
    change (pullback.fst s g) ((s.baseChangeFieldPoint k' p).1.base default) = P
    rw [← Scheme.Hom.comp_apply, Scheme.Hom.baseChangeFieldPoint, pullback.lift_fst,
      Scheme.Hom.comp_apply]
    have hg : g default = (default : Spec (.of k)) := Subsingleton.elim _ _
    change p.1 (g default) = P
    rw [hg]
    exact hp
  have huniq (Q : X') (hQ : (pullback.fst s g) Q = P) : Q = P' := by
    exact (s.baseChangeFieldPoint_eq_of_fst_eq k' p (hQ.trans hp.symm)).symm
  have hc : P' ∈ closedPoints X' := by
    have h := p'.1.isClosedEmbedding.isClosedMap {default} isClosed_singleton
    change IsClosed {p'.1.base default}
    simpa only [Set.image_singleton] using h
  have hπ := Scheme.rational_point_base_change_stalk k k' X s P hP P' hP'
  have : SmoothOfRelativeDimension 1 s :=
    (smoothOfRelativeDimension_iff_topologicalKrullDim_eq s 1).mpr
      (IsConnectedCurve.krullDim_eq_one (f := s))
  have : SmoothOfRelativeDimension 1 s' :=
    (smoothOfRelativeDimension_iff_topologicalKrullDim_eq s' 1).mpr
      (IsConnectedCurve.krullDim_eq_one (f := s'))
  let : IsDiscreteValuationRing (X.presheaf.stalk P) :=
    IsRegularLocalRing.isDiscreteValuationRing _
      (ringKrullDim_stalk_eq_one_of_smoothOfRelativeDimension_one s hP)
  let : IsDiscreteValuationRing (X'.presheaf.stalk P') :=
    IsRegularLocalRing.isDiscreteValuationRing _
      (ringKrullDim_stalk_eq_one_of_smoothOfRelativeDimension_one s' hc)
  let φ := (pullback.fst s g).stalkMap P'
  have hinj : Function.Injective φ := by
    have : Flat g := Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
    have : Flat (pullback.fst s g) := inferInstance
    algebraize [φ.hom]
    have : Module.Flat (X.presheaf.stalk ((pullback.fst s g) P'))
        (X'.presheaf.stalk P') := Flat.stalkMap (pullback.fst s g) P'
    have : IsLocalHom (algebraMap (X.presheaf.stalk ((pullback.fst s g) P'))
        (X'.presheaf.stalk P')) := inferInstanceAs (IsLocalHom φ.hom)
    have := Module.FaithfullyFlat.of_flat_of_isLocalHom
      (A := X.presheaf.stalk ((pullback.fst s g) P')) (B := X'.presheaf.stalk P')
    exact FaithfulSMul.algebraMap_injective _ _
  let ψ := (algebraMap (X'.presheaf.stalk P') X'.functionField).comp φ.hom
  have hinjψ : Function.Injective ψ := (IsFractionRing.injective _ _).comp hinj
  let ρ : X.functionField →+* X'.functionField := IsFractionRing.lift hinjψ
  have hρ (r : X.presheaf.stalk ((pullback.fst s g) P')) :
      ρ (algebraMap _ X.functionField r) =
        algebraMap _ X'.functionField (φ r) := IsFractionRing.lift_algebraMap hinjψ r
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance,
    P', hP', huniq, inferInstance, inferInstance, ρ, hρ, ?_⟩
  intro f
  let : IsDiscreteValuationRing (X.presheaf.stalk ((pullback.fst s g) P')) :=
    hP'.symm ▸ inferInstance
  have hord := ord_eq_of_stalk_uniformizer X X' ((pullback.fst s g) P') P'
    φ.hom hπ ρ hρ (f : X.functionField)
  have hp : (pullback.fst s g) P' = P := hP'
  rw [hp] at hord
  exact hord

end AlgebraicGeometry
