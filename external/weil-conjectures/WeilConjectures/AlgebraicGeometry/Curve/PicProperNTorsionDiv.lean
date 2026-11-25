/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.Picard.Group
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Final
import WeilConjectures.AlgebraicGeometry.Picard.Jacobian
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected
@[expose] public section
universe u
open CategoryTheory
namespace AlgebraicGeometry
/-- Degree-zero Picard divisibility for a proper smooth curve.
Source: blueprint `corollary-torsion-jacobian-field-extension`, the Jacobian calculation.
(blueprint: lem-sc-pic-proper-ntorsion-div)

Proof in words: Smoothness gives local Noetherianity and regularity, so connectedness
makes C integral. Over the algebraically closed (hence separably closed) field,
connectedness gives geometric connectedness; smoothness then gives geometric
irreducibility and geometric reducedness, hence geometric integrality. The dimension-one
hypothesis and smoothness give smooth relative dimension one. Jacobian representability
therefore applies to the proper curve and identifies its degree-zero Picard subgroup
with the rational points of a proper, smooth, geometrically integral commutative group
scheme J. These properties make J an abelian variety. The subgroup used by the Jacobian
is the kernel of the degree homomorphism, whose underlying set is f.picZero.
The hypothesis `(n : k) ≠ 0` excludes n = 0, hence n is positive. Clause (d) of the
abelian-variety estimate says the nth-power map on the Jacobian's rational points is
surjective. For a degree-zero class L, take an nth root of its image in the Jacobian and
transport that root back along the group equivalence. It is a degree-zero class M;
the homomorphism property and injectivity of the equivalence give M ^ n = L.
For n = 1 one can take M = L. -/
theorem Scheme.Hom.pic_proper_ntorsion_div
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f] [IsProper f]
    (n : ℕ) (_hn : (n : k) ≠ 0) :
    ∀ L : C.Pic, L ∈ f.picZero → ∃ M : C.Pic, M ∈ f.picZero ∧ M ^ n = L := by
  let : C.Over (Spec (.of k)) := ⟨f⟩
  have : ConnectedSpace C := IsConnectedCurve.connectedSpace (f := f)
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsRegular C := IsRegular.of_smooth f
  have : IsIntegral C := IsRegular.isIntegral C
  have : GeometricallyConnected f :=
    GeometricallyConnected.of_connectedSpace_of_isSepClosed f
  have : GeometricallyIrreducible f :=
    GeometricallyIrreducible.of_smooth_of_geometricallyConnected f
  have : GeometricallyIntegral f :=
    GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible f
  have : SmoothOfRelativeDimension 1 f :=
    (smoothOfRelativeDimension_iff_topologicalKrullDim_eq f 1).mpr
      (IsConnectedCurve.krullDim_eq_one (f := f))
  have : SmoothOfRelativeDimension 1 (C ↘ Spec (.of k)) := ‹SmoothOfRelativeDimension 1 f›
  have : IsProper (C ↘ Spec (.of k)) := ‹IsProper f›
  have : GeometricallyIntegral (C ↘ Spec (.of k)) := ‹GeometricallyIntegral f›
  obtain ⟨J, hJ, _, hP, hS, hG, _, ⟨e⟩⟩ := exists_jacobian (k := k) (X := C)
  let := hJ
  let := CategoryTheory.Hom.group (X := MonoidalCategory.tensorUnit (Over (Spec (.of k)))) (G := J)
  let := hP
  let := hS
  let := hG
  have : IsAbelianVariety J :=
    { toIsProper := hP
      toSmooth := SmoothOfRelativeDimension.smooth (Scheme.arithmeticGenus k C) J.hom
      toConnectedSpace := GeometricallyConnected.connectedSpace_of_subsingleton J.hom }
  have hn : 0 < n := Nat.pos_of_ne_zero fun h ↦ _hn (by simp [h])
  intro L hL
  have hL' : L ∈ picardZero k C := by
    change L ∈ (picardZero k C : Set C.Pic)
    rw [Scheme.coe_ker_picDegreeHom]
    exact hL
  obtain ⟨a, ha⟩ :=
    (abelianVariety_estimate_of_isAlgClosed (ringChar k) J).2.2.1 n hn (e ⟨L, hL'⟩)
  refine ⟨(e.symm a).1, ?_, ?_⟩
  · have hM := (e.symm a).2
    change (e.symm a).1 ∈ (picardZero k C : Set C.Pic) at hM
    rwa [Scheme.coe_ker_picDegreeHom] at hM
  · have hroot : (e.symm a) ^ n = ⟨L, hL'⟩ := by
      apply e.injective
      rw [map_pow, e.apply_symm_apply]
      exact ha
    exact congrArg Subtype.val hroot
end AlgebraicGeometry
