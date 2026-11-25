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
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected
/-!
# Prime-to-characteristic torsion in the Picard group of a proper curve

Source: blueprint `corollary-torsion-jacobian-field-extension`, the Jacobian calculation.
(blueprint: lem-sc-pic-proper-ntorsion-torsion)
-/

@[expose] public section
universe u
open CategoryTheory
namespace AlgebraicGeometry
private def kernelEquiv {G H : Type*} [CommGroup G] [CommGroup H]
    (e : G ≃* H) (n : ℕ) :
    (powMonoidHom n : G →* G).ker ≃* (powMonoidHom n : H →* H).ker where
  toFun x := ⟨e x, by
    change (e x) ^ n = 1
    rw [← map_pow, show (x : G) ^ n = 1 from x.property, map_one]⟩
  invFun x := ⟨e.symm x, by
    change (e.symm x) ^ n = 1
    rw [← map_pow, show (x : H) ^ n = 1 from x.property, map_one]⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x)
  right_inv x := Subtype.ext (e.apply_symm_apply x)
  map_mul' x y := Subtype.ext (e.map_mul x y)

private def kernelTorsionEquiv (G : Type*) [CommGroup G] (n : ℕ) :
    (powMonoidHom n : G →* G).ker ≃*
      Multiplicative (AddSubgroup.torsionBy (Additive G) (n : ℤ)) where
  toFun x := Multiplicative.ofAdd ⟨Additive.ofMul x, by
    rw [AddSubgroup.torsionBy.nsmul_iff]
    change Additive.ofMul ((x : G) ^ n) = 0
    exact congrArg Additive.ofMul x.property⟩
  invFun x := ⟨Additive.toMul (Multiplicative.toAdd x).val, by
    have h := (AddSubgroup.torsionBy.nsmul_iff).mp (Multiplicative.toAdd x).property
    exact congrArg Additive.toMul h⟩
  left_inv x := rfl
  right_inv x := rfl
  map_mul' x y := rfl

/-- The prime-to-characteristic Picard torsion for a proper smooth curve.
Source: blueprint `corollary-torsion-jacobian-field-extension`, the Jacobian calculation.
(blueprint: lem-sc-pic-proper-ntorsion-torsion)

Proof in words: Finite type gives local Noetherianity, smoothness gives regularity,
and connectedness then gives irreducibility. The dimension-one condition therefore makes
`f` smooth of relative dimension one. Over the separably closed field, connectedness is
geometric connectedness. Smoothness makes each field base change regular and reduced;
geometric connectedness makes it irreducible, so the curve is geometrically integral.
Apply `exists_jacobian`: its degree-zero Picard group is the group of rational points of
an abelian variety J, smooth of relative dimension the arithmetic genus. Its topological
Krull dimension is consequently that genus; Serre duality identifies it with `f.genus`.
The nonzero image of n in k implies n > 0 and that the characteristic does not divide n.
Clause (c) of `abelianVariety_estimate_of_isAlgClosed` computes the additive n-torsion of
J(k). For a Picard class L with L^n = 1, applying the degree homomorphism gives
n * degree(L) = 0 in the integers. Since n is nonzero, degree(L) = 0. Inclusion therefore
identifies the power-map kernel in Pic(C) with that in Pic⁰(C), with inverse the same class
viewed in the degree-zero subgroup. Restrict the Jacobian group equivalence to these kernels,
identify the power-map kernel with the additive n-torsion subgroup, and compose with the
abelian-variety torsion equivalence written multiplicatively. This works also for n = 1
and genus zero, when the resulting finite function group is trivial. -/
theorem Scheme.Hom.pic_proper_ntorsion_torsion
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f] [IsProper f]
    (n : ℕ) (_hn : (n : k) ≠ 0) :
    Nonempty ((powMonoidHom n : C.Pic →* C.Pic).ker ≃*
      Multiplicative (Fin (2 * f.genus) → ZMod n)) := by
  classical
  have hn : n ≠ 0 := by
    intro h
    exact _hn (by simp [h])
  let : C.Over (Spec (.of k)) := ⟨f⟩
  have : ConnectedSpace C := IsConnectedCurve.connectedSpace (f := f)
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsRegular C := IsRegular.of_smooth f
  have : IrreducibleSpace C := IsRegular.irreducibleSpace C
  have : SmoothOfRelativeDimension 1 f :=
    (smoothOfRelativeDimension_iff_topologicalKrullDim_eq f 1).mpr
      (IsConnectedCurve.krullDim_eq_one (f := f))
  have : SmoothOfRelativeDimension 1 (C ↘ Spec (.of k)) := ‹SmoothOfRelativeDimension 1 f›
  have : IsProper (C ↘ Spec (.of k)) := ‹IsProper f›
  have : GeometricallyConnected f :=
    GeometricallyConnected.of_connectedSpace_of_isSepClosed f
  have : GeometricallyIrreducible f :=
    GeometricallyIrreducible.of_smooth_of_geometricallyConnected f
  have : GeometricallyReduced f := Smooth.geometricallyReduced f
  have : GeometricallyIntegral f :=
    GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible f
  have : GeometricallyIntegral (C ↘ Spec (.of k)) := ‹GeometricallyIntegral f›
  obtain ⟨J, hJ, _, hproper, hsmooth, hgeo, _, ⟨eJ⟩⟩ := exists_jacobian (k := k) (X := C)
  let := hJ
  let : CommGroup (MonoidalCategoryStruct.tensorUnit (Over (Spec (.of k))) ⟶ J) :=
    CategoryTheory.Hom.commGroup
  let := hproper
  let : SmoothOfRelativeDimension (Scheme.arithmeticGenus k C) J.hom := hsmooth
  let : Smooth J.hom := hsmooth.smooth
  let := hgeo
  have : ConnectedSpace J.left := GeometricallyConnected.connectedSpace J.hom J.hom.isOpenMap
  let : IsAbelianVariety J := ⟨⟩
  have hdim : IsAbelianVariety.dim J = f.genus := by
    have hg := Scheme.genus_eq_arithmeticGenus (k := k) (X := C)
    have hjg : IsAbelianVariety.dim J = Scheme.arithmeticGenus k C := by
      have h := topologicalKrullDim_eq_of_smoothOfRelativeDimension
        J.hom (Scheme.arithmeticGenus k C)
      rw [IsAbelianVariety.topologicalKrullDim_eq] at h
      exact_mod_cast h
    exact hjg.trans hg.symm
  obtain ⟨t⟩ := (abelianVariety_estimate_of_isAlgClosed (ringChar k) J).1 n
    (Nat.pos_of_ne_zero hn) ((CharP.cast_eq_zero_iff k (ringChar k) n).not.mp _hn)
  let d := Scheme.picDegreeHom k C
  have hd (x : (powMonoidHom n : C.Pic →* C.Pic).ker) : d x = 1 := by
    have h : (d x) ^ n = 1 := by
      rw [← map_pow, show (x : C.Pic) ^ n = 1 from x.property, map_one]
    have hz : (n : ℤ) * Multiplicative.toAdd (d x) = 0 := by
      exact congrArg Multiplicative.toAdd h
    have hz' : Multiplicative.toAdd (d x) = 0 :=
      (mul_eq_zero.mp hz).resolve_left (Int.natCast_ne_zero.mpr hn)
    exact congrArg Multiplicative.ofAdd hz'
  let e0 : (powMonoidHom n : C.Pic →* C.Pic).ker ≃*
      (powMonoidHom n : picardZero k C →* picardZero k C).ker := {
    toFun x := ⟨⟨x, hd x⟩, Subtype.ext x.property⟩
    invFun x := ⟨x.val.val, congrArg Subtype.val x.property⟩
    left_inv x := rfl
    right_inv x := rfl
    map_mul' x y := rfl }
  rw [hdim] at t
  have ht : Nonempty ((powMonoidHom n : C.Pic →* C.Pic).ker ≃*
      Multiplicative (Fin (2 * f.genus) → ZMod n)) :=
    ⟨e0.trans ((kernelEquiv eJ n).trans
      ((kernelTorsionEquiv _ n).trans (AddEquiv.toMultiplicative t)))⟩
  exact ht
end AlgebraicGeometry
