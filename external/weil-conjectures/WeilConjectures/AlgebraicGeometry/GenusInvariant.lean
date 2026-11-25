/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Jacobian
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
import WeilConjectures.AlgebraicGeometry.JacobianBaseChangeCompatible
import WeilConjectures.AlgebraicGeometry.BaseChangeCurve
import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
import WeilConjectures.AlgebraicGeometry.Curve
import WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch
import WeilConjectures.AlgebraicGeometry.Picard.Jacobian
import WeilConjectures.AlgebraicGeometry.Regular

/-!
# Genus and Jacobians under algebraically closed extension

Source: blueprint, `sec-curve-estimates/sbc-thm-algebraically-closed-invariance`, order 1030
(blueprint: proposition-cohomology-smooth-affine-curve--4).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme

namespace AlgebraicGeometry

private theorem exists_jacobian_of_connected
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f] [IsProper f]
    [GeometricallyIntegral f] :
    ∃ (J : Over (Spec (.of k))) (_ : GrpObj J), IsJacobian f J := by
  let : C.Over (Spec (.of k)) := ⟨f⟩
  have : IsIntegral C := GeometricallyIntegral.isIntegral_of_subsingleton f
  have : SmoothOfRelativeDimension 1 f :=
    (smoothOfRelativeDimension_iff_topologicalKrullDim_eq f 1).mpr
      (IsConnectedCurve.krullDim_eq_one (f := f))
  have : SmoothOfRelativeDimension 1 (C ↘ Spec (.of k)) := ‹SmoothOfRelativeDimension 1 f›
  have : IsProper (C ↘ Spec (.of k)) := ‹IsProper f›
  have : GeometricallyIntegral (C ↘ Spec (.of k)) := ‹GeometricallyIntegral f›
  obtain ⟨J, hJ, e, hP, hS, hG, he, -⟩ := exists_jacobian (k := k) (X := C)
  let := hJ
  let := hP
  let := hS
  let := hG
  have : IsIntegral J.left := GeometricallyIntegral.isIntegral_of_subsingleton J.hom
  change (picardFunctorDegree f 0).obj.RepresentableBy J at e
  change IsPicardZeroMul f e at he
  have : IsAbelianVariety J :=
    { toIsProper := hP
      toSmooth := SmoothOfRelativeDimension.smooth (arithmeticGenus k C) J.hom
      toConnectedSpace := GeometricallyConnected.connectedSpace_of_subsingleton J.hom }
  refine ⟨J, inferInstance, ?_⟩
  refine { dim_eq := ?_, represents := ?_ }
  · have hd := (smoothOfRelativeDimension_iff_topologicalKrullDim_eq J.hom
      (arithmeticGenus k C)).mp hS
    rw [IsAbelianVariety.topologicalKrullDim_eq] at hd
    have hd' : IsAbelianVariety.dim J = arithmeticGenus k C := by exact_mod_cast hd
    exact hd'.trans (genus_eq_arithmeticGenus (k := k) (X := C)).symm
  · refine ⟨((Functor.RepresentableBy.equivUliftYonedaIso _ J) e).symm, ?_⟩
    rw [Iso.symm_symm_eq, Equiv.symm_apply_apply]
    exact he

/-- Source: blueprint, `sec-curve-estimates/sbc-thm-algebraically-closed-invariance`, order 1030
(blueprint: proposition-cohomology-smooth-affine-curve--4).

The genus is unchanged, and any two Jacobian identifications are carried to one another
by an isomorphism over the extended field. Compatibility is tested on degree-zero line
bundles over every test scheme: the canonical iterated-pullback isomorphism transports the
line bundle, and the classifying morphisms agree after projection to the original Jacobian.
The maps from line bundles to the Picard sheaf are locally surjective, so this tests equality
of the representing identifications, including on sheafified sections.

Proof: a connected scheme over a separably closed field is geometrically connected.
Smoothness then gives geometric irreducibility and geometric reducedness, hence geometric
integrality. `baseChange_curve` gives the connected-curve structure after extension;
geometric integrality and smoothness are stable under base change. On an integral smooth
curve, dimension one gives smoothness of relative dimension one. The comparison of genus
with arithmetic genus and `arithmeticGenus_pullback` prove the genus equality.
For each curve, `exists_jacobian` supplies a representing commutative group scheme,
proper, geometrically integral, and smooth of relative dimension the arithmetic genus.
These properties give `IsAbelianVariety`; its Krull dimension is that relative dimension,
so the genus comparison and the given representation give `IsJacobian`.
Finally `jacobian_compatibility` gives the compatibility square for the chosen pair of
representing identifications. -/
theorem genus_jacobian_invariant
    {k K : Type u} [Field k] [Field K] [IsAlgClosed k] [IsAlgClosed K] [Algebra k K]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k))
    [IsConnectedCurve f] [Smooth f] [IsProper f] :
    let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
    let fK := pullback.snd f b
    ∃ (_ : GeometricallyIntegral f) (_ : IsConnectedCurve fK)
      (_ : GeometricallyIntegral fK),
      fK.genus = f.genus ∧
      (∃ (J : Over (Spec (.of k))) (_ : GrpObj J), IsJacobian f J) ∧
      (∃ (J : Over (Spec (.of K))) (_ : GrpObj J), IsJacobian fK J) ∧
      ∀ (J : Over (Spec (.of k))) [GrpObj J] [IsJacobian f J]
        (e : (picardFunctorDegree f 0).obj.RepresentableBy J), IsPicardZeroMul f e →
      ∀ (JK : Over (Spec (.of K))) [GrpObj JK] [IsJacobian fK JK]
        (eK : (picardFunctorDegree fK 0).obj.RepresentableBy JK), IsPicardZeroMul fK eK →
      ∃ i : JK ≅ Over.mk (pullback.snd J.hom b),
      ∀ (T : Over (Spec (.of K))) (L : (pullback f (T.hom ≫ b)).Pic)
        (hL : L ∈ (picardSubfunctorDegree f 0).obj (.op ((Over.map b).obj T))),
      ∃ hLK : Pic.map (pullbackLeftPullbackSndIso f b T.hom).hom L ∈
          (picardSubfunctorDegree fK 0).obj (.op T),
        (eK.homEquiv.symm ((toSheafify (Scheme.fppfTopology.over (Spec (.of K)))
          (picardSubfunctorDegree fK 0).toFunctor).app (.op T)
            ⟨Pic.map (pullbackLeftPullbackSndIso f b T.hom).hom L, hLK⟩)).left ≫
            i.hom.left ≫ pullback.fst J.hom b =
        (e.homEquiv.symm ((toSheafify (Scheme.fppfTopology.over (Spec (.of k)))
          (picardSubfunctorDegree f 0).toFunctor).app (.op ((Over.map b).obj T))
            ⟨L, hL⟩)).left := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let fK := pullback.snd f b
  have : ConnectedSpace C := IsConnectedCurve.connectedSpace (f := f)
  have : GeometricallyConnected f :=
    GeometricallyConnected.of_connectedSpace_of_isSepClosed f
  have : GeometricallyIrreducible f :=
    GeometricallyIrreducible.of_smooth_of_geometricallyConnected f
  have hG : GeometricallyIntegral f :=
    GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible f
  have hC : IsConnectedCurve fK := (baseChange_curve (k' := K) f).2.2.2.2.2 inferInstance
  let := hC
  have hGK : GeometricallyIntegral fK := inferInstance
  let _ : GeometricallyIntegral f := hG
  let _ : GeometricallyIntegral fK := hGK
  refine ⟨hG, hC, hGK, ?_, exists_jacobian_of_connected f,
    exists_jacobian_of_connected fK, ?_⟩
  · let : C.Over (Spec (.of k)) := ⟨f⟩
    have : IsIntegral C := GeometricallyIntegral.isIntegral_of_subsingleton f
    have : SmoothOfRelativeDimension 1 f :=
      (smoothOfRelativeDimension_iff_topologicalKrullDim_eq f 1).mpr
        (IsConnectedCurve.krullDim_eq_one (f := f))
    have : SmoothOfRelativeDimension 1 fK :=
      (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
        (IsPullback.of_hasPullback f b) inferInstance
    let : (pullback f b).Over (Spec (.of K)) := ⟨fK⟩
    have : SmoothOfRelativeDimension 1 (C ↘ Spec (.of k)) :=
      ‹SmoothOfRelativeDimension 1 f›
    have : SmoothOfRelativeDimension 1 (pullback f b ↘ Spec (.of K)) :=
      ‹SmoothOfRelativeDimension 1 fK›
    have : IsProper (C ↘ Spec (.of k)) := ‹IsProper f›
    have : IsProper (pullback f b ↘ Spec (.of K)) := inferInstanceAs (IsProper fK)
    change (pullback f b ↘ Spec (.of K)).genus = (C ↘ Spec (.of k)).genus
    rw [genus_eq_arithmeticGenus, genus_eq_arithmeticGenus]
    exact arithmeticGenus_pullback K
  · intro J _ _ e he JK _ _ eK heK
    exact jacobian_compatibility f J e he JK eK heK

end AlgebraicGeometry
