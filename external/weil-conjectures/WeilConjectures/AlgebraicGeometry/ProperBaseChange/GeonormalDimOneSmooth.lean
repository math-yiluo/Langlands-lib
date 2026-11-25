/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.Topology.KrullDimension
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.FieldBaseChangeDimension
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.AlgebraicGeometry.Geometric.GeometricRegularitySmoothFieldCriterion

/-!
# Geometrically normal schemes of dimension at most one

## References

* Stacks Project, Tags 0BX2, 038X, 00P3, 033M, and the proof of Tag 0GK5
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A geometrically normal finite type scheme of dimension at most one over a field is
smooth and geometrically reduced; any connected nonempty field base change is irreducible.
-/
theorem smooth_and_geometricallyReduced_of_geonormal_dim_le_one
    (k : Type u) [Field k] (Z : Scheme.{u}) [Z.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (Z ↘ Spec (CommRingCat.of k))]
    (hdim : topologicalKrullDim Z ≤ 1)
    (hnormal : ∀ (L : Type u) [Field L] [Algebra k L],
      ∀ x : ↥(pullback (Z ↘ Spec (CommRingCat.of k))
        (Spec.map (CommRingCat.ofHom (algebraMap k L)))),
      IsDomain ((pullback (Z ↘ Spec (CommRingCat.of k))
        (Spec.map (CommRingCat.ofHom (algebraMap k L)))).presheaf.stalk x) ∧
      IsIntegrallyClosed ((pullback (Z ↘ Spec (CommRingCat.of k))
        (Spec.map (CommRingCat.ofHom (algebraMap k L)))).presheaf.stalk x)) :
    Smooth (Z ↘ Spec (CommRingCat.of k)) ∧
      GeometricallyReduced (Z ↘ Spec (CommRingCat.of k)) ∧
      ∀ (L : Type u) [Field L] [Algebra k L],
        ConnectedSpace ↥(pullback (Z ↘ Spec (CommRingCat.of k))
          (Spec.map (CommRingCat.ofHom (algebraMap k L)))) →
        IrreducibleSpace ↥(pullback (Z ↘ Spec (CommRingCat.of k))
          (Spec.map (CommRingCat.ofHom (algebraMap k L)))) := by
  have hregular (L : Type u) [Field L] [Algebra k L] :
      IsRegular (pullback (Z ↘ Spec (CommRingCat.of k))
        (Spec.map (CommRingCat.ofHom (algebraMap k L)))) := by
    have := LocallyOfFiniteType.isLocallyNoetherian
      (pullback.snd (Z ↘ Spec (CommRingCat.of k))
        (Spec.map (CommRingCat.ofHom (algebraMap k L))))
    exact IsRegular.of_isIntegrallyClosed_stalk (hnormal L)
      ((topologicalKrullDim_pullback_eq_of_field (Z ↘ Spec (CommRingCat.of k))
        (Spec.map (CommRingCat.ofHom (algebraMap k L)))).le.trans hdim)
  have hsmooth : Smooth (Z ↘ Spec (CommRingCat.of k)) := by
    apply (smooth_iff_regularLocalRing_finitelyGenerated_field_baseChange k _).mpr
    intro L _ _ _ x
    have := hregular L
    exact IsRegular.isRegularLocalRing_stalk x
  have hreduced : GeometricallyReduced (Z ↘ Spec (CommRingCat.of k)) := by
    refine ⟨geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms.mpr ?_⟩
    intro L _ _
    refine @isReduced_of_isReduced_stalk _ (fun x ↦ ?_)
    have := (hnormal L x).1
    infer_instance
  refine ⟨hsmooth, hreduced, ?_⟩
  intro L _ _ hconnected
  have := hconnected
  have := hregular L
  have := LocallyOfFiniteType.isLocallyNoetherian
    (pullback.snd (Z ↘ Spec (CommRingCat.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k L))))
  have := IsRegular.isIntegral (pullback (Z ↘ Spec (CommRingCat.of k))
    (Spec.map (CommRingCat.ofHom (algebraMap k L))))
  infer_instance

end AlgebraicGeometry
