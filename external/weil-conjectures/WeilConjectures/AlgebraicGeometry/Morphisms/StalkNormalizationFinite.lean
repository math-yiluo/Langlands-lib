/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Functoriality
public import Mathlib.AlgebraicGeometry.Normalization
import WeilConjectures.AlgebraicGeometry.Morphisms.SmoothConnectedGenericGeometryCore
import WeilConjectures.AlgebraicGeometry.Morphisms.FiniteEtaleOpenIntegralClosure

/-!
# Finiteness of the normalization over a stalk

## References

* Stacks Project, Tag 0EYJ, proof of the local claim
* Stacks Project, local claim
* Tags 0EYG, 0EYH (tame normalization) and 0EY6 (depth-two extension)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
/-- Finiteness of the concrete normalization at a generic boundary point. -/
theorem stalk_normalization_finite {S C : Scheme.{u}} [IsNoetherian S]
    [QuasiSeparatedSpace S] [IsIntegral S]
    (hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x))
    (c : C ⟶ S) [QuasiCompact c] [QuasiSeparated c] [Smooth c] [GeometricallyConnected c]
    {Cη : Scheme.{u}} (q : Cη ⟶ Spec S.functionField) (j : Cη ⟶ C)
    (hCη : IsPullback q j (S.fromSpecStalk (genericPoint S)) c)
    (U : S.Opens)
    (PA : (c ⁻¹ᵁ U).toScheme.FiniteEtale)
    (s : S) :
    letI : IsFinite PA.obj.hom := PA.property
    letI : QuasiCompact (c ⁻¹ᵁ U).ι :=
      MorphismProperty.of_isPullback (isPullback_morphismRestrict c U)
        (inferInstance : QuasiCompact U.ι)
    IsFinite (pullback.snd (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization
      (pullback.fst c (S.fromSpecStalk s))) := by
  classical
  let : IsFinite PA.obj.hom := PA.property
  let : QuasiCompact (c ⁻¹ᵁ U).ι :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict c U)
      (inferInstance : QuasiCompact U.ι)
  cases isEmpty_or_nonempty C with
  | inl h =>
    let : IsEmpty ↥(pullback c (S.fromSpecStalk s)) :=
      (pullback.fst c (S.fromSpecStalk s)).base.hom.1.isEmpty
    infer_instance
  | inr h =>
    obtain ⟨hC, hη, hnC, hnη⟩ :=
      smooth_connected_generic_geometry_core hS c q j hCη
    let := hC
    let : IsNoetherian C := isNoetherian_of_locallyOfFiniteType c
    let f := PA.obj.hom ≫ (c ⁻¹ᵁ U).ι
    have hf : IsFinite f.fromNormalization := by
      refine { finite_app := ?_ }
      intro V hV
      let : Algebra Γ(C, V) Γ(PA.obj.left, f ⁻¹ᵁ V) := (f.app V).hom.toAlgebra
      have hfin : Module.Finite Γ(C, V)
          (integralClosure Γ(C, V) Γ(PA.obj.left, f ⁻¹ᵁ V)) :=
        finiteEtale_open_integralClosure_finite hnC (c ⁻¹ᵁ U) PA V hV
      rw [Scheme.Hom.fromNormalization_app f hV]
      exact (RingHom.finite_respectsIso.cancel_right_isIso
        (CommRingCat.ofHom (algebraMap _ _))
        (Scheme.Hom.normalizationObjIso f hV).inv).2 (RingHom.finite_algebraMap.2 hfin)
    exact inferInstanceAs (IsFinite (pullback.snd f.fromNormalization
      (pullback.fst c (S.fromSpecStalk s))))

end AlgebraicGeometry.Scheme
