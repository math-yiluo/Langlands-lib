/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.AlgebraicGeometry.AffineDerivedPushforwardConservative
import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorQCoh
import WeilConjectures.AlgebraicGeometry.FiniteAffineDerivedEquivalence
import WeilConjectures.AlgebraicGeometry.DerivedAdjoint
import WeilConjectures.AlgebraicGeometry.DerivedPullbackPerfect

/-! # Affine pullback of a perfect generator

Source: Stacks Project, Derived Categories of Schemes, Remark 36.16.4, Tag 0BQT
(blueprint: lem-pc-perfect-generator-pullback).

The weak generator condition is expressed by the shifted-Hom vanishing criterion,
just as in `AlgebraicGeometry.exists_perfect_generator`. All test objects belong to
`D_QCoh`, while the Hom groups and shifts are computed in the ambient derived category.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The derived pullback of a perfect generator along an affine morphism of qcqs schemes
is a perfect generator of the quasi-coherent derived category of the source.
Source: Stacks Project, Tag 0BQT (blueprint: lem-pc-perfect-generator-pullback).

Proof:
1. By `lem-pc-derived-pullback-tensor-qcoh`, derived pullback preserves quasi-coherent
cohomology. The adjunction `lem-pc-ringed-spaces-derived-adjoint` applies to the chosen
scheme functors. The comparison in `lem-sc-finite-affine-derived-equivalence` transports
quasi-coherence to the derived pushforward of E. The shift compatibility supplied by
`lemma-coherent-base-change-invertible-sheaves--2` and the adjunction identify Hom from the shifted
pullback of M to E with Hom from the shifted M to the derived pushforward of E.
2. If all the former Hom groups are subsingletons, so are the latter. The hypothesis
`hgen` gives that the derived pushforward of E is zero.
3. By `lem-sc-affine-derived-pushforward-conservative`, affine derived pushforward reflects
isomorphisms between quasi-coherent objects. The zero endomorphism of E becomes an
isomorphism because its image has zero source and target. Thus it is itself invertible,
forcing the identity of E to be zero. Conversely, Hom into a zero object is subsingleton.
This is precisely the generator criterion on the source.
4. The pullback is perfect by `lem-pc-derived-pullback-perfect`. -/
theorem perfect_generator_pullback {X X' : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace X'] [QuasiSeparatedSpace X']
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X'.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    [∀ U : X'.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X'.toRingedSpace).over U))]
    (g : X' ⟶ X) [IsAffineHom g] (M : schemeDerivedQCohCategory X)
    (hperfect : Scheme.IsPerfect X M.obj)
    (hgen : ∀ E : schemeDerivedQCohCategory X,
      IsZero E.obj ↔ ∀ n : ℤ, Subsingleton (M.obj⟦n⟧ ⟶ E.obj)) :
    Scheme.IsPerfect X' ((derivedPullback g).obj M.obj) ∧
    schemeDerivedQCohProperty X' ((derivedPullback g).obj M.obj) ∧
      ∀ E : schemeDerivedQCohCategory X',
        IsZero E.obj ↔ ∀ n : ℤ,
          Subsingleton (((derivedPullback g).obj M.obj)⟦n⟧ ⟶ E.obj) := by
  classical
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, ⟨cs, ht⟩, _⟩ :=
    (derivedPullback_spec g)
  let : (derivedPullback g).CommShift ℤ := cs
  obtain ⟨adj⟩ := nonempty_derivedPullbackAdjunction g
  refine ⟨derivedPullback_preserve_perfect g M.obj hperfect, ?_⟩
  constructor
  · exact (derivedPullback_tensor_preserve_QCoh g).1 M.obj M.property
  · intro E
    constructor
    · intro hE n
      exact ⟨fun a b ↦ hE.eq_of_tgt a b⟩
    · intro hE
      let : HasDerivedCategory
          (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace g))) :=
        HasDerivedCategory.standard _
      obtain ⟨Φ, _, S, _, ⟨eΦ⟩⟩ := finite_affine_derived_equivalence g
      have hRq : schemeDerivedQCohProperty X ((schemeDerivedDirectImage g).obj E.obj) := by
        intro n
        exact (SheafOfModules.isQuasicoherent (moduleRings X.toRingedSpace)).prop_of_iso
          ((DerivedCategory.homologyFunctor _ n).mapIso (eΦ.app E))
          ((S.obj (Φ.functor.obj E)).property n)
      have hR : IsZero ((schemeDerivedDirectImage g).obj E.obj) := by
        apply (hgen ⟨_, hRq⟩).mpr
        intro n
        let e := ((derivedPullback g).commShiftIso n).app M.obj
        let h := (Iso.homCongr e.symm (Iso.refl E.obj)).trans
          (adj.homEquiv (M.obj⟦n⟧) E.obj)
        let : Subsingleton ((derivedPullback g ⋙
            shiftFunctor (schemeDerivedCategory X') n).obj M.obj ⟶ E.obj) := hE n
        exact h.symm.subsingleton
      have : IsIso ((schemeDerivedDirectImage g).map (0 : E.obj ⟶ E.obj)) :=
        hR.isIso hR _
      have : IsIso (0 : E.obj ⟶ E.obj) :=
        schemeDerivedDirectImage_isIso_of_affine g E.property E.property (0 : E.obj ⟶ E.obj)
      apply (IsZero.iff_id_eq_zero E.obj).mpr
      have h := IsIso.hom_inv_id (0 : E.obj ⟶ E.obj)
      rw [zero_comp] at h
      exact h.symm

end AlgebraicGeometry
