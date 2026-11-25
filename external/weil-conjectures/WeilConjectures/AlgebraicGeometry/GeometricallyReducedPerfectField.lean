/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # Reduced schemes of finite type over a perfect field

A reduced scheme locally of finite type over a perfect field `k` stays reduced after every
field extension; its structure morphism is flat, locally of finite presentation and has
geometrically reduced fibres.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Blueprint `lemma-kunneth-finite-direct-image--1`: let `X` be a reduced scheme locally of
finite type over a perfect field `k`. Then for every field extension `L / k` the base change
`X_L` is reduced, and `X ⟶ Spec k` is flat, locally of finite presentation and geometrically
reduced.

Proof: geometric reducedness over a perfect field is `GeometricallyReduced.of_perfectField`,
which gives reducedness of `X_L`; every morphism to the spectrum of a field is flat
(`Flat.of_field`); and `Spec k` is Noetherian, so locally of finite type is the same as locally
of finite presentation. -/
theorem isReduced_pullback_and_flat_and_locallyOfFinitePresentation_of_perfectField
    {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [IsReduced X] [LocallyOfFiniteType f] :
    (∀ (L : Type u) [Field L] [Algebra k L],
      IsReduced (Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap k L))))) ∧
      Flat f ∧ LocallyOfFinitePresentation f ∧ GeometricallyReduced f := by
  have hred := GeometricallyReduced.of_perfectField f
  refine ⟨fun L _ _ ↦ ?_, Flat.of_field k f,
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.2 inferInstance, hred⟩
  exact (geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms.1
    hred.geometrically_isReduced) L

end AlgebraicGeometry
