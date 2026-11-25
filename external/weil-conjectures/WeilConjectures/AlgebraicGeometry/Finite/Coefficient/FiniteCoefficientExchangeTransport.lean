/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Ringed.RingedEtaleOriginWitness
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteLevelRingedProEtaleBaseChange

/-!
# Transport of finite coefficient exchange

This is the coefficient transport step for the finite-level proper base-change theorem.
Source: Stacks Tags 09C8 and 09C9 (blueprint:
proposition-proper-direct-image-constructible-complexes--5). (blueprint:
lem-weil-pbc-finite-origin-exchange-transport).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- After restriction from the continuous-function coefficient presentation to the constant
coefficient presentation, the ambient finite exchange is invertible. The proof transports the
constant-coefficient proper-base-change theorem through the canonical coefficient equivalence,
using the mate compatibility of exact restriction of scalars. This statement is strictly an
intermediate transport result: it retains arbitrary coefficient identifications and only asserts
invertibility after applying `finiteOriginToConstant`.
Source: Stacks Tags 09C8 and 09C9 (blueprint:
proposition-proper-direct-image-constructible-complexes--5). (blueprint:
lem-weil-pbc-finite-origin-exchange-transport). Proof: use the constants-to-functions isomorphism at
each corner as the scalar-change square. The coherence hypothesis makes the scalar-change comparison
commute on both paths of the chosen Cartesian square. The derived pullback and direct-image
comparison isomorphisms from `proEtaleRingSheafChangeAdjunction` identify the restriction of the
function-coefficient mate with the constant-coefficient mate. Apply
`finiteConstantRingedExchange_isIso` to the finite-coefficient object obtained by realizing the
retained étale complex. Finally conjugate by the witness isomorphism `_W.iso`; isomorphism
reflection for exact restriction gives the displayed restricted map.
-/
theorem finiteOriginToConstant_map_ambientExchange_isIso
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (sq : ChosenCartesianSquare g' f' f g) [IsProper f]
    (c_f : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
      (finiteOriginFunctionRing Y Λ) ≅ finiteOriginFunctionRing X Λ)
    (c_g : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
      (finiteOriginFunctionRing Y Λ) ≅ finiteOriginFunctionRing Y' Λ)
    (c_g' : (proEtaleSheafInverseImage g' CommRingCat.{u + 1}).obj
      (finiteOriginFunctionRing X Λ) ≅ finiteOriginFunctionRing X' Λ)
    (c_f' : (proEtaleSheafInverseImage f' CommRingCat.{u + 1}).obj
      (finiteOriginFunctionRing Y' Λ) ≅ finiteOriginFunctionRing X' Λ)
    (hc : HEq
      (proEtaleRingCompositeCoefficients g' f (finiteOriginFunctionRing Y Λ)
        (finiteOriginFunctionRing X Λ) (finiteOriginFunctionRing X' Λ) c_f c_g')
      (proEtaleRingCompositeCoefficients f' g (finiteOriginFunctionRing Y Λ)
        (finiteOriginFunctionRing Y' Λ) (finiteOriginFunctionRing X' Λ) c_g c_f'))
    (K : DerivedCategory (proEtaleRingModules X (finiteOriginFunctionRing X Λ)))
    (_W : FiniteEtaleOriginWitness X Λ K) :
    IsIso ((finiteOriginToConstant Y' Λ).map
      ((proEtaleAmbientRingedExchange sq (finiteOriginFunctionRing X Λ)
        (finiteOriginFunctionRing Y Λ) (finiteOriginFunctionRing X' Λ)
        (finiteOriginFunctionRing Y' Λ) c_f c_g c_g' c_f' hc).app K)) := by
  sorry

end AlgebraicGeometry.Scheme
