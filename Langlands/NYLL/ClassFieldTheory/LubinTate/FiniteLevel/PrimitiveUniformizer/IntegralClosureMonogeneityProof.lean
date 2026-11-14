/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 572, 14 November 2026: adapt source M346.002 to the
published proposition target, import the exact M346.001 proof, and preserve
the full source telescope with four independent universes.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveUniformizer.MonogeneityStatements
import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveUniformizer.IntegralElementsProof

/-! # Integral-closure generation by an Eisenstein power-basis lift -/

universe u v w x

namespace Langlands.NYLL.PortInternal.M346

theorem d002
    {R : Type u} {K' : Type v} {L : Type w} {A : Type x}
    [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K'] [Field L] [CommRing A]
    [Algebra R K'] [Algebra K' L] [Algebra R L]
    [Algebra R A] [Algebra A L]
    [IsScalarTower R K' L] [IsScalarTower R A L]
    [IsFractionRing R K'] [FiniteDimensional K' L]
    [Algebra.IsSeparable K' L] [IsIntegralClosure A R L]
    (B : PowerBasis K' L) (pi : R) (hpi : Irreducible pi)
    (a : A) (ha : algebraMap A L a = B.gen)
    (hmap_injective : Function.Injective (algebraMap A L))
    (hBint : IsIntegral R B.gen)
    (hei : (minpoly R B.gen).IsEisensteinAt
      (Ideal.span ({pi} : Set R))) :
    Langlands.NYLL.PortInternal.M346.d002Statement
      (R := R) (K' := K') (L := L) (A := A)
      B pi hpi a ha hmap_injective hBint hei := by
  change Algebra.adjoin R ({a} : Set A) = ⊤
  apply top_unique
  intro z _hz
  let j : A →ₐ[R] L := IsScalarTower.toAlgHom R A L
  have hzint : IsIntegral R (j z) :=
    IsIntegralClosure.isIntegral_iff.mpr ⟨z, rfl⟩
  have hzfield :
      j z ∈ Algebra.adjoin R ({B.gen} : Set L) :=
    Langlands.NYLL.PortInternal.M346.d001 B pi hpi hBint hei hzint
  have hmap :
      (Algebra.adjoin R ({a} : Set A)).map j =
        Algebra.adjoin R ({B.gen} : Set L) := by
    rw [AlgHom.map_adjoin_singleton]
    change Algebra.adjoin R ({algebraMap A L a} : Set L) = _
    rw [ha]
  rw [← hmap] at hzfield
  rcases hzfield with ⟨y, hy, hyz⟩
  have hya : y = z := hmap_injective hyz
  exact hya ▸ hy

end Langlands.NYLL.PortInternal.M346
