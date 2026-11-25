/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import WeilConjectures.AlgebraicGeometry.Thickening
import WeilConjectures.AlgebraicGeometry.LocallyOfFiniteTypeThickening
import WeilConjectures.AlgebraicGeometry.ThickeningIntegral

/-!
# Finiteness across a cartesian finite order thickening

Source: Stacks Project, More on Morphisms, Lemma 37.3.3 (Tag 09ZW), part (8)
(blueprint: lem-weil-pbc-thickening-finite-cartesian).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Finiteness is equivalent before and after base change along a finite order thickening.
Source: Stacks Project, Tag 09ZW, part (8)
(blueprint: lem-weil-pbc-thickening-finite-cartesian).

Proof:
1. If `f'` is finite, its base change is finite
   (lem-weil-pbc-finite-morphism-permanence).
2. Nilpotence of `i.ker` gives full support, hence surjectivity of the closed immersion
   `i`. Its base change to `X'` is a surjective closed immersion
   (def-sbc-first-order-thickening, lem-weil-pbc-closed-immersion-base-change,
   lem-weil-pbc-surjective-base-change, def-pc-base-change).
   Thus the cartesian square is a morphism of thickenings, as in Stacks Tag 09ZU.
3. If the base change is finite, it is integral and locally of finite type
   (lem-weil-pbc-finite-iff-integral-lft).
4. Integrality lifts along this morphism of thickenings
   (lem-weil-pbc-thickening-integral, Stacks Tag 09ZV (5)).
5. Local finite type lifts along the cartesian finite order thickening
   (lem-weil-pbc-thickening-lft-cartesian, Stacks Tag 09ZW (2)).
6. Hence `f'` is integral and locally of finite type, and therefore finite
   (lem-weil-pbc-finite-iff-integral-lft). Together with step 1 this gives the equivalence. -/
theorem isFinite_iff_of_finiteOrderThickening {S S' X' : Scheme.{u}}
    (i : S ⟶ S') (f' : X' ⟶ S') (hi : IsFiniteOrderThickening i) :
    IsFinite (pullback.snd f' i) ↔ IsFinite f' := by
  obtain ⟨n, hclosed, hnil⟩ := hi
  let : IsClosedImmersion i := hclosed
  have hsupport : i.ker.support = ⊤ := by
    rw [← Scheme.IdealSheafData.support_pow_succ i.ker n, hnil]
    exact Scheme.IdealSheafData.support_bot
  have hsurj : Function.Surjective i := by
    apply Set.range_eq_univ.mp
    rw [← i.isClosedEmbedding.isClosed_range.closure_eq, ← i.support_ker, hsupport]
    rfl
  let : Surjective i := ⟨hsurj⟩
  constructor
  · intro hf
    let : IsFinite (pullback.snd f' i) := hf
    have hint : IsIntegralHom f' :=
      (isIntegralHom_iff_of_thickenings i (pullback.fst f' i) f'
        (pullback.snd f' i) ⟨hclosed, inferInstance⟩
        ⟨inferInstance, inferInstance⟩ pullback.condition).mp inferInstance
    have hlft : LocallyOfFiniteType (pullback.fst i f') := by
      rw [← pullbackSymmetry_hom_comp_snd i f']
      infer_instance
    exact (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType f').mpr
      ⟨hint, (locallyOfFiniteType_iff_of_finiteOrderThickening i f' ⟨n, hclosed, hnil⟩).mp hlft⟩
  · intro hf
    let : IsFinite f' := hf
    infer_instance

end AlgebraicGeometry
