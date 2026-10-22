import Langlands.Automorphic.Smooth
import Langlands.Representation.FiniteVectors

/-!
# Subgroup-finite adelic functions

Finiteness under an infinite-factor subgroup is preserved by that subgroup and
by the commuting finite adelic factor. No maximal compactness is assumed.
-/

noncomputable section

universe u

namespace Langlands.Global.AdelicGL

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

theorem ofFinite_commute_ofInfinite (b : FiniteAdelicGL K n)
    (a : InfiniteAdelicGL K n) :
    Commute (ofFinite K n b) (ofInfinite K n a) := by
  change ofFinite K n b * ofInfinite K n a = ofInfinite K n a * ofFinite K n b
  simp only [ofFinite_eq_pair, ofInfinite_eq_pair, pair_mul, one_mul, mul_one]

end Langlands.Global.AdelicGL

namespace Langlands.Automorphic

open Langlands.Global NumberField ContinuousRationalFunctions

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)
  (U : Subgroup (InfiniteAdelicGL K n))

/-- Restrict actual right translation to the specified infinite-factor subgroup. -/
def infiniteSubgroupRightAction :
    Representation ℂ U (ContinuousRationalFunctions K n) :=
  (continuousRightAction K n).comp
    ((AdelicGL.ofInfinite K n).toMonoidHom.comp U.subtype)

theorem infiniteOrbitSpan_eq (f : ContinuousRationalFunctions K n) :
    infiniteOrbitSpan K n U f =
      FiniteVectors.orbitSpan (infiniteSubgroupRightAction K n U) f := rfl

theorem isInfiniteFinite_iff (f : ContinuousRationalFunctions K n) :
    IsInfiniteFinite K n U f ↔
      FiniteVectors.IsFiniteVector (infiniteSubgroupRightAction K n U) f := Iff.rfl

/-- The existing infinite-finiteness condition forms an actual subrepresentation. -/
def infiniteFiniteSubrepresentation :
    Subrepresentation (infiniteSubgroupRightAction K n U) :=
  FiniteVectors.subrepresentation (k := ℂ) (G := U)
    (V := ContinuousRationalFunctions K n) (infiniteSubgroupRightAction K n U)

@[simp]
theorem mem_infiniteFiniteSubrepresentation (f : ContinuousRationalFunctions K n) :
    f ∈ infiniteFiniteSubrepresentation K n U ↔ IsInfiniteFinite K n U f := Iff.rfl

abbrev InfiniteFiniteRationalFunctions :=
  (infiniteFiniteSubrepresentation K n U).toSubmodule

/-- The infinite subgroup acts on its finite vectors by actual right translation. -/
def infiniteFiniteRightAction :
    Representation ℂ U (InfiniteFiniteRationalFunctions K n U) :=
  (infiniteFiniteSubrepresentation K n U).toRepresentation

/-- Finite adelic translation intertwines the infinite subgroup action. -/
def finiteTranslateIntertwiner (b : FiniteAdelicGL K n) :
    (infiniteSubgroupRightAction K n U).IntertwiningMap
      (infiniteSubgroupRightAction K n U) where
  toLinearMap := finiteRightAction K n b
  isIntertwining' a := by
    change continuousRightAction K n (AdelicGL.ofFinite K n b) *
        continuousRightAction K n (AdelicGL.ofInfinite K n a.val) =
      continuousRightAction K n (AdelicGL.ofInfinite K n a.val) *
        continuousRightAction K n (AdelicGL.ofFinite K n b)
    rw [← map_mul, ← map_mul, (AdelicGL.ofFinite_commute_ofInfinite K n b a.val).eq]

@[simp]
theorem finiteTranslateIntertwiner_apply (b : FiniteAdelicGL K n)
    (f : ContinuousRationalFunctions K n) :
    finiteTranslateIntertwiner K n U b f = finiteRightAction K n b f := rfl

theorem isInfiniteFinite_finiteRightAction (b : FiniteAdelicGL K n)
    {f : ContinuousRationalFunctions K n} (hf : IsInfiniteFinite K n U f) :
    IsInfiniteFinite K n U (finiteRightAction K n b f) := by
  apply (isInfiniteFinite_iff K n U _).mpr
  have h := (isInfiniteFinite_iff K n U f).mp hf
  have h' : FiniteVectors.IsFiniteVector (infiniteSubgroupRightAction K n U)
      (finiteTranslateIntertwiner K n U b f) :=
    @FiniteVectors.IsFiniteVector.map ℂ (inferInstance) U (inferInstance)
      (ContinuousRationalFunctions K n) (inferInstance) (inferInstance)
      (ContinuousRationalFunctions K n) (inferInstance) (inferInstance)
      (infiniteSubgroupRightAction K n U) (infiniteSubgroupRightAction K n U)
      (finiteTranslateIntertwiner K n U b) f h
  simpa only [finiteTranslateIntertwiner_apply] using h'

theorem isInfiniteFinite_finiteRightAction_iff (b : FiniteAdelicGL K n)
    (f : ContinuousRationalFunctions K n) :
    IsInfiniteFinite K n U (finiteRightAction K n b f) ↔ IsInfiniteFinite K n U f := by
  refine ⟨fun hf => ?_, isInfiniteFinite_finiteRightAction K n U b⟩
  have h := isInfiniteFinite_finiteRightAction K n U b⁻¹ hf
  simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
    Module.End.one_apply] using h

/-- The same finite-vector subspace is invariant under the finite adelic factor. -/
def infiniteFiniteFiniteSubrepresentation :
    Subrepresentation (finiteRightAction K n) where
  toSubmodule := (infiniteFiniteSubrepresentation K n U).toSubmodule
  apply_mem_toSubmodule b _ hf := isInfiniteFinite_finiteRightAction K n U b hf

/-- The finite adelic action on infinite-subgroup-finite functions. -/
def infiniteFiniteFiniteRightAction :
    Representation ℂ (FiniteAdelicGL K n) (InfiniteFiniteRationalFunctions K n U) :=
  (infiniteFiniteFiniteSubrepresentation K n U).toRepresentation

theorem infiniteFinite_actions_commute (a : U) (b : FiniteAdelicGL K n)
    (f : InfiniteFiniteRationalFunctions K n U) :
    infiniteFiniteFiniteRightAction K n U b (infiniteFiniteRightAction K n U a f) =
      infiniteFiniteRightAction K n U a (infiniteFiniteFiniteRightAction K n U b f) := by
  apply Subtype.ext
  exact Representation.IntertwiningMap.isIntertwining _ _
    (finiteTranslateIntertwiner K n U b) a f.val

/-- Faithful equivariant realization of the finite adelic action in ambient functions. -/
def infiniteFiniteFiniteInclusion :
    (infiniteFiniteFiniteRightAction K n U).IntertwiningMap (finiteRightAction K n) where
  toLinearMap := (infiniteFiniteSubrepresentation K n U).toSubmodule.subtype
  isIntertwining' _ := by ext; rfl

theorem infiniteFiniteFiniteInclusion_injective :
    Function.Injective (infiniteFiniteFiniteInclusion K n U) := Subtype.val_injective

@[simp]
theorem evaluate_infiniteFiniteFiniteRightAction (b : FiniteAdelicGL K n)
    (f : InfiniteFiniteRationalFunctions K n U) (x : AdelicGL K n) :
    evaluate K n (infiniteFiniteFiniteRightAction K n U b f).val x =
      evaluate K n f.val (x * AdelicGL.ofFinite K n b) := rfl

@[simp]
theorem evaluate_infiniteFiniteRightAction (a : U)
    (f : InfiniteFiniteRationalFunctions K n U) (x : AdelicGL K n) :
    evaluate K n (infiniteFiniteRightAction K n U a f).val x =
      evaluate K n f.val (x * AdelicGL.ofInfinite K n a.val) := rfl

/-- Intersect subgroup finiteness with any full adelic invariant subspace. -/
def infiniteFiniteIntersection
    (S : Subrepresentation (continuousRightAction K n)) :
    Subrepresentation (finiteRightAction K n) where
  toSubmodule := S.toSubmodule ⊓ (infiniteFiniteSubrepresentation K n U).toSubmodule
  apply_mem_toSubmodule b _ hf :=
    ⟨S.apply_mem_toSubmodule (AdelicGL.ofFinite K n b) hf.1,
      isInfiniteFinite_finiteRightAction K n U b hf.2⟩

@[simp]
theorem mem_infiniteFiniteIntersection
    (S : Subrepresentation (continuousRightAction K n))
    (f : ContinuousRationalFunctions K n) :
    f ∈ infiniteFiniteIntersection K n U S ↔ f ∈ S ∧ IsInfiniteFinite K n U f := Iff.rfl

/-- Slice-wise smooth functions satisfying actual infinite-subgroup finiteness. -/
def smoothInfiniteFiniteSubrepresentation : Subrepresentation (finiteRightAction K n) :=
  infiniteFiniteIntersection K n U (smoothSubrepresentation K n)

/-- Real-smooth functions with one open finite stabilizer and subgroup finiteness. -/
def finiteSmoothInfiniteFiniteSubrepresentation :
    Subrepresentation (finiteRightAction K n) :=
  infiniteFiniteIntersection K n U (finiteSmoothRationalSubrepresentation K n)

theorem finiteSmoothInfiniteFinite_le_smoothInfiniteFinite :
    finiteSmoothInfiniteFiniteSubrepresentation K n U ≤
      smoothInfiniteFiniteSubrepresentation K n U := by
  intro f hf
  exact ⟨finiteSmoothRational_le_smooth K n hf.1, hf.2⟩

end Langlands.Automorphic
