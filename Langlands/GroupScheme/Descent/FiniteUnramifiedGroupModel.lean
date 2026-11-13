import Langlands.GroupScheme.Descent.FiniteCoefficientGroup
import Langlands.Galois.Local.SeparableUnramifiedProof

/-! # Finite unramified coefficients for smooth affine group schemes -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped ValuativeRel

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.Descent.FiniteUnramified

open Langlands.LocalGalois.Separable

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

local instance : Algebra ↥𝒪[F] (fixedFieldIntegers F) :=
  Valuation.HasExtension.instAlgebraInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

/-- The integers of an intermediate field, viewed inside the maximal
unramified integers. -/
def integerCoefficients (E : IntermediateField F (SeparableClosure F)) :
    Subalgebra ↥𝒪[F] (fixedFieldIntegers F) where
  carrier := {x | fixedFieldToSepClosure F (x : inertiaFixedField F) ∈ E}
  zero_mem' := E.zero_mem
  one_mem' := E.one_mem
  add_mem' hx hy := E.add_mem hx hy
  mul_mem' hx hy := E.mul_mem hx hy
  algebraMap_mem' x := E.algebraMap_mem (x : F)

@[simp]
theorem mem_integerCoefficients (E : IntermediateField F (SeparableClosure F))
    (x : fixedFieldIntegers F) :
    x ∈ integerCoefficients F E ↔
      fixedFieldToSepClosure F (x : inertiaFixedField F) ∈ E := Iff.rfl

/-- A finitely generated coefficient algebra is contained in the integers of
one finite Galois unramified intermediate field. -/
theorem exists_integerCoefficients
    (T : Subalgebra ↥𝒪[F] (fixedFieldIntegers F)) (hT : T.FG) :
    ∃ E : IntermediateField F (SeparableClosure F),
      FiniteDimensional F E ∧ IsGalois F E ∧ E ≤ inertiaFixedField F ∧
      ArithmeticUnramified F E ∧ T ≤ integerCoefficients F E := by
  classical
  obtain ⟨s, hs⟩ := hT
  obtain ⟨E, hfin, hgal, hE, hunr, hcoeff⟩ :=
    (separableUnramified F).2 (s.image fun x => (x : inertiaFixedField F))
  refine ⟨E, hfin, hgal, hE, hunr, ?_⟩
  rw [← hs]
  apply Algebra.adjoin_le
  intro x hx
  apply hcoeff
  simpa using Finset.mem_image_of_mem (fun y : fixedFieldIntegers F =>
    (y : inertiaFixedField F)) hx

/-- An actual finite unramified group model, together with its recovery
isomorphism over the maximal unramified integers. -/
structure GroupModel
    (G : GroupScheme (Spec (CommRingCat.of (fixedFieldIntegers F)))) where
  field : IntermediateField F (SeparableClosure F)
  finite : FiniteDimensional F field
  galois : IsGalois F field
  inertia : field ≤ inertiaFixedField F
  unramified : ArithmeticUnramified F field
  group : GroupScheme (Spec (CommRingCat.of (integerCoefficients F field)))
  affine : IsAffineHom group.X.hom
  smooth : Smooth group.X.hom
  iso : G ≅ (baseChange (Spec.algebraMap (integerCoefficients F field)
    (fixedFieldIntegers F))).obj group

/-- Smooth affine group schemes over the maximal unramified integers admit
actual models over finite Galois unramified integer coefficients. -/
theorem nonempty_groupModel
    (G : GroupScheme (Spec (CommRingCat.of (fixedFieldIntegers F))))
    [IsAffine G.X.left] [Smooth G.X.hom] : Nonempty (GroupModel F G) := by
  let D := FiniteCoefficient.groupModel ↥𝒪[F] (fixedFieldIntegers F) G
  obtain ⟨E, hfin, hgal, hE, hunr, hcoeff⟩ :=
    exists_integerCoefficients F D.coefficients D.finite
  let b := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hcoeff).toRingHom)
  let a := Spec.algebraMap (integerCoefficients F E) (fixedFieldIntegers F)
  let c := Spec.algebraMap D.coefficients (fixedFieldIntegers F)
  have hcomp : a ≫ b = c := by
    dsimp [a, b, c, Spec.algebraMap]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  refine ⟨{ field := E
            finite := hfin
            galois := hgal
            inertia := hE
            unramified := hunr
            group := (baseChange b).obj D.group
            affine := ?_
            smooth := ?_
            iso := D.iso ≪≫ (pullbackComparison b a c hcomp D.group).symm }⟩
  · let := D.affine
    change IsAffineHom (pullback.snd D.group.X.hom b)
    infer_instance
  · let := D.smooth
    change Smooth (pullback.snd D.group.X.hom b)
    infer_instance

/-- Choose an actual finite Galois unramified integer model. -/
def groupModel
    (G : GroupScheme (Spec (CommRingCat.of (fixedFieldIntegers F))))
    [IsAffine G.X.left] [Smooth G.X.hom] : GroupModel F G :=
  Classical.choice (nonempty_groupModel F G)

end Langlands.GroupScheme.Descent.FiniteUnramified
