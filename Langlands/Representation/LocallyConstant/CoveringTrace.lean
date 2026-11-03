import Langlands.Topology.LocallyConstant.CoveringTrace
import Langlands.Representation.LocallyConstant.CompactSupport

/-! # Equivariant covering trace on full compact-support modules -/

noncomputable section

universe uX uG uR uV

namespace Langlands.CompactAction.LocallyConstantModule.CompactSupport

open CategoryTheory Topology
open Langlands.LocallyConstantCovering

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G]
  {X Y Z : Type uX} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  {V : Type uV} [AddCommGroup V] [Module R V]

/-- Restrict the actual finite-fiber trace to every compactly supported
locally constant function. -/
def traceLinear (q : X → Y) [∀ y, Finite (q ⁻¹' {y})] (hq : IsCoveringMap q) :
    Functions R X V →ₗ[R] Functions R Y V :=
  ((traceLinearMap R q hq).comp (submodule R X V).subtype).codRestrict
    (submodule R Y V) (fun f => hasCompactSupport_trace q hq f.val f.property)

@[simp]
theorem traceLinear_apply (q : X → Y) [∀ y, Finite (q ⁻¹' {y})]
    (hq : IsCoveringMap q) (f : Functions R X V) (y : Y) :
    (traceLinear q hq f).val y = fiberSum q f.val y := rfl

variable [MulAction G X] [MulAction G Y]
  [ContinuousConstSMul G X] [ContinuousConstSMul G Y]

/-- The unnormalized sum intertwines the original diagonal representations. -/
def traceIntertwiner (ρ : Representation R G V)
    (q : X → Y) [∀ y, Finite (q ⁻¹' {y})] (hq : IsCoveringMap q)
    (heq : ∀ (g : G) (x : X), q (g • x) = g • q x) :
    (representation (X := X) ρ).IntertwiningMap (representation (X := Y) ρ) where
  toLinearMap := traceLinear q hq
  isIntertwining' g := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    apply LocallyConstant.ext
    intro y
    change fiberSum q (fun x => ρ g (f.val (g⁻¹ • x))) y =
      ρ g (fiberSum q f.val (g⁻¹ • y))
    calc
      _ = ρ g (fiberSum q (fun x => f.val (g⁻¹ • x)) y) := by
        simp [fiberSum, map_sum]
      _ = _ := congrArg (ρ g) (fiberSum_translate q heq g f.val y)

@[simp]
theorem traceIntertwiner_apply (ρ : Representation R G V)
    (q : X → Y) [∀ y, Finite (q ⁻¹' {y})] (hq : IsCoveringMap q)
    (heq : ∀ (g : G) (x : X), q (g • x) = g • q x)
    (f : Functions R X V) (y : Y) :
    (traceIntertwiner ρ q hq heq f).val y = fiberSum q f.val y := rfl

variable [TopologicalSpace G] [IsTopologicalGroup G]
  [ContinuousSMul G X] [ContinuousSMul G Y]

/-- Covering trace between the full, already proved smooth compact-support
representations, for arbitrary smooth coefficients. -/
def smoothTrace (A : SmoothRep.{uR, uG, uV} R G)
    (q : X → Y) [∀ y, Finite (q ⁻¹' {y})] (hq : IsCoveringMap q)
    (heq : ∀ (g : G) (x : X), q (g • x) = g • q x) :
    smoothRepresentation (X := X) A ⟶ smoothRepresentation (X := Y) A :=
  SmoothRep.ofHom (traceIntertwiner A.representation q hq heq)

@[simp]
theorem smoothTrace_apply (A : SmoothRep.{uR, uG, uV} R G)
    (q : X → Y) [∀ y, Finite (q ⁻¹' {y})] (hq : IsCoveringMap q)
    (heq : ∀ (g : G) (x : X), q (g • x) = g • q x)
    (f : Functions R X A) (y : Y) :
    (SmoothRep.hom (smoothTrace A q hq heq) f).val y = fiberSum q f.val y := rfl

/-- Pointwise coefficient intertwiners commute with the original fiber sum. -/
theorem smoothTrace_naturality (q : X → Y) [∀ y, Finite (q ⁻¹' {y})]
    (hq : IsCoveringMap q) (heq : ∀ (g : G) (x : X), q (g • x) = g • q x)
    {A B : SmoothRep.{uR, uG, uV} R G} (a : A ⟶ B) :
    (coefficientFunctor (X := X)).map a ≫ smoothTrace B q hq heq =
      smoothTrace A q hq heq ≫ (coefficientFunctor (X := Y)).map a := by
  ext f
  apply Subtype.ext
  exact trace_map q hq (SmoothRep.hom a).toLinearMap f.val

/-- A natural transformation on the entire smooth coefficient category. -/
def traceNatTrans (q : X → Y) [∀ y, Finite (q ⁻¹' {y})]
    (hq : IsCoveringMap q) (heq : ∀ (g : G) (x : X), q (g • x) = g • q x) :
    coefficientFunctor (R := R) (G := G) (X := X) ⟶
      coefficientFunctor (X := Y) where
  app A := smoothTrace A q hq heq
  naturality {_ _} a := smoothTrace_naturality q hq heq a

@[simp]
theorem smoothTrace_id [∀ x : X, Finite ((id : X → X) ⁻¹' {x})]
    (hq : IsCoveringMap (id : X → X)) (A : SmoothRep.{uR, uG, uV} R G) :
    smoothTrace A id hq (fun _ _ => rfl) = 𝟙 (smoothRepresentation (X := X) A) := by
  ext f
  apply Subtype.ext
  apply LocallyConstant.ext
  intro x
  exact fiberSum_id f.val x

variable [MulAction G Z] [ContinuousConstSMul G Z] [ContinuousSMul G Z]

/-- Composition retains the actual composite map and its original action. -/
theorem smoothTrace_comp (q : X → Y) (p : Y → Z)
    [∀ y, Finite (q ⁻¹' {y})] [∀ z, Finite (p ⁻¹' {z})]
    [∀ z, Finite ((p ∘ q) ⁻¹' {z})]
    (hq : IsCoveringMap q) (hp : IsCoveringMap p) (hpq : IsCoveringMap (p ∘ q))
    (heq : ∀ (g : G) (x : X), q (g • x) = g • q x)
    (hep : ∀ (g : G) (y : Y), p (g • y) = g • p y)
    (A : SmoothRep.{uR, uG, uV} R G) :
    smoothTrace A (p ∘ q) hpq (fun g x => by
      dsimp only [Function.comp_apply]
      rw [heq, hep]) =
      smoothTrace A q hq heq ≫ smoothTrace A p hp hep := by
  ext f
  apply Subtype.ext
  apply LocallyConstant.ext
  intro z
  exact fiberSum_comp q p f.val z

end Langlands.CompactAction.LocallyConstantModule.CompactSupport
