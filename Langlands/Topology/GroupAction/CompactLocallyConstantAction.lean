import Langlands.Topology.GroupAction.CompactLocallyConstantStabilizer
import Langlands.CategoryTheory.TopCatSelfForget

/-! # Discrete continuous actions on locally constant functions -/

noncomputable section

universe u v w t

namespace Langlands.CompactAction

open CategoryTheory Topology

/-- Locally constant functions with their own discrete topology and domain action. -/
structure DiscreteLocallyConstant (X : Type u) [TopologicalSpace X] (A : Type w) where
  toLocallyConstant : LocallyConstant X A

namespace DiscreteLocallyConstant

variable {X : Type u} [TopologicalSpace X] {A : Type w}

instance : FunLike (DiscreteLocallyConstant X A) X A where
  coe f := f.toLocallyConstant
  coe_injective := by
    rintro ⟨f⟩ ⟨h⟩ heq
    exact congrArg DiscreteLocallyConstant.mk (DFunLike.coe_injective heq)

@[ext]
theorem ext {f h : DiscreteLocallyConstant X A} (heq : ∀ x, f x = h x) : f = h :=
  DFunLike.ext f h heq

/-- Forgetting the wrapper is an equivalence of the actual function sets. -/
def equiv : DiscreteLocallyConstant X A ≃ LocallyConstant X A where
  toFun := toLocallyConstant
  invFun := DiscreteLocallyConstant.mk
  left_inv _ := rfl
  right_inv _ := rfl

instance : TopologicalSpace (DiscreteLocallyConstant X A) := ⊥

instance : DiscreteTopology (DiscreteLocallyConstant X A) := ⟨rfl⟩

/-- Pullback retains the given continuous map of domains. -/
def pullback {Y : Type t} [TopologicalSpace Y] (q : C(X, Y))
    (f : DiscreteLocallyConstant Y A) : DiscreteLocallyConstant X A :=
  ⟨LocallyConstant.comap q f.toLocallyConstant⟩

@[simp]
theorem pullback_apply {Y : Type t} [TopologicalSpace Y] (q : C(X, Y))
    (f : DiscreteLocallyConstant Y A) (x : X) : pullback q f x = f (q x) := rfl

/-- Surjectivity of the original domain map detects equality of functions. -/
theorem pullback_injective {Y : Type t} [TopologicalSpace Y]
    (q : C(X, Y)) (hq : Function.Surjective q) :
    Function.Injective (pullback (A := A) q) := by
  intro f h heq
  ext y
  obtain ⟨x, rfl⟩ := hq y
  exact congrArg (fun k : DiscreteLocallyConstant X A => k x) heq

variable (G : Type v) [Group G] [MulAction G X] [ContinuousConstSMul G X]

/-- Inverse precomposition, with no action or topology on the coefficient set. -/
instance : MulAction G (DiscreteLocallyConstant X A) where
  smul g f := ⟨⟨fun x => f (g⁻¹ • x),
    f.toLocallyConstant.isLocallyConstant.comp_continuous (continuous_const_smul _)⟩⟩
  one_smul f := by
    ext x
    change f ((1 : G)⁻¹ • x) = f x
    simp
  mul_smul g h f := by
    ext x
    change f ((g * h)⁻¹ • x) = f (h⁻¹ • (g⁻¹ • x))
    rw [mul_inv_rev, mul_smul]

@[simp]
theorem smul_apply (g : G) (f : DiscreteLocallyConstant X A) (x : X) :
    (g • f) x = f (g⁻¹ • x) := rfl

/-- Fixedness for inverse precomposition is precisely the full function stabilizer. -/
theorem stabilizer_eq (f : DiscreteLocallyConstant X A) :
    MulAction.stabilizer G f = functionStabilizer G f := by
  apply Subgroup.ext
  intro g
  change (g • f = f) ↔ ∀ x, f (g • x) = f x
  constructor
  · intro h x
    have hx := congrArg (fun k : DiscreteLocallyConstant X A => k (g • x)) h
    simpa using hx.symm
  · intro h
    ext x
    exact (by simpa using (h (g⁻¹ • x)).symm)

/-- Equivariant pullback commutes with the actual inverse-precomposition actions. -/
theorem pullback_smul {Y : Type t} [TopologicalSpace Y]
    [MulAction G Y] [ContinuousConstSMul G Y]
    (q : C(X, Y)) (heq : ∀ (g : G) (x : X), q (g • x) = g • q x)
    (g : G) (f : DiscreteLocallyConstant Y A) :
    pullback q (g • f) = g • pullback q f := by
  ext x
  exact congrArg f (heq g⁻¹ x).symm

attribute [local instance] Langlands.Analytic.NormContinuousAffinoidAction.topCatSelfForget

/-- The discrete function space with its actual inverse-precomposition operators. -/
def action : Action TopCat.{max u w} G where
  V := TopCat.of (DiscreteLocallyConstant X A)
  ρ :=
    { toFun := fun g => TopCat.ofHom ⟨fun f => g • f, continuous_of_discreteTopology⟩
      map_one' := by
        apply TopCat.ext
        intro f
        exact one_smul G f
      map_mul' := by
        intro g h
        apply TopCat.ext
        intro f
        exact mul_smul g h f }

variable [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace X] [ContinuousSMul G X]

/-- The original group topology gives a jointly continuous action on the
entire discrete locally constant function space of a compact action space. -/
instance : ContinuousSMul G (DiscreteLocallyConstant X A) := by
  apply continuousSMul_iff_stabilizer_isOpen.mpr
  intro f
  rw [stabilizer_eq]
  exact functionStabilizer_isOpen G f.toLocallyConstant

/-- Bundle the constructed action and its proved joint continuity. -/
def continuousAction : ContAction TopCat.{max u w} G :=
  ⟨action (X := X) (A := A) G, (Action.isContinuous_def _).mpr
    (continuous_smul : Continuous (fun p : G × DiscreteLocallyConstant X A => p.1 • p.2))⟩

end DiscreteLocallyConstant
end Langlands.CompactAction
