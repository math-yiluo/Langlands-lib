import Langlands.Topology.GroupAction.CompactLocallyConstantFunctor
import Langlands.Representation.Category.Basic
import Langlands.Representation.Smooth.Transfer.StabilizerProof
import Mathlib.Topology.LocallyConstant.Algebra

/-! # Smooth diagonal representations on locally constant functions -/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe uX uG uR uV

namespace Langlands.CompactAction.LocallyConstantModule

open CategoryTheory Topology

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G]
  {X : Type uX} [TopologicalSpace X] [MulAction G X] [ContinuousConstSMul G X]
  {V : Type uV} [AddCommGroup V] [Module R V]

/-- The diagonal action on all locally constant module-valued functions. -/
def diagonalRepresentation (ρ : Representation R G V) :
    Representation R G (LocallyConstant X V) where
  toFun g := (LocallyConstant.mapₗ R (ρ g)).comp
    (LocallyConstant.comapₗ R ⟨fun x => g⁻¹ • x, continuous_const_smul _⟩)
  map_one' := by
    ext f x
    change ρ 1 (f ((1 : G)⁻¹ • x)) = f x
    simp
  map_mul' g h := by
    ext f x
    change ρ (g * h) (f ((g * h)⁻¹ • x)) =
      ρ g (ρ h (f (h⁻¹ • (g⁻¹ • x))))
    simp [mul_inv_rev, mul_smul, map_mul]

@[simp]
theorem diagonalRepresentation_apply (ρ : Representation R G V) (g : G)
    (f : LocallyConstant X V) (x : X) :
    diagonalRepresentation ρ g f x = ρ g (f (g⁻¹ • x)) := rfl

/-- Pullback along the original continuous equivariant domain map is linear
and intertwines the diagonal representations. -/
def pullbackIntertwiner {Y : Type*} [TopologicalSpace Y] [MulAction G Y]
    [ContinuousConstSMul G Y] (ρ : Representation R G V) (q : C(X, Y))
    (heq : ∀ (g : G) (x : X), q (g • x) = g • q x) :
    (diagonalRepresentation (X := Y) ρ).IntertwiningMap
      (diagonalRepresentation (X := X) ρ) where
  toLinearMap := LocallyConstant.comapₗ R q
  isIntertwining' g := by
    ext f x
    exact congrArg (ρ g) (congrArg f (heq g⁻¹ x).symm)

/-- Postcomposition by the original coefficient intertwiner is linear and
intertwines the diagonal representations. -/
def coefficientIntertwiner {W : Type*} [AddCommGroup W] [Module R W]
    {ρ : Representation R G V} {σ : Representation R G W}
    (a : ρ.IntertwiningMap σ) :
    (diagonalRepresentation (X := X) ρ).IntertwiningMap
      (diagonalRepresentation (X := X) σ) where
  toLinearMap := LocallyConstant.mapₗ R a.toLinearMap
  isIntertwining' g := by
    ext f x
    exact Representation.IntertwiningMap.isIntertwining ρ σ a g (f (g⁻¹ • x))

variable [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace X] [ContinuousSMul G X]

/-- A common open subgroup fixes the spatial function and every coefficient
value in its finite image. -/
def commonOpenStabilizer (ρ : Representation R G V) (hρ : IsSmooth ρ)
    (f : LocallyConstant X V) : OpenSubgroup G := by
  letI : Finite (Set.range f) := f.range_finite.to_subtype
  exact openStabilizer G f ⊓ OpenSubgroup.iInfOfFinite
    (fun a : Set.range f =>
      ⟨ρ.stabilizer a.val, (isSmoothVector_iff_isOpen_stabilizer a.val).mp (hρ a.val)⟩)

omit [ContinuousConstSMul G X] in
@[simp]
theorem mem_commonOpenStabilizer (ρ : Representation R G V) (hρ : IsSmooth ρ)
    (f : LocallyConstant X V) (g : G) :
    g ∈ commonOpenStabilizer ρ hρ f ↔
      (∀ x, f (g • x) = f x) ∧ ∀ a : Set.range f, ρ g a.val = a.val := by
  change (g ∈ functionStabilizer G f ∧
    g ∈ (⨅ a : Set.range f, ρ.stabilizer a.val)) ↔ _
  simp only [Subgroup.mem_iInf]
  rfl

/-- Compactness and coefficient smoothness prove smoothness of the entire
locally constant function module. -/
theorem diagonalRepresentation_isSmooth (ρ : Representation R G V) (hρ : IsSmooth ρ) :
    IsSmooth (diagonalRepresentation (X := X) ρ) := by
  intro f
  refine ⟨commonOpenStabilizer ρ hρ f, ?_⟩
  intro g
  apply LocallyConstant.ext
  intro x
  change ρ (g : G) (f ((g : G)⁻¹ • x)) = f x
  have hs := ((mem_commonOpenStabilizer ρ hρ f (g : G)⁻¹).mp
    ((commonOpenStabilizer ρ hρ f).inv_mem g.property)).1 x
  rw [hs]
  exact ((mem_commonOpenStabilizer ρ hρ f g).mp g.property).2
    ⟨f x, ⟨x, rfl⟩⟩

/-- Bundle all locally constant functions with the proved smooth diagonal action. -/
def smoothRepresentation (A : SmoothRep.{uR, uG, uV} R G) :
    SmoothRep.{uR, uG, max uX uV} R G :=
  SmoothRep.of (diagonalRepresentation (X := X) A.representation)
    (diagonalRepresentation_isSmooth A.representation A.isSmooth)

end Langlands.CompactAction.LocallyConstantModule

namespace Langlands.CompactAction.CompactContinuousAction

open CategoryTheory Topology

attribute [local instance] Langlands.Analytic.NormContinuousAffinoidAction.topCatSelfForget

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G]

local instance (S : CompactContinuousAction.{uX, uG} G) : CompactSpace S.obj.obj.V := S.property

local instance (S : CompactContinuousAction.{uX, uG} G) : MulAction G S.obj.obj.V :=
  inferInstanceAs (MulAction G
    ((forget₂ (Action TopCat.{uX} G) TopCat.{uX}).obj S.obj.obj))

local instance (S : CompactContinuousAction.{uX, uG} G) : ContinuousSMul G S.obj.obj.V :=
  S.obj.property

/-- All locally constant coefficient functions on an actual compact action space. -/
def locallyConstantModuleAction (S : CompactContinuousAction.{uX, uG} G)
    (A : SmoothRep.{uR, uG, uV} R G) : SmoothRep.{uR, uG, max uX uV} R G :=
  LocallyConstantModule.smoothRepresentation (X := S.obj.obj.V) A

/-- Every original continuous equivariant map gives diagonal-equivariant linear pullback. -/
def locallyConstantModulePullback {S T : CompactContinuousAction.{uX, uG} G}
    (q : S ⟶ T) (A : SmoothRep.{uR, uG, uV} R G) :
    locallyConstantModuleAction T A ⟶ locallyConstantModuleAction S A :=
  SmoothRep.ofHom (LocallyConstantModule.pullbackIntertwiner A.representation
    q.hom.hom.hom.hom (fun g x =>
      congrArg (fun k => k x) (q.hom.hom.comm g)))

@[simp]
theorem locallyConstantModulePullback_apply {S T : CompactContinuousAction.{uX, uG} G}
    (q : S ⟶ T) (A : SmoothRep.{uR, uG, uV} R G)
    (f : LocallyConstant T.obj.obj.V A) (x : S.obj.obj.V) :
    LocallyConstant.toFun (SmoothRep.hom (locallyConstantModulePullback q A) f) x = f (q.hom.hom.hom x) := rfl

/-- A contravariant functor on compact continuous action spaces with arbitrary
smooth module coefficients. -/
def locallyConstantModuleFunctor (A : SmoothRep.{uR, uG, uV} R G) :
    (CompactContinuousAction.{uX, uG} G)ᵒᵖ ⥤ SmoothRep.{uR, uG, max uX uV} R G where
  obj S := locallyConstantModuleAction S.unop A
  map q := locallyConstantModulePullback q.unop A
  map_id _ := by
    ext f
    rfl
  map_comp _ _ := by
    ext f
    rfl

/-- The actual coefficient intertwiner acts by pointwise postcomposition. -/
def locallyConstantModuleCoefficientMap {A B : SmoothRep.{uR, uG, uV} R G}
    (a : A ⟶ B) : (locallyConstantModuleFunctor A :
      (CompactContinuousAction.{uX, uG} G)ᵒᵖ ⥤ SmoothRep.{uR, uG, max uX uV} R G) ⟶
      locallyConstantModuleFunctor B where
  app S := SmoothRep.ofHom
    (LocallyConstantModule.coefficientIntertwiner (X := S.unop.obj.obj.V) (SmoothRep.hom a))
  naturality {S T} q := by
    ext f
    rfl

@[simp]
theorem locallyConstantModuleCoefficientMap_apply {A B : SmoothRep.{uR, uG, uV} R G}
    (a : A ⟶ B) (S : CompactContinuousAction.{uX, uG} G)
    (f : LocallyConstant S.obj.obj.V A) (x : S.obj.obj.V) :
    LocallyConstant.toFun
      (SmoothRep.hom ((locallyConstantModuleCoefficientMap a).app (Opposite.op S)) f) x =
      SmoothRep.hom a (f x) := rfl

/-- The constructions form a functor in smooth coefficients, retaining every
equivariant linear map and every original continuous domain map. -/
def locallyConstantModuleCoefficients : SmoothRep.{uR, uG, uV} R G ⥤
    ((CompactContinuousAction.{uX, uG} G)ᵒᵖ ⥤ SmoothRep.{uR, uG, max uX uV} R G) where
  obj := locallyConstantModuleFunctor
  map := locallyConstantModuleCoefficientMap
  map_id _ := by
    ext S f
    rfl
  map_comp _ _ := by
    ext S f
    rfl

end Langlands.CompactAction.CompactContinuousAction
