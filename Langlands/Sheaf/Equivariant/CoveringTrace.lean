import Langlands.Sheaf.Equivariant.DirectImage
import Langlands.Topology.LocallyConstant.Correspondence

/-! # Finite-covering trace on full equivariant locally constant sheaves -/

noncomputable section

universe u v r w

namespace Langlands.Sheaf.Equivariant.DirectImage

open CategoryTheory TopologicalSpace Opposite Topology
open Langlands.LocallyConstantCovering
open scoped BigOperators

variable {G : Type v} [Group G]
  {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  [MulAction G X] [MulAction G Y] [MulAction G Z]
  (f : C(X, Y)) (hf : ∀ (g : G) (x : X), f (g • x) = g • f x)

/-- Restricting the map to the inverse image of an open retains its entire fiber. -/
def pointMapFiberEquiv (U : ActionOpens G Y) (y : U.openSet) :
    (pointMap f hf U) ⁻¹' {y} ≃ f ⁻¹' {y.val} where
  toFun x := ⟨x.val.val, congrArg Subtype.val x.property⟩
  invFun x := ⟨⟨x.val, by
    change f x.val ∈ U.openSet
    rw [show f x.val = y.val from x.property]
    exact y.property⟩, Subtype.ext x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance pointMap_finiteFiber [∀ y, Finite (f ⁻¹' {y})]
    (U : ActionOpens G Y) :
    ∀ y : U.openSet, Finite ((pointMap f hf U) ⁻¹' {y}) :=
  fun y => Finite.of_equiv (f ⁻¹' {y.val}) (pointMapFiberEquiv f hf U y).symm

/-- The restricted map is itself an actual covering map. -/
theorem pointMap_isCoveringMap (h : IsCoveringMap f) (U : ActionOpens G Y) :
    IsCoveringMap (pointMap f hf U) :=
  h.restrictPreimage U.openSet

variable [ContinuousConstSMul G X] [ContinuousConstSMul G Y]

/-- Each labelled restriction identifies the original fibers by its group action. -/
def labelledPointMapFiberEquiv {U V : ActionOpens G Y} (k : U ⟶ V)
    (y : U.openSet) :
    (pointMap f hf U) ⁻¹' {y} ≃
      (pointMap f hf V) ⁻¹' {LocallyConstantSheaf.pointMap k y} where
  toFun x :=
    ⟨LocallyConstantSheaf.pointMap ((preimage f hf).map k) x.val, by
      apply Subtype.ext
      change f (k.label • x.val.val) = k.label • y.val
      rw [hf, show f x.val.val = y.val from congrArg Subtype.val x.property]⟩
  invFun x :=
    ⟨⟨k.label⁻¹ • x.val.val, by
      change f (k.label⁻¹ • x.val.val) ∈ U.openSet
      rw [hf, show f x.val.val = k.label • y.val from
        congrArg Subtype.val x.property, inv_smul_smul]
      exact y.property⟩, by
      apply Subtype.ext
      change f (k.label⁻¹ • x.val.val) = y.val
      rw [hf, show f x.val.val = k.label • y.val from
        congrArg Subtype.val x.property, inv_smul_smul]⟩
  left_inv x := Subtype.ext (Subtype.ext (inv_smul_smul k.label x.val.val))
  right_inv x := Subtype.ext (Subtype.ext (smul_inv_smul k.label x.val.val))

variable [∀ y, Finite (f ⁻¹' {y})]
  {R : Type r} [CommRing R] {M : Type w} [AddCommGroup M] [Module R M]

/-- The finite trace on every open commutes with every original labelled restriction. -/
theorem trace_restriction (h : IsCoveringMap f) (ρ : Representation R G M)
    {U V : ActionOpens G Y} (k : U ⟶ V)
    (s : LocallyConstant ((preimage f hf).obj V).openSet M) :
    LocallyConstantSheaf.pullback ρ k
        (trace (pointMap f hf V) (pointMap_isCoveringMap f hf h V) s) =
      trace (pointMap f hf U) (pointMap_isCoveringMap f hf h U)
        (LocallyConstantSheaf.pullback ρ ((preimage f hf).map k) s) := by
  classical
  apply LocallyConstant.ext
  intro y
  let := Fintype.ofFinite ((pointMap f hf U) ⁻¹' {y})
  change ρ k.label⁻¹
      (fiberSum (pointMap f hf V) s (LocallyConstantSheaf.pointMap k y)) =
    fiberSum (pointMap f hf U)
      (LocallyConstantSheaf.pullback ρ ((preimage f hf).map k) s) y
  rw [fiberSum_eq_sum _ _ _ (labelledPointMapFiberEquiv f hf k y), map_sum]
  rfl

/-- Unnormalized finite-fiber trace on the entire ordinary-open equivariant sheaf. -/
def coefficientTrace (h : IsCoveringMap f) (ρ : Representation R G M) :
    (sheaf f hf (ModuleCat.{max u w} R)).obj (LocallyConstantSheaf.sheaf (X := X) ρ) ⟶
      LocallyConstantSheaf.sheaf (X := Y) ρ :=
  ObjectProperty.homMk
    { app U := by
        letI := pointMap_finiteFiber f hf U.unop
        exact ModuleCat.ofHom
          (traceLinearMap R (pointMap f hf U.unop)
            (pointMap_isCoveringMap f hf h U.unop))
      naturality U V k := by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro s
        exact (trace_restriction f hf h ρ k.unop s).symm }

@[simp]
theorem coefficientTrace_apply (h : IsCoveringMap f) (ρ : Representation R G M)
    (U : ActionOpens G Y) (s : LocallyConstant ((preimage f hf).obj U).openSet M)
    (y : U.openSet) :
    LocallyConstant.toFun (((coefficientTrace f hf h ρ).hom.app (op U)).hom s) y =
      fiberSum (pointMap f hf U) s y := rfl

/-- The sheaf trace sums every point of the original fiber, without normalization. -/
theorem coefficientTrace_apply_sum (h : IsCoveringMap f) (ρ : Representation R G M)
    (U : ActionOpens G Y) (s : LocallyConstant ((preimage f hf).obj U).openSet M)
    (y : U.openSet) [Fintype (f ⁻¹' {y.val})] :
    LocallyConstant.toFun (((coefficientTrace f hf h ρ).hom.app (op U)).hom s) y =
      ∑ x : f ⁻¹' {y.val}, s ⟨x.val, by
        change f x.val ∈ U.openSet
        rw [show f x.val = y.val from x.property]
        exact y.property⟩ :=
  fiberSum_eq_sum _ _ _ (pointMapFiberEquiv f hf U y).symm

/-- Pullback followed by trace counts the entire original fiber at each point. -/
theorem coefficientTrace_pullback_apply (h : IsCoveringMap f)
    (ρ : Representation R G M) (U : ActionOpens G Y)
    (s : LocallyConstant U.openSet M) (y : U.openSet) :
    LocallyConstant.toFun
        (((coefficientMap f hf ρ ≫ coefficientTrace f hf h ρ).hom.app (op U)).hom s) y =
      Nat.card (f ⁻¹' {y.val}) • s y := by
  change fiberSum (pointMap f hf U) (s ∘ pointMap f hf U) y = _
  rw [fiberSum_comap, Nat.card_congr (pointMapFiberEquiv f hf U y)]

/-- Every original coefficient intertwiner commutes with the full sheaf trace. -/
def coefficientTraceNatTrans (h : IsCoveringMap f) :
    LocallyConstantSheaf.functor R G X ⋙ sheaf f hf (ModuleCat.{max u w} R) ⟶
      LocallyConstantSheaf.functor R G Y where
  app P := coefficientTrace f hf h P.ρ
  naturality P Q k := by
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    exact trace_map (pointMap f hf U.unop)
      (pointMap_isCoveringMap f hf h U.unop) k.hom.toLinearMap s

section Identity

local instance finite_identityFiber :
    ∀ x : X, Finite ((ContinuousMap.id X) ⁻¹' {x}) := finite_id_fiber

/-- The actual one-sheeted identity covering has the identity sheaf trace. -/
@[simp]
theorem coefficientTrace_id (ρ : Representation R G M) :
    coefficientTrace (ContinuousMap.id X) (fun (_ : G) (_ : X) => rfl)
        isCoveringMap_id ρ =
      𝟙 (LocallyConstantSheaf.sheaf (X := X) ρ) := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  change LocallyConstant U.unop.openSet M at s
  apply LocallyConstant.ext
  intro x
  let : ∀ x : U.unop.openSet, Finite ((id : U.unop.openSet → U.unop.openSet) ⁻¹' {x}) :=
    finite_id_fiber
  change fiberSum (id : U.unop.openSet → U.unop.openSet) s x = s x
  exact fiberSum_id s x

/-- Identity trace is natural in the entire original coefficient category. -/
@[simp]
theorem coefficientTraceNatTrans_id :
    coefficientTraceNatTrans (R := R) (ContinuousMap.id X)
        (fun (_ : G) (_ : X) => rfl) isCoveringMap_id =
      𝟙 (LocallyConstantSheaf.functor R G X) := by
  apply NatTrans.ext
  funext P
  exact coefficientTrace_id P.ρ

end Identity

/-- The trace for the actual composite agrees with successive direct-image traces.
Covering of the composite is retained explicitly. -/
theorem coefficientTrace_comp [ContinuousConstSMul G Z]
    (g : C(Y, Z)) (hg : ∀ (k : G) (y : Y), g (k • y) = k • g y)
    [∀ z, Finite (g ⁻¹' {z})] [∀ z, Finite ((g.comp f) ⁻¹' {z})]
    (h : IsCoveringMap f) (h' : IsCoveringMap g) (hcomp : IsCoveringMap (g.comp f))
    (ρ : Representation R G M) :
    coefficientTrace (g.comp f)
        (fun k x => by change g (f (k • x)) = k • g (f x); rw [hf, hg]) hcomp ρ =
      (sheaf g hg (ModuleCat.{max u w} R)).map (coefficientTrace f hf h ρ) ≫
        coefficientTrace g hg h' ρ := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  change LocallyConstant ((preimage f hf).obj ((preimage g hg).obj U.unop)).openSet M at s
  apply LocallyConstant.ext
  intro y
  let : ∀ z, Finite
      (((pointMap g hg U.unop) ∘ (pointMap f hf ((preimage g hg).obj U.unop))) ⁻¹' {z}) :=
    finite_comp_fiber _ _
  exact fiberSum_comp
    (pointMap f hf ((preimage g hg).obj U.unop)) (pointMap g hg U.unop) s y

/-- Composition of full sheaf traces preserves every coefficient intertwiner. -/
theorem coefficientTraceNatTrans_comp [ContinuousConstSMul G Z]
    (g : C(Y, Z)) (hg : ∀ (k : G) (y : Y), g (k • y) = k • g y)
    [∀ z, Finite (g ⁻¹' {z})] [∀ z, Finite ((g.comp f) ⁻¹' {z})]
    (h : IsCoveringMap f) (h' : IsCoveringMap g) (hcomp : IsCoveringMap (g.comp f)) :
    coefficientTraceNatTrans (R := R) (g.comp f)
        (fun k x => by change g (f (k • x)) = k • g (f x); rw [hf, hg]) hcomp =
      Functor.whiskerRight (coefficientTraceNatTrans f hf h)
          (sheaf g hg (ModuleCat.{max u w} R)) ≫
        coefficientTraceNatTrans g hg h' := by
  apply NatTrans.ext
  funext P
  exact coefficientTrace_comp f hf g hg h h' hcomp P.ρ

end Langlands.Sheaf.Equivariant.DirectImage
