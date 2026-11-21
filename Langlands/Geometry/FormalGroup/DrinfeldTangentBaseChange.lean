import Langlands.Geometry.FormalGroup.DrinfeldTangentComponents

/-! # Coefficient base change of the actual Drinfeld tangent projectors -/

noncomputable section

namespace Langlands.FormalGroup

universe u v w s

namespace ModuleLaw.OrderAction

variable {O : Type u} [CommRing O] {A : Type w} [Ring A] [Algebra O A]
  {R S : Type v} [CommRing R] [CommRing S] [Algebra O R] [Algebra O S]
  {I : Type} [Finite I] {M : ModuleLaw O R I} (E : OrderAction A M)

/-- Passing to a new coefficient algebra commutes with the actual tangent action. -/
theorem tangentAction_map_apply (φ : R →ₐ[O] S) (a : A) (x : I → R) :
    (fun i => φ (E.tangentAction a x i)) = (E.map φ).tangentAction a (fun i => φ (x i)) := by
  let := Fintype.ofFinite I
  change (fun i => φ (E.fiberTangent (RingHom.id R) a x i)) =
    (E.map φ).fiberTangent (RingHom.id S) a (fun i => φ (x i))
  rw [E.fiberTangent_map, RingHom.id_comp]
  funext i
  rw [E.fiberTangent_apply_apply, E.fiberTangent_apply_apply, map_sum]
  simp only [RingHom.id_apply, map_mul]
  rfl

end ModuleLaw.OrderAction

namespace LocalDivision

open IsLocalRing ValuativeRel CentralDivision CentralSimple CategoryTheory ModuleLaw
open scoped TensorProduct

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] (ι : L →ₐ[K] D)

local instance tangentBaseChangeLocalHom : IsLocalHom (algebraMap 𝒪[K] (SubfieldIntegerRing K D ι)) :=
  subfieldIntegerAlgebra_isLocalHom ι

variable {κ : Type u} [Field κ] [Algebra 𝒪[K] κ] [Algebra 𝓀[K] κ]
  [IsScalarTower 𝒪[K] 𝓀[K] κ]
variable (hL : IsUnramifiedSubfieldOfReducedDegree K D ι)
variable (χ : ResidueField (SubfieldIntegerRing K D ι) →ₐ[𝓀[K]] κ)
variable {π : 𝒪[K]} {B B' : Nilp.{u, v} 𝒪[K] π} (ψ : κ →ₐ[𝒪[K]] Nilp.Reduction π B.obj)
variable {I : Type} [Finite I] {M : ModuleLaw 𝒪[K] B.obj I}
  (E : OrderAction (IntegerRing K D) M) (f : B ⟶ B')

local notation "C" => SubfieldIntegerRing K D ι
local notation "d" => CentralSimple.reducedDegree K D
local notation "iC" => subfieldIntegerInclusion K D ι
local notation "φ" => CommAlgCat.Hom.hom (InducedCategory.Hom.hom f)
local notation "ψ'" => AlgHom.comp (Nilp.reductionMap φ) ψ

/-- The whole split coefficient action on tangent vectors is compatible with affine Nilp base change. -/
theorem drinfeldTangentCharacterAction_natural (a : Fin d → B.obj) (x : I → B.obj) :
    (fun i => φ (drinfeldTangentCharacterAction ι hL χ ψ E a x i)) =
      drinfeldTangentCharacterAction ι hL χ ψ' (E.map φ) (fun i => φ (a i)) (fun i => φ (x i)) := by
  let sp := subfieldCyclicSplitting hL χ ψ
  let sp' := subfieldCyclicSplitting hL χ ψ'
  let ext := Algebra.TensorProduct.map φ (AlgHom.id 𝒪[K] C)
  let x' := fun i => φ (x i)
  obtain ⟨z, rfl⟩ := sp.surjective a
  have hsp : (fun i => φ (sp z i)) = sp' (ext z) := by
    funext i
    exact (subfieldCyclicSplitting_natural hL χ ψ f z i).symm
  rw [hsp]
  let α := (E.tangentAction.comp iC).liftEquiv 𝒪[K] B.obj C (Module.End B.obj (I → B.obj))
  let α' := ((E.map φ).tangentAction.comp iC).liftEquiv 𝒪[K] B'.obj C (Module.End B'.obj (I → B'.obj))
  change (fun i => φ (α (sp.symm (sp z)) x i)) = α' (sp'.symm (sp' (ext z))) x'
  rw [AlgEquiv.symm_apply_apply, AlgEquiv.symm_apply_apply]
  clear hsp
  induction z using TensorProduct.inductionOn with
  | tmul b a =>
    have h := E.tangentAction_map_apply φ (iC a) x
    change (fun i => φ (((E.tangentAction.comp iC).liftEquiv 𝒪[K] B.obj C
      (Module.End B.obj (I → B.obj))) (b ⊗ₜ[𝒪[K]] a) x i)) =
      (((E.map φ).tangentAction.comp iC).liftEquiv 𝒪[K] B'.obj C
        (Module.End B'.obj (I → B'.obj))) (φ b ⊗ₜ[𝒪[K]] a) x'
    rw [AlgHom.liftEquiv_tmul, AlgHom.liftEquiv_tmul]
    funext i
    change φ (b * E.tangentAction (iC a) x i) = φ b * (E.map φ).tangentAction (iC a) x' i
    rw [map_mul, congrFun h i]
  | add z w hz hw =>
    funext i
    simp only [map_add, LinearMap.add_apply, Pi.add_apply, congrFun hz i, congrFun hw i]

/-- The actual tangent projector for a fixed character commutes with coefficient transport. -/
theorem drinfeldTangentProjector_natural (j : Fin d) (x : I → B.obj) :
    (fun i => φ (drinfeldTangentProjector ι hL χ ψ E j x i)) =
      drinfeldTangentProjector ι hL χ ψ' (E.map φ) j (fun i => φ (x i)) := by
  have h : (fun i => φ ((Pi.single j 1 : Fin d → B.obj) i)) = (Pi.single j 1 : Fin d → B'.obj) := by
    funext i
    by_cases hi : i = j <;> simp [hi]
  simpa only [drinfeldTangentProjector, h] using
    drinfeldTangentCharacterAction_natural ι hL χ ψ E f (Pi.single j 1) x

/-- The projector square restricts the coefficient map to the two actual character components. -/
def drinfeldTangentComponentMap (j : Fin d) :
    (drinfeldTangentComponent ι hL χ ψ E j) →ₛₗ[(φ).toRingHom]
      (drinfeldTangentComponent ι hL χ ψ' (E.map φ) j) where
  toFun x := ⟨fun i => φ (x.val i), by
    obtain ⟨v, hv⟩ := x.property
    refine ⟨fun i => φ (v i), ?_⟩
    exact (drinfeldTangentProjector_natural ι hL χ ψ E f j v).symm.trans
      (congrArg (fun w : I → B.obj => fun i => φ (w i)) hv)⟩
  map_add' x y := Subtype.ext (funext fun i => map_add φ (x.val i) (y.val i))
  map_smul' b x := Subtype.ext (funext fun i => map_mul φ b (x.val i))

end LocalDivision
end Langlands.FormalGroup
