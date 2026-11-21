import Langlands.Geometry.FormalGroup.DrinfeldTangentBaseChange
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Scalar extension of the actual Drinfeld tangent components -/

noncomputable section

namespace Langlands.FormalGroup.LocalDivision

open IsLocalRing ValuativeRel CentralDivision CentralSimple CategoryTheory ModuleLaw
open scoped TensorProduct

universe u v s

section ProjectorImage

variable {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]

private theorem rangeRestrict_subtype (p : Module.End R M) (hp : p * p = p) :
    p.rangeRestrict.comp (LinearMap.range p).subtype = LinearMap.id := by
  apply LinearMap.ext
  intro y
  apply Subtype.ext
  obtain ⟨x, hx⟩ := y.property
  change p y.val = y.val
  rw [← hx]
  exact congrArg (fun h : Module.End R M => h x) hp

private def projectorImageBaseChange (p : Module.End R M) (q : Module.End S N)
    (hp : p * p = p) (hq : q * q = q)
    (e : S ⊗[R] M ≃ₗ[S] N) (he : ∀ z, e (p.baseChange S z) = q (e z)) :
    S ⊗[R] LinearMap.range p ≃ₗ[S] LinearMap.range q := by
  let incl := (LinearMap.range p).subtype.baseChange S
  let proj := p.rangeRestrict.baseChange S
  have hproj (z : S ⊗[R] LinearMap.range p) : proj (incl z) = z := by
    have h := congrArg (fun w : LinearMap.range p →ₗ[R] LinearMap.range p => w.baseChange S)
      (rangeRestrict_subtype p hp)
    rw [LinearMap.baseChange_comp, LinearMap.baseChange_id] at h
    exact congrArg (fun w : Module.End S (S ⊗[R] LinearMap.range p) => w z) h
  have hincl (z : S ⊗[R] M) : incl (proj z) = p.baseChange S z := by
    have h := congrArg (fun w : Module.End R M => w.baseChange S)
      (LinearMap.subtype_comp_rangeRestrict (f := p))
    rw [LinearMap.baseChange_comp] at h
    exact congrArg (fun w : Module.End S (S ⊗[R] M) => w z) h
  let forward := (e.toLinearMap.comp incl).codRestrict (LinearMap.range q) (fun z => by
    refine ⟨e (incl z), ?_⟩
    change q (e (incl z)) = e (incl z)
    rw [← he, ← hincl, hproj])
  refine LinearEquiv.ofLinearMap forward
    (proj.comp (e.symm.toLinearMap.comp (LinearMap.range q).subtype)) ?_ ?_
  · apply LinearMap.ext
    intro z
    apply Subtype.ext
    change e (incl (proj (e.symm z.val))) = z.val
    rw [hincl, he, LinearEquiv.apply_symm_apply]
    obtain ⟨y, hy⟩ := z.property
    change q y = z.val at hy
    rw [← hy]
    exact congrArg (fun w : Module.End S N => w y) hq
  · apply LinearMap.ext
    intro z
    change proj (e.symm (e (incl z))) = z
    rw [LinearEquiv.symm_apply_apply, hproj]

private def coordinateTensorEquiv (R S I : Type*) [CommRing R] [CommRing S] [Algebra R S] [Finite I] :
    S ⊗[R] (I → R) ≃ₗ[S] (I → S) := by
  classical
  let := Fintype.ofFinite I
  exact ((Pi.basisFun R I).baseChange S).equivFun

private theorem coordinateTensorEquiv_tmul {R S I : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Finite I] (b : S) (x : I → R) :
    coordinateTensorEquiv R S I (b ⊗ₜ[R] x) = b • (fun i => algebraMap R S (x i)) := by
  classical
  let := Fintype.ofFinite I
  funext i
  change ((Pi.basisFun R I).baseChange S).equivFun (b ⊗ₜ[R] x) i = _
  rw [Module.Basis.equivFun_apply, Module.Basis.baseChange_repr_tmul, Pi.basisFun_repr]
  exact (Algebra.smul_def _ _).trans (mul_comm _ _)

end ProjectorImage

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] (ι : L →ₐ[K] D)

local instance tangentComponentTransportLocalHom :
    IsLocalHom (algebraMap 𝒪[K] (SubfieldIntegerRing K D ι)) := subfieldIntegerAlgebra_isLocalHom ι

variable {κ : Type u} [Field κ] [Algebra 𝒪[K] κ] [Algebra 𝓀[K] κ]
  [IsScalarTower 𝒪[K] 𝓀[K] κ]
variable (hL : IsUnramifiedSubfieldOfReducedDegree K D ι)
variable (χ : ResidueField (SubfieldIntegerRing K D ι) →ₐ[𝓀[K]] κ)
variable {π : 𝒪[K]} {B B' : Nilp.{u, v} 𝒪[K] π} (ψ : κ →ₐ[𝒪[K]] Nilp.Reduction π B.obj)
variable {I : Type} [Finite I] {M : ModuleLaw 𝒪[K] B.obj I} (E : OrderAction (IntegerRing K D) M)

local notation "d" => CentralSimple.reducedDegree K D
local notation "P" => drinfeldTangentProjector ι hL χ ψ E
local notation "W" => drinfeldTangentComponent ι hL χ ψ E

/-- The actual tangent component is a finite module. -/
theorem drinfeldTangentComponent_finite (i : Fin d) : Module.Finite B.obj (W i) :=
  Module.Finite.of_surjective (P i).rangeRestrict (P i).surjective_rangeRestrict

/-- The actual tangent component is projective by its projector splitting. -/
theorem drinfeldTangentComponent_projective (i : Fin d) : Module.Projective B.obj (W i) :=
  Module.Projective.of_split (LinearMap.range (P i)).subtype (P i).rangeRestrict
    (rangeRestrict_subtype (P i) (drinfeldTangentProjector_mul_same ι hL χ ψ E i))

variable (f : B ⟶ B')

local notation "φ" => CommAlgCat.Hom.hom (InducedCategory.Hom.hom f)
local notation "ψ'" => AlgHom.comp (Nilp.reductionMap φ) ψ
local notation "P'" => drinfeldTangentProjector ι hL χ ψ' (E.map φ)
local notation "W'" => drinfeldTangentComponent ι hL χ ψ' (E.map φ)

/-- Extending the actual tangent component along a Nilp map gives the new projector image. -/
def drinfeldTangentComponentBaseChange (i : Fin d) :
    letI : Algebra B.obj B'.obj := (φ).toRingHom.toAlgebra
    B'.obj ⊗[B.obj] W i ≃ₗ[B'.obj] W' i := by
  letI : Algebra B.obj B'.obj := (φ).toRingHom.toAlgebra
  apply projectorImageBaseChange (P i) (P' i)
    (drinfeldTangentProjector_mul_same ι hL χ ψ E i)
    (drinfeldTangentProjector_mul_same ι hL χ ψ' (E.map φ) i)
    (coordinateTensorEquiv B.obj B'.obj I)
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul b x =>
    rw [LinearMap.baseChange_tmul, coordinateTensorEquiv_tmul, coordinateTensorEquiv_tmul, map_smul]
    exact congrArg (b • ·) (drinfeldTangentProjector_natural ι hL χ ψ E f i x)
  | add x y hx hy =>
    simp only [map_add, hx, hy]

end Langlands.FormalGroup.LocalDivision
