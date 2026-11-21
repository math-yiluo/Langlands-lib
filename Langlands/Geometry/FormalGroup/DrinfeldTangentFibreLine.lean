import Langlands.Geometry.FormalGroup.DrinfeldTangentUniformizer

/-! # Geometric rank one of the actual Drinfeld tangent components -/

noncomputable section

namespace Langlands.FormalGroup.LocalDivision

open IsLocalRing ValuativeRel CentralDivision CentralSimple ModuleLaw CategoryTheory

universe u v s

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] (ι : L →ₐ[K] D)

local instance tangentFibreLineLocalHom : IsLocalHom (algebraMap 𝒪[K] (SubfieldIntegerRing K D ι)) :=
  subfieldIntegerAlgebra_isLocalHom ι

variable {κ : Type u} [Field κ] [Algebra 𝒪[K] κ] [Algebra 𝓀[K] κ]
  [IsScalarTower 𝒪[K] 𝓀[K] κ]
variable (χ : ResidueField (SubfieldIntegerRing K D ι) →ₐ[𝓀[K]] κ)
variable {π : 𝒪[K]}

section FibreDecomposition

variable {B : Nilp.{u, v} 𝒪[K] π} [IsDomain B.obj]
variable (ψ : κ →ₐ[𝒪[K]] Nilp.Reduction π B.obj) (Y : SpecialModule K D ι B.obj)

local notation "C" => SubfieldIntegerRing K D ι
local notation "d" => CentralSimple.reducedDegree K D
local notation "V" => (Fin d → B.obj)
local notation "iC" => subfieldIntegerInclusion K D ι
local notation "P" => drinfeldTangentProjector ι Y.unramified χ ψ Y.order
local notation "W" => drinfeldTangentComponent ι Y.unramified χ ψ Y.order
local notation "θ" => (fun i : Fin d => subfieldCoefficientLift Y.unramified
  (subfieldCyclicCharacter ι Y.unramified χ i) ψ)

private def tangentLineOfDecomposition
    (dec : Y.order.TangentCharacterDecomposition (iC).toRingHom d (RingHom.id B.obj))
    (i : Fin d) : W i ≃ₗ[B.obj] B.obj := by
  classical
  have geom_character (j k : Fin d) (x : V) (hx : x ∈ W j)
      (hnz : dec.coordinates x k ≠ 0) : dec.characters k = (θ j).toRingHom := by
    apply RingHom.ext
    intro a
    have he := (mem_drinfeldTangentComponent_iff ι χ ψ Y.unramified Y.order j x).mp hx a
    have hc := congrArg (fun w : V => dec.coordinates w k) he
    change dec.coordinates (Y.order.fiberTangent (RingHom.id B.obj) ((iC).toRingHom a) x) k =
      dec.coordinates (θ j a • x) k at hc
    rw [dec.diagonalizes a x k, map_smul, Pi.smul_apply, smul_eq_mul] at hc
    exact mul_right_cancel₀ hnz hc
  have match_character (k : Fin d) : ∃ j, dec.characters k = (θ j).toRingHom := by
    let x := dec.coordinates.symm (Pi.single k 1)
    have hx : (∑ j : Fin d, (P j x : V)) = x := by
      rw [← LinearMap.sum_apply,
        sum_drinfeldTangentProjector ι Y.unramified χ ψ Y.order]
      rfl
    have hsum' : (∑ j : Fin d, dec.coordinates (P j x) k) = 1 := by
      have hsum := congrArg (fun w : V => dec.coordinates w k) hx
      change dec.coordinates (∑ j : Fin d, (P j x : V)) k = dec.coordinates x k at hsum
      rw [map_sum, Finset.sum_apply] at hsum
      simpa only [x, LinearEquiv.apply_symm_apply, Pi.single_eq_same] using hsum
    have hne : (∑ j : Fin d, dec.coordinates (P j x) k) ≠ 0 := hsum'.trans_ne one_ne_zero
    obtain ⟨j, _, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    exact ⟨j, geom_character j k (P j x) ⟨x, rfl⟩ hj⟩
  choose index hindex using match_character
  have hinj : Function.Injective index := by
    intro k l hkl
    apply dec.distinct
    rw [hindex k, hindex l, hkl]
  let match_i := Finite.surjective_of_injective hinj i
  let k := match_i.choose
  have hk : index k = i := match_i.choose_spec
  have hχ : dec.characters k = (θ i).toRingHom := by rw [hindex, hk]
  let insert (a : B.obj) : W i := ⟨dec.coordinates.symm (Pi.single k a), by
    apply (mem_drinfeldTangentComponent_iff ι χ ψ Y.unramified Y.order i _).mpr
    intro b
    apply dec.coordinates.injective
    funext j
    change dec.coordinates (Y.order.fiberTangent (RingHom.id B.obj) ((iC).toRingHom b)
      (dec.coordinates.symm (Pi.single k a))) j =
      dec.coordinates (θ i b • dec.coordinates.symm (Pi.single k a)) j
    rw [dec.diagonalizes b (dec.coordinates.symm (Pi.single k a)) j, map_smul, Pi.smul_apply,
      smul_eq_mul, LinearEquiv.apply_symm_apply]
    by_cases hj : j = k
    · subst j
      rw [hχ]
      rfl
    · simp [Pi.single_eq_of_ne hj]⟩
  exact
    { toFun := fun x => dec.coordinates x.val k
      invFun := insert
      left_inv := fun x => by
        apply Subtype.ext
        apply dec.coordinates.injective
        funext j
        change dec.coordinates (dec.coordinates.symm (Pi.single k (dec.coordinates x.val k))) j = _
        rw [LinearEquiv.apply_symm_apply]
        by_cases hj : j = k
        · subst j; exact Pi.single_eq_same _ _
        · have hz : dec.coordinates x.val j = 0 := by
            by_contra hne
            exact hj (dec.distinct ((geom_character i j x.val x.property hne).trans hχ.symm))
          rw [Pi.single_eq_of_ne hj, hz]
      right_inv := fun a => by
        change dec.coordinates (dec.coordinates.symm (Pi.single k a)) k = _
        rw [LinearEquiv.apply_symm_apply, Pi.single_eq_same]
      map_add' := fun x y => by
        change dec.coordinates (x.val + y.val) k = _
        rw [map_add]
        rfl
      map_smul' := fun a x => by
        change dec.coordinates (a • x.val) k = _
        rw [map_smul]
        rfl }

end FibreDecomposition

variable {S : Type (max u v)} [Field S] [Algebra 𝒪[K] S] [IsAlgClosed S]
variable (hπS : IsNilpotent (algebraMap 𝒪[K] S π))
variable (ψ : κ →ₐ[𝒪[K]] Nilp.Reduction π (Nilp.of 𝒪[K] π S hπS).obj)
variable (Y : SpecialModule K D ι (Nilp.of 𝒪[K] π S hπS).obj)

local notation "d" => CentralSimple.reducedDegree K D
local notation "testField" => Nilp.of 𝒪[K] π S hπS
local notation "W" => drinfeldTangentComponent ι (B := testField) Y.unramified χ ψ Y.order

/-- The actual projector image over an algebraically closed test field is a line. -/
def drinfeldTangentFibreLine (i : Fin d) : W i ≃ₗ[(testField).obj] (testField).obj := by
  let : IsDomain (testField).obj := inferInstanceAs (IsDomain S)
  exact tangentLineOfDecomposition ι χ ψ Y (Y.tangent S (RingHom.id S)).some i

/-- Geometric specialness supplies dimension one for every actual character component. -/
theorem drinfeldTangentFibreLine_finrank (i : Fin d) : Module.finrank (testField).obj (W i) = 1 := by
  let : Nontrivial (testField).obj := inferInstanceAs (Nontrivial S)
  exact (drinfeldTangentFibreLine ι χ hπS ψ Y i).finrank_eq.trans (Module.finrank_self (testField).obj)

end Langlands.FormalGroup.LocalDivision
