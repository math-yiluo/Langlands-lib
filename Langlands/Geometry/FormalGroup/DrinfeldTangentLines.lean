import Langlands.Geometry.FormalGroup.DrinfeldTangentGrading
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-! # The homogeneous tangent lines of a Drinfeld special module -/

noncomputable section

open scoped BigOperators TensorProduct

namespace Langlands.FormalGroup.LocalDivision

open CategoryTheory ValuativeRel CentralDivision

universe u v s

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] {ι : L →ₐ[K] D}
variable {κ : Type u} [Field κ] [Algebra 𝒪[K] κ] [Algebra 𝓀[K] κ]
  [IsScalarTower 𝒪[K] 𝓀[K] κ]
variable {π : 𝒪[K]} {B : Nilp.{u, v} 𝒪[K] π}

local instance : IsLocalHom (algebraMap 𝒪[K] (SubfieldIntegerRing K D ι)) :=
  subfieldIntegerAlgebra_isLocalHom ι

local notation "d" => CentralSimple.reducedDegree K D
local notation "C" => SubfieldIntegerRing K D ι

namespace SpecialModule

section TestAlgebra

variable (X : SpecialModule K D ι B.obj)
  (j : IsLocalRing.ResidueField (SubfieldIntegerRing K D ι) →ₐ[𝓀[K]] κ)
  (ψ : κ →ₐ[𝒪[K]] Nilp.Reduction π B.obj)

private theorem tangentProjector_isProj (i : Fin d) :
    LinearMap.IsProj (X.tangentComponent j ψ i) (X.tangentProjector j ψ i) :=
  (LinearMap.isProj_range_iff_isIdempotentElem _).2 (X.tangentProjector_idempotent j ψ i)

instance tangentComponent_finite (i : Fin d) :
    Module.Finite B.obj (X.tangentComponent j ψ i) :=
  Module.Finite.range (X.tangentProjector j ψ i)

instance tangentComponent_projective (i : Fin d) :
    Module.Projective B.obj (X.tangentComponent j ψ i) := by
  let h := X.tangentProjector_isProj j ψ i
  exact Module.Projective.of_split (X.tangentComponent j ψ i).subtype h.codRestrict
    (LinearMap.ext h.codRestrict_apply_cod)

/-- Extending scalars on a tangent component gives the corresponding component after base change. -/
def tangentComponentBaseChange {B' : Nilp.{u, v} 𝒪[K] π} [Algebra B.obj B'.obj]
    [IsScalarTower 𝒪[K] B.obj B'.obj] (i : Fin d) :
    let θ := IsScalarTower.toAlgHom 𝒪[K] B.obj B'.obj
    B'.obj ⊗[B.obj] X.tangentComponent j ψ i ≃ₗ[B'.obj]
      (X.mapSameUniverse θ).tangentComponent j ((Nilp.reductionMap θ).comp ψ) i := by
  let θ := IsScalarTower.toAlgHom 𝒪[K] B.obj B'.obj
  let f : B ⟶ B' := ObjectProperty.homMk (CommAlgCat.ofHom θ)
  let P := X.tangentProjector j ψ i
  let Q := (X.mapSameUniverse θ).tangentProjector j ((Nilp.reductionMap θ).comp ψ) i
  let e := TensorProduct.piScalarRight B.obj B'.obj B'.obj (Fin d)
  have he (b : B'.obj) (x : Fin d → B.obj) :
      e (b ⊗ₜ[B.obj] x) = b • (fun k => θ (x k)) := by
    rw [show e = TensorProduct.piScalarRight B.obj B'.obj B'.obj (Fin d) from rfl,
      TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
    funext k
    change x k • b = b * θ (x k)
    rw [Algebra.smul_def]
    exact mul_comm (θ (x k)) b
  have hcomm : Q.comp e.toLinearMap = e.toLinearMap.comp (P.baseChange B'.obj) := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro b x
    change Q (e (b ⊗ₜ[B.obj] x)) = e ((P.baseChange B'.obj) (b ⊗ₜ[B.obj] x))
    rw [LinearMap.baseChange_tmul, he, he, map_smul]
    apply congrArg (b • ·)
    funext k
    exact X.tangentProjector_natural j ψ f i x k
  let h := X.tangentProjector_isProj j ψ i
  let incl := (X.tangentComponent j ψ i).subtype
  let proj := h.codRestrict
  have hsplit : proj.comp incl = LinearMap.id := LinearMap.ext h.codRestrict_apply_cod
  have hincl : (proj.baseChange B'.obj).comp (incl.baseChange B'.obj) = LinearMap.id := by
    rw [← LinearMap.baseChange_comp, hsplit, LinearMap.baseChange_id]
  have hinv : Function.LeftInverse (proj.baseChange B'.obj) (incl.baseChange B'.obj) :=
    fun x => LinearMap.congr_fun hincl x
  let g := e.toLinearMap.comp (incl.baseChange B'.obj)
  have hginj : Function.Injective g := e.injective.comp hinv.injective
  have hgcomp : g.comp (proj.baseChange B'.obj) = Q.comp e.toLinearMap := by
    change (e.toLinearMap.comp (incl.baseChange B'.obj)).comp (proj.baseChange B'.obj) = _
    rw [LinearMap.comp_assoc, ← LinearMap.baseChange_comp, h.subtype_comp_codRestrict]
    exact hcomm.symm
  have hgrange : LinearMap.range g = LinearMap.range Q := by
    rw [← LinearMap.range_comp_of_range_eq_top g (LinearMap.range_eq_top.mpr hinv.surjective), hgcomp,
      LinearMap.range_comp_of_range_eq_top _ e.range]
  exact (LinearEquiv.ofInjective g hginj).trans (LinearEquiv.ofEq _ _ hgrange)

end TestAlgebra

private theorem exists_eval_of_pi {F : Type*} [Field F] {n : ℕ}
    (g : (Fin n → F) →ₐ[F] F) : ∃ k, ∀ x, g x = x k := by
  have hsum : ∑ k, g (Pi.single k 1) = 1 := by
    rw [← map_sum, show ∑ k, Pi.single k (1 : F) = (1 : Fin n → F) from
      Finset.univ_sum_single (1 : Fin n → F), map_one]
  obtain ⟨k, hk⟩ : ∃ k, g (Pi.single k 1) ≠ 0 := by
    by_contra! h
    simp [h] at hsum
  refine ⟨k, fun x => ?_⟩
  have h : x * Pi.single k 1 = algebraMap F (Fin n → F) (x k) * Pi.single k 1 := by
    rw [← Pi.single_mul_right, ← Pi.single_mul_right]
    rfl
  have hg := congrArg g h
  simp only [map_mul, AlgHom.commutes, Algebra.algebraMap_self_apply] at hg
  exact mul_right_cancel₀ hk hg

section GeometricPoint

variable {F : Type (max u v)} [Field F] [IsAlgClosed F] [Algebra 𝒪[K] F]
  (hπ : IsNilpotent (algebraMap 𝒪[K] F π))

private abbrev geometricNilp : Nilp.{u, max u v} 𝒪[K] π :=
  ⟨CommAlgCat.of 𝒪[K] F, hπ⟩

local notation "BF" => geometricNilp hπ

/-- Each projector image over an algebraically closed test field is a line. -/
def tangentComponentGeometricEquiv
    (X : SpecialModule K D ι F)
    (j : IsLocalRing.ResidueField (SubfieldIntegerRing K D ι) →ₐ[𝓀[K]] κ)
    (ψ : κ →ₐ[𝒪[K]] Nilp.Reduction π (BF).obj) (i : Fin d) :
    X.tangentComponent (B := BF) j ψ i ≃ₗ[F] F := by
  let h := (X.tangent F (RingHom.id F)).some
  let χ (k : Fin d) : C →ₐ[𝒪[K]] F :=
    { toRingHom := h.characters k
      commutes' a := h.character_scalar ((subfieldIntegerInclusion K D ι).commutes a) k }
  let ev := subfieldCyclicSplitting (B := BF) X.unramified j ψ
  let extend (k : Fin d) := AlgHom.liftEquiv 𝒪[K] F C F (χ k)
  let g (k : Fin d) : (Fin d → F) →ₐ[F] F := (extend k).comp ev.symm.toAlgHom
  choose p hp using fun k => exists_eval_of_pi (g k)
  have heval (l : Fin d) (a : C) :
      h.characters l a = ev (1 ⊗ₜ[𝒪[K]] a) (p l) := by
    have hl := hp l (ev (1 ⊗ₜ[𝒪[K]] a))
    change extend l (ev.symm (ev (1 ⊗ₜ[𝒪[K]] a))) = _ at hl
    rw [ev.symm_apply_apply] at hl
    change χ l a = _
    simpa only [extend, AlgHom.liftEquiv_tmul, one_smul] using hl
  have hp_injective : Function.Injective p := by
    intro k l hkl
    apply h.distinct
    apply RingHom.ext
    intro a
    rw [heval k, heval l, hkl]
  have hi := Finite.surjective_of_injective hp_injective i
  let k := hi.choose
  have hk : p k = i := hi.choose_spec
  have hdiag (t : F ⊗[𝒪[K]] C) (x : Fin d → F) (l : Fin d) :
      h.coordinates (X.subfieldTangentTensor (B := BF) t x) l =
        extend l t * h.coordinates x l := by
    induction t using TensorProduct.inductionOn with
    | tmul b a =>
      calc
        _ = h.coordinates (b • X.subfieldTangent (B := BF) a x) l :=
          congrArg (fun z => h.coordinates z l) (X.subfieldTangentTensor_tmul (B := BF) b a x)
        _ = _ := by
          change h.coordinates
            (b • X.order.fiberTangent (RingHom.id F) ((subfieldIntegerInclusion K D ι).toRingHom a) x)
            l = _
          rw [map_smul, Pi.smul_apply, h.diagonalizes]
          change b * (h.characters l a * h.coordinates x l) =
            (b * h.characters l a) * h.coordinates x l
          exact (mul_assoc _ _ _).symm
    | add t₁ t₂ h₁ h₂ =>
      simp only [map_add, LinearMap.add_apply, Pi.add_apply, h₁, h₂, add_mul]
  have hproj (x : Fin d → F) (l : Fin d) :
      h.coordinates (X.tangentProjector (B := BF) j ψ i x) l =
        (Pi.single i 1 : Fin d → F) (p l) * h.coordinates x l := by
    change h.coordinates (X.subfieldTangentTensor (B := BF) (ev.symm (Pi.single i 1)) x) l = _
    rw [hdiag]
    exact congrArg (· * h.coordinates x l) (hp l (Pi.single i 1))
  have hzero (x : X.tangentComponent (B := BF) j ψ i) (l : Fin d) (hl : l ≠ k) :
      h.coordinates x l = 0 := by
    have hfix := (X.mem_tangentComponent_iff_fixed (B := BF) j ψ i x).1 x.2
    have hne : p l ≠ i := fun e => hl (hp_injective (e.trans hk.symm))
    simpa only [hfix, Pi.single_eq_of_ne hne, zero_mul] using hproj x l
  refine
    { toFun := fun x => h.coordinates x k
      map_add' := fun x y => by simp
      map_smul' := fun a x => by simp
      invFun := fun a => ⟨h.coordinates.symm (Pi.single k a), ?_⟩
      left_inv := ?_
      right_inv := fun a => by simp }
  · apply (X.mem_tangentComponent_iff_fixed (B := BF) j ψ i _).2
    apply h.coordinates.injective
    funext l
    rw [hproj, h.coordinates.apply_symm_apply]
    by_cases hl : l = k
    · subst l
      simp [hk]
    · simp [Pi.single_eq_of_ne hl]
  · intro x
    apply Subtype.ext
    apply h.coordinates.injective
    funext l
    change h.coordinates (h.coordinates.symm (Pi.single k (h.coordinates x k))) l = _
    rw [h.coordinates.apply_symm_apply]
    by_cases hl : l = k
    · subst l
      simp
    · rw [Pi.single_eq_of_ne hl, hzero x l hl]

end GeometricPoint

section RankAtStalk

variable {A : Nilp.{u, u} 𝒪[K] π}

/-- The homogeneous tangent component has rank one at every prime. -/
theorem tangentComponent_rankAtStalk (X : SpecialModule K D ι A.obj)
    (j : IsLocalRing.ResidueField (SubfieldIntegerRing K D ι) →ₐ[𝓀[K]] κ)
    (ψ : κ →ₐ[𝒪[K]] Nilp.Reduction π A.obj) (i : Fin d) (p : PrimeSpectrum A.obj) :
    Module.rankAtStalk (X.tangentComponent j ψ i) p = 1 := by
  let F := AlgebraicClosure p.asIdeal.ResidueField
  let θ := IsScalarTower.toAlgHom 𝒪[K] A.obj F
  have hπ : IsNilpotent (algebraMap 𝒪[K] F π) := θ.commutes π ▸ A.nilpotent.map θ
  let A' : Nilp.{u, u} 𝒪[K] π := geometricNilp hπ
  let ψ' := (Nilp.reductionMap (A := A.obj) (B := A'.obj) θ).comp ψ
  let e := (X.tangentComponentBaseChange j ψ (B' := A') i).trans
    (tangentComponentGeometricEquiv hπ (X.mapSameUniverse θ) j ψ' i)
  let q : PrimeSpectrum F := ⟨⊥, inferInstance⟩
  have hq : q.comap (algebraMap A.obj F) = p := by
    apply PrimeSpectrum.ext
    ext x
    change (algebraMap A.obj F x ∈ (⊥ : Ideal F)) ↔ x ∈ p.asIdeal
    rw [Ideal.mem_bot, IsScalarTower.algebraMap_apply A.obj p.asIdeal.ResidueField F,
      map_eq_zero_iff _ (RingHom.injective _), Ideal.algebraMap_residueField_eq_zero]
  have h := congrFun (Module.rankAtStalk_eq_of_equiv e) q
  rw [Module.rankAtStalk_baseChange, hq, Module.rankAtStalk_self, Pi.one_apply] at h
  exact h

end RankAtStalk

end SpecialModule

end Langlands.FormalGroup.LocalDivision
