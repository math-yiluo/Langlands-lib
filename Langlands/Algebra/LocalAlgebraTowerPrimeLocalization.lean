import Langlands.Algebra.LocalAlgebraTowerSystem
import Langlands.Algebra.PrimeLocalizationCriterion

/-! # Prime localization of the composite tower transition -/

open scoped TensorProduct

universe uI uA uB uC uR uS uT

namespace Langlands.Algebra

namespace LocalAlgebraTowerApproximation

attribute [local instance] _root_.Algebra.TensorProduct.rightAlgebra

open _root_.Algebra.TensorProduct in
/-- Pasting of base changes. Suppose `B'` is a localization of `B ⊗[A] A'` through `φ₁` and
`C'` is a local localization of `C ⊗[B] B'` through `φ₂`. Then any ring map
`φ₃ : C ⊗[A] A' → C'` with the corresponding values on pure tensors is the localization of
`C ⊗[A] A'` at the inverse image of the maximal ideal of `C'`. -/
theorem isLocalization_atPrime_tensor_comp
    {A A' B B' C C' : Type*} [CommRing A] [CommRing A'] [CommRing B] [CommRing B']
    [CommRing C] [CommRing C'] [IsLocalRing C']
    [Algebra A A'] [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [Algebra A' B'] [Algebra B B'] [Algebra B' C']
    (hB : ∀ a, algebraMap B B' (algebraMap A B a) = algebraMap A' B' (algebraMap A A' a))
    (fC : C →+* C')
    (φ₁ : B ⊗[A] A' →+* B')
    (hφ₁ : ∀ b a, φ₁ (b ⊗ₜ a) = algebraMap B B' b * algebraMap A' B' a)
    (φ₂ : C ⊗[B] B' →+* C')
    (hφ₂ : ∀ c b, φ₂ (c ⊗ₜ b) = fC c * algebraMap B' C' b)
    (φ₃ : C ⊗[A] A' →+* C')
    (hφ₃ : ∀ c a, φ₃ (c ⊗ₜ a) = fC c * algebraMap B' C' (algebraMap A' B' a))
    (M : Submonoid (B ⊗[A] A')) (N : Submonoid (C ⊗[B] B'))
    (hM : letI := φ₁.toAlgebra; IsLocalization M B')
    (hN : letI := φ₂.toAlgebra; IsLocalization N C') :
    letI := φ₃.toAlgebra
    IsLocalization.AtPrime C' ((IsLocalRing.maximalIdeal C').comap φ₃) := by
  let : Algebra (B ⊗[A] A') B' := φ₁.toAlgebra
  let : Algebra (C ⊗[B] B') C' := φ₂.toAlgebra
  let : Algebra (C ⊗[A] A') C' := φ₃.toAlgebra
  -- The map `B ⊗[A] A' → C ⊗[A] A'`.
  let ψPX : B ⊗[A] A' →ₐ[A] C ⊗[A] A' :=
    map (IsScalarTower.toAlgHom A B C) (AlgHom.id A A')
  let : Algebra (B ⊗[A] A') (C ⊗[A] A') := ψPX.toRingHom.toAlgebra
  have hψPX (b : B) (a : A') :
      algebraMap (B ⊗[A] A') (C ⊗[A] A') (b ⊗ₜ a) = algebraMap B C b ⊗ₜ a := rfl
  -- The map `C ⊗[A] A' → C ⊗[B] B'`.
  let g : A' →ₐ[A] C ⊗[B] B' :=
    { (includeRight : B' →ₐ[B] C ⊗[B] B').toRingHom.comp (algebraMap A' B') with
      commutes' := fun a ↦ by
        change (1 : C) ⊗ₜ[B] algebraMap A' B' (algebraMap A A' a) = _
        rw [← hB, ← tmul_one_eq_one_tmul, IsScalarTower.algebraMap_apply A B (C ⊗[B] B'),
          algebraMap_apply] }
  let ψXY : C ⊗[A] A' →ₐ[A] C ⊗[B] B' :=
    lift (includeLeft (R := B) (S := A)) g fun _ _ ↦ Commute.all _ _
  let : Algebra (C ⊗[A] A') (C ⊗[B] B') := ψXY.toRingHom.toAlgebra
  have hψXY (c : C) (a : A') :
      algebraMap (C ⊗[A] A') (C ⊗[B] B') (c ⊗ₜ a) = c ⊗ₜ algebraMap A' B' a := by
    change ψXY (c ⊗ₜ a) = _
    simp [ψXY, g, lift_tmul, includeLeft_apply, tmul_mul_tmul]
  let : Algebra (B ⊗[A] A') (C ⊗[B] B') :=
    ((algebraMap B' (C ⊗[B] B')).comp φ₁).toAlgebra
  -- The required scalar towers.
  have : IsScalarTower B (B ⊗[A] A') (C ⊗[A] A') := .of_algebraMap_eq fun b ↦ by
    rw [algebraMap_apply, algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, hψPX]
  have : IsScalarTower B (B ⊗[A] A') B' := .of_algebraMap_eq fun b ↦ by
    change _ = φ₁ (algebraMap B (B ⊗[A] A') b)
    rw [algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, hφ₁, map_one, mul_one]
  have : IsScalarTower (B ⊗[A] A') B' (C ⊗[B] B') := .of_algebraMap_eq' rfl
  have : IsScalarTower (B ⊗[A] A') (C ⊗[A] A') (C ⊗[B] B') := .of_algebraMap_eq fun p ↦ by
    induction p with
    | add x y hx hy => rw [map_add, hx, hy, map_add, map_add]
    | tmul b a =>
      change (1 : C) ⊗ₜ[B] φ₁ (b ⊗ₜ a) = _
      rw [hψPX, hψXY, hφ₁, ← mul_one (algebraMap B C b), ← one_mul (algebraMap A' B' a),
        ← tmul_mul_tmul, tmul_one_eq_one_tmul, tmul_mul_tmul, one_mul, mul_one]
  have : IsScalarTower B (C ⊗[A] A') (C ⊗[B] B') := .of_algebraMap_eq fun b ↦ by
    rw [algebraMap_apply, algebraMap_apply, hψXY, map_one]
  have : IsScalarTower C (C ⊗[A] A') (C ⊗[B] B') := .of_algebraMap_eq fun c ↦ by
    rw [algebraMap_apply, algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      hψXY, map_one]
  have : IsScalarTower (C ⊗[A] A') (C ⊗[B] B') C' := .of_algebraMap_eq fun x ↦ by
    change φ₃ x = φ₂ (algebraMap (C ⊗[A] A') (C ⊗[B] B') x)
    induction x with
    | add x y hx hy => rw [map_add, hx, hy, map_add, map_add]
    | tmul c a => rw [hψXY, hφ₂, hφ₃]
  -- Pasting the pushout squares.
  have : _root_.Algebra.IsPushout B C (B ⊗[A] A') (C ⊗[A] A') :=
    _root_.Algebra.IsPushout.tensorProduct_tensorProduct A A' B C (by ext a; simp [hψPX])
  have : _root_.Algebra.IsPushout B (B ⊗[A] A') C (C ⊗[A] A') :=
    _root_.Algebra.IsPushout.symm inferInstance
  have hpush : _root_.Algebra.IsPushout (B ⊗[A] A') B' (C ⊗[A] A') (C ⊗[B] B') :=
    (_root_.Algebra.IsPushout.comp_iff B (B ⊗[A] A') C (C ⊗[A] A')).mp inferInstance
  have := hM
  have := hN
  have : IsLocalization (_root_.Algebra.algebraMapSubmonoid (C ⊗[A] A') M) (C ⊗[B] B') :=
    (_root_.Algebra.isLocalization_iff_isPushout M B').mpr hpush.symm
  have := IsLocalization.localization_localization_isLocalization
    (_root_.Algebra.algebraMapSubmonoid (C ⊗[A] A') M) N C'
  exact isLocalization_atPrime_of_local_target
    (IsLocalization.localizationLocalizationSubmodule
      (_root_.Algebra.algebraMapSubmonoid (C ⊗[A] A') M) N)

end LocalAlgebraTowerApproximation

namespace LocalAlgebraTowerSystem

variable {ι : Type uI} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
  {R : Type uR} {S : Type uS} {T : Type uT} [CommRing R] [CommRing S] [CommRing T]
  [IsLocalRing R] [IsLocalRing S] [IsLocalRing T]
  [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
  [IsLocalHom (algebraMap R S)] [IsLocalHom (algebraMap S T)]

/-- In any synchronized tower, prime localization of a lower transition and of the
corresponding upper transition gives prime localization of the composite transition. -/
theorem rt_isPrimeLocalization (D : LocalAlgebraTowerSystem.{uI, uA, uB, uC} ι R S T)
    {i j : ι} (h : i ≤ j) (hrs : D.rs.IsPrimeLocalization h)
    (hst : D.st.IsPrimeLocalization h) :
    letI := composite_local R S T
    D.rt.IsPrimeLocalization h := by
  let := composite_local R S T
  obtain ⟨p, hp, hpl⟩ := hrs
  obtain ⟨q, hq, hql⟩ := hst
  let := (D.rs.baseMap i j h).toAlgebra
  let := (D.rs.algMap i j h).toAlgebra
  let := (D.rt.ringBaseChangeMap h).toAlgebra
  refine ⟨(IsLocalRing.maximalIdeal (D.top j)).comap (D.rt.ringBaseChangeMap h),
    Ideal.IsPrime.comap _, ?_⟩
  exact LocalAlgebraTowerApproximation.isLocalization_atPrime_tensor_comp
    (A := D.rs.base i) (A' := D.rs.base j) (B := D.rs.alg i) (B' := D.rs.alg j)
    (C := D.top i) (C' := D.top j)
    (fun a ↦ D.rs.map_comm i j h a) (D.topMap i j h)
    (D.rs.ringBaseChangeMap h) (fun _ _ ↦ rfl)
    (D.st.ringBaseChangeMap h) (fun _ _ ↦ rfl)
    (D.rt.ringBaseChangeMap h) (fun _ _ ↦ rfl)
    p.primeCompl q.primeCompl hpl hql

end LocalAlgebraTowerSystem

end Langlands.Algebra
