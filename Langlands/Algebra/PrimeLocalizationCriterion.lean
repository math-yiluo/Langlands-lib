import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Localization.BaseChange

universe u v w x y z

namespace Langlands.Algebra

/-- A local target is the localization at the inverse image of its maximal ideal
when fractions exist and every element of the kernel is annihilated by a denominator. -/
theorem isLocalization_atPrime_of_fractions
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [IsLocalRing B]
    [Algebra A B]
    (hsurj : ∀ b : B, ∃ a s : A, IsUnit (algebraMap A B s) ∧ b * algebraMap A B s = algebraMap A B a)
    (hker : ∀ a : A, algebraMap A B a = 0 → ∃ s : A, IsUnit (algebraMap A B s) ∧ s * a = 0) :
    IsLocalization.AtPrime B ((IsLocalRing.maximalIdeal B).comap (algebraMap A B)) := by
  let p : Ideal A := (IsLocalRing.maximalIdeal B).comap (algebraMap A B)
  have hunit (s : A) : s ∈ p.primeCompl ↔ IsUnit (algebraMap A B s) := by
    simp [p, Ideal.mem_primeCompl_iff, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff]
  change IsLocalization p.primeCompl B
  rw [isLocalization_iff]
  refine ⟨fun s ↦ (hunit s).mp s.prop, ?_, ?_⟩
  · intro b
    obtain ⟨a, s, hs, h⟩ := hsurj b
    exact ⟨⟨a, ⟨s, (hunit s).mpr hs⟩⟩, h⟩
  · intro x y hxy
    obtain ⟨s, hs, h⟩ := hker (x - y) (by simpa using sub_eq_zero.mpr hxy)
    exact ⟨⟨s, (hunit s).mpr hs⟩, sub_eq_zero.mp (by simpa [mul_sub] using h)⟩

/-- Any localization with a local target is localization at the contracted maximal ideal. -/
theorem isLocalization_atPrime_of_local_target
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [IsLocalRing B]
    [Algebra A B] (M : Submonoid A) [IsLocalization M B] :
    IsLocalization.AtPrime B ((IsLocalRing.maximalIdeal B).comap (algebraMap A B)) := by
  apply isLocalization_atPrime_of_fractions
  · intro b
    obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.surj M b
    exact ⟨a, s, IsLocalization.map_units B s, h⟩
  · intro a ha
    obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff M B a).mp ha
    exact ⟨s, IsLocalization.map_units B s, hs⟩

/-- Two localizations of a common ring with a compatible map form a prime-localization
map whenever the final target is local. The supplied algebra structure is preserved. -/
theorem isLocalization_atPrime_of_common_localization
    {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C] [IsLocalRing C]
    [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
    (M N : Submonoid A) [IsLocalization M B] [IsLocalization N C] :
    IsLocalization.AtPrime C ((IsLocalRing.maximalIdeal C).comap (algebraMap B C)) := by
  let p : Ideal A := (IsLocalRing.maximalIdeal C).comap (algebraMap A C)
  let : IsLocalization.AtPrime C p := isLocalization_atPrime_of_local_target N
  have hle : M ≤ p.primeCompl := by
    intro s hs
    change algebraMap A C s ∉ IsLocalRing.maximalIdeal C
    have hu : IsUnit (algebraMap A C s) := by
      rw [IsScalarTower.algebraMap_apply A B C]
      exact (IsLocalization.map_units B ⟨s, hs⟩).map (algebraMap B C)
    simpa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hu
  let := IsLocalization.isLocalization_of_submonoid_le M p.primeCompl hle
    (S := B) (T := C)
  exact isLocalization_atPrime_of_local_target (p.primeCompl.map (algebraMap A B))

open scoped TensorProduct

attribute [local instance] _root_.Algebra.TensorProduct.rightAlgebra

section TensorPushoutMap

variable {A : Type u} {B : Type v} {Q : Type w} {Q' : Type x} {L : Type y}
    [CommRing A] [CommRing B] [CommRing Q] [CommRing Q'] [CommRing L]
    [Algebra A B] [Algebra A Q] [Algebra A Q'] [Algebra Q Q'] [Algebra B Q']
    [IsScalarTower A Q Q'] [IsScalarTower A B Q']
    [_root_.Algebra.IsPushout A Q B Q']
    [Algebra A L] [Algebra Q L] [IsScalarTower A Q L]

/-- The canonical map from a pushout to a tensor product after extending the first factor. -/
noncomputable def tensorPushoutMap : Q' →ₐ[B] (L ⊗[A] B) :=
  { _root_.Algebra.pushoutDesc Q'
      ((_root_.Algebra.TensorProduct.includeLeft (R := A) (S := A) (B := B)).comp
        (IsScalarTower.toAlgHom A Q L))
      (_root_.Algebra.TensorProduct.includeRight (R := A) (A := L))
      (fun _ _ ↦ mul_comm _ _) with
    commutes' := fun b ↦ _root_.Algebra.pushoutDesc_right _ _ _ _ b }

/-- Compatibility of the canonical pushout map with the original algebra. -/
theorem tensorPushoutMap_comp :
    (tensorPushoutMap (A := A) (B := B) (Q := Q) (Q' := Q') (L := L)).toRingHom.comp
      (algebraMap Q Q') =
    (_root_.Algebra.TensorProduct.includeLeftRingHom (R := A) (B := B)).comp
      (algebraMap Q L) := by
  ext q
  simp [tensorPushoutMap, _root_.Algebra.pushoutDesc_left]

/-- A ring map out of the tensor product agrees with a map out of the pushout
when they agree on the original quotient and the new base ring. -/
theorem comp_tensorPushoutMap
    {C : Type z} [CommRing C]
    (f : L ⊗[A] B →+* C) (g : Q' →+* C)
    (hfQ : (f.comp (_root_.Algebra.TensorProduct.includeLeftRingHom
        (R := A) (B := B))).comp (algebraMap Q L) =
      g.comp (algebraMap Q Q'))
    (hfB : f.comp (_root_.Algebra.TensorProduct.includeRight
        (R := A) (A := L)).toRingHom =
      g.comp (algebraMap B Q')) :
    f.comp (tensorPushoutMap (A := A) (B := B) (Q := Q) (Q' := Q')
      (L := L)).toRingHom = g := by
  let ψ := tensorPushoutMap (A := A) (B := B) (Q := Q) (Q' := Q') (L := L)
  have hq (q : Q) : ψ (algebraMap Q Q' q) =
      _root_.Algebra.TensorProduct.includeLeftRingHom (algebraMap Q L q) :=
    DFunLike.congr_fun tensorPushoutMap_comp q
  have hb (b : B) : ψ (algebraMap B Q' b) =
      _root_.Algebra.TensorProduct.includeRight b := ψ.commutes b
  ext x
  obtain ⟨t, rfl⟩ := (_root_.Algebra.IsPushout.equiv A Q B Q').surjective x
  induction t with
  | add x y hx hy =>
    simpa only [map_add, RingHom.comp_apply] using congrArg₂ (· + ·) hx hy
  | tmul q b =>
    change f (ψ ((_root_.Algebra.IsPushout.equiv A Q B Q') (q ⊗ₜ[A] b))) =
      g ((_root_.Algebra.IsPushout.equiv A Q B Q') (q ⊗ₜ[A] b))
    rw [_root_.Algebra.IsPushout.equiv_tmul, map_mul, map_mul, hq, hb, map_mul]
    exact congrArg₂ (· * ·) (DFunLike.congr_fun hfQ q) (DFunLike.congr_fun hfB b)

end TensorPushoutMap

/-- Base change of a localization through a supplied pushout. The algebra structure
on the tensor product is induced by the given compatible map `ψ`. -/
theorem isLocalization_tensor_of_isPushout
    {A : Type u} {B : Type v} {Q : Type w} {Q' : Type x} {L : Type y}
    [CommRing A] [CommRing B] [CommRing Q] [CommRing Q'] [CommRing L]
    [Algebra A B] [Algebra A Q] [Algebra A Q'] [Algebra Q Q'] [Algebra B Q']
    [IsScalarTower A Q Q'] [IsScalarTower A B Q']
    [_root_.Algebra.IsPushout A Q B Q']
    [Algebra A L] [Algebra Q L] [IsScalarTower A Q L]
    (M : Submonoid Q) [IsLocalization M L]
    (ψ : Q' →ₐ[B] (L ⊗[A] B))
    (hψ : ψ.toRingHom.comp (algebraMap Q Q') =
      (_root_.Algebra.TensorProduct.includeLeftRingHom (R := A) (B := B)).comp (algebraMap Q L)) :
    letI := ψ.toAlgebra
    IsLocalization (M.map (algebraMap Q Q')) (L ⊗[A] B) := by
  let : Algebra Q' (L ⊗[A] B) := ψ.toAlgebra
  have : IsScalarTower Q L (L ⊗[A] B) := inferInstance
  have : IsScalarTower Q Q' (L ⊗[A] B) := .of_algebraMap_eq' hψ.symm
  have : IsScalarTower B Q' (L ⊗[A] B) :=
    .of_algebraMap_eq fun b ↦ (ψ.commutes b).symm
  have : IsScalarTower A Q' (L ⊗[A] B) := .to₁₃₄ _ B _ _
  have : _root_.Algebra.IsPushout Q L Q' (L ⊗[A] B) :=
    (_root_.Algebra.IsPushout.comp_iff A Q B Q').mp inferInstance
  exact (_root_.Algebra.isLocalization_iff_isPushout M L).mpr
    (_root_.Algebra.IsPushout.symm inferInstance)

/-- A compatible actual map from the tensor base change to a local localization
of the later quotient is localization at the inverse image of the maximal ideal. -/
theorem isLocalization_atPrime_tensor_of_isPushout
    {A : Type u} {B : Type v} {Q : Type w} {Q' : Type x}
    {L : Type y} {C : Type z}
    [CommRing A] [CommRing B] [CommRing Q] [CommRing Q'] [CommRing L] [CommRing C]
    [IsLocalRing C]
    [Algebra A B] [Algebra A Q] [Algebra A Q'] [Algebra Q Q'] [Algebra B Q']
    [IsScalarTower A Q Q'] [IsScalarTower A B Q']
    [_root_.Algebra.IsPushout A Q B Q']
    [Algebra A L] [Algebra Q L] [IsScalarTower A Q L] [Algebra Q' C]
    (M : Submonoid Q) (N : Submonoid Q') [IsLocalization M L] [IsLocalization N C]
    (ψ : Q' →ₐ[B] (L ⊗[A] B))
    (hψ : ψ.toRingHom.comp (algebraMap Q Q') =
      (_root_.Algebra.TensorProduct.includeLeftRingHom (R := A) (B := B)).comp
        (algebraMap Q L))
    (f : L ⊗[A] B →+* C) (hf : f.comp ψ.toRingHom = algebraMap Q' C) :
    letI := f.toAlgebra
    IsLocalization.AtPrime C ((IsLocalRing.maximalIdeal C).comap f) := by
  let : Algebra Q' (L ⊗[A] B) := ψ.toAlgebra
  have : IsLocalization (M.map (algebraMap Q Q')) (L ⊗[A] B) :=
    isLocalization_tensor_of_isPushout M ψ hψ
  let : Algebra (L ⊗[A] B) C := f.toAlgebra
  have : IsScalarTower Q' (L ⊗[A] B) C := .of_algebraMap_eq' hf.symm
  exact isLocalization_atPrime_of_common_localization (M.map (algebraMap Q Q')) N

/-- The tensor prime-localization criterion using the canonical pushout map.
It suffices to check the actual map on the original quotient and the new base ring. -/
theorem isLocalization_atPrime_tensor_of_isPushout_canonical
    {A : Type u} {B : Type v} {Q : Type w} {Q' : Type x}
    {L : Type y} {C : Type z}
    [CommRing A] [CommRing B] [CommRing Q] [CommRing Q'] [CommRing L] [CommRing C]
    [IsLocalRing C]
    [Algebra A B] [Algebra A Q] [Algebra A Q'] [Algebra Q Q'] [Algebra B Q']
    [IsScalarTower A Q Q'] [IsScalarTower A B Q']
    [_root_.Algebra.IsPushout A Q B Q']
    [Algebra A L] [Algebra Q L] [IsScalarTower A Q L] [Algebra Q' C]
    (M : Submonoid Q) (N : Submonoid Q') [IsLocalization M L] [IsLocalization N C]
    (f : L ⊗[A] B →+* C)
    (hfQ : (f.comp (_root_.Algebra.TensorProduct.includeLeftRingHom
        (R := A) (B := B))).comp (algebraMap Q L) =
      (algebraMap Q' C).comp (algebraMap Q Q'))
    (hfB : f.comp (_root_.Algebra.TensorProduct.includeRight
        (R := A) (A := L)).toRingHom =
      (algebraMap Q' C).comp (algebraMap B Q')) :
    letI := f.toAlgebra
    IsLocalization.AtPrime C ((IsLocalRing.maximalIdeal C).comap f) :=
  isLocalization_atPrime_tensor_of_isPushout M N
    tensorPushoutMap tensorPushoutMap_comp f (comp_tensorPushoutMap f _ hfQ hfB)

end Langlands.Algebra
