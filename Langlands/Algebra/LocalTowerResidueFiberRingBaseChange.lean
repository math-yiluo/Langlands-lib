import Langlands.Algebra.LocalTowerResidueFiberRingBaseChangeStatement
import Langlands.Algebra.LocalTowerResidueFiberSystem
import Langlands.Algebra.PrimeLocalizationCriterion

/-! # Prime-localization preservation for the actual upper residue-fibre transition

Proof of `LocalTowerResidueFiberRingBaseChangeStatement`. The fibre transition
`G_i ⊗[F_i] F_j → G_j` is the base change of the upper transition `T_i ⊗[S_i] S_j → T_j`
along `S_j → F_j`; three pastings of pushout squares identify it as such, a base change of a
localization is a localization, and the target `G_j` is local.
-/

open scoped TensorProduct

universe uI uA uB uC uR uS uT

namespace Langlands.Algebra

namespace ResidueFiberRingBaseChangeProof

attribute [local instance] _root_.Algebra.TensorProduct.rightAlgebra

/-- Base change of a localization across pushout squares. Suppose `G₀` and `G₁` are pushouts
of `T₀, F₀` over `S₀` and of `T₁, F₁` over `S₁`, `A` is a pushout of `T₀, S₁` over `S₀`, `Q` is
a pushout of `G₀, F₁` over `F₀`, and `T₁` is a localization of `A`. If a ring map `Q → G₁` and
the map `A → T₁` agree on the generators, and `G₁` is local, then `G₁` is the localization of `Q`
at the inverse image of its maximal ideal. -/
theorem isLocalization_atPrime_of_pushout_squares
    {S₀ T₀ F₀ G₀ S₁ T₁ F₁ G₁ A Q : Type*}
    [CommRing S₀] [CommRing T₀] [CommRing F₀] [CommRing G₀]
    [CommRing S₁] [CommRing T₁] [CommRing F₁] [CommRing G₁] [IsLocalRing G₁]
    [CommRing A] [CommRing Q]
    [Algebra S₀ T₀] [Algebra S₀ F₀] [Algebra F₀ G₀] [Algebra T₀ G₀] [Algebra S₀ G₀]
    [IsScalarTower S₀ F₀ G₀] [IsScalarTower S₀ T₀ G₀] [_root_.Algebra.IsPushout S₀ T₀ F₀ G₀]
    [Algebra S₁ T₁] [Algebra S₁ F₁] [Algebra F₁ G₁] [Algebra T₁ G₁] [Algebra S₁ G₁]
    [IsScalarTower S₁ F₁ G₁] [IsScalarTower S₁ T₁ G₁] [_root_.Algebra.IsPushout S₁ T₁ F₁ G₁]
    [Algebra S₀ S₁] [Algebra F₀ F₁]
    [Algebra S₀ A] [Algebra T₀ A] [Algebra S₁ A]
    [IsScalarTower S₀ T₀ A] [IsScalarTower S₀ S₁ A] [_root_.Algebra.IsPushout S₀ S₁ T₀ A]
    [Algebra F₀ Q] [Algebra G₀ Q] [Algebra F₁ Q]
    [IsScalarTower F₀ G₀ Q] [IsScalarTower F₀ F₁ Q] [_root_.Algebra.IsPushout F₀ F₁ G₀ Q]
    [Algebra A T₁] [Algebra Q G₁] (M : Submonoid A) [IsLocalization M T₁]
    (hSF : ∀ s : S₀, algebraMap F₀ F₁ (algebraMap S₀ F₀ s) =
      algebraMap S₁ F₁ (algebraMap S₀ S₁ s))
    (hS : ∀ s : S₁, algebraMap A T₁ (algebraMap S₁ A s) = algebraMap S₁ T₁ s)
    (hF : ∀ f : F₁, algebraMap Q G₁ (algebraMap F₁ Q f) = algebraMap F₁ G₁ f)
    (hT : ∀ t : T₀, algebraMap Q G₁ (algebraMap G₀ Q (algebraMap T₀ G₀ t)) =
      algebraMap T₁ G₁ (algebraMap A T₁ (algebraMap T₀ A t))) :
    IsLocalization.AtPrime G₁ ((IsLocalRing.maximalIdeal G₁).comap (algebraMap Q G₁)) := by
  -- Composite structures on `F₁` and `Q`.
  let _ : Algebra S₀ F₁ := ((algebraMap F₀ F₁).comp (algebraMap S₀ F₀)).toAlgebra
  have _ : IsScalarTower S₀ F₀ F₁ := .of_algebraMap_eq' rfl
  have _ : IsScalarTower S₀ S₁ F₁ := .of_algebraMap_eq hSF
  let _ : Algebra S₀ Q := ((algebraMap F₀ Q).comp (algebraMap S₀ F₀)).toAlgebra
  have _ : IsScalarTower S₀ F₀ Q := .of_algebraMap_eq' rfl
  have _ : IsScalarTower S₀ F₁ Q := .of_algebraMap_eq fun s ↦
    IsScalarTower.algebraMap_apply F₀ F₁ Q (algebraMap S₀ F₀ s)
  have _ : IsScalarTower S₀ G₀ Q := .of_algebraMap_eq fun s ↦ by
    rw [IsScalarTower.algebraMap_apply S₀ F₀ G₀, ← IsScalarTower.algebraMap_apply F₀ G₀ Q]
    rfl
  let _ : Algebra T₀ Q := ((algebraMap G₀ Q).comp (algebraMap T₀ G₀)).toAlgebra
  have _ : IsScalarTower T₀ G₀ Q := .of_algebraMap_eq' rfl
  have _ : IsScalarTower S₀ T₀ Q := .of_algebraMap_eq fun s ↦ by
    rw [IsScalarTower.algebraMap_apply S₀ G₀ Q, IsScalarTower.algebraMap_apply S₀ T₀ G₀]
    rfl
  let _ : Algebra S₁ Q := ((algebraMap F₁ Q).comp (algebraMap S₁ F₁)).toAlgebra
  have _ : IsScalarTower S₁ F₁ Q := .of_algebraMap_eq' rfl
  have _ : IsScalarTower S₀ S₁ Q := .of_algebraMap_eq fun s ↦ by
    rw [IsScalarTower.algebraMap_apply S₀ F₁ Q, IsScalarTower.algebraMap_apply S₀ S₁ F₁]
    rfl
  -- The comparison `A → Q` out of the pushout `A`.
  let ψ : A →ₐ[S₀] Q := _root_.Algebra.pushoutDesc A (IsScalarTower.toAlgHom S₀ S₁ Q)
    (IsScalarTower.toAlgHom S₀ T₀ Q) (fun _ _ ↦ mul_comm _ _)
  let _ : Algebra A Q := ψ.toAlgebra
  have _ : IsScalarTower S₁ A Q := .of_algebraMap_eq fun s ↦
    (_root_.Algebra.pushoutDesc_left A (IsScalarTower.toAlgHom S₀ S₁ Q)
      (IsScalarTower.toAlgHom S₀ T₀ Q) (fun _ _ ↦ mul_comm _ _) s).symm
  have _ : IsScalarTower T₀ A Q := .of_algebraMap_eq fun t ↦
    (_root_.Algebra.pushoutDesc_right A (IsScalarTower.toAlgHom S₀ S₁ Q)
      (IsScalarTower.toAlgHom S₀ T₀ Q) (fun _ _ ↦ mul_comm _ _) t).symm
  have _ : IsScalarTower S₀ A Q := .of_algebraMap_eq fun s ↦ (ψ.commutes s).symm
  -- First and second pastings: `Q` is the pushout of `A` and `F₁` over `S₁`.
  have _ : _root_.Algebra.IsPushout S₀ F₀ T₀ G₀ := _root_.Algebra.IsPushout.symm inferInstance
  have hQ₀ : _root_.Algebra.IsPushout S₀ F₁ T₀ Q :=
    (_root_.Algebra.IsPushout.comp_iff (R := S₀) (S := F₀) (R' := T₀) (S' := G₀)
      (T := F₁) (T' := Q)).mpr inferInstance
  have hQ₁ : _root_.Algebra.IsPushout S₁ F₁ A Q :=
    (_root_.Algebra.IsPushout.comp_iff (R := S₀) (S := S₁) (R' := T₀) (S' := A)
      (T := F₁) (T' := Q)).mp hQ₀
  have _ : _root_.Algebra.IsPushout S₁ A F₁ Q := hQ₁.symm
  -- Structures on `G₁`.
  let _ : Algebra A G₁ := ((algebraMap T₁ G₁).comp (algebraMap A T₁)).toAlgebra
  have _ : IsScalarTower A T₁ G₁ := .of_algebraMap_eq' rfl
  have _ : IsScalarTower S₁ A T₁ := .of_algebraMap_eq fun s ↦ (hS s).symm
  have _ : IsScalarTower F₁ Q G₁ := .of_algebraMap_eq fun f ↦ (hF f).symm
  have _ : IsScalarTower S₁ Q G₁ := .of_algebraMap_eq fun s ↦ by
    rw [IsScalarTower.algebraMap_apply S₁ F₁ G₁, IsScalarTower.algebraMap_apply S₁ F₁ Q, hF]
  have _ : IsScalarTower A Q G₁ := .of_algebraMap_eq fun a ↦ by
    refine IsBaseChange.inductionOn
      (_root_.Algebra.IsPushout.out (R := S₀) (S := S₁) (R' := T₀) (S' := A)) a
      (motive := fun a ↦ algebraMap A G₁ a = algebraMap Q G₁ (algebraMap A Q a)) ?_ ?_ ?_
    · intro t
      change algebraMap T₁ G₁ (algebraMap A T₁ (algebraMap T₀ A t)) =
        algebraMap Q G₁ (algebraMap A Q (algebraMap T₀ A t))
      rw [← IsScalarTower.algebraMap_apply T₀ A Q, IsScalarTower.algebraMap_apply T₀ G₀ Q, hT]
    · intro s n hn
      rw [Algebra.smul_def, map_mul, map_mul, map_mul, hn]
      congr 1
      change algebraMap T₁ G₁ (algebraMap A T₁ (algebraMap S₁ A s)) = _
      rw [← IsScalarTower.algebraMap_apply S₁ A Q, hS, ← IsScalarTower.algebraMap_apply S₁ T₁ G₁,
        IsScalarTower.algebraMap_apply S₁ Q G₁]
    · intro x y hx hy
      rw [map_add, map_add, map_add, hx, hy]
  -- Third pasting: `G₁` is the pushout of `T₁` and `Q` over `A`.
  have hG : _root_.Algebra.IsPushout A T₁ Q G₁ :=
    (_root_.Algebra.IsPushout.comp_iff (R := S₁) (S := A) (R' := F₁) (S' := Q)
      (T := T₁) (T' := G₁)).mp inferInstance
  have _ : IsLocalization (_root_.Algebra.algebraMapSubmonoid Q M) G₁ :=
    (_root_.Algebra.isLocalization_iff_isPushout M T₁).mpr hG.symm
  exact isLocalization_atPrime_of_local_target (_root_.Algebra.algebraMapSubmonoid Q M)

section Upper
variable (R S K T : Type*) [CommRing R] [CommRing S] [CommRing K] [CommRing T]
  [Algebra R S] [Algebra R K] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

open scoped ResidueFiberTensor

/-- The upper tensor-ring map `S ⊗[R] K → T ⊗[R] K` is compatible with the left `S`-actions. -/
theorem upperMap_isScalarTower : IsScalarTower S (S ⊗[R] K) (T ⊗[R] K) :=
  .of_algebraMap_eq fun _ ↦ rfl

attribute [local instance] upperMap_isScalarTower

/-- The square `S → T`, `S → S ⊗[R] K` with corner `T ⊗[R] K` is a pushout. -/
theorem upperMap_isPushout : _root_.Algebra.IsPushout S T (S ⊗[R] K) (T ⊗[R] K) :=
  _root_.Algebra.IsPushout.tensorProduct_tensorProduct R K S T (by ext; simp)

end Upper

end ResidueFiberRingBaseChangeProof

open scoped ResidueFiberTensor

attribute [local instance] _root_.Algebra.TensorProduct.rightAlgebra
  ResidueFiberRingBaseChangeProof.upperMap_isScalarTower
  ResidueFiberRingBaseChangeProof.upperMap_isPushout

/-- Prime-localization preservation for the actual upper residue-fibre transition: if
`T_i ⊗[S_i] S_j → T_j` is a localization at a prime, so is `G_i ⊗[F_i] F_j → G_j`. -/
theorem localTowerResidueFiberRingBaseChange :
    LocalTowerResidueFiberRingBaseChangeStatement.{uI, uA, uB, uC, uR, uS, uT} := by
  intro ι _ _ _ R S T _ _ _ _ _ _ _ _ _ _ _ _ D i j h hst
  let _ : Algebra (D.rs.FiberRing i) (D.rs.FiberRing j) := (D.rs.fiberRingMap h).toAlgebra
  let _ := (D.upperFiberBaseChangeMap h).toAlgebra
  let _ : Algebra (D.rs.alg i) (D.rs.alg j) := (D.rs.algMap i j h).toAlgebra
  obtain ⟨p, hp, hloc⟩ := hst
  let _ : Algebra (D.st.RingBaseChange h) (D.top j) := (D.st.ringBaseChangeMap h).toAlgebra
  have _ : IsLocalization p.primeCompl (D.top j) := hloc
  refine ⟨(IsLocalRing.maximalIdeal (D.UpperFiberRing j)).comap (algebraMap _ _),
    inferInstance, ?_⟩
  refine ResidueFiberRingBaseChangeProof.isLocalization_atPrime_of_pushout_squares
    (S₀ := D.rs.alg i) (T₀ := D.top i) (F₀ := D.rs.FiberRing i) (G₀ := D.UpperFiberRing i)
    (S₁ := D.rs.alg j) (T₁ := D.top j) (F₁ := D.rs.FiberRing j) (G₁ := D.UpperFiberRing j)
    (A := D.st.RingBaseChange h)
    (Q := D.UpperFiberRing i ⊗[D.rs.FiberRing i] D.rs.FiberRing j) p.primeCompl
    (fun s ↦ ?_) (fun s ↦ ?_) (fun f ↦ ?_) (fun t ↦ ?_)
  · change D.rs.fiberRingMap h (s ⊗ₜ 1) = D.rs.algMap i j h s ⊗ₜ 1
    rw [LocalAlgebraSystem.fiberRingMap_tmul, map_one]
  · change D.st.ringBaseChangeMap h (1 ⊗ₜ s) = _
    rw [LocalAlgebraSystem.ringBaseChangeMap_tmul, map_one, one_mul]
  · change D.upperFiberBaseChangeMap h (1 ⊗ₜ f) = _
    rw [LocalAlgebraTowerSystem.upperFiberBaseChangeMap_tmul, map_one, one_mul]
    rfl
  · change D.upperFiberBaseChangeMap h ((t ⊗ₜ 1) ⊗ₜ 1) =
      D.st.ringBaseChangeMap h (t ⊗ₜ 1) ⊗ₜ 1
    rw [LocalAlgebraTowerSystem.upperFiberBaseChangeMap_tmul,
      LocalAlgebraTowerSystem.upperFiberRingMap_tmul, LocalAlgebraSystem.ringBaseChangeMap_tmul,
      map_one, map_one, map_one, mul_one, mul_one]

end Langlands.Algebra
