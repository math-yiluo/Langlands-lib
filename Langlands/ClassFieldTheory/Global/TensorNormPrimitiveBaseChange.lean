import Langlands.ClassFieldTheory.Global.TensorNormPrimitiveComparison
import Langlands.GroupScheme.Torus.WeilRestrictionNormBaseChange

/-! # Base change of tensor-unit cochains and the norm modulo powers condition -/

noncomputable section

universe u

open scoped TensorProduct

namespace Langlands.ClassFieldTheory.Global.TensorUnitShapiro

open Langlands.Algebra Langlands.Global GroupScheme.WeilGm
open GroupScheme.KummerCocycle

set_option backward.isDefEq.respectTransparency false

variable {F B K D M : Type u} [Field F] [Field B] [Field K] [Field D] [Field M]
  [Algebra F B] [Algebra F K] [Algebra K D] [Algebra K M] [Algebra F M] [IsScalarTower F K M]
  (e : K ⊗[F] B ≃ₐ[K] D)

/-- If the base-changed left factor is identified with a field, replace it in the tensor
algebra over the larger coefficient field. -/
def baseChangeTensorUnitEquiv : (B ⊗[F] M)ˣ ≃* (D ⊗[K] M)ˣ :=
  Units.mapEquiv ((baseChangeTensorEquiv F K B M).trans
    (Algebra.TensorProduct.congr e (AlgEquiv.refl (R := K) (A₁ := M))).toRingEquiv).toMulEquiv

/-- The base-change equivalence compares the actual automorphism actions. -/
theorem baseChangeTensorUnitEquiv_action (σ : Gal(M/K)) (x : (B ⊗[F] M)ˣ) :
    baseChangeTensorUnitEquiv e (tensorAction F B M (σ.restrictScalars F) x) =
      tensorAction K D M σ (baseChangeTensorUnitEquiv e x) := by
  apply Units.ext
  let c : (K ⊗[F] B) ⊗[K] M ≃ₐ[K] D ⊗[K] M :=
    Algebra.TensorProduct.congr e (AlgEquiv.refl (R := K) (A₁ := M))
  change c (baseChangeTensorEquiv F K B M
      (Algebra.TensorProduct.lTensor (S := B) B (σ.restrictScalars F).toAlgHom (x : B ⊗[F] M))) =
    Algebra.TensorProduct.lTensor (S := D) D σ.toAlgHom (c (baseChangeTensorEquiv F K B M (x : B ⊗[F] M)))
  rw [baseChangeTensorEquiv_natural F K B M σ.toAlgHom (σ.restrictScalars F).toAlgHom (fun _ => rfl)]
  generalize baseChangeTensorEquiv F K B M (x : B ⊗[F] M) = t
  induction t using TensorProduct.inductionOn with
  | tmul a b => rfl
  | add t s ht hs => simp only [map_add, ht, hs]

/-- The base-change equivalence preserves the actual determinant norm. -/
theorem baseChangeTensorUnitEquiv_norm [FiniteDimensional F B] [FiniteDimensional K D]
    (x : (B ⊗[F] M)ˣ) :
    tensorNormUnits K D M (baseChangeTensorUnitEquiv e x) = tensorNormUnits F B M x := by
  apply Units.ext
  let c : (K ⊗[F] B) ⊗[K] M ≃ₐ[K] D ⊗[K] M :=
    Algebra.TensorProduct.congr e (AlgEquiv.refl (R := K) (A₁ := M))
  change tensorNorm K D M (c (baseChangeTensorEquiv F K B M (x : B ⊗[F] M))) =
    tensorNorm F B M (x : B ⊗[F] M)
  rw [← Langlands.GroupScheme.WeilGm.tensorNorm_baseChange F K B M]
  let d : M ⊗[K] (K ⊗[F] B) ≃ₐ[M] M ⊗[K] D :=
    Algebra.TensorProduct.congr (AlgEquiv.refl (R := M) (A₁ := M)) e
  have h (t : (K ⊗[F] B) ⊗[K] M) :
      Algebra.TensorProduct.comm K D M (c t) =
        d (Algebra.TensorProduct.comm K (K ⊗[F] B) M t) := by
    induction t using TensorProduct.inductionOn with
    | tmul a b => rfl
    | add t s ht hs => simp only [map_add, ht, hs]
  change Algebra.norm M (Algebra.TensorProduct.comm K D M (c _)) =
    Algebra.norm M (Algebra.TensorProduct.comm K (K ⊗[F] B) M _)
  rw [h, Algebra.norm_eq_of_algEquiv]

variable {L : Type u} [Field L] [Algebra F L] [IsGalois F L] [Algebra L M] [IsScalarTower F L M]

/-- Restriction to the new base followed by restriction to the original coefficient field. -/
abbrev coefficientRestriction : Gal(M/K) →* Gal(L/F) :=
  (AlgEquiv.restrictNormalHom L).comp (AlgEquiv.restrictScalarsHom F)

/-- Transport tensor units along a compatible new coefficient field and base. -/
def transferTensorUnit : (B ⊗[F] L)ˣ →* (D ⊗[K] M)ˣ :=
  (baseChangeTensorUnitEquiv e).toMonoidHom.comp (extendTensorUnit M)

/-- Transfer intertwines the original restricted action and the local action. -/
theorem transferTensorUnit_action (σ : Gal(M/K)) (x : (B ⊗[F] L)ˣ) :
    tensorAction K D M σ (transferTensorUnit e x) =
      transferTensorUnit e (tensorAction F B L (coefficientRestriction σ) x) := by
  change tensorAction K D M σ (baseChangeTensorUnitEquiv e (extendTensorUnit M x)) = _
  rw [← baseChangeTensorUnitEquiv_action, extendTensorUnit_action]
  rfl

/-- The transferred cochain has the transferred degree-two differential. -/
theorem transferTensorUnit_differential (a : Gal(L/F) → (B ⊗[F] L)ˣ) (σ τ : Gal(M/K)) :
    tensorDifferential (fun γ => transferTensorUnit e (a (coefficientRestriction γ))) σ τ =
      transferTensorUnit e (tensorDifferential a (coefficientRestriction σ) (coefficientRestriction τ)) := by
  simp only [tensorDifferential, transferTensorUnit_action, map_mul, map_div]

variable [FiniteDimensional F B] [FiniteDimensional K D]

omit [IsGalois F L] in
/-- The norm of a transferred tensor unit is the original norm extended to the new field. -/
theorem transferTensorUnit_norm (x : (B ⊗[F] L)ˣ) :
    tensorNormUnits K D M (transferTensorUnit e x) =
      Units.map (algebraMap L M).toMonoidHom (tensorNormUnits F B L x) :=
  (baseChangeTensorUnitEquiv_norm e (extendTensorUnit M x)).trans (tensorNormUnits_extend M x)

variable [FiniteDimensional K M] [IsGalois K M] [Algebra D M] [Algebra.IsSeparable K D]
  [IsScalarTower K D M]

/-- A norm-one local primitive over the identified field factor yields the local norm
modulo powers condition on the original scalar radicand. -/
theorem isNormMulPower_of_transferred_primitive [CharZero K]
    (n : ℕ) (a : Gal(L/F) → (B ⊗[F] L)ˣ) (ha : ∀ σ, a σ ^ n = 1)
    (b : Gal(M/K) → (D ⊗[K] M)ˣ) (hb : ∀ σ, b σ ^ n = 1)
    (hn : ∀ σ, tensorNormUnits K D M (b σ) = 1)
    (hd : ∀ σ τ, tensorDifferential b σ τ =
      transferTensorUnit e (tensorDifferential a (coefficientRestriction σ) (coefficientRestriction τ)))
    {s : Fˣ} {z : Lˣ} (hz : z ^ n = Units.map (algebraMap F L).toMonoidHom s)
    (hN : ∀ σ, tensorNormUnits F B L (a σ) = value z σ) :
    IsNormMulPower (E := D) n (Units.map (algebraMap F K).toMonoidHom s) := by
  let ρ : Gal(M/K) →* Gal(L/F) := coefficientRestriction
  let a' (σ : Gal(M/K)) : (D ⊗[K] M)ˣ := transferTensorUnit e (a (ρ σ))
  let j := Units.map (algebraMap L M).toMonoidHom
  let z' := j z
  have ha' (σ : Gal(M/K)) : a' σ ^ n = 1 := by
    dsimp only [a']
    rw [← map_pow, ha, map_one]
  have hD (σ τ : Gal(M/K)) : tensorDifferential a' σ τ = tensorDifferential b σ τ :=
    (transferTensorUnit_differential e a σ τ).trans (hd σ τ).symm
  have hz' : z' ^ n = Units.map (algebraMap K M).toMonoidHom (Units.map (algebraMap F K).toMonoidHom s) := by
    change j z ^ n = _
    rw [← map_pow, hz]
    apply Units.ext
    exact (IsScalarTower.algebraMap_apply F L M (s : F)).symm.trans
      (IsScalarTower.algebraMap_apply F K M (s : F))
  have hN' (σ : Gal(M/K)) : tensorNormUnits K D M (a' σ) = value z' σ := by
    change tensorNormUnits K D M (transferTensorUnit e (a (coefficientRestriction σ))) = _
    rw [transferTensorUnit_norm, hN, value, map_div, value]
    apply congrArg (fun t : Mˣ => t / z')
    apply Units.ext
    exact (σ.restrictScalars F).restrictNormal_commutes L (z : L)
  exact tensorNormPrimitiveComparison n a' b ha' hb hn hD _ z' hz' hN'

end Langlands.ClassFieldTheory.Global.TensorUnitShapiro
