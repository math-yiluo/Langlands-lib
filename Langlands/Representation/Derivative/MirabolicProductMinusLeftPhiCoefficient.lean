import Langlands.Representation.Derivative.MirabolicMixedOrbitCharacters
import Langlands.Representation.Mirabolic.MixedProducts

/-! Actual left-orbit radical coefficient localizations for positive Phi. -/

noncomputable section

open scoped TensorProduct

namespace Langlands.Derivative.MirabolicProductMinus

open GeneralLinear GeneralLinear.Mirabolic GeneralLinear.Mirabolic.MixedOrbit
  HarmonicAnalysis Jacquet.Localization

universe uR uV uW uV' uW'

variable {R : Type uR} [CommRing R] (k r : ℕ)

/-- The actual source-radical map at the left identity orbit is onto. -/
theorem leftRadicalSource_one_surjective :
    Function.Surjective (leftRadicalSource k r (R := R) 1) := by
  intro w
  let v : Fin (k + r + 2) → R := fun i =>
    if h : k + 1 ≤ i.val then
      radicalCoordinates w ⟨i.val - (k + 1), by omega⟩ else 0
  refine ⟨leftOrbitRadicalElement k r 1 v, ?_⟩
  apply Subtype.ext
  change (leftRadicalCoefficient k r R 1 (leftOrbitRadicalElement k r 1 v)).2 = w.val
  rw [leftRadicalCoefficient_one]
  have hv : (fun j : Fin (r + 1) => v ⟨k + 1 + j.val, by omega⟩) =
      radicalCoordinates w := by
    funext j
    dsimp only [v]
    rw [dite_eq_left (by omega)]
    congr 1
    apply Fin.ext
    change k + 1 + j.val - (k + 1) = j.val
    omega
  change (radicalElement (fun j : Fin (r + 1) => v ⟨k + 1 + j.val, by omega⟩)).val = _
  rw [hv, radicalElement_coordinates]

variable [TopologicalSpace R] (ψ : UnitaryAdditiveCharacter R)
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]
variable (ρ : Representation ℂ (GeneralLinear (k + 1) R) V)
  (τ : Representation ℂ (mirabolic (r + 1) R) W)

/-- The entire tensor coefficient restricted to the actual left radical intersection. -/
abbrev leftPhiOrbitRepresentation (i : Fin 2) :=
  (MixedProductTensor.external ρ τ).comp (leftRadicalCoefficient k r R i)

/-- The ambient positive character, regarded as a character of the whole intersection. -/
abbrev leftPhiOrbitCharacter (i : Fin 2) :=
  (leftOrbitTheta k r ψ i).comp (⊤ : Subgroup (leftRadicalIntersection k r R i)).subtype

/-- Localization at all elements of the actual intersection, without normalization. -/
abbrev leftPhiCoefficientQuotient (i : Fin 2) :=
  Coinvariants (leftPhiOrbitRepresentation k r ρ τ i) ⊤ (leftPhiOrbitCharacter k r ψ i)

/-- Quotient map for the actual left-orbit coefficient. -/
abbrev leftPhiCoefficientMk (i : Fin 2) :
    V ⊗[ℂ] W →ₗ[ℂ] leftPhiCoefficientQuotient k r ψ ρ τ i :=
  mk (leftPhiOrbitRepresentation k r ρ τ i) ⊤ (leftPhiOrbitCharacter k r ψ i)

omit [TopologicalSpace R] in
/-- The identity-orbit coefficient acts on the second factor through its actual source radical. -/
theorem leftPhiOrbitRepresentation_one_tmul
    (u : leftRadicalIntersection k r R 1) (v : V) (w : W) :
    leftPhiOrbitRepresentation k r ρ τ 1 u (v ⊗ₜ w) =
      v ⊗ₜ τ (leftRadicalSource k r 1 u).val w := by
  change MixedProductTensor.external ρ τ (leftRadicalCoefficient k r R 1 u) (v ⊗ₜ w) = _
  rw [leftRadicalCoefficient_eq, MixedProductTensor.external_tmul, map_one,
    Module.End.one_apply]

/-- The forward quotient map sends a tensor class to the tensor of the source class. -/
def leftPhiTensorForward :
    leftPhiCoefficientQuotient k r ψ ρ τ 1 →ₗ[ℂ]
      V ⊗[ℂ] Coinvariants τ (radical (r + 1) R) (Mirabolic.theta ψ r) :=
  lift _ _ _ (TensorProduct.map LinearMap.id (mk τ _ _)) (by
    intro u x
    induction x using TensorProduct.inductionOn with
    | tmul v w =>
      change TensorProduct.map LinearMap.id (mk τ _ _)
          (leftPhiOrbitRepresentation k r ρ τ 1 u.val (v ⊗ₜ w)) = _
      rw [leftPhiOrbitRepresentation_one_tmul, TensorProduct.map_tmul,
        LinearMap.id_apply, mk_apply_subgroup, TensorProduct.tmul_smul]
      rw [show leftPhiOrbitCharacter k r ψ 1 u =
        Mirabolic.theta ψ r (leftRadicalSource k r 1 u.val) from
          DFunLike.congr_fun (leftOrbitTheta_one k r ψ) u.val]
      rfl
    | add x y hx hy => simp only [map_add, hx, hy, smul_add])

@[simp] theorem leftPhiTensorForward_mk_tmul (v : V) (w : W) :
    leftPhiTensorForward k r ψ ρ τ (leftPhiCoefficientMk k r ψ ρ τ 1 (v ⊗ₜ w)) =
      v ⊗ₜ mk τ (radical (r + 1) R) (Mirabolic.theta ψ r) w := rfl

/-- Source-radical relations hold in the actual identity-orbit coefficient quotient. -/
theorem leftPhiCoefficientMk_one_source
    (u : radical (r + 1) R) (v : V) (w : W) :
    leftPhiCoefficientMk k r ψ ρ τ 1 (v ⊗ₜ τ u.val w) =
      (Mirabolic.theta ψ r u : ℂ) • leftPhiCoefficientMk k r ψ ρ τ 1 (v ⊗ₜ w) := by
  obtain ⟨a, ha⟩ := leftRadicalSource_one_surjective k r u
  have hact : leftPhiOrbitRepresentation k r ρ τ 1 a (v ⊗ₜ w) =
      v ⊗ₜ τ u.val w :=
    (leftPhiOrbitRepresentation_one_tmul k r ρ τ a v w).trans
      (congrArg (fun b : radical (r + 1) R => v ⊗ₜ τ b.val w) ha)
  have hθ : leftPhiOrbitCharacter k r ψ 1 ⟨a, Subgroup.mem_top a⟩ =
      Mirabolic.theta ψ r u :=
    (DFunLike.congr_fun (leftOrbitTheta_one k r ψ) a).trans
      (congrArg (Mirabolic.theta ψ r) ha)
  calc
    _ = leftPhiCoefficientMk k r ψ ρ τ 1
        (leftPhiOrbitRepresentation k r ρ τ 1 a (v ⊗ₜ w)) :=
      congrArg (leftPhiCoefficientMk k r ψ ρ τ 1) hact.symm
    _ = (leftPhiOrbitCharacter k r ψ 1 ⟨a, Subgroup.mem_top a⟩ : ℂ) •
        leftPhiCoefficientMk k r ψ ρ τ 1 (v ⊗ₜ w) :=
      mk_apply_subgroup (leftPhiOrbitRepresentation k r ρ τ 1) ⊤
        (leftPhiOrbitCharacter k r ψ 1) ⟨a, Subgroup.mem_top a⟩ (v ⊗ₜ w)
    _ = _ := congrArg
      (fun c : ℂˣ => (c : ℂ) • leftPhiCoefficientMk k r ψ ρ τ 1 (v ⊗ₜ w)) hθ

/-- Descend the second slot of the tensor-valued coefficient quotient map. -/
def leftPhiTensorBilinear :
    Coinvariants τ (radical (r + 1) R) (Mirabolic.theta ψ r) →ₗ[ℂ]
      V →ₗ[ℂ] leftPhiCoefficientQuotient k r ψ ρ τ 1 :=
  lift τ _ _ ((TensorProduct.mk ℂ V W).flip.compr₂
    (leftPhiCoefficientMk k r ψ ρ τ 1)) (by
    intro u w
    apply LinearMap.ext
    intro v
    exact leftPhiCoefficientMk_one_source k r ψ ρ τ u v w)

/-- The inverse map tensors with a source-localized class and takes its coefficient class. -/
def leftPhiTensorBackward :
    V ⊗[ℂ] Coinvariants τ (radical (r + 1) R) (Mirabolic.theta ψ r) →ₗ[ℂ]
      leftPhiCoefficientQuotient k r ψ ρ τ 1 :=
  TensorProduct.lift (leftPhiTensorBilinear k r ψ ρ τ).flip

@[simp] theorem leftPhiTensorBackward_tmul_mk (v : V) (w : W) :
    leftPhiTensorBackward k r ψ ρ τ
      (v ⊗ₜ mk τ (radical (r + 1) R) (Mirabolic.theta ψ r) w) =
      leftPhiCoefficientMk k r ψ ρ τ 1 (v ⊗ₜ w) := rfl

/-- The actual identity-orbit coefficient localization is the tensor with the source localization. -/
def leftPhiTensorEquiv :
    leftPhiCoefficientQuotient k r ψ ρ τ 1 ≃ₗ[ℂ]
      V ⊗[ℂ] Coinvariants τ (radical (r + 1) R) (Mirabolic.theta ψ r) :=
  LinearEquiv.ofLinearMap (leftPhiTensorForward k r ψ ρ τ)
    (leftPhiTensorBackward k r ψ ρ τ)
    (by
      apply TensorProduct.ext'
      intro v q
      obtain ⟨w, rfl⟩ := mk_surjective τ (radical (r + 1) R) (Mirabolic.theta ψ r) q
      rfl)
    (by
      apply hom_ext
      apply TensorProduct.ext'
      intro v w
      rfl)

@[simp] theorem leftPhiTensorEquiv_mk_tmul (v : V) (w : W) :
    leftPhiTensorEquiv k r ψ ρ τ (leftPhiCoefficientMk k r ψ ρ τ 1 (v ⊗ₜ w)) =
      v ⊗ₜ mk τ (radical (r + 1) R) (Mirabolic.theta ψ r) w := rfl

@[simp] theorem leftPhiTensorEquiv_symm_tmul_mk (v : V) (w : W) :
    (leftPhiTensorEquiv k r ψ ρ τ).symm
      (v ⊗ₜ mk τ (radical (r + 1) R) (Mirabolic.theta ψ r) w) =
      leftPhiCoefficientMk k r ψ ρ τ 1 (v ⊗ₜ w) := rfl

variable {V' : Type uV'} [AddCommGroup V'] [Module ℂ V']
variable {W' : Type uW'} [AddCommGroup W'] [Module ℂ W']
variable {ρ' : Representation ℂ (GeneralLinear (k + 1) R) V'}
  {τ' : Representation ℂ (mirabolic (r + 1) R) W'}

/-- Arbitrary intertwiners induce maps on the actual orbit-coefficient quotients. -/
def leftPhiCoefficientMap (f : ρ.IntertwiningMap ρ') (g : τ.IntertwiningMap τ')
    (i : Fin 2) :
    leftPhiCoefficientQuotient k r ψ ρ τ i →ₗ[ℂ]
      leftPhiCoefficientQuotient k r ψ ρ' τ' i :=
  mapLinear ⊤ (leftPhiOrbitCharacter k r ψ i)
    (MixedProductTensor.pullbackMap (leftRadicalCoefficient k r R i)
      (MixedProductTensor.externalMap f g))

@[simp] theorem leftPhiCoefficientMap_mk_tmul
    (f : ρ.IntertwiningMap ρ') (g : τ.IntertwiningMap τ')
    (i : Fin 2) (v : V) (w : W) :
    leftPhiCoefficientMap k r ψ ρ τ f g i
      (leftPhiCoefficientMk k r ψ ρ τ i (v ⊗ₜ w)) =
      leftPhiCoefficientMk k r ψ ρ' τ' i (f v ⊗ₜ g w) := rfl

/-- The tensor equivalence is natural in both factors, with independent carrier universes. -/
theorem leftPhiTensorEquiv_naturality
    (f : ρ.IntertwiningMap ρ') (g : τ.IntertwiningMap τ')
    (z : leftPhiCoefficientQuotient k r ψ ρ τ 1) :
    leftPhiTensorEquiv k r ψ ρ' τ'
        (leftPhiCoefficientMap k r ψ ρ τ f g 1 z) =
      TensorProduct.map f.toLinearMap
        (mapLinear (radical (r + 1) R) (Mirabolic.theta ψ r) g)
        (leftPhiTensorEquiv k r ψ ρ τ z) := by
  obtain ⟨x, rfl⟩ := mk_surjective
    (leftPhiOrbitRepresentation k r ρ τ 1) ⊤ (leftPhiOrbitCharacter k r ψ 1) z
  induction x using TensorProduct.inductionOn with
  | tmul v w => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The entire left-cycle quotient map vanishes, by the nontrivial ambient character. -/
theorem leftPhiCoefficientMk_zero :
    leftPhiCoefficientMk k r ψ ρ τ 0 = 0 :=
  leftOrbitTheta_zero_equivariant_eq_zero k r ψ (MixedProductTensor.external ρ τ)
    (leftPhiCoefficientMk k r ψ ρ τ 0) (fun u v =>
      mk_apply_subgroup (leftPhiOrbitRepresentation k r ρ τ 0) ⊤
        (leftPhiOrbitCharacter k r ψ 0) ⟨u, Subgroup.mem_top u⟩ v)

/-- The actual positive-character coefficient localization of the left cycle is zero. -/
theorem leftPhiCoefficientQuotient_zero_subsingleton :
    Subsingleton (leftPhiCoefficientQuotient k r ψ ρ τ 0) := by
  refine ⟨fun a b => ?_⟩
  obtain ⟨v, rfl⟩ := mk_surjective
    (leftPhiOrbitRepresentation k r ρ τ 0) ⊤ (leftPhiOrbitCharacter k r ψ 0) a
  obtain ⟨w, rfl⟩ := mk_surjective
    (leftPhiOrbitRepresentation k r ρ τ 0) ⊤ (leftPhiOrbitCharacter k r ψ 0) b
  exact (LinearMap.congr_fun (leftPhiCoefficientMk_zero k r ψ ρ τ) v).trans
    (LinearMap.congr_fun (leftPhiCoefficientMk_zero k r ψ ρ τ) w).symm

end Langlands.Derivative.MirabolicProductMinus
