import Langlands.Weil.Representation.SumsTensor
import Langlands.Weil.Representation.CharacterLine
import Mathlib.RingTheory.Flat.Basic

/-! # Tensor product on exact virtual continuous representations -/

noncomputable section

open scoped TensorProduct

universe uG uV uW uA uB uC

namespace Langlands.FiniteRepresentation

variable {G : Type uG} [Group G]

/-- Tensoring actual intertwiners on the right preserves short exactness. -/
theorem isShortExact_tensor_right
    {A : FiniteRepresentation.{0, uG, uA} ℂ G}
    {B : FiniteRepresentation.{0, uG, uB} ℂ G}
    {C : FiniteRepresentation.{0, uG, uC} ℂ G}
    {f : A.representation.IntertwiningMap B.representation}
    {g : B.representation.IntertwiningMap C.representation}
    (h : IsShortExact f g) (D : FiniteRepresentation.{0, uG, uW} ℂ G) :
    IsShortExact (tensorMap f (Representation.IntertwiningMap.id D.representation))
      (tensorMap g (Representation.IntertwiningMap.id D.representation)) := by
  refine ⟨Module.Flat.rTensor_preserves_injective_linearMap f.toLinearMap h.1,
    LinearMap.rTensor_surjective D h.2.1, ?_⟩
  exact (Module.Flat.rTensor_exact D (LinearMap.exact_iff.mpr h.2.2.symm)).linearMap_ker_eq.symm

/-- Tensoring actual intertwiners on the left preserves short exactness. -/
theorem isShortExact_tensor_left
    {A : FiniteRepresentation.{0, uG, uA} ℂ G}
    {B : FiniteRepresentation.{0, uG, uB} ℂ G}
    {C : FiniteRepresentation.{0, uG, uC} ℂ G}
    {f : A.representation.IntertwiningMap B.representation}
    {g : B.representation.IntertwiningMap C.representation}
    (h : IsShortExact f g) (D : FiniteRepresentation.{0, uG, uW} ℂ G) :
    IsShortExact (tensorMap (Representation.IntertwiningMap.id D.representation) f)
      (tensorMap (Representation.IntertwiningMap.id D.representation) g) := by
  refine ⟨Module.Flat.lTensor_preserves_injective_linearMap f.toLinearMap h.1,
    LinearMap.lTensor_surjective D h.2.1, ?_⟩
  exact (Module.Flat.lTensor_exact D (LinearMap.exact_iff.mpr h.2.2.symm)).linearMap_ker_eq.symm

/-- The actual tensor with a lifted character line is the scalar twist. -/
def tensorCharacterLineEquiv (A : FiniteRepresentation.{0, uG, uV} ℂ G)
    (χ : G →* ℂˣ) :
    Equiv (tensor A (characterLine.{uG, uV} χ)) (twist χ A) where
  toLinearEquiv := (TensorProduct.congr (LinearEquiv.refl ℂ A)
    (ULift.moduleEquiv : ULift.{uV} ℂ ≃ₗ[ℂ] ℂ)).trans (TensorProduct.rid ℂ A)
  isIntertwining' g := by
    apply TensorProduct.ext'
    intro x y
    change ((χ g : ℂ) * y.down) • A.representation g x =
      (χ g : ℂ) • A.representation g (y.down • x)
    rw [map_smul, mul_smul]

variable [TopologicalSpace G]

/-- Continuity of the genuine tensor representation in the usual module topology. -/
theorem isContinuous_tensor
    {A : FiniteRepresentation.{0, uG, uV} ℂ G}
    {B : FiniteRepresentation.{0, uG, uW} ℂ G}
    (hA : A.IsContinuous) (hB : B.IsContinuous) : (tensor A B).IsContinuous :=
  Weil.OperationClosure.continuous_tensor A.representation B.representation hA hB

end Langlands.FiniteRepresentation

namespace Langlands.VirtualRepresentation.ExactGrothendieckGroup

open FiniteRepresentation

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- Exact virtual continuous representations, with independent group/carrier universes. -/
abbrev Continuous (G : Type uG) [Group G] [TopologicalSpace G] :=
  ExactGrothendieckGroup (fun A : FiniteRepresentation.{0, uG, uV} ℂ G => A.IsContinuous)

/-- Tensor product on genuine continuous isomorphism classes. -/
def continuousTensorClass :
    IsomorphismClassesWith (fun A : FiniteRepresentation.{0, uG, uV} ℂ G => A.IsContinuous) →
    IsomorphismClassesWith (fun B : FiniteRepresentation.{0, uG, uW} ℂ G => B.IsContinuous) →
    IsomorphismClassesWith (fun C : FiniteRepresentation.{0, uG, max uV uW} ℂ G =>
      C.IsContinuous) :=
  Quotient.map₂ (fun A B => ⟨tensor A.val B.val, isContinuous_tensor A.property B.property⟩)
    (fun _ _ ⟨e⟩ _ _ ⟨f⟩ => ⟨tensorEquiv e f⟩)

/-- Every exact relation vanishes after tensoring with a fixed genuine left factor. -/
theorem continuousTensorClass_isExactAdditive_right
    (a : IsomorphismClassesWith
      (fun A : FiniteRepresentation.{0, uG, uV} ℂ G => A.IsContinuous)) :
    IsExactAdditive (fun B : FiniteRepresentation.{0, uG, uW} ℂ G => B.IsContinuous)
      (fun b => ofClass _ (continuousTensorClass a b)) := by
  induction a using Quotient.inductionOn with
  | h A =>
    intro B C D f g h
    exact ofRepresentation_shortExact _ (isShortExact_tensor_left h A.val)

/-- Tensoring a virtual right factor with a genuine left factor. -/
def continuousTensorWithClass
    (a : IsomorphismClassesWith
      (fun A : FiniteRepresentation.{0, uG, uV} ℂ G => A.IsContinuous)) :
    Continuous.{uG, uW} G →ₗ[ℤ] Continuous.{uG, max uV uW} G :=
  lift _ (fun b => ofClass _ (continuousTensorClass a b))
    (continuousTensorClass_isExactAdditive_right a)

@[simp]
theorem continuousTensorWithClass_ofClass
    (a : IsomorphismClassesWith
      (fun A : FiniteRepresentation.{0, uG, uV} ℂ G => A.IsContinuous))
    (b : IsomorphismClassesWith
      (fun B : FiniteRepresentation.{0, uG, uW} ℂ G => B.IsContinuous)) :
    continuousTensorWithClass a (ofClass _ b) = ofClass _ (continuousTensorClass a b) :=
  lift_ofClass _ _ _ _

/-- Exact relations in the left factor vanish as equality of linear maps. -/
theorem continuousTensorWithClass_isExactAdditive :
    IsExactAdditive (fun A : FiniteRepresentation.{0, uG, uV} ℂ G => A.IsContinuous)
      (continuousTensorWithClass.{uG, uV, uW} (G := G)) := by
  intro A B C f g h
  apply hom_ext _
  intro d
  induction d using Quotient.inductionOn with
  | h D =>
    change continuousTensorWithClass (exactClassOf _ B) (ofRepresentation _ D) =
      continuousTensorWithClass (exactClassOf _ A) (ofRepresentation _ D) +
      continuousTensorWithClass (exactClassOf _ C) (ofRepresentation _ D)
    unfold continuousTensorWithClass
    rw [lift_ofRepresentation, lift_ofRepresentation, lift_ofRepresentation]
    exact ofRepresentation_shortExact _ (isShortExact_tensor_right h D.val)

/-- The constructed integer-bilinear tensor product on the exact quotients. -/
def continuousTensor :
    Continuous.{uG, uV} G →ₗ[ℤ]
      Continuous.{uG, uW} G →ₗ[ℤ] Continuous.{uG, max uV uW} G :=
  lift _ continuousTensorWithClass continuousTensorWithClass_isExactAdditive

@[simp]
theorem continuousTensor_ofRepresentation
    (A : ContinuousObjects.{uG, uV} G) (B : ContinuousObjects.{uG, uW} G) :
    continuousTensor (ofRepresentation _ A) (ofRepresentation _ B) =
      ofRepresentation _ ⟨tensor A.val B.val, isContinuous_tensor A.property B.property⟩ := by
  unfold continuousTensor ofRepresentation
  rw [lift_ofClass, continuousTensorWithClass_ofClass]
  rfl

/-- Same-carrier-universe specialization for arithmetic consumers. -/
abbrev continuousTensorSame :
    Continuous.{uG, uV} G →ₗ[ℤ] Continuous.{uG, uV} G →ₗ[ℤ] Continuous.{uG, uV} G :=
  continuousTensor

@[simp]
theorem continuousTensor_add_left (x x' : Continuous.{uG, uV} G)
    (y : Continuous.{uG, uW} G) :
    continuousTensor (x + x') y = continuousTensor x y + continuousTensor x' y :=
  LinearMap.congr_fun (map_add continuousTensor x x') y

@[simp]
theorem continuousTensor_add_right (x : Continuous.{uG, uV} G)
    (y y' : Continuous.{uG, uW} G) :
    continuousTensor x (y + y') = continuousTensor x y + continuousTensor x y' :=
  map_add (continuousTensor x) y y'

@[simp]
theorem continuousTensor_smul_left (n : ℤ) (x : Continuous.{uG, uV} G)
    (y : Continuous.{uG, uW} G) :
    continuousTensor (n • x) y = n • continuousTensor x y :=
  by rw [map_smul, LinearMap.smul_apply]

@[simp]
theorem continuousTensor_smul_right (n : ℤ) (x : Continuous.{uG, uV} G)
    (y : Continuous.{uG, uW} G) :
    continuousTensor x (n • y) = n • continuousTensor x y :=
  map_smul (continuousTensor x) n y

@[simp]
theorem continuousTensor_zero_left (y : Continuous.{uG, uW} G) :
    continuousTensor (0 : Continuous.{uG, uV} G) y = 0 :=
  LinearMap.congr_fun (map_zero continuousTensor) y

@[simp]
theorem continuousTensor_zero_right (x : Continuous.{uG, uV} G) :
    continuousTensor x (0 : Continuous.{uG, uW} G) = 0 :=
  map_zero (continuousTensor x)

/-- Equality of bilinear degree maps, proved on genuine generators in both slots. -/
theorem degree_compr₂_continuousTensor :
    (continuousTensor.{uG, uV, uW} (G := G)).compr₂ (degree _) =
      (LinearMap.lsmul ℤ ℤ).compl₁₂
        (degree (fun A : FiniteRepresentation.{0, uG, uV} ℂ G => A.IsContinuous))
        (degree (fun B : FiniteRepresentation.{0, uG, uW} ℂ G => B.IsContinuous)) := by
  apply hom_ext _
  intro a
  induction a using Quotient.inductionOn with
  | h A =>
    apply hom_ext _
    intro b
    induction b using Quotient.inductionOn with
    | h B =>
      change degree _ (continuousTensor (ofRepresentation _ A) (ofRepresentation _ B)) =
        degree _ (ofRepresentation _ A) * degree _ (ofRepresentation _ B)
      erw [continuousTensor_ofRepresentation, degree_ofRepresentation,
        degree_ofRepresentation, degree_ofRepresentation]
      change (Module.finrank ℂ (A.val ⊗[ℂ] B.val) : ℤ) = _
      rw [Module.finrank_tensorProduct, Nat.cast_mul]
      rfl

/-- Tensor degree is the product of genuine integer degrees, also for virtual differences. -/
theorem degree_continuousTensor (x : Continuous.{uG, uV} G)
    (y : Continuous.{uG, uW} G) :
    degree _ (continuousTensor x y) = degree _ x * degree _ y :=
  LinearMap.congr_fun (LinearMap.congr_fun degree_compr₂_continuousTensor x) y

/-- Every genuine zero-dimensional object represents zero in the exact quotient. -/
theorem ofRepresentation_eq_zero_of_rank_zero (A : ContinuousObjects.{uG, uV} G)
    (hA : A.val.rank = 0) : ofRepresentation _ A = 0 := by
  let : Subsingleton A.val := Module.finrank_zero_iff.mp hA
  have h : IsShortExact (A := A.val) (B := A.val) (C := A.val) 0 0 := by
    refine ⟨fun _ _ _ => Subsingleton.elim _ _, fun x => ⟨0, Subsingleton.elim _ _⟩, ?_⟩
    exact Subsingleton.elim _ _
  have he := ofRepresentation_shortExact (fun B : FiniteRepresentation.{0, uG, uV} ℂ G =>
    B.IsContinuous) (A := A) (B := A) (C := A) h
  exact (add_left_cancel (a := ofRepresentation _ A) (by simpa using he.symm))

/-- Zero-rank genuine left factors tensor to zero. -/
theorem continuousTensor_rank_zero_left (A : ContinuousObjects.{uG, uV} G)
    (hA : A.val.rank = 0) (y : Continuous.{uG, uW} G) :
    continuousTensor (ofRepresentation _ A) y = 0 := by
  rw [ofRepresentation_eq_zero_of_rank_zero A hA, continuousTensor_zero_left]

/-- Zero-rank genuine right factors tensor to zero. -/
theorem continuousTensor_rank_zero_right (x : Continuous.{uG, uV} G)
    (B : ContinuousObjects.{uG, uW} G) (hB : B.val.rank = 0) :
    continuousTensor x (ofRepresentation _ B) = 0 := by
  rw [ofRepresentation_eq_zero_of_rank_zero B hB, continuousTensor_zero_right]

/-- Tensor by a genuine continuous character line agrees with the published exact twist. -/
theorem continuousTensor_characterClass (χ : G →ₜ* ℂˣ) (x : Continuous.{uG, uV} G) :
    continuousTensorSame x (characterClass.{uG, uV} χ) = continuousTwist χ x := by
  have h : (continuousTensorSame (G := G)).flip (characterClass.{uG, uV} χ) =
      (continuousTwist.{uG, uV} χ).toLinearMap := by
    apply hom_ext _
    intro a
    induction a using Quotient.inductionOn with
    | h A =>
      change continuousTensor (ofRepresentation _ A)
          (ofRepresentation _ (continuousCharacterLine χ)) =
        twist χ.toMonoidHom _ _ _ (ofRepresentation _ A)
      erw [continuousTensor_ofRepresentation, twist_ofRepresentation]
      exact ofRepresentation_eq_of_equiv _ (tensorCharacterLineEquiv A.val χ.toMonoidHom)
  exact LinearMap.congr_fun h x

end Langlands.VirtualRepresentation.ExactGrothendieckGroup
