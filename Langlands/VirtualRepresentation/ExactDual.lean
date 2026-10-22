import Langlands.VirtualRepresentation.Exact
import Langlands.Weil.Representation.DualClasses

/-!
# Contragredient duality on exact virtual representations

Actual dual intertwiners reverse short exact sequences. This proves descent to
exact virtual classes, where the finite-dimensional bidual gives an involution.
-/

noncomputable section

universe uK uG uV uA uB uC

namespace Langlands.FiniteRepresentation

variable {K : Type uK} {G : Type uG} [Field K] [Group G]

/-- Full algebraic duality reverses actual short exact sequences. The proof uses
only linear duality; no equivariant splitting of the sequence is required. -/
theorem isShortExact_dual
    {A : FiniteRepresentation.{uK, uG, uA} K G}
    {B : FiniteRepresentation.{uK, uG, uB} K G}
    {C : FiniteRepresentation.{uK, uG, uC} K G}
    {f : A.representation.IntertwiningMap B.representation}
    {g : B.representation.IntertwiningMap C.representation}
    (h : IsShortExact f g) :
    IsShortExact (A := dual C) (B := dual B) (C := dual A)
      (Langlands.dualIntertwining g) (Langlands.dualIntertwining f) := by
  refine ⟨LinearMap.dualMap_injective_of_surjective h.2.1,
    LinearMap.dualMap_surjective_of_injective h.1, ?_⟩
  change LinearMap.range g.toLinearMap.dualMap = LinearMap.ker f.toLinearMap.dualMap
  rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker,
    LinearMap.ker_dualMap_eq_dualAnnihilator_range, h.2.2]

end Langlands.FiniteRepresentation

namespace Langlands.VirtualRepresentation.ExactGrothendieckGroup

open FiniteRepresentation

variable {G : Type uG} [Group G]
variable (P : FiniteRepresentation.{0, uG, uV} ℂ G → Prop)
variable (hP : ∀ A, P A → P (FiniteRepresentation.dual A))

/-- The actual dual on genuine classes in a family closed under duality. -/
def dualClassWith : IsomorphismClassesWith P → IsomorphismClassesWith P :=
  Quotient.map
    (fun A => ⟨FiniteRepresentation.dual A.val, hP A.val A.property⟩)
    (fun _ _ ⟨e⟩ => ⟨(FiniteRepresentation.dualEquiv e).symm⟩)

@[simp]
theorem dualClassWith_exactClassOf
    (A : {A : FiniteRepresentation.{0, uG, uV} ℂ G // P A}) :
    dualClassWith P hP (exactClassOf P A) =
      exactClassOf P ⟨FiniteRepresentation.dual A.val, hP A.val A.property⟩ := rfl

/-- Reversing the two ends does not change their sum in the exact relation. -/
theorem dualClassWith_isExactAdditive :
    IsExactAdditive P (fun c => ofClass P (dualClassWith P hP c)) := by
  intro A B C f g h
  change ofRepresentation P ⟨FiniteRepresentation.dual B.val, hP B.val B.property⟩ =
    ofRepresentation P ⟨FiniteRepresentation.dual A.val, hP A.val A.property⟩ +
    ofRepresentation P ⟨FiniteRepresentation.dual C.val, hP C.val C.property⟩
  rw [add_comm]
  exact ofRepresentation_shortExact P (isShortExact_dual h)

/-- Duality descended through every genuine short exact relation. -/
def dual : ExactGrothendieckGroup P →ₗ[ℤ] ExactGrothendieckGroup P :=
  lift P (fun c => ofClass P (dualClassWith P hP c))
    (dualClassWith_isExactAdditive P hP)

@[simp]
theorem dual_ofClass (c : IsomorphismClassesWith P) :
    dual P hP (ofClass P c) = ofClass P (dualClassWith P hP c) :=
  lift_ofClass P _ _ c

@[simp]
theorem dual_ofRepresentation
    (A : {A : FiniteRepresentation.{0, uG, uV} ℂ G // P A}) :
    dual P hP (ofRepresentation P A) =
      ofRepresentation P ⟨FiniteRepresentation.dual A.val, hP A.val A.property⟩ :=
  dual_ofClass P hP _

/-- The finite-dimensional bidual identifies the square with identity. -/
theorem dual_comp_dual : (dual P hP).comp (dual P hP) = LinearMap.id := by
  apply hom_ext P
  intro c
  induction c using Quotient.inductionOn with
  | h A =>
    change dual P hP (dual P hP (ofRepresentation P A)) = ofRepresentation P A
    rw [dual_ofRepresentation, dual_ofRepresentation]
    exact ofRepresentation_eq_of_equiv P (FiniteRepresentation.dualDualEquiv A.val).symm

@[simp]
theorem dual_dual (x : ExactGrothendieckGroup P) : dual P hP (dual P hP x) = x :=
  LinearMap.congr_fun (dual_comp_dual P hP) x

/-- The actual contragredient involution of a dual-closed exact virtual group. -/
def dualEquivalence : ExactGrothendieckGroup P ≃ₗ[ℤ] ExactGrothendieckGroup P where
  toLinearMap := dual P hP
  invFun := dual P hP
  left_inv := dual_dual P hP
  right_inv := dual_dual P hP

@[simp]
theorem dualEquivalence_symm : (dualEquivalence P hP).symm = dualEquivalence P hP := rfl

/-- Virtual dimension is unchanged by the descended dual. -/
theorem degree_comp_dual : (degree P).comp (dual P hP) = degree P := by
  apply hom_ext P
  intro c
  induction c using Quotient.inductionOn with
  | h A =>
    change degree P (dual P hP (ofRepresentation P A)) = degree P (ofRepresentation P A)
    simp only [dual_ofRepresentation, degree_ofRepresentation, rank_dual]

@[simp]
theorem degree_dual (x : ExactGrothendieckGroup P) :
    degree P (dual P hP x) = degree P x :=
  LinearMap.congr_fun (degree_comp_dual P hP) x

/-- The same involution restricted to the actual kernel of virtual dimension. -/
def dualDegreeZero : degreeZero P ≃ₗ[ℤ] degreeZero P where
  toLinearMap := (dual P hP).restrict fun x hx => by
    change degree P (dual P hP x) = 0
    rw [degree_dual, (mem_degreeZero P x).mp hx]
  invFun x := ⟨dual P hP x.val, by
    change degree P (dual P hP x.val) = 0
    rw [degree_dual, (mem_degreeZero P x.val).mp x.property]⟩
  left_inv x := Subtype.ext (dual_dual P hP x.val)
  right_inv x := Subtype.ext (dual_dual P hP x.val)

@[simp]
theorem dualDegreeZero_coe (x : degreeZero P) :
    (dualDegreeZero P hP x).val = dual P hP x.val := rfl

section Continuous

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- The contragredient on continuous exact virtual representations. Ordinary
complex-topology continuity and preservation of exactness are proved inputs. -/
def continuousDual :
    ExactGrothendieckGroup (fun A : FiniteRepresentation.{0, uG, uV} ℂ G =>
      A.IsContinuous) ≃ₗ[ℤ]
      ExactGrothendieckGroup (fun A : FiniteRepresentation.{0, uG, uV} ℂ G =>
        A.IsContinuous) :=
  dualEquivalence _ (fun A hA => (isContinuous_dual_iff A).mpr hA)

@[simp]
theorem continuousDual_ofClass
    (c : IsomorphismClassesWith (fun A : FiniteRepresentation.{0, uG, uV} ℂ G =>
      A.IsContinuous)) :
    continuousDual (ofClass _ c) =
      ofClass _ (dualClassWith _ (fun A hA => (isContinuous_dual_iff A).mpr hA) c) :=
  dual_ofClass _ _ c

@[simp]
theorem continuousDual_ofRepresentation
    (A : {A : FiniteRepresentation.{0, uG, uV} ℂ G // A.IsContinuous}) :
    continuousDual (ofRepresentation _ A) =
      ofRepresentation _ ⟨FiniteRepresentation.dual A.val,
        (isContinuous_dual_iff A.val).mpr A.property⟩ :=
  dual_ofRepresentation _ _ A

@[simp]
theorem continuousDual_symm :
    (continuousDual.{uG, uV} (G := G)).symm = continuousDual := rfl

@[simp]
theorem continuousDual_apply_apply
    (x : ExactGrothendieckGroup (fun A : FiniteRepresentation.{0, uG, uV} ℂ G =>
      A.IsContinuous)) : continuousDual (continuousDual x) = x :=
  dual_dual _ _ x

theorem continuousDual_involutive : Function.Involutive (continuousDual.{uG, uV} (G := G)) :=
  continuousDual_apply_apply

@[simp]
theorem degree_continuousDual
    (x : ExactGrothendieckGroup (fun A : FiniteRepresentation.{0, uG, uV} ℂ G =>
      A.IsContinuous)) : degree _ (continuousDual x) = degree _ x :=
  degree_dual _ _ x

/-- Continuous duality on the degree-zero submodule, with no additional hypotheses. -/
def continuousDualDegreeZero :
    degreeZero (fun A : FiniteRepresentation.{0, uG, uV} ℂ G => A.IsContinuous) ≃ₗ[ℤ]
      degreeZero (fun A : FiniteRepresentation.{0, uG, uV} ℂ G => A.IsContinuous) :=
  dualDegreeZero _ (fun A hA => (isContinuous_dual_iff A).mpr hA)

@[simp]
theorem continuousDualDegreeZero_coe
    (x : degreeZero (fun A : FiniteRepresentation.{0, uG, uV} ℂ G => A.IsContinuous)) :
    (continuousDualDegreeZero x).val = continuousDual x.val := rfl

@[simp]
theorem continuousDualDegreeZero_apply_apply
    (x : degreeZero (fun A : FiniteRepresentation.{0, uG, uV} ℂ G => A.IsContinuous)) :
    continuousDualDegreeZero (continuousDualDegreeZero x) = x :=
  Subtype.ext (continuousDual_apply_apply x.val)

@[simp]
theorem continuousDualDegreeZero_symm :
    (continuousDualDegreeZero.{uG, uV} (G := G)).symm = continuousDualDegreeZero := by
  ext x
  rfl

end Continuous

end Langlands.VirtualRepresentation.ExactGrothendieckGroup
