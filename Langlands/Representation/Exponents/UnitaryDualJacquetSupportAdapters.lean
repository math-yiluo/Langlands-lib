import Langlands.Representation.Exponents.DualJacquetStatement
import Langlands.Representation.Classification.OppositeJacquetReciprocity
import Langlands.Representation.Parabolic.StandardOppositeJacquetAdmissibilityProof
import Langlands.Group.GL.CompactOpen
import Mathlib.RingTheory.Finiteness.Basic

/-! Algebraic and admissibility adapters for prescribed opposite support. -/

noncomputable section

namespace Langlands.UnitaryDualJacquetSupport

universe uG uF uV uW

/-- Irreducibility implies finite generation over the group algebra. -/
theorem moduleFinite_of_irreducible
    {G : Type uG} [Group G] {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (hρ : Representation.IsIrreducible ρ) :
    Module.Finite (MonoidAlgebra ℂ G) ρ.asModule := by
  let := hρ
  infer_instance

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
variable (T : F.TopologicalData) {n : ℕ} (B : GeneralLinear.BlockShape n)

/-- The two published normalizations use definitionally the same action. -/
theorem jacquetAction_eq (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier)) :
    OppositeSupport.jacquetAction T B A.ρ =
      (CuspidalJacquetMultiplicity.oppositeJacquet T B A).ρ := rfl

/-- The actual opposite Jacquet module of a tempered source is admissible. -/
theorem jacquet_admissible
    (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier)) (hA : T.IsTempered A.ρ) :
    letI := T.topology
    IsAdmissible (CuspidalJacquetMultiplicity.oppositeJacquet T B A).ρ := by
  let := T.topology
  exact Parabolic.isAdmissible_standardOppositeJacquet F T B A A.ρ hA.isAdmissible

/-- Compact open subgroups are cofinal among open subgroups of the full Levi. -/
theorem levi_compactOpen_cofinal :
    letI := T.topology
    ∀ H : OpenSubgroup (B.Levi F.Carrier),
      ∃ K : OpenSubgroup (B.Levi F.Carrier),
        IsCompact (K : Set (B.Levi F.Carrier)) ∧ K ≤ H := by
  let := T.topology
  intro H
  obtain ⟨K, hK, hKH⟩ := T.leviCompactOpen B H (H.isOpen.mem_nhds H.one_mem)
  exact ⟨K, hK, fun _ hx => hKH hx⟩

/-- An actual dual exponent supplies a nonzero full-dual eigenfunctional
with the prescribed character and no inversion. -/
theorem exists_dualEigenfunctional
    (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier))
    (χ : (Fin B.length → F.Carrierˣ) →* ℂˣ)
    (hχ : T.IsDualJacquetExponent B A χ) :
    ∃ φ : Module.Dual ℂ (CuspidalJacquetMultiplicity.oppositeJacquet T B A),
      φ ≠ 0 ∧ ∀ a v,
        φ ((CuspidalJacquetMultiplicity.oppositeJacquet T B A).ρ
          (B.blockScalarLevi F.Carrier a) v) = (χ a : ℂ) * φ v := by
  have hne :
      (commutativeCharacterSpace (T.splitCentreDualJacquet B A).ρ χ 1).toSubmodule ≠
        ⊥ := by
    intro h
    apply hχ.2
    apply Subrepresentation.toSubmodule_injective
    exact h
  obtain ⟨f, hf, hf0⟩ := (Submodule.ne_bot_iff _).mp hne
  let φ : Module.Dual ℂ (T.splitCentreOppositeJacquet B A) := f
  refine ⟨φ, hf0, ?_⟩
  have he : ∀ a,
      commutativeTranspose (T.splitCentreOppositeJacquet B A).ρ a φ = (χ a : ℂ) • φ :=
    (mem_commutativeCharacterSpace_one _ _ _).mp hf
  change ∀ (a : Fin B.length → F.Carrierˣ) (v : T.splitCentreOppositeJacquet B A),
    φ ((T.splitCentreOppositeJacquet B A).ρ a v) = (χ a : ℂ) * φ v
  intro a v
  have hv := congrArg
    (fun f : Module.Dual ℂ (T.splitCentreOppositeJacquet B A) => f v) (he a)
  change commutativeTranspose (T.splitCentreOppositeJacquet B A).ρ a φ v =
    (χ a : ℂ) * φ v at hv
  rw [commutativeTranspose_apply] at hv
  exact hv

/-- Choose an actual full-dual functional belonging to the prescribed
ordinary dual exponent. -/
def dualEigenfunctional
    (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier))
    (χ : (Fin B.length → F.Carrierˣ) →* ℂˣ)
    (hχ : T.IsDualJacquetExponent B A χ) :
    Module.Dual ℂ (CuspidalJacquetMultiplicity.oppositeJacquet T B A) :=
  Classical.choose (exists_dualEigenfunctional T B A χ hχ)

theorem dualEigenfunctional_ne_zero
    (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier))
    (χ : (Fin B.length → F.Carrierˣ) →* ℂˣ)
    (hχ : T.IsDualJacquetExponent B A χ) :
    dualEigenfunctional T B A χ hχ ≠ 0 :=
  (Classical.choose_spec (exists_dualEigenfunctional T B A χ hχ)).1

theorem dualEigenfunctional_apply
    (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier))
    (χ : (Fin B.length → F.Carrierˣ) →* ℂˣ)
    (hχ : T.IsDualJacquetExponent B A χ)
    (a : Fin B.length → F.Carrierˣ)
    (v : CuspidalJacquetMultiplicity.oppositeJacquet T B A) :
    dualEigenfunctional T B A χ hχ
        ((CuspidalJacquetMultiplicity.oppositeJacquet T B A).ρ
          (B.blockScalarLevi F.Carrier a) v) =
      (χ a : ℂ) * dualEigenfunctional T B A χ hχ v :=
  (Classical.choose_spec (exists_dualEigenfunctional T B A χ hχ)).2 a v

/-- A quotient of the whole opposite Jacquet module is in particular an
actual class exponent, with the top subrepresentation as its witness. -/
theorem classExponent_of_quotient
    (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier))
    (S : Rep.{uW} ℂ (B.Levi F.Carrier))
    (hS : Representation.IsIrreducible S.ρ)
    (hSadm : letI := T.topology; IsAdmissible S.ρ)
    (q : (CuspidalJacquetMultiplicity.oppositeJacquet T B A).ρ.IntertwiningMap S.ρ)
    (hq : Function.Surjective q) :
    T.IsOppositeJacquetClassExponent B A S := by
  let := T.topology
  refine ⟨hS, hSadm, ⊤, ?_⟩
  let i : (⊤ : Subrepresentation
      (CuspidalJacquetMultiplicity.oppositeJacquet T B A).ρ).toRepresentation.IntertwiningMap
        (CuspidalJacquetMultiplicity.oppositeJacquet T B A).ρ :=
    { toLinearMap := Submodule.subtype _
      isIntertwining' := fun _ => rfl }
  refine ⟨q.comp i, ?_⟩
  intro w
  obtain ⟨v, hv⟩ := hq w
  exact ⟨⟨v, Submodule.mem_top⟩, hv⟩

/-- Actual opposite adjunction turns a whole Jacquet quotient into the
required injective intertwiner from the irreducible smooth source. -/
theorem embedding_of_quotient
    (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier))
    (S : Rep.{uW} ℂ (B.Levi F.Carrier))
    (hA : Representation.IsIrreducible A.ρ)
    (hAsm : letI := T.topology; IsSmooth A.ρ)
    (hS : Representation.IsIrreducible S.ρ)
    (q : (CuspidalJacquetMultiplicity.oppositeJacquet T B A).ρ.IntertwiningMap S.ρ)
    (hq : Function.Surjective q) :
    letI := T.topology
    ∃ j : A.ρ.IntertwiningMap (T.normalizedOppositeParabolicInduced B S.ρ),
      Function.Injective j := by
  exact (OppositeSupport.quotient_iff_embedding T B A.ρ S.ρ hAsm hA hS).mp ⟨q, hq⟩

end Langlands.UnitaryDualJacquetSupport
