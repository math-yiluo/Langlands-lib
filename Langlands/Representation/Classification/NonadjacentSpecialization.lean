import Langlands.Representation.Classification.NonadjacentAssembly
import Langlands.Representation.Classification.TwoSupercuspidalProductDualTwist
import Langlands.Representation.Classification.CuspidalIntegralTwistFreenessProof
import Langlands.Representation.Smooth.Contragredient.InvariantPairingProof
import Langlands.Representation.Filtration.ObjectTransport
import Langlands.HarmonicAnalysis.PadicUnitaryAdditiveCharacterExistsProof

/-! Specialization of the BZ77 Theorem 4.2 core (`NonadjacentAssembly`) to
two supercuspidal blocks.

A nonzero invariant form between irreducible `A` and `ν B~` forces `B ≅ ν A`; under
the nonadjacency hypotheses and integral twist freeness, no such form exists
between the derivative pieces of `ρ × ρ'` and of `ν (ρ × ρ')~`. -/

noncomputable section

open CategoryTheory

namespace Langlands.Classification.NonadjacentAssembly

open GeneralLinear HarmonicAnalysis Derivative InvariantBilinear

universe uF u uV uW

section Separation

variable {G : Type*} [Group G] [TopologicalSpace G]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {W : Type*} [AddCommGroup W] [Module ℂ W]

/-- The left kernel of an invariant form is invariant. -/
def leftKernel {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (B : forms ρ σ (fun _ => (1 : ℂ))) : Subrepresentation ρ where
  toSubmodule := LinearMap.ker B.val
  apply_mem_toSubmodule g v hv := by
    rw [LinearMap.mem_ker] at hv ⊢
    ext w
    have h := B.property g v (σ g⁻¹ w)
    rw [σ.self_inv_apply] at h
    rw [h, hv]
    simp

omit [TopologicalSpace G] in
/-- An invariant form on irreducible representations is zero or left nondegenerate. -/
theorem left_nondegenerate {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (hρ : ρ.IsIrreducible) (B : forms ρ σ (fun _ => (1 : ℂ))) (hB : B ≠ 0) :
    ∀ v, (∀ w, B.val v w = 0) → v = 0 := by
  intro v hv
  rcases hρ.eq_bot_or_eq_top (leftKernel B) with h | h
  · have hv' : v ∈ (leftKernel B).toSubmodule := LinearMap.mem_ker.mpr (LinearMap.ext hv)
    rw [h] at hv'
    exact (Submodule.mem_bot ℂ).mp hv'
  · exfalso
    apply hB
    apply Subtype.ext
    ext x w
    have hx : x ∈ (leftKernel B).toSubmodule := by
      rw [h]
      exact Submodule.mem_top
    exact congrArg (fun f => f w) (LinearMap.mem_ker.mp hx)

/-- A nonzero invariant form between an irreducible admissible `ρ` and an
irreducible smooth `σ` identifies `σ` with the smooth dual of `ρ`. -/
theorem nonempty_equiv_of_forms_ne_zero [IsTopologicalGroup G]
    (hcof : CompactOpenCofinal G) {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (hρ : IsAdmissible ρ) (hσ : IsSmooth σ) (hρi : ρ.IsIrreducible) (hσi : σ.IsIrreducible)
    (B : forms ρ σ (fun _ => (1 : ℂ))) (hB : B ≠ 0) :
    Nonempty (σ.Equiv (smoothContragredient ρ)) := by
  have hBf : (flipEquiv ρ σ _ B) ≠ 0 := by
    intro h
    exact hB ((flipEquiv ρ σ _).map_eq_zero_iff.mp h)
  obtain ⟨E, -⟩ := smoothInvariantPairingDuality (G := G) hcof ρ σ hρ hσ B.val.flip
    (fun g w v => by
      have h := B.property g v w
      simpa using h)
    (left_nondegenerate hσi _ hBf)
    (left_nondegenerate hρi B hB)
  exact ⟨E⟩

end Separation

section Classes

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

open ProductDualTwist

/-- A nonzero invariant form between `A` and `ν B'~` forces `B' ≅ ν A`. -/
theorem twist_class_eq_of_length_ne_zero' {a : ℕ}
    (A B' : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := a))
    (hB : letI := T.topology
      length A.obj.representation (dualTwist F T B').obj.representation
        (fun _ => (1 : ℂ)) ≠ 0) :
    letI := T.topology
    B'.isoClass = T.supercuspidalClassRealPowerTwist a 1 A.isoClass := by
  let _ := T.topology
  let _ := T.generalLinearTopologicalGroup a
  have hcof := GeneralLinear.compactOpen_cofinal F T a
  have hsc := T.supercuspidalContragredientClosed supercuspidalContragredient.{uF, uV} a
  have hnt : Nontrivial (forms A.obj.representation (dualTwist F T B').obj.representation
      (fun _ => (1 : ℂ))) := by
    rw [← not_subsingleton_iff_nontrivial]
    exact fun h => hB (Module.length_eq_zero_iff.mpr h)
  obtain ⟨β, hβ⟩ := exists_ne (0 : forms A.obj.representation
    (dualTwist F T B').obj.representation (fun _ => (1 : ℂ)))
  obtain ⟨E⟩ := nonempty_equiv_of_forms_ne_zero hcof A.property.2.1
    (dualTwist F T B').obj.isSmooth A.property.1 (dualTwist F T B').property.1 β hβ
  have hc : SupercuspidalClass.contragredient hcof hsc A.isoClass =
      (dualTwist F T B').isoClass :=
    (SupercuspidalClass.contragredient_isoClass_eq_isoClass_iff hcof hsc A _).mpr ⟨E.symm⟩
  have hA : A.isoClass = T.supercuspidalClassRealPowerTwist a (-1) B'.isoClass := by
    rw [← SupercuspidalClass.contragredient_contragredient hcof hsc A.isoClass, hc]
    change SupercuspidalClass.contragredient hcof hsc
      (SupercuspidalClass.twist _ _ _ (SupercuspidalClass.contragredient hcof hsc B'.isoClass)) = _
    rw [SupercuspidalClass.contragredient_twist, SupercuspidalClass.contragredient_contragredient]
    exact SupercuspidalClass.twist_congr
      (realPowerCharacter_neg (T.determinantNorm a) 1).symm _ _ _ _ _
  rw [hA, T.supercuspidalClassRealPowerTwist_add, add_neg_cancel,
    T.supercuspidalClassRealPowerTwist_zero]

/-- A nonzero invariant form between `A` and `ν B'~`, after identifying both
ranks with `m`, forces `B' ≅ ν A` as rank-indexed supercuspidal classes. -/
theorem twist_class_eq_of_length_ne_zero {a b m : ℕ}
    (A : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := a))
    (B' : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := b))
    (h1 : a = m) (h2 : b = m)
    (hB : letI := T.topology
      length ((generalLinearRankCast T h1).obj A.obj).representation
        ((generalLinearRankCast T h2).obj (dualTwist F T B').obj).representation
        (fun _ => (1 : ℂ)) ≠ 0) :
    letI := T.topology
    (⟨b, B'.isoClass⟩ : Σ d : ℕ, SupercuspidalClass.{uV, uF} (F := F.Carrier) (n := d)) =
      ⟨a, T.supercuspidalClassRealPowerTwist a 1 A.isoClass⟩ := by
  subst h1 h2
  exact congrArg (Sigma.mk _) (twist_class_eq_of_length_ne_zero' F T A B' hB)

/-- No positive-rank supercuspidal class is fixed by `ν`, as a rank-indexed class. -/
theorem sigma_ne_twist {a : ℕ} (ha : 0 < a)
    (A : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := a)) :
    letI := T.topology
    (⟨a, A.isoClass⟩ : Σ d : ℕ, SupercuspidalClass.{uV, uF} (F := F.Carrier) (n := d)) ≠
      ⟨a, T.supercuspidalClassRealPowerTwist a 1 A.isoClass⟩ := by
  let _ := T.topology
  intro h
  have h' : A.isoClass = T.supercuspidalClassRealPowerTwist a 1 A.isoClass :=
    eq_of_heq (Sigma.mk.inj_iff.mp h).2
  have hfix : (PadicField.TopologicalData.CuspidalDatum.mk a ha A.isoClass :
      T.CuspidalDatum.{uV, uF}).twist ((1 : ℤ) : ℝ) =
        PadicField.TopologicalData.CuspidalDatum.mk a ha A.isoClass := by
    change PadicField.TopologicalData.CuspidalDatum.mk a ha
      (T.supercuspidalClassRealPowerTwist a ((1 : ℤ) : ℝ) A.isoClass) = _
    rw [Int.cast_one, ← h']
  exact one_ne_zero ((cuspidalIntegralTwistFreeness.{uF, uV} F T _ 1).mp hfix)

end Classes

end Langlands.Classification.NonadjacentAssembly
