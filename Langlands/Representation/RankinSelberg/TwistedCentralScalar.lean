import Langlands.Representation.RankinSelberg.CentralSpectralElement
import Langlands.Representation.Smooth.Contragredient.LawsProof
import Langlands.Representation.Twist.Definitions
import Mathlib.RepresentationTheory.Irreducible
import Langlands.Representation.Shahidi.Induction

/-! # Central scalars forced by a normalized contragredient twist -/

noncomputable section

namespace Langlands.RankinSelberg

universe uG uF uV uW

section General

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V] [Nontrivial V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {π : Representation ℂ G V} {σ : Representation ℂ G W}

/-- The evaluation pairing of a twisted contragredient equivalence forces the
product of any two simultaneous scalar actions. -/
theorem scalar_product_of_twisted_contragredient
    (χ : G →* ℂˣ) (e : (Langlands.twist χ π).Equiv (smoothContragredient σ))
    (g : G) (a b : ℂ)
    (ha : ∀ v, π g v = a • v) (hb : ∀ w, σ g w = b • w) :
    (χ g : ℂ) * (a * b) = 1 := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hev : e v ≠ 0 := by
    intro hz
    apply hv
    apply e.toLinearEquiv.injective
    change e v = e (0 : V)
    simpa only [map_zero] using hz
  obtain ⟨w, hw⟩ : ∃ w : W, (e v).val w ≠ 0 := by
    by_contra hz
    apply hev
    apply Subtype.ext
    ext w
    exact not_not.mp (not_exists.mp hz w)
  have ht := Representation.IntertwiningMap.isIntertwining
    (Langlands.twist χ π) (smoothContragredient σ) e.toIntertwiningMap g v
  change e (Langlands.twist χ π g v) = smoothContragredient σ g (e v) at ht
  have hi := smoothDualPairing_invariant g (e v) w
  rw [← ht] at hi
  change smoothDualPairing σ (e ((χ g : ℂ) • π g v)) (σ g w) =
    smoothDualPairing σ (e v) w at hi
  rw [ha, hb] at hi
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at hi
  apply mul_right_cancel₀ hw
  simpa only [smoothDualPairing, Submodule.subtype_apply,
    mul_assoc, mul_comm, mul_left_comm, one_mul] using hi

end General

section Padic

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
  (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)

/-- The normalized determinant weight at `-u` cancels the product of the two
central scalar actions. -/
def HasDeterminantCentralScalarIdentity (u : ℂ) : Prop :=
  ∀ (z : Subgroup.center (Langlands.GeneralLinear (n + 1) F.Carrier)) (a b : ℂ),
    (∀ v, π z v = a • v) → (∀ w, σ z w = b • w) →
      determinantWeight (normalizedAbsoluteValue T)
        (z : Langlands.GeneralLinear (n + 1) F.Carrier) (-u) * (a * b) = 1

/-- An actual normalized contragredient twist proves the central scalar
identity without a convergence or unitarity hypothesis. -/
theorem hasDeterminantCentralScalarIdentity_of_contragredient_twist
    (u : ℂ) (hπ : π.IsIrreducible) :
    letI := T.topology
    haveI := T.generalLinearTopologicalGroup (n + 1)
    Nonempty ((Langlands.twist (T.determinantComplexPower (n + 1) (-u)) π).Equiv
      (smoothContragredient σ)) →
      HasDeterminantCentralScalarIdentity T π σ u := by
  let := T.topology
  let := T.generalLinearTopologicalGroup (n + 1)
  intro ⟨e⟩ z a b ha hb
  let := hπ
  let : Nontrivial V := IsSimpleModule.nontrivial
    (MonoidAlgebra ℂ (Langlands.GeneralLinear (n + 1) F.Carrier)) π.asModule
  have h := scalar_product_of_twisted_contragredient
    (T.determinantComplexPower (n + 1) (-u)) e
      (z : Langlands.GeneralLinear (n + 1) F.Carrier) a b ha hb
  rwa [T.determinantComplexPower_apply] at h

/-- At the inverse-uniformizer scalar, the identity uses the actual spectral
parameter and the common rank. -/
theorem HasDeterminantCentralScalarIdentity.spectralPoint_identity
    {u : ℂ} (h : HasDeterminantCentralScalarIdentity T π σ u) (a b : ℂ)
    (ha : ∀ v, π (centralSpectralElement T (n + 1)) v = a • v)
    (hb : ∀ w, σ (centralSpectralElement T (n + 1)) w = b • w) :
    spectralPoint T.residueCardinality u ^ (n + 1) * (a * b) = 1 := by
  have h' := h ⟨centralSpectralElement T (n + 1),
    centralSpectralElement_mem_center T (n + 1)⟩ a b ha hb
  rwa [determinantWeight_centralSpectralElement] at h'

end Padic

end Langlands.RankinSelberg
