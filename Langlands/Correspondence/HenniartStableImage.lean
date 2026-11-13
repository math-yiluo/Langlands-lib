import Langlands.VirtualRepresentation.UnitaryDegreeGenerators
import Langlands.Correspondence.HenniartStableMapStatement

/-!
# Common candidates and stable images

Elementary consequences of the definitions in `HenniartStableMapStatement`.
A candidate at a finite quotient `q` is a candidate at every quotient through
which `q` factors. Products of finitely many quotients, together with candidate
existence, give one candidate whose values are the stable images of finitely
many classes at once. Stable images are unique and are the classes of unitary
supercuspidal representations of the same rank.
-/

noncomputable section

namespace Langlands.Henniart.StableMap

open Langlands.Correspondence Langlands.VirtualRepresentation

universe uK uW uV uE uQ uR

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p)

/-- A class factoring through `f ∘ q` factors through `q`. -/
theorem unitaryFiniteFactoringSupported_comp_le {Q : Type uQ} [Group Q] [Finite Q]
    {R : Type uR} [Group R] [Finite R]
    (q : Field.absoluteGaloisGroup K.Carrier →* Q) (f : Q →* R) :
    LocalWeil.unitaryFiniteFactoringSupported.{uK, uW, uR} K (f.comp q) ≤
      LocalWeil.unitaryFiniteFactoringSupported.{uK, uW, uQ} K q := by
  intro x hx
  simp only [LocalWeil.unitaryFiniteFactoringSupported, Weil.unitaryFactoringSupported,
    supported, Finsupp.mem_supported] at hx ⊢
  intro b hb
  obtain ⟨A, hA⟩ := hx hb
  exact ⟨FiniteRepresentation.of (A.representation.comp f), hA⟩

/-- A candidate at `q` is a candidate at every quotient `f ∘ q`. -/
theorem IsCandidate.comp {Q : Type uQ} [Group Q] [Finite Q] {R : Type uR} [Group R]
    [Finite R] {q : Field.absoluteGaloisGroup K.Carrier →* Q} (f : Q →* R)
    {W : Submodule ℤ (LocalWeil.UnitaryLattice.{uK, uW} K)}
    {A : Submodule ℤ (PadicSupercuspidal.UnitaryLattice.{uK, uV} K)}
    {Φ : W ≃ₗ[ℤ] A} (h : IsCandidate.{uK, uW, uV, uE, uQ} K q Φ) :
    IsCandidate.{uK, uW, uV, uE, uR} K (f.comp q) Φ :=
  ⟨(unitaryFiniteFactoringSupported_comp_le K q f).trans h.1, h.2⟩

/-- The body of `IsStableImage` at one specified quotient. -/
theorem IsStableImage.exists_quotient {σ : LocalWeil.UnitaryBasis.{uK, uW} K}
    {y : PadicSupercuspidal.UnitaryLattice.{uK, uV} K}
    (h : IsStableImage.{uK, uW, uV, uE} K σ y) :
    ∃ (Q : Type uK) (_ : Group Q) (_ : Finite Q)
      (q : Field.absoluteGaloisGroup K.Carrier →* Q),
      generator σ ∈ LocalWeil.unitaryFiniteFactoringSupported.{uK, uW, uK} K q ∧
      ∀ {R : Type uK} [Group R] [Finite R] (r : Field.absoluteGaloisGroup K.Carrier →* R)
        (f : R →* Q), f.comp r = q →
        ∀ (W : Submodule ℤ (LocalWeil.UnitaryLattice.{uK, uW} K))
          (A : Submodule ℤ (PadicSupercuspidal.UnitaryLattice.{uK, uV} K))
          (Φ : W ≃ₗ[ℤ] A), IsCandidate.{uK, uW, uV, uE, uK} K r Φ →
          ∃ x : W, (x : LocalWeil.UnitaryLattice.{uK, uW} K) = generator σ ∧
            (Φ x : PadicSupercuspidal.UnitaryLattice.{uK, uV} K) = y := by
  obtain ⟨Q, _, _, q, hσ, -, hall⟩ := h
  refine ⟨Q, inferInstance, inferInstance, q, hσ, ?_⟩
  intro R _ _ r f hfr W A Φ hΦ
  have hΦq : IsCandidate.{uK, uW, uV, uE, uK} K q Φ := by
    rw [← hfr]
    exact hΦ.comp K f
  refine ⟨⟨generator σ, hΦq.1 hσ⟩, rfl, ?_⟩
  exact hall W A Φ hΦq _ rfl

/-- Candidate existence at all finite quotients gives, for finitely many classes
with stable images, one candidate sending each class to its stable image. -/
theorem exists_common_candidate
    (hexist : CandidateExistenceStatement.{uK, uW, uV, uE, uK})
    {ι : Type} [Finite ι] (σ : ι → LocalWeil.UnitaryBasis.{uK, uW} K)
    (y : ι → PadicSupercuspidal.UnitaryLattice.{uK, uV} K)
    (h : ∀ i, IsStableImage.{uK, uW, uV, uE} K (σ i) (y i)) :
    ∃ (W : Submodule ℤ (LocalWeil.UnitaryLattice.{uK, uW} K))
      (A : Submodule ℤ (PadicSupercuspidal.UnitaryLattice.{uK, uV} K)) (Φ : W ≃ₗ[ℤ] A),
      LatticeMap.HenniartProperties.{uK, uW, uV, uE} K Φ ∧
      ∀ i, ∃ x : W, (x : LocalWeil.UnitaryLattice.{uK, uW} K) = generator (σ i) ∧
        (Φ x : PadicSupercuspidal.UnitaryLattice.{uK, uV} K) = y i := by
  choose Q hQ hQf q hq hall using fun i => (h i).exists_quotient K
  let := hQ
  let := hQf
  let r : Field.absoluteGaloisGroup K.Carrier →* ((i : ι) → Q i) := MonoidHom.pi q
  obtain ⟨W, A, Φ, hΦ⟩ := hexist p K ((i : ι) → Q i) r
  refine ⟨W, A, Φ, hΦ.2, fun i => ?_⟩
  exact hall i r (Pi.evalMonoidHom Q i) (by ext g; rfl) W A Φ hΦ

/-- Stable images are unique once candidates exist at all finite quotients. -/
theorem IsStableImage.unique
    (hexist : CandidateExistenceStatement.{uK, uW, uV, uE, uK})
    {σ : LocalWeil.UnitaryBasis.{uK, uW} K}
    {y₁ y₂ : PadicSupercuspidal.UnitaryLattice.{uK, uV} K}
    (h₁ : IsStableImage.{uK, uW, uV, uE} K σ y₁)
    (h₂ : IsStableImage.{uK, uW, uV, uE} K σ y₂) : y₁ = y₂ := by
  obtain ⟨W, A, Φ, -, hx⟩ := exists_common_candidate K hexist (fun _ : Bool => σ)
    (fun b => if b then y₁ else y₂) (fun b => by cases b <;> simpa)
  obtain ⟨x₁, hx₁, hΦ₁⟩ := hx true
  obtain ⟨x₂, hx₂, hΦ₂⟩ := hx false
  have : x₁ = x₂ := Subtype.ext (hx₁.trans hx₂.symm)
  simp only [ite_true] at hΦ₁
  simp only [Bool.false_eq_true, ite_false] at hΦ₂
  rw [← hΦ₁, ← hΦ₂, this]

/-- A candidate sends a generator in its domain to the generator of a unitary
supercuspidal class of the same rank. -/
theorem IsCandidate.exists_generator {W : Submodule ℤ (LocalWeil.UnitaryLattice.{uK, uW} K)}
    {A : Submodule ℤ (PadicSupercuspidal.UnitaryLattice.{uK, uV} K)} {Φ : W ≃ₗ[ℤ] A}
    (hΦ : LatticeMap.HenniartProperties.{uK, uW, uV, uE} K Φ)
    (σ : LocalWeil.UnitaryBasis.{uK, uW} K) (x : W)
    (hx : (x : LocalWeil.UnitaryLattice.{uK, uW} K) = generator σ) :
    ∃ π : PadicSupercuspidal.UnitaryBasis.{uK, uV} K,
      (Φ x : PadicSupercuspidal.UnitaryLattice.{uK, uV} K) = generator π ∧
        π.val.1 = σ.val.1 := by
  obtain ⟨π, hπ⟩ := (hΦ.1.2.1 x).mp ⟨σ, hx⟩
  refine ⟨π, hπ, ?_⟩
  have hdeg := hΦ.1.1.2 x
  rw [hπ, hx, PadicSupercuspidal.unitaryDegree_generator,
    LocalWeil.unitaryDegree_generator] at hdeg
  exact PNat.coe_injective (by exact_mod_cast hdeg)

/-- A stable image is the generator of a unitary supercuspidal class of the same
rank. -/
theorem IsStableImage.exists_generator {σ : LocalWeil.UnitaryBasis.{uK, uW} K}
    {y : PadicSupercuspidal.UnitaryLattice.{uK, uV} K}
    (h : IsStableImage.{uK, uW, uV, uE} K σ y) :
    ∃ π : PadicSupercuspidal.UnitaryBasis.{uK, uV} K, y = generator π ∧ π.val.1 = σ.val.1 := by
  obtain ⟨Q, _, _, q, hσ, ⟨W, A, Φ, hΦ⟩, hall⟩ := h
  have hy := hall W A Φ hΦ ⟨generator σ, hΦ.1 hσ⟩ rfl
  obtain ⟨π, hπ, hrank⟩ := IsCandidate.exists_generator K hΦ.2 σ ⟨generator σ, hΦ.1 hσ⟩ rfl
  exact ⟨π, hy.symm.trans hπ, hrank⟩

/-- A stable image determines its class: the unique stable image of a class
factoring through a finite quotient. -/
theorem IsStableImage.isFiniteFactoring {σ : LocalWeil.UnitaryBasis.{uK, uW} K}
    {y : PadicSupercuspidal.UnitaryLattice.{uK, uV} K}
    (h : IsStableImage.{uK, uW, uV, uE} K σ y) : IsFiniteFactoring K σ := by
  obtain ⟨Q, hQ, hQf, q, hσ, -⟩ := h
  exact ⟨Q, hQ, hQf, q, hσ⟩

end Langlands.Henniart.StableMap
