import Langlands.Correspondence.HenniartStableImage
import Langlands.VirtualRepresentation.Weil.FiniteFactoringReduction

/-!
# Extending stable images by unramified twists

Henniart (2000), §4.4. Every irreducible class of the local Weil group is an
unramified twist `z · b₀` of a unitary class `b₀` factoring through a finite
quotient. Given stable images in every rank, `z · b₀` is sent to the unramified
twist by `z` of the stable image of `b₀`. The unramified-twist independence
statement makes this independent of the decomposition. The result is a
rank-preserving map of bases and a supercuspidal map agreeing with the stable
images on finite-image unitary classes.
-/

noncomputable section

namespace Langlands.Henniart.Extension

open Langlands.Correspondence Langlands.VirtualRepresentation StableMap

universe uK uW uV uE

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p)

/-- `b` is the unramified twist by `z` of the unitary class `b₀`, whose stable
image is the generator of `π₀`. -/
def IsStableDecomposition (b : LocalWeil.Basis.{uK, uW} K) (z : ℂˣ)
    (b₀ : LocalWeil.UnitaryBasis.{uK, uW} K)
    (π₀ : PadicSupercuspidal.UnitaryBasis.{uK, uV} K) : Prop :=
  Weil.twistBasisEquiv (Weil.Local.localUnramifiedCharacter K z) b₀.val = b ∧
    IsStableImage.{uK, uW, uV, uE} K b₀ (generator π₀)

theorem IsStableDecomposition.eq_twist_inv {b : LocalWeil.Basis.{uK, uW} K} {z : ℂˣ}
    {b₀ : LocalWeil.UnitaryBasis.{uK, uW} K} {π₀ : PadicSupercuspidal.UnitaryBasis.{uK, uV} K}
    (h : IsStableDecomposition.{uK, uW, uV, uE} K b z b₀ π₀) :
    b₀.val = weilUnramifiedTwist K z⁻¹ b := by
  rw [← h.1, weilUnramifiedTwist, ← Equiv.trans_apply, Weil.twistBasisEquiv_mul]
  have : Weil.Local.unramifiedCharacter (Weil.Local.localDegree K) z⁻¹ *
      Weil.Local.localUnramifiedCharacter K z = 1 := by
    ext w
    simp [Weil.Local.localUnramifiedCharacter]
  rw [this, Weil.twistBasisEquiv_one]
  rfl

/-- Stable images in every rank give a stable decomposition of every class. -/
theorem exists_stableDecomposition
    (hSC : StableCorrespondenceStatement.{uK, uW, uV, uE}) (b : LocalWeil.Basis.{uK, uW} K) :
    ∃ (z : ℂˣ) (π₀ : PadicSupercuspidal.UnitaryBasis.{uK, uV} K),
      ∃ b₀ : LocalWeil.UnitaryBasis.{uK, uW} K,
        IsStableDecomposition.{uK, uW, uV, uE} K b z b₀ π₀ := by
  obtain ⟨z, b₀, Q, hQ, hQf, q, hq, hb, -⟩ :=
    LocalWeil.unramifiedTwistFiniteFactoring.{uK, uW} p K b
  obtain ⟨y, hy⟩ := (hSC p K b₀.val.1).1 b₀ rfl ⟨Q, hQ, hQf, q, hq⟩
  obtain ⟨π₀, rfl, -⟩ := hy.exists_generator K
  exact ⟨z, π₀, b₀, hb, hy⟩

/-- The extension of the stable images to all irreducible classes, as a map of
bases: a chosen stable decomposition `b = z · b₀` is sent to `z` times the stable
image of `b₀`. -/
def extensionBasis (hSC : StableCorrespondenceStatement.{uK, uW, uV, uE})
    (b : LocalWeil.Basis.{uK, uW} K) : PadicSupercuspidal.Basis.{uK, uV} K :=
  PadicSupercuspidal.unramifiedTwistBasisEquiv K
    (exists_stableDecomposition K hSC b).choose
    (exists_stableDecomposition K hSC b).choose_spec.choose.val

theorem extensionBasis_spec (hSC : StableCorrespondenceStatement.{uK, uW, uV, uE})
    (b : LocalWeil.Basis.{uK, uW} K) :
    ∃ (z : ℂˣ) (π₀ : PadicSupercuspidal.UnitaryBasis.{uK, uV} K)
      (b₀ : LocalWeil.UnitaryBasis.{uK, uW} K),
      IsStableDecomposition.{uK, uW, uV, uE} K b z b₀ π₀ ∧
        extensionBasis K hSC b = PadicSupercuspidal.unramifiedTwistBasisEquiv K z π₀.val :=
  ⟨_, _, _, (exists_stableDecomposition K hSC b).choose_spec.choose_spec.choose_spec, rfl⟩

/-- Unramified-twist independence makes the extension independent of the stable
decomposition. -/
theorem extensionBasis_eq (hSC : StableCorrespondenceStatement.{uK, uW, uV, uE})
    (hUTI : UnramifiedTwistIndependenceStatement.{uK, uW, uV, uE})
    {b : LocalWeil.Basis.{uK, uW} K} {z : ℂˣ} {b₀ : LocalWeil.UnitaryBasis.{uK, uW} K}
    {π₀ : PadicSupercuspidal.UnitaryBasis.{uK, uV} K}
    (h : IsStableDecomposition.{uK, uW, uV, uE} K b z b₀ π₀) :
    extensionBasis K hSC b = PadicSupercuspidal.unramifiedTwistBasisEquiv K z π₀.val := by
  obtain ⟨z₁, π₁, b₁, h₁, he⟩ := extensionBasis_spec K hSC b
  rw [he]
  have hgen := hUTI p K b z₁ z b₁ b₀ (generator π₁) (generator π₀)
    (IsStableDecomposition.eq_twist_inv K h₁) (IsStableDecomposition.eq_twist_inv K h) h₁.2 h.2
  have hinc : ∀ π : PadicSupercuspidal.UnitaryBasis.{uK, uV} K,
      PadicSupercuspidal.includeUnitary K (generator π) = generator π.val := by
    intro π
    simp [PadicSupercuspidal.includeUnitary, Supercuspidal.includeUnitary, includeSubset,
      VirtualRepresentation.map, generator]
  rw [hinc, hinc, PadicSupercuspidal.unramifiedTwistLatticeEquiv_generator,
    PadicSupercuspidal.unramifiedTwistLatticeEquiv_generator] at hgen
  exact Finsupp.single_left_injective one_ne_zero hgen

/-- The extension preserves rank. -/
theorem extensionBasis_rank (hSC : StableCorrespondenceStatement.{uK, uW, uV, uE})
    (b : LocalWeil.Basis.{uK, uW} K) : (extensionBasis K hSC b).1 = b.1 := by
  obtain ⟨z, π₀, b₀, h, he⟩ := extensionBasis_spec K hSC b
  rw [he, PadicSupercuspidal.unramifiedTwistBasisEquiv_rank]
  obtain ⟨π, hπ, hrank⟩ := h.2.exists_generator K
  have : π = π₀ := by
    have := Finsupp.single_left_injective (one_ne_zero (α := ℤ)) hπ
    exact this.symm
  subst this
  rw [hrank, ← h.1, Weil.twistBasisEquiv_rank]

/-- Read a supercuspidal basis class of rank `n` in the class space of rank `n`. -/
def rankCast {n : ℕ+} (B : PadicSupercuspidal.Basis.{uK, uV} K) (h : B.1 = n) :
    SupercuspidalAutomorphicClass.{uK, uV} K n :=
  h ▸ B.2

theorem sigma_rankCast {n : ℕ+} (B : PadicSupercuspidal.Basis.{uK, uV} K) (h : B.1 = n) :
    (⟨n, rankCast K B h⟩ : PadicSupercuspidal.Basis.{uK, uV} K) = B := by
  subst h
  rfl

/-- The supercuspidal map of Henniart's §4.4. -/
def extensionMap (hSC : StableCorrespondenceStatement.{uK, uW, uV, uE}) :
    SupercuspidalMap.{uK, uW, uV} K :=
  fun n σ => rankCast K (extensionBasis K hSC ⟨n, σ⟩) (extensionBasis_rank K hSC ⟨n, σ⟩)

theorem sigma_extensionMap (hSC : StableCorrespondenceStatement.{uK, uW, uV, uE})
    (n : ℕ+) (σ : IrreducibleWeilClass.{uK, uW} K n) :
    (⟨n, extensionMap K hSC n σ⟩ : PadicSupercuspidal.Basis.{uK, uV} K) =
      extensionBasis K hSC ⟨n, σ⟩ :=
  sigma_rankCast K _ _

/-- On a finite-image unitary class the extension is the stable image. -/
theorem extensionMap_agrees (hSC : StableCorrespondenceStatement.{uK, uW, uV, uE})
    (hUTI : UnramifiedTwistIndependenceStatement.{uK, uW, uV, uE})
    (σ : LocalWeil.UnitaryBasis.{uK, uW} K) (hσ : IsFiniteFactoring K σ) :
    ∃ y : PadicSupercuspidal.UnitaryLattice.{uK, uV} K,
      IsStableImage.{uK, uW, uV, uE} K σ y ∧
        PadicSupercuspidal.includeUnitary K y =
          generator (⟨σ.val.1, extensionMap K hSC σ.val.1 σ.val.2⟩ :
            PadicSupercuspidal.Basis.{uK, uV} K) := by
  obtain ⟨y, hy⟩ := (hSC p K σ.val.1).1 σ rfl hσ
  obtain ⟨π₀, rfl, -⟩ := hy.exists_generator K
  refine ⟨generator π₀, hy, ?_⟩
  have hdec : IsStableDecomposition.{uK, uW, uV, uE} K σ.val 1 σ π₀ := by
    refine ⟨?_, hy⟩
    have : Weil.Local.localUnramifiedCharacter K 1 = 1 := by
      ext w
      simp [Weil.Local.localUnramifiedCharacter]
    rw [this, Weil.twistBasisEquiv_one]
    rfl
  rw [sigma_extensionMap]
  change PadicSupercuspidal.includeUnitary K (generator π₀) = generator (extensionBasis K hSC σ.val)
  rw [extensionBasis_eq K hSC hUTI hdec, PadicSupercuspidal.unramifiedTwistBasisEquiv_one]
  simp [PadicSupercuspidal.includeUnitary, Supercuspidal.includeUnitary, includeSubset,
    VirtualRepresentation.map, generator]

end Langlands.Henniart.Extension
