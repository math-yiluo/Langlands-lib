import Langlands.Group.GL.CartanQuotientLawsProof

/-!
# Constructing normalized Cartan coordinates

Subtracting the last coordinate gives an actual element of the published
normalized chamber. The construction preserves the existing quotient cells
and radial modulus; it assumes no Cartan covering or uniqueness theorem.
-/

noncomputable section

namespace Langlands.GeneralLinear.CartanQuotient

universe uF

theorem antitone_shift {n : ℕ} {lam : Fin n → ℤ} (hlam : Antitone lam) (c : ℤ) :
    Antitone (shift lam c) := by
  intro i j hij
  have h := hlam hij
  simp only [shift]
  omega

/-- Normalize an antitone tuple of positive rank by subtracting its last entry. -/
def normalize {m : ℕ} (lam : Fin (m + 1) → ℤ) (hlam : Antitone lam) :
    NormalizedTuple (m + 1) :=
  ⟨shift lam (-lam (Fin.last m)),
    (normalized_iff_antitone_last_eq_zero m _).mpr
      ⟨antitone_shift hlam _, by simp [shift]⟩⟩

@[simp] theorem normalize_apply {m : ℕ} (lam : Fin (m + 1) → ℤ)
    (hlam : Antitone lam) (i : Fin (m + 1)) :
    (normalize lam hlam).val i = lam i - lam (Fin.last m) :=
  rfl

@[simp] theorem normalize_last {m : ℕ} (lam : Fin (m + 1) → ℤ)
    (hlam : Antitone lam) :
    (normalize lam hlam).val (Fin.last m) = 0 := by
  simp

theorem normalize_eq_self {m : ℕ} (lam : NormalizedTuple (m + 1)) :
    normalize lam.val lam.property.1 = lam := by
  apply Subtype.ext
  funext i
  have hlast := (normalized_iff_antitone_last_eq_zero m lam.val).mp lam.property
  simp [hlast.2]

theorem normalize_shift {m : ℕ} (lam : Fin (m + 1) → ℤ)
    (hlam : Antitone lam) (c : ℤ) :
    normalize (shift lam c) (antitone_shift hlam c) = normalize lam hlam := by
  apply Subtype.ext
  funext i
  simp [shift]

theorem normalize_eq_iff_shift {m : ℕ} (lam mu : Fin (m + 1) → ℤ)
    (hlam : Antitone lam) (hmu : Antitone mu) :
    normalize lam hlam = normalize mu hmu ↔ ∃ c : ℤ, mu = shift lam c := by
  constructor
  · intro h
    refine ⟨mu (Fin.last m) - lam (Fin.last m), ?_⟩
    funext i
    have hi := congrArg (fun a : NormalizedTuple (m + 1) => a.val i) h
    simp only [normalize_apply] at hi
    change mu i = lam i + (mu (Fin.last m) - lam (Fin.last m))
    omega
  · rintro ⟨c, rfl⟩
    exact (normalize_shift lam hlam c).symm

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData)

theorem subgroupCell_normalize {m : ℕ} (H : Subgroup (GeneralLinear (m + 1) F.Carrier))
    (lam : Fin (m + 1) → ℤ) (hlam : Antitone lam) :
    subgroupCell T H (normalize lam hlam).val = subgroupCell T H lam :=
  subgroupCell_shift T H lam (-lam (Fin.last m))

theorem cell_normalize {m : ℕ} (lam : Fin (m + 1) → ℤ) (hlam : Antitone lam) :
    cell T (normalize lam hlam).val = cell T lam :=
  cell_shift T lam (-lam (Fin.last m))

theorem degree_normalize {m : ℕ} (lam : Fin (m + 1) → ℤ) (hlam : Antitone lam) :
    degree (normalize lam hlam).val = degree lam :=
  degree_shift lam (-lam (Fin.last m))

theorem delta_normalize {m : ℕ} (lam : Fin (m + 1) → ℤ) (hlam : Antitone lam) :
    delta T (normalize lam hlam).val = delta T lam :=
  delta_shift T lam (-lam (Fin.last m))

theorem quotientMap_representative_normalize {m : ℕ} (lam : Fin (m + 1) → ℤ)
    (hlam : Antitone lam) :
    quotientMap F (m + 1) (representative T (normalize lam hlam).val) =
      quotientMap F (m + 1) (representative T lam) :=
  quotientMap_representative_shift T lam (-lam (Fin.last m))

end Langlands.GeneralLinear.CartanQuotient
