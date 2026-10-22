import Langlands.Weil.Local.RepresentationStatements
import Langlands.Weil.Local.AssemblyProof
import Langlands.Weil.Representation.CharacterNormalizationProof
import Langlands.LocalField.Normalization.Proof

/-! # Character normalization and norm hypotheses on the actual local Weil group -/

noncomputable section

namespace Langlands.Weil.Local

universe u v

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)

/-- Inertia-trivial characters are the continuous degree characters, uniquely
determined by their value at the chosen geometric Frobenius. -/
theorem localUnramifiedCharacterClassificationFor :
    LocalUnramifiedCharacterClassificationFor F := by
  intro χ
  constructor
  · intro hχ
    have heq :
        (localUnramifiedCharacter F (χ (localGeometricFrobenius F))).toMonoidHom = χ := by
      apply MonoidHom.ext
      intro g
      have hd :
          localDegree F (localGeometricFrobenius F ^ localDegreeInt F g) =
            localDegree F g := by
        rw [map_zpow, localGeometricFrobenius_degree]
        apply Multiplicative.toAdd.injective
        simp [localDegreeInt]
      have hi : g / localGeometricFrobenius F ^ localDegreeInt F g ∈ localInertia F := by
        change localDegree F (g / localGeometricFrobenius F ^ localDegreeInt F g) = 1
        rw [map_div, hd, div_self']
      have hc := hχ ⟨_, hi⟩
      have hg : χ g / χ (localGeometricFrobenius F) ^ localDegreeInt F g = 1 := by
        simpa using hc
      change χ (localGeometricFrobenius F) ^ localDegreeInt F g = χ g
      exact (div_eq_one.mp hg).symm
    refine ⟨?_, χ (localGeometricFrobenius F), ⟨heq, rfl⟩, ?_⟩
    · rw [← heq]
      exact (localUnramifiedCharacter F _).continuous
    · intro z hz
      exact hz.2
  · rintro ⟨_, z, ⟨hz, _⟩, _⟩ i
    rw [← hz]
    exact localUnramifiedCharacter_on_inertia F z i

/-- Bundle the generic determinant and rank-one characters with their proved
continuity, retaining determinant equality and uniqueness. -/
theorem localWeilCharacterNormalizationFor :
    LocalWeilCharacterNormalizationFor.{u, v} F := by
  intro A hA
  obtain ⟨hdet, hrank⟩ := representationCharacterNormalization
    (localWeilGroup F) A A.representation hA
  obtain ⟨δ, hδ, _⟩ := hdet
  constructor
  · refine ⟨⟨δ, hδ.1⟩, hδ.2, ?_⟩
    intro η hη
    ext g
    exact (hη g).trans (hδ.2 g).symm
  · intro hdim
    obtain ⟨χ, hχ, _⟩ := hrank hdim
    have hχdet (g : localWeilGroup F) :
        (χ g : ℂ) = LinearMap.det (A.representation g) := by
      obtain ⟨e⟩ := hχ.2
      have he := FiniteRepresentation.determinantCharacter_eq
        (A := A) (B := FiniteRepresentation.of (Langlands.characterRepresentation χ)) e
      have hg := congrArg (fun η : localWeilGroup F →* ℂˣ => (η g : ℂ)) he
      change LinearMap.det (A.representation g) =
        LinearMap.det (Langlands.characterRepresentation χ g) at hg
      rw [LinearMap.det_ring] at hg
      change LinearMap.det (A.representation g) = (χ g : ℂ) * 1 at hg
      simpa only [mul_one] using hg.symm
    refine ⟨⟨χ, hχ.1⟩, ⟨hχ.2, hχdet⟩, ?_⟩
    intro η hη
    ext g
    exact (hη.2 g).trans (hχdet g).symm

private theorem cardinality_zpow_eq_one_iff (q : ℕ) (hq : 1 < q) (n : ℤ) :
    (q : ℂ) ^ n = 1 ↔ n = 0 := by
  constructor
  · intro h
    have hn : (q : ℝ) ^ n = 1 := by
      simpa only [Complex.norm_zpow, Complex.norm_natCast, norm_one] using
        congrArg norm h
    exact (zpow_eq_one_iff_right₀ (Nat.cast_nonneg q)
      (ne_of_gt (show (1 : ℝ) < q by exact_mod_cast hq))).mp hn
  · rintro rfl
    exact zpow_zero _

/-- The norm has exactly inertia as kernel, and its nonzero-degree values
have no nonzero integer power equal to one. -/
theorem localNormFaithfulnessFor : LocalNormFaithfulnessFor F := by
  have hq := F.canonicalTopologicalData.residueCardinality_gt_one
  have hker (g : localWeilGroup F) :
      localNormCharacter F g = 1 ↔ localDegreeInt F g = 0 := by
    rw [← Units.val_inj, localNormCharacter_apply]
    simpa only [Units.val_one, neg_eq_zero] using
      cardinality_zpow_eq_one_iff F.canonicalTopologicalData.residueCardinality
        hq (-localDegreeInt F g)
  constructor
  · ext g
    change localNormCharacter F g = 1 ↔ localDegree F g = 1
    rw [hker]
    exact Multiplicative.toAdd.injective.eq_iff
  · intro g hg n hn he
    have hc := congrArg (fun z : ℂˣ => (z : ℂ)) he
    rw [Units.val_zpow_eq_zpow_val, localNormCharacter_apply, ← zpow_mul] at hc
    have hzero : -localDegreeInt F g * n = 0 :=
      (cardinality_zpow_eq_one_iff F.canonicalTopologicalData.residueCardinality hq _).mp hc
    exact (mul_ne_zero (neg_ne_zero.mpr hg) hn) hzero

/-- The local norm formula and compact inertia give exactly the hypotheses
consumed by the generic Frobenius and block statements. -/
theorem localFrobeniusHypothesesFor : LocalFrobeniusHypothesesFor F := by
  refine ⟨⟨F.canonicalTopologicalData.residueCardinality_gt_one,
    localNormCharacter_apply F⟩, ?_⟩
  exact isCompact_iff_compactSpace.mp (localInertia_isCompact F)

end Langlands.Weil.Local
