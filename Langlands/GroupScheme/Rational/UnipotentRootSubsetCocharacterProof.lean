import Langlands.GroupScheme.Rational.RootSubsetAmbient
import Langlands.GroupScheme.Rational.DominantChamberMove
import Langlands.GroupScheme.Rational.RelativeRootSystemProof
import Langlands.GroupScheme.Rational.RelativeWeylRootPermutation
import Langlands.GroupScheme.Rational.WeylPositiveCocharacter

/-! # The positive-cocharacter criterion for unipotent root subsets -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {i : T.toGrp ⟶ G} [IsAffineHom G.X.hom]
  {R : Set (characterLattice T)}

variable [Mono i.hom.hom.left]

/-- The integral Weyl action preserves both actual roots and indivisible roots. -/
theorem IsRelativeRootAmbient.mapsTo_relativeWeylCharacterAction
    (hR : IsRelativeRootAmbient i R) (w : relativeWeylGroup i) :
    Set.MapsTo (relativeWeylCharacterAction i w) R R := by
  have hroots (v : relativeWeylGroup i) {α : characterLattice T}
      (hα : α ∈ relativeRoots i) :
      relativeWeylCharacterAction i v α ∈ relativeRoots i :=
    (relativeWeylRootPermutation i v ⟨α, hα⟩).property
  rcases hR with rfl | rfl
  · exact fun _ hα => hroots w hα
  · intro α hα
    refine ⟨hroots w hα.1, ?_⟩
    intro β hβ m hm hmul
    apply hα.2 (relativeWeylCharacterAction i w⁻¹ β) (hroots w⁻¹ hβ) m hm
    have h := congrArg (relativeWeylCharacterAction i w⁻¹) hmul
    rw [map_nsmul, ← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one] at h
    exact h

/-- A closed subset is unipotent exactly when an integral cocharacter is
strictly positive on it, in either permitted ambient set of relative roots. -/
theorem unipotentRootSubsetCocharacter : UnipotentRootSubsetCocharacterStatement.{u} := by
  intro k _ G hG T i hi
  let := hG.isAffineHom
  let := hi.isSplitSubtorus.mono
  intro R hR ν hν X
  constructor
  · rintro ⟨hclosed, w, hw⟩
    refine ⟨hclosed, relativeWeylCocharacterAction i w ν, ?_⟩
    intro γ hγ
    obtain ⟨α, hα, rfl⟩ := hw hγ
    rw [latticePairing_relativeWeyl]
    exact hα.2
  · rintro ⟨hclosed, ζ, hζ⟩
    have hroot := relativeRootSystem k G hG T i hi
    have hT := hi.isSplitSubtorus.1
    obtain ⟨n, hn⟩ := hroot.exists_normalizerPoint_dominant i hT ν ζ
    let w : relativeWeylGroup i := QuotientGroup.mk n
    refine ⟨hclosed, w⁻¹, ?_⟩
    intro γ hγ
    let β := relativeWeylCharacterAction i w γ
    have hβR : β ∈ R :=
      hR.mapsTo_relativeWeylCharacterAction w (hclosed.1 hγ)
    have hβr : β ∈ relativeRoots i := hR.subset_relativeRoots hβR
    have hβζ : 0 < latticePairing T β (cocharacterAut (normalizingAut i n) ζ) := by
      change 0 < latticePairing T (relativeWeylCharacterAction i w γ)
        (relativeWeylCocharacterAction i w ζ)
      rw [latticePairing_relativeWeyl]
      exact hζ γ hγ
    have hβν : 0 < latticePairing T β ν := by
      by_contra h
      have hne := hν β hβr
      have hneg : latticePairing T β ν < 0 := by omega
      have hnβ := hn (-β) ⟨hroot.neg_mem_relativeRoots i hT hβr, by
        simpa only [map_neg, LinearMap.neg_apply] using neg_pos.mpr hneg⟩
      simp only [map_neg, LinearMap.neg_apply] at hnβ
      omega
    refine ⟨β, ⟨hβR, hβν⟩, ?_⟩
    change relativeWeylCharacterAction i w⁻¹ (relativeWeylCharacterAction i w γ) = γ
    rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl

end Langlands.GroupScheme
