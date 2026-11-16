import Langlands.GroupScheme.Reductive.FibrewiseRootDatum
import Langlands.GroupScheme.Rational.StandardParabolic

/-! # Root lattice comparisons for uniform parabolic faces -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

variable {k l : Type u} [Field k] [Field l]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {U : CommGroupScheme (Spec (CommRingCat.of l))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {H : GroupScheme (Spec (CommRingCat.of l))}
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  {i : T.toGrp ⟶ G} {j : U.toGrp ⟶ H}

/-- A comparison of the full integral lattices preserving actual roots and
character/cocharacter pairings. The field bases may be unrelated. -/
structure ParabolicRootLatticeComparison (i : T.toGrp ⟶ G) (j : U.toGrp ⟶ H) where
  characterEquiv : characterLattice T ≃+ characterLattice U
  cocharacterEquiv : cocharacterLattice T ≃+ cocharacterLattice U
  root_mem_iff : ∀ α, characterEquiv α ∈ relativeRoots j ↔ α ∈ relativeRoots i
  pairing : ∀ α ν,
    latticePairing U (characterEquiv α) (cocharacterEquiv ν) = latticePairing T α ν

namespace ParabolicRootLatticeComparison

variable (d : ParabolicRootLatticeComparison i j)

/-- Genericity is preserved by the integral lattice comparison. -/
theorem generic_iff (ν : cocharacterLattice T) :
    IsGenericCocharacter j (d.cocharacterEquiv ν) ↔ IsGenericCocharacter i ν := by
  constructor
  · intro h α hα
    rw [← d.pairing]
    exact h _ ((d.root_mem_iff α).mpr hα)
  · intro h β hβ
    obtain ⟨α, rfl⟩ := d.characterEquiv.surjective β
    rw [d.pairing]
    exact h α ((d.root_mem_iff α).mp hβ)

/-- Positivity is preserved for every root. -/
theorem positive_iff (ν : cocharacterLattice T) (α : characterLattice T) :
    d.characterEquiv α ∈ positiveRelativeRoots j (d.cocharacterEquiv ν) ↔
      α ∈ positiveRelativeRoots i ν := by
  change (_ ∧ _) ↔ (_ ∧ _)
  rw [d.root_mem_iff, d.pairing]

/-- Indecomposability among positive roots is preserved. -/
theorem simple_iff (ν : cocharacterLattice T) (α : characterLattice T) :
    d.characterEquiv α ∈ simpleRelativeRoots j (d.cocharacterEquiv ν) ↔
      α ∈ simpleRelativeRoots i ν := by
  constructor
  · rintro ⟨hα, hn⟩
    refine ⟨(d.positive_iff ν α).mp hα, ?_⟩
    rintro ⟨β, hβ, γ, hγ, heq⟩
    apply hn
    exact ⟨d.characterEquiv β, (d.positive_iff ν β).mpr hβ,
      d.characterEquiv γ, (d.positive_iff ν γ).mpr hγ, by rw [heq, map_add]⟩
  · rintro ⟨hα, hn⟩
    refine ⟨(d.positive_iff ν α).mpr hα, ?_⟩
    rintro ⟨β, hβ, γ, hγ, heq⟩
    obtain ⟨β, rfl⟩ := d.characterEquiv.surjective β
    obtain ⟨γ, rfl⟩ := d.characterEquiv.surjective γ
    apply hn
    refine ⟨β, (d.positive_iff ν β).mp hβ, γ, (d.positive_iff ν γ).mp hγ, ?_⟩
    apply d.characterEquiv.injective
    rw [map_add]
    exact heq

/-- Subsets of the simple roots correspond over the two field bases. -/
def faceEquiv (ν : cocharacterLattice T) :
    {A : Set (characterLattice T) // A ⊆ simpleRelativeRoots i ν} ≃
      {B : Set (characterLattice U) //
        B ⊆ simpleRelativeRoots j (d.cocharacterEquiv ν)} where
  toFun A := ⟨d.characterEquiv '' A.1, by
    rintro _ ⟨α, hα, rfl⟩
    exact (d.simple_iff ν α).mpr (A.2 hα)⟩
  invFun B := ⟨d.characterEquiv ⁻¹' B.1, fun α hα =>
    (d.simple_iff ν α).mp (B.2 hα)⟩
  left_inv A := by
    apply Subtype.ext
    exact Set.preimage_image_eq _ d.characterEquiv.injective
  right_inv B := by
    apply Subtype.ext
    exact Set.image_preimage_eq _ d.characterEquiv.surjective

/-- A standard integral cocharacter for a face remains standard for its
corresponding face. -/
theorem standard_iff (ν ζ : cocharacterLattice T)
    (A : {A : Set (characterLattice T) // A ⊆ simpleRelativeRoots i ν}) :
    IsStandardCocharacter j (d.cocharacterEquiv ν) (d.faceEquiv ν A).1
        (d.cocharacterEquiv ζ) ↔ IsStandardCocharacter i ν A.1 ζ := by
  constructor
  · rintro ⟨_, hzero, hpos⟩
    refine ⟨A.2, fun α hα => ?_, fun α hα hn => ?_⟩
    · rw [← d.pairing]
      exact hzero _ ⟨α, hα, rfl⟩
    · rw [← d.pairing]
      exact hpos _ ((d.simple_iff ν α).mpr hα) (by
        rintro ⟨β, hβ, heq⟩
        exact hn ((d.characterEquiv.injective heq) ▸ hβ))
  · rintro ⟨_, hzero, hpos⟩
    refine ⟨(d.faceEquiv ν A).2, ?_, ?_⟩
    · rintro _ ⟨α, hα, rfl⟩
      rw [d.pairing]
      exact hzero α hα
    · intro β hβ hn
      obtain ⟨α, rfl⟩ := d.characterEquiv.surjective β
      rw [d.pairing]
      exact hpos α ((d.simple_iff ν α).mp hβ) (fun hα => hn ⟨α, hα, rfl⟩)

end ParabolicRootLatticeComparison

end Langlands.GroupScheme
