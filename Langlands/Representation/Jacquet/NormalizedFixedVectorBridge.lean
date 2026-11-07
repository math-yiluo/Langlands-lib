import Langlands.Representation.Smooth.FixedVectors.NormalizedJacquetBridgeProof
import Langlands.Representation.Smooth.FixedVectors.Definitions

/-! # Compact fixed vectors in normalized and unnormalized Jacquet modules -/

set_option autoImplicit false

noncomputable section

namespace Langlands.NormalizedJacquetBridge

universe uG uV uI

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]

/-- On a compact intersection with a closed Levi, the actual normalized Jacquet
fixed vectors identify linearly with the unnormalized coinvariant fixed vectors. -/
def normalizedFixedVectorsEquiv
    (N M : Subgroup G) (hN : IsClosed (N : Set G))
    (hMN : M ≤ Subgroup.normalizer N) (hM : IsClosed (M : Set G))
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (A : SmoothRep.{0, uG, uV} ℂ G) :
    fixedVectors
        ((Aubert.General.normalizedJacquetFunctor N M hN hMN).obj A).representation
        (K.toSubgroup.comap M.subtype) ≃ₗ[ℂ]
      fixedVectors (Jacquet.action A.representation N M hMN)
        (K.toSubgroup.comap M.subtype) :=
  (LinearEquiv.ofEq _ _ (fixedVectors_twist_eq_of_le_ker
    (HaarModulus.closedInverseHalfCharacter N hN M hMN)
    (Jacquet.Localization.action A.representation N 1 M hMN
      (Jacquet.Localization.isInvariant_one N M hMN))
    (K.toSubgroup.comap M.subtype) (character_trivial N M hN hMN hM K hK))).trans
      (Langlands.fixedVectorsEquiv
        (Jacquet.Localization.trivialEquiv A.representation N M hMN)
        (K.toSubgroup.comap M.subtype))

/-- Surjectivity of the actual unnormalized fixed-vector map lifts nonvanishing
from the normalized Jacquet module, with no finite-dimensionality assumption. -/
theorem nonzero_fixed_of_surjective
    (N M : Subgroup G) (hN : IsClosed (N : Set G))
    (hMN : M ≤ Subgroup.normalizer N) (hM : IsClosed (M : Set G))
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (D : SmoothRep.{0, uG, uV} ℂ G)
    (hsurj : Function.Surjective
      (Jacquet.fixedJacquetMap D.representation N M hMN K.toSubgroup))
    (hD : ∃ w : (Aubert.General.normalizedJacquetFunctor N M hN hMN).obj D,
      w ∈ fixedVectors
        ((Aubert.General.normalizedJacquetFunctor N M hN hMN).obj D).representation
        (K.toSubgroup.comap M.subtype) ∧ w ≠ 0) :
    ∃ v : D, v ∈ fixedVectors D.representation K.toSubgroup ∧ v ≠ 0 := by
  obtain ⟨w, hw, hw0⟩ := hD
  let e := normalizedFixedVectorsEquiv N M hN hMN hM K hK D
  obtain ⟨v, hv⟩ := hsurj (e ⟨w, hw⟩)
  refine ⟨v.val, v.property, ?_⟩
  intro hv0
  have hvz : v = 0 := Subtype.ext hv0
  have hez : e ⟨w, hw⟩ = 0 := hv.symm.trans (by rw [hvz, map_zero])
  have hwz : (⟨w, hw⟩ : fixedVectors
      ((Aubert.General.normalizedJacquetFunctor N M hN hMN).obj D).representation
        (K.toSubgroup.comap M.subtype)) = 0 :=
    e.injective (hez.trans (map_zero e).symm)
  exact hw0 (congrArg Subtype.val hwz)

/-- Fixed-vector generation passes to the actual normalized Jacquet module
under the given factorization and compact character triviality. -/
theorem normalized_generation
    (N M : Subgroup G) (hN : IsClosed (N : Set G))
    (hMN : M ≤ Subgroup.normalizer N) (hM : IsClosed (M : Set G))
    (K : OpenSubgroup G) (K₀ : Subgroup G) (hK : IsCompact (K : Set G))
    (hK₀ : K₀ ≤ Subgroup.normalizer K.toSubgroup)
    (hfactor : ∀ x : G, ∃ m ∈ M, ∃ n ∈ N, ∃ k ∈ K₀, x = m * n * k)
    (A : SmoothRep.{0, uG, uV} ℂ G)
    (hgen : ∀ S : Subrepresentation A.representation,
      fixedVectors A.representation K.toSubgroup ≤ S.toSubmodule → S = ⊤) :
    ∀ S : Subrepresentation
        ((Aubert.General.normalizedJacquetFunctor N M hN hMN).obj A).representation,
      fixedVectors
          ((Aubert.General.normalizedJacquetFunctor N M hN hMN).obj A).representation
          (K.toSubgroup.comap M.subtype) ≤ S.toSubmodule → S = ⊤ := by
  let χ := HaarModulus.closedInverseHalfCharacter N hN M hMN
  let ρ := Jacquet.Localization.action A.representation N 1 M hMN
    (Jacquet.Localization.isInvariant_one N M hMN)
  let KM := K.toSubgroup.comap M.subtype
  have hχ : KM ≤ χ.ker := character_trivial N M hN hMN hM K hK
  have hgenOld := Jacquet.fixedVectors_generate_of_factorization
    A.representation N M K.toSubgroup K₀ hMN hK₀ hfactor hgen
  have hgenLoc : ∀ S : Subrepresentation ρ,
      fixedVectors ρ KM ≤ S.toSubmodule → S = ⊤ :=
    generation_of_equiv
      (Jacquet.Localization.trivialEquiv A.representation N M hMN).symm KM hgenOld
  intro S hS
  let T : Subrepresentation ρ := untwistSubrepresentation χ S
  have hT : T = ⊤ := by
    apply hgenLoc T
    intro v hv
    apply hS
    change v ∈ fixedVectors (twist χ ρ) KM
    rwa [fixedVectors_twist_eq_of_le_ker χ ρ KM hχ]
  apply Subrepresentation.toSubmodule_injective
  have hTsub : T.toSubmodule = (⊤ : Subrepresentation ρ).toSubmodule :=
    congrArg Subrepresentation.toSubmodule hT
  exact hTsub

/-- Generation, actual subquotient occurrence and nonzero fixed-vector lifting,
using explicit fixed-Jacquet-map surjectivity in place of finite fixed dimension. -/
theorem bridge_of_surjective
    (N M : Subgroup G) (hN : IsClosed (N : Set G))
    (hMN : M ≤ Subgroup.normalizer N) (hM : IsClosed (M : Set G))
    (hcompact : ∀ s : Finset N, ∃ L : OpenSubgroup N,
      IsCompact (L : Set N) ∧ ∀ n ∈ s, n ∈ L)
    (K : OpenSubgroup G) (K₀ : Subgroup G) (hK : IsCompact (K : Set G))
    (hK₀ : K₀ ≤ Subgroup.normalizer K.toSubgroup)
    (hfactor : ∀ x : G, ∃ m ∈ M, ∃ n ∈ N, ∃ k ∈ K₀, x = m * n * k)
    (A D : SmoothRep.{0, uG, uV} ℂ G)
    (hsurj : Function.Surjective
      (Jacquet.fixedJacquetMap D.representation N M hMN K.toSubgroup))
    (hgen : ∀ S : Subrepresentation A.representation,
      fixedVectors A.representation K.toSubgroup ≤ S.toSubmodule → S = ⊤)
    (hDA : SmoothRep.IsSubquotient D A) :
    let JA := (Aubert.General.normalizedJacquetFunctor N M hN hMN).obj A
    let JD := (Aubert.General.normalizedJacquetFunctor N M hN hMN).obj D
    (∀ S : Subrepresentation JA.representation,
      fixedVectors JA.representation (K.toSubgroup.comap M.subtype) ≤ S.toSubmodule →
        S = ⊤) ∧
    SmoothRep.IsSubquotient JD JA ∧
    ((∃ w : JD, w ∈ fixedVectors JD.representation (K.toSubgroup.comap M.subtype) ∧
      w ≠ 0) →
      ∃ v : D, v ∈ fixedVectors D.representation K.toSubgroup ∧ v ≠ 0) :=
  ⟨normalized_generation N M hN hMN hM K K₀ hK hK₀ hfactor A hgen,
    normalized_isSubquotient N M hN hMN hcompact hDA,
    nonzero_fixed_of_surjective N M hN hMN hM K hK D hsurj⟩

end Langlands.NormalizedJacquetBridge
