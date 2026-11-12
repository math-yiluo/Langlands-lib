import Langlands.Representation.Smooth.FixedVectors.NormalizedJacquetBridgeProof

/-! # Lifting fixed vectors from an actual normalized Jacquet module

The weak Jacquet lemma needs only finite-dimensional fixed vectors of the
representation itself; no generation or subquotient hypothesis is used.
-/

set_option autoImplicit false

noncomputable section

namespace Langlands.Renard.AlgebraicFamily.InducedTwistsDetection

universe uG uV

open CategoryTheory

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]

/-- A nonzero `K ∩ M`-fixed vector of the actual normalized Jacquet module lifts
to a nonzero `K`-fixed vector, when `D^K` is finite dimensional and `K` has an
Iwahori contraction relative to `(N, M, X)`. -/
theorem exists_fixed_of_normalizedJacquet_fixed
    (N M X : Subgroup G) (hN : IsClosed (N : Set G))
    (hMN : M ≤ Subgroup.normalizer N) (hM : IsClosed (M : Set G))
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (g : G)
    (hcon : Jacquet.IsIwahoriContraction K N M X g)
    (D : SmoothRep.{0, uG, uV} ℂ G)
    (hfin : FiniteDimensional ℂ (fixedVectors D.representation K.toSubgroup))
    (hw : ∃ w : (Aubert.General.normalizedJacquetFunctor N M hN hMN).obj D,
      w ∈ fixedVectors ((Aubert.General.normalizedJacquetFunctor N M hN hMN).obj D).representation
        (K.toSubgroup.comap M.subtype) ∧ w ≠ 0) :
    ∃ v : D, v ∈ fixedVectors D.representation K.toSubgroup ∧ v ≠ 0 := by
  obtain ⟨w, hw, hw0⟩ := hw
  let χ := HaarModulus.closedInverseHalfCharacter N hN M hMN
  let ρD := Jacquet.Localization.action D.representation N 1 M hMN
    (Jacquet.Localization.isInvariant_one N M hMN)
  let KM := K.toSubgroup.comap M.subtype
  have hχ : KM ≤ χ.ker := NormalizedJacquetBridge.character_trivial N M hN hMN hM K hK
  have hwLoc : w ∈ fixedVectors ρD KM := by
    change w ∈ fixedVectors (twist χ ρD) KM at hw
    rwa [fixedVectors_twist_eq_of_le_ker χ ρD KM hχ] at hw
  let e := Jacquet.Localization.trivialEquiv D.representation N M hMN
  have hew : e w ∈ fixedVectors (Jacquet.action D.representation N M hMN) KM :=
    map_mem_fixedVectors e.toIntertwiningMap hwLoc
  have hew0 : e w ≠ 0 := fun hz => hw0 (e.injective (hz.trans (map_zero e).symm))
  obtain ⟨d, hd⟩ := Jacquet.fixedJacquetMap_surjective_of_iwahoriContraction
    D.representation D.isSmooth hK hcon hMN hfin ⟨e w, hew⟩
  refine ⟨d.val, d.property, ?_⟩
  intro hz
  apply hew0
  have hdw : Jacquet.mk D.representation N d.val = e w := congrArg Subtype.val hd
  exact hdw.symm.trans (by rw [hz, map_zero])

end Langlands.Renard.AlgebraicFamily.InducedTwistsDetection
