import Langlands.Representation.Aubert.General.RationalLeviWeylComparison
import Langlands.Representation.Aubert.General.RationalRootSignTarget
import Langlands.GroupScheme.Rational.RelativeWeylCoxeterAssembly
import Langlands.GroupScheme.Absolute.RegularPerturbation

/-! # Pairing stabilizers and actual standard Levi Weyl images -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme Group.RelativeWeylIndexing

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
  (ν : cocharacterLattice T)
  (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)

/-- The actual point-Weyl subgroup preserving pairing with a cocharacter. -/
def pointCocharacterPairingWeylStabilizer (ζ : cocharacterLattice T) :
    Subgroup (Weyl i) where
  carrier := {w | ∀ χ : characterLattice T,
    latticePairing T (weylCharacterAction i hN hZ w χ) ζ = latticePairing T χ ζ}
  one_mem' := by simp
  mul_mem' := by
    intro v w hv hw χ
    rw [map_mul, LinearEquiv.mul_apply, hv, hw]
  inv_mem' := by
    intro w hw χ
    have h := hw (weylCharacterAction i hN hZ w⁻¹ χ)
    simpa using h.symm

omit [IsAffineHom G.X.hom] in
/-- Pairing invariance detects dynamic centralizer membership at the same
normalizer representative, using perfectness for the split torus. -/
theorem pointNormalizer_mem_dynamicCentralizer_iff_pairing
    (hT : IsSplitTorus T.toGrp)
    (n : Group.RelativeWeyl.normalizer (torusPoints i)) (ζ : cocharacterLattice T) :
    (n : RationalPoint k G.X) ∈
        (Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ i)).carrier
          (Over.mk (𝟙 (Spec (CommRingCat.of k)))) ↔
      QuotientGroup.mk n ∈ pointCocharacterPairingWeylStabilizer i hN hZ ζ := by
  let m := (normalizerEquiv i hN).symm n
  change (m : Over.mk (𝟙 _) ⟶ G.X) ∈
    (Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ i)).carrier
      (Over.mk (𝟙 (Spec (CommRingCat.of k)))) ↔
      QuotientGroup.mk n ∈ pointCocharacterPairingWeylStabilizer i hN hZ ζ
  rw [normalizerPoint_mem_dynamicCentralizer_iff i m ζ]
  change cocharacterAut (normalizingAut i m) ζ = ζ ↔
    ∀ χ : characterLattice T,
      latticePairing T (weylCharacterAction i hN hZ (QuotientGroup.mk n) χ) ζ =
        latticePairing T χ ζ
  simp only [weylCharacterAction_point_mk]
  constructor
  · intro hχ χ
    rw [← hχ, weylAction_apply, ← characterAut_apply,
      latticePairing_characterAut_cocharacterAut]
    rw [hχ]
  · intro hχ
    apply hT.isPerfPair_latticePairing.bijective_right.injective
    apply LinearMap.ext
    intro χ
    obtain ⟨α, rfl⟩ := (characterAut (normalizingAut i m)).surjective χ
    exact (latticePairing_characterAut_cocharacterAut (normalizingAut i m) α ζ).trans
      (hχ α).symm

/-- The image of the actual Levi Weyl quotient consists exactly of the
classes preserving every standard cocharacter pairing of its face. -/
theorem mem_pointStandardWeyl_iff_pairing
    (hT : IsSplitTorus T.toGrp) (I : Finset (SimpleRoot i ν)) (w : Weyl i) :
    w ∈ pointStandardWeyl i ν I ↔
      ∀ ζ : cocharacterLattice T, IsStandardCocharacter i ν (rootSet i ν I) ζ →
        w ∈ pointCocharacterPairingWeylStabilizer i hN hZ ζ := by
  constructor
  · intro hw ζ hζ
    obtain ⟨n, hn, rfl⟩ := (mem_pointStandardWeyl_iff i ν I w).mp hw
    apply (pointNormalizer_mem_dynamicCentralizer_iff_pairing i hN hZ hT n ζ).mp
    exact (mem_standardLevi i ν).mp hn ζ hζ
  · intro hw
    obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective w
    apply (mem_pointStandardWeyl_iff i ν I _).mpr
    refine ⟨n, ?_, rfl⟩
    apply (mem_standardLevi i ν).mpr
    intro ζ hζ
    exact (pointNormalizer_mem_dynamicCentralizer_iff_pairing i hN hZ hT n ζ).mpr
      (hw ζ hζ)

variable {CM : CoxeterMatrix (SimpleRoot i ν)}
  (cs : ActualCoxeterSystem (torusPoints i) CM)

/-- The remaining whole-character-lattice simple-reflection law used by
the conditional identification below. It is not asserted or proved here. -/
def SimpleReflectionPairingInvariance : Prop :=
  ∀ (a : SimpleRoot i ν) (ζ : cocharacterLattice T),
    latticePairing T a.val ζ = 0 →
      cs.simple a ∈ pointCocharacterPairingWeylStabilizer i hN hZ ζ

/-- The simple-reflection pairing law implies invariance for every element
of the Coxeter subgroup of a standard face. -/
theorem standardSubgroup_le_pointPairingStabilizer_of_simplePairing
    (hFix : SimpleReflectionPairingInvariance i ν hN hZ cs)
    {I : Finset (SimpleRoot i ν)} {ζ : cocharacterLattice T}
    (hζ : IsStandardCocharacter i ν (rootSet i ν I) ζ) :
    standardSubgroup cs I ≤ pointCocharacterPairingWeylStabilizer i hN hZ ζ := by
  rw [standardSubgroup, Subgroup.closure_le]
  rintro _ ⟨a, ha, rfl⟩
  exact hFix a ζ (hζ.2.1 a.val ⟨a, ha, rfl⟩)

/-- Right descent identifies the actual pairing stabilizer with the standard
Coxeter subgroup, conditional only on the stated simple-reflection law. -/
theorem pointPairingStabilizer_eq_standardSubgroup_of_simplePairing
    (hT : IsSplitTorus T.toGrp) (hRoots : HasRelativeRootSystem i)
    (hν : IsGenericCocharacter i ν)
    (hLength : RootLengthComparison i ν hN hZ cs)
    (hFix : SimpleReflectionPairingInvariance i ν hN hZ cs)
    {I : Finset (SimpleRoot i ν)} {ζ : cocharacterLattice T}
    (hζ : IsStandardCocharacter i ν (rootSet i ν I) ζ) :
    pointCocharacterPairingWeylStabilizer i hN hZ ζ = standardSubgroup cs I := by
  classical
  apply le_antisymm ?_
    (standardSubgroup_le_pointPairingStabilizer_of_simplePairing i ν hN hZ cs hFix hζ)
  intro w hw
  generalize hn : cs.length w = n
  induction n using Nat.strong_induction_on generalizing w with
  | h n ih =>
    by_cases hw1 : w = 1
    · simp [hw1]
    obtain ⟨a, ha⟩ := cs.exists_rightDescent_of_ne_one hw1
    change cs.length (w * cs.simple a) < cs.length w at ha
    have hnot : weylCharacterAction i hN hZ w a.val ∉ positiveRelativeRoots i ν := by
      intro hpos
      have := (hLength w a).mpr hpos
      omega
    have hroot := (weylCharacterAction_mem_relativeRoots_iff i hN hZ w a.val).mpr
      a.property.1.1
    have hneg : -(weylCharacterAction i hN hZ w a.val) ∈
        positiveRelativeRoots i ν := by
      refine ⟨hRoots.neg_mem_relativeRoots i hT hroot, ?_⟩
      have hne := hν _ hroot
      have hnpos : ¬0 < latticePairing T (weylCharacterAction i hN hZ w a.val) ν :=
        fun hpos => hnot ⟨hroot, hpos⟩
      simp only [map_neg, LinearMap.neg_apply]
      omega
    have hnonneg := hζ.pairing_nonneg_of_positive i ν hneg
    have heq := hw a.val
    have haI : a ∈ I := by
      by_contra hnotI
      have hpos := hζ.2.2 a.val a.property (by
        rintro ⟨b, hb, he⟩
        have hab : b = a := Subtype.ext he
        exact hnotI (hab ▸ hb))
      simp only [map_neg, LinearMap.neg_apply] at hnonneg
      omega
    have hs := standardSubgroup_le_pointPairingStabilizer_of_simplePairing
      i ν hN hZ cs hFix hζ (simple_mem_standardSubgroup cs haI)
    have hws : w * cs.simple a ∈ standardSubgroup cs I :=
      ih _ (by omega)
        ((pointCocharacterPairingWeylStabilizer i hN hZ ζ).mul_mem hw hs) rfl
    have := (standardSubgroup cs I).mul_mem hws (simple_mem_standardSubgroup cs haI)
    simpa only [mul_assoc, cs.simple_mul_simple_self, mul_one] using this

/-- The same simple-reflection pairing law yields the exact range of the
actual Levi Weyl inclusion for the original point Coxeter system. -/
theorem actualLeviWeylIdentification_of_simplePairing
    (hT : IsSplitTorus T.toGrp) (hRoots : HasRelativeRootSystem i)
    (hν : IsGenericCocharacter i ν)
    (hLength : RootLengthComparison i ν hN hZ cs)
    (hFix : SimpleReflectionPairingInvariance i ν hN hZ cs) :
    actualLeviWeylIdentification (torusPoints i) (levi i ν) cs := by
  intro I
  change pointStandardWeyl i ν I = standardSubgroup cs I
  ext w
  rw [mem_pointStandardWeyl_iff_pairing i ν hN hZ hT I w]
  constructor
  · intro hw
    obtain ⟨ζ, hζ⟩ := hRoots.exists_standardCocharacter i ν hT hν
      (rootSet i ν I) (rootSet_subset i ν I)
    rw [← pointPairingStabilizer_eq_standardSubgroup_of_simplePairing
      i ν hN hZ cs hT hRoots hν hLength hFix hζ]
    exact hw ζ hζ
  · intro hw ζ hζ
    exact standardSubgroup_le_pointPairingStabilizer_of_simplePairing
      i ν hN hZ cs hFix hζ hw

end Langlands.Aubert.General.RationalPointFamily
