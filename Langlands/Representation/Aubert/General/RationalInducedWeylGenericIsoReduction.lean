import Langlands.Representation.Aubert.General.RationalSameLeviGenericIsoStatement
import Langlands.Representation.Aubert.General.RationalConjugateInductionK0Comparison
import Langlands.Representation.Aubert.General.RationalLeviUnimodularityReduction
import Langlands.Representation.Aubert.General.RationalOppositeJacquetFiniteLength
import Langlands.Representation.Aubert.General.RationalInductionDualityReduction
import Langlands.BruhatTits.Parabolic.QuotientCompactProof
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof
import Langlands.Representation.Smooth.FiniteLengthGrothendieckTwist
import Langlands.Representation.Smooth.IrreducibleGrothendieckProof

/-! # Induced exact-K0 Weyl conjugacy from admissibility and generic isomorphism -/

noncomputable section

universe u v uH uV

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme SmoothRep Langlands.AlgebraicGeometry.PointTopology Plancherel
open HarmonicAnalysis MeasureTheory _root_.Topology Langlands.VirtualRepresentation

section Generic

variable {H : Type uH} [Group H] [TopologicalSpace H] {X D Idx : Type*} [AddCommGroup D]

/-- An integer-linear family of maps on the exact finite-length Grothendieck
group which vanishes on every irreducible class off a nonzero polynomial
vanishes on every class off a nonzero polynomial. -/
theorem exists_ne_zero_vanishing_of_irreducible
    (Δ : FiniteLengthGrothendieckGroup.{0, uH, uV} ℂ H →ₗ[ℤ] (X → D))
    (Z : MvPolynomial Idx ℂ → Set X) (hZmul : ∀ p q, Z (p * q) ⊆ Z p ∩ Z q)
    (hirr : ∀ (A : SmoothRep.{0, uH, uV} ℂ H) (hA : A.IsIrreducible),
      ∃ p : MvPolynomial Idx ℂ, p ≠ 0 ∧ ∀ χ ∈ Z p,
        Δ (FiniteLengthGrothendieckGroup.ofRepresentation A
          (hasFiniteLength_of_isIrreducible hA)) χ = 0)
    (x : FiniteLengthGrothendieckGroup.{0, uH, uV} ℂ H) :
    ∃ p : MvPolynomial Idx ℂ, p ≠ 0 ∧ ∀ χ ∈ Z p, Δ x χ = 0 := by
  obtain ⟨w, rfl⟩ := (irreducibleGrothendieckStatement.{0, uH, uV} ℂ H).2 x
  induction w using Finsupp.induction_linear with
  | zero => exact ⟨1, one_ne_zero, fun χ _ => by simp⟩
  | add f g hf hg =>
    obtain ⟨p, hp, hpf⟩ := hf
    obtain ⟨q, hq, hqg⟩ := hg
    refine ⟨p * q, mul_ne_zero hp hq, fun χ hχ => ?_⟩
    have h := hZmul p q hχ
    simp only [map_add, Pi.add_apply, hpf χ h.1, hqg χ h.2, add_zero]
  | single c z =>
    obtain ⟨A, hA, rfl⟩ := IrreducibleIsoClass.exists_eq c
    obtain ⟨p, hp, hpA⟩ := hirr A hA
    refine ⟨p, hp, fun χ hχ => ?_⟩
    have hz : Finsupp.single (irreducibleIsoClass A hA) z =
        z • generator (irreducibleIsoClass A hA) := by
      simp [generator]
    rw [hz, map_zsmul, realizeIrreducibles_generator_irreducibleIsoClass A hA
      (hasFiniteLength_of_isIrreducible hA), map_zsmul, Pi.smul_apply, hpA χ hχ, smul_zero]

end Generic

section Comparison

variable {F : Type u} [Field F] [TopologicalSpace F]
  [ValuativeRel F] [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T) (I J : Finset (SimpleRoot i ν))

local instance instRationalInducedWeylGenericIso1 : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance instRationalInducedWeylGenericIso2 :
    IsClosedImmersion (Standard.leviHom i ν (rootSet i ν J)).hom.hom.left :=
  Standard.isClosedSubgroup_leviHom i ν (rootSet i ν J)
local instance instRationalInducedWeylGenericIso3 :
    IsAffine (Standard.leviScheme i ν (rootSet i ν J)).X.left :=
  isAffine_of_isAffineHom (Standard.leviHom i ν (rootSet i ν J)).hom.hom.left
local instance instRationalInducedWeylGenericIso4 : TopologicalSpace (rationalPoints G) :=
  pointTopology
local instance instRationalInducedWeylGenericIso5 :
    TopologicalSpace (rationalPoints (Standard.leviScheme i ν (rootSet i ν J))) :=
  rationalPointTopology F (Standard.leviScheme i ν (rootSet i ν J)).X

variable [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)] [T2Space (rationalPoints G)]
  [MeasurableSpace (rationalPoints G)] [BorelSpace (rationalPoints G)]
  {P U Q V : Subgroup (rationalPoints G)}
  (hI : IsSemidirectDecomposition P (levi i ν I) U)
  (hJ : IsSemidirectDecomposition Q (levi i ν J) V)
  (g : rationalPoints G)
  (hIJ : ∀ x : rationalPoints G,
    x ∈ levi i ν J ↔ g⁻¹ * x * g ∈ levi i ν I)
  (hU : IsClosed (U : Set (rationalPoints G)))
  (hV : IsClosed (V : Set (rationalPoints G)))
  (hprojI : Continuous hI.projection) (hprojJ : Continuous hJ.projection)
  (μG : Measure (rationalPoints G)) [μG.IsHaarMeasure] [μG.Regular]
  [CompactSpace (Induction.LeftQuotient P)] [CompactSpace (Induction.LeftQuotient Q)]

local instance instRationalInducedWeylGenericIso6 :
    CompactSpace (Induction.LeftQuotient (conjugateSubgroup g P)) :=
  compactSpace_leftQuotient_conjugateSubgroup g P

/-- Generic isomorphism on irreducible coefficients gives the actual nonzero
principal-open comparison locus for every finite-length coefficient. -/
theorem exists_principalOpen_subset_comparisonLocus_of_genericIso
    (hAdm : ∀ (C : SmoothRep.{0, u, max u v} ℂ (rationalPoints G)),
      C.HasFiniteLength → C.IsAdmissible)
    (hAdmJ : ∀ (A : SmoothRep.{0, u, max u v} ℂ (levi i ν J)),
      A.HasFiniteLength → A.IsAdmissible)
    (hlI : PreservesFiniteLength (normalizedInductionFunctor.{u, max u v} hI hU))
    (hxI : PreservesFiniteLengthShortExact (normalizedInductionFunctor.{u, max u v} hI hU))
    (hlJ : PreservesFiniteLength (normalizedInductionFunctor.{u, max u v} hJ hV))
    (hxJ : PreservesFiniteLengthShortExact (normalizedInductionFunctor.{u, max u v} hJ hV))
    (hLJ : IsConnectedReductive (Standard.leviScheme i ν (rootSet i ν J)))
    (hiso : ∀ σ : SmoothRep.{0, u, max u v} ℂ (levi i ν J),
      σ.IsIrreducible → σ.IsAdmissible →
      ∃ p : MvPolynomial
          (Fin (rationalImageRank (Standard.leviScheme i ν (rootSet i ν J)))) ℂ,
        p ≠ 0 ∧ ∀ χ ∈ leviUnramifiedPrincipalOpen i ν J hLJ p,
          Nonempty
            ((normalizedInductionFunctor hJ hV).obj
                (σ.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker _ χ)) ≅
              (conjugateInductionFunctor hI g hIJ hU).obj
                (σ.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker _ χ))))
    (σ : FiniteLengthObject.{0, u, max u v} ℂ (levi i ν J)) :
    ∃ p : MvPolynomial
        (Fin (rationalImageRank (Standard.leviScheme i ν (rootSet i ν J)))) ℂ,
      p ≠ 0 ∧ leviUnramifiedPrincipalOpen i ν J hLJ p ⊆
        rationalConjugateInductionComparisonLocus i ν I J hI hJ g hIJ hU hV
          hprojI hprojJ μG σ.val (hAdmJ σ.val σ.property) := by
  have hlI' : PreservesFiniteLength (normalizedInductionFunctor.{u, max u v}
      (hI.conjugateWithLevi g hIJ) (isClosed_conjugateSubgroup g hU)) :=
    conjugateInductionFunctor_preservesFiniteLength hI g hIJ hU hlI
  have hxI' : PreservesFiniteLengthShortExact (normalizedInductionFunctor.{u, max u v}
      (hI.conjugateWithLevi g hIJ) (isClosed_conjugateSubgroup g hU)) :=
    conjugateInductionFunctor_preservesShortExact hI g hIJ hU hxI
  let E := Character.exactK0DistributionCharacter μG hAdm
  let tw : unramifiedCharacters (leviRationalNormCharacters i ν J) →
      FiniteLengthGrothendieckGroup.{0, u, max u v} ℂ (levi i ν J) →ₗ[ℤ]
        FiniteLengthGrothendieckGroup.{0, u, max u v} ℂ (levi i ν J) := fun χ =>
    FiniteLengthGrothendieckGroup.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker _ χ)
  let Φ : unramifiedCharacters (leviRationalNormCharacters i ν J) →
      FiniteLengthGrothendieckGroup.{0, u, max u v} ℂ (levi i ν J) →ₗ[ℤ]
        Distribution (rationalPoints G) := fun χ =>
    E.comp ((inductionK0 hJ hV hlJ hxJ).comp (tw χ))
  let Ψ : unramifiedCharacters (leviRationalNormCharacters i ν J) →
      FiniteLengthGrothendieckGroup.{0, u, max u v} ℂ (levi i ν J) →ₗ[ℤ]
        Distribution (rationalPoints G) := fun χ =>
    E.comp ((inductionK0 (hI.conjugateWithLevi g hIJ) (isClosed_conjugateSubgroup g hU)
      hlI' hxI').comp (tw χ))
  let Δ : FiniteLengthGrothendieckGroup.{0, u, max u v} ℂ (levi i ν J) →ₗ[ℤ]
      (unramifiedCharacters (leviRationalNormCharacters i ν J) →
        Distribution (rationalPoints G)) :=
    LinearMap.pi (fun χ => Φ χ - Ψ χ)
  have hevalJ : ∀ (A : SmoothRep.{0, u, max u v} ℂ (levi i ν J)) (hA : A.HasFiniteLength)
      (χ : unramifiedCharacters (leviRationalNormCharacters i ν J)),
      Φ χ (FiniteLengthGrothendieckGroup.ofRepresentation A hA) =
        rationalLeviUnramifiedInductionDistribution i ν J hJ hV hprojJ μG A (hAdmJ A hA) χ := by
    intro A hA χ
    have hAt : (A.twist χ.val.toMonoidHom
        (unramifiedCharacter_isOpen_ker _ χ)).HasFiniteLength :=
      twistFunctor_preservesFiniteLength χ.val.toMonoidHom
        (unramifiedCharacter_isOpen_ker _ χ) A hA
    simp only [Φ, tw, LinearMap.comp_apply]
    rw [FiniteLengthGrothendieckGroup.twist_ofRepresentation _ _ A hA hAt,
      inductionK0_ofRepresentation, Character.exactK0DistributionCharacter_ofRepresentation]
    rfl
  have hevalI : ∀ (A : SmoothRep.{0, u, max u v} ℂ (levi i ν J)) (hA : A.HasFiniteLength)
      (χ : unramifiedCharacters (leviRationalNormCharacters i ν J)),
      Ψ χ (FiniteLengthGrothendieckGroup.ofRepresentation A hA) =
        rationalLeviUnramifiedInductionDistribution i ν J (hI.conjugateWithLevi g hIJ)
          (isClosed_conjugateSubgroup g hU)
          (hI.continuous_conjugateWithLevi_projection hprojI g hIJ) μG A (hAdmJ A hA) χ := by
    intro A hA χ
    have hAt : (A.twist χ.val.toMonoidHom
        (unramifiedCharacter_isOpen_ker _ χ)).HasFiniteLength :=
      twistFunctor_preservesFiniteLength χ.val.toMonoidHom
        (unramifiedCharacter_isOpen_ker _ χ) A hA
    simp only [Ψ, tw, LinearMap.comp_apply]
    rw [FiniteLengthGrothendieckGroup.twist_ofRepresentation _ _ A hA hAt,
      inductionK0_ofRepresentation, Character.exactK0DistributionCharacter_ofRepresentation]
    rfl
  have hirr : ∀ (A : SmoothRep.{0, u, max u v} ℂ (levi i ν J)) (hA : A.IsIrreducible),
      ∃ p : MvPolynomial
          (Fin (rationalImageRank (Standard.leviScheme i ν (rootSet i ν J)))) ℂ,
        p ≠ 0 ∧ ∀ χ ∈ leviUnramifiedPrincipalOpen i ν J hLJ p,
          Δ (FiniteLengthGrothendieckGroup.ofRepresentation A
            (hasFiniteLength_of_isIrreducible hA)) χ = 0 := by
    intro A hA
    have hAfl := hasFiniteLength_of_isIrreducible hA
    obtain ⟨p, hp, hpA⟩ := hiso A hA (hAdmJ A hAfl)
    refine ⟨p, hp, fun χ hχ => ?_⟩
    obtain ⟨e⟩ := hpA χ hχ
    let e' := SmoothRep.equivOfIso e
    change Φ χ _ - Ψ χ _ = 0
    rw [sub_eq_zero, hevalJ A hAfl χ, hevalI A hAfl χ]
    exact Character.distribution_eq_of_equivariant μG _ _ _ _
      e'.toLinearEquiv e'.toIntertwiningMap.isIntertwining
  obtain ⟨p, hp, hpσ⟩ := exists_ne_zero_vanishing_of_irreducible Δ
    (leviUnramifiedPrincipalOpen i ν J hLJ)
    (fun p q χ hχ => by
      rw [mem_leviUnramifiedPrincipalOpen, map_mul] at hχ
      exact ⟨(mem_leviUnramifiedPrincipalOpen i ν J hLJ p χ).mpr (left_ne_zero_of_mul hχ),
        (mem_leviUnramifiedPrincipalOpen i ν J hLJ q χ).mpr (right_ne_zero_of_mul hχ)⟩)
    hirr (FiniteLengthGrothendieckGroup.ofRepresentation σ.val σ.property)
  refine ⟨p, hp, fun χ hχ => ?_⟩
  have h : Φ χ (FiniteLengthGrothendieckGroup.ofRepresentation σ.val σ.property) -
      Ψ χ (FiniteLengthGrothendieckGroup.ofRepresentation σ.val σ.property) = 0 := hpσ χ hχ
  rw [sub_eq_zero, hevalJ σ.val σ.property χ, hevalI σ.val σ.property χ] at h
  exact h

end Comparison

/-- The reduction of `RationalInducedK0WeylConjugacyStatement` to the two
published finite-length admissibility targets and the generic isomorphism
target. -/
def RationalInducedK0WeylFromGenericIsoStatement : Prop :=
  RationalPointsFiniteLengthAdmissibleStatement.{u, max (u + 1) v} →
    DynamicLeviFiniteLengthAdmissibleStatement.{u, max (u + 1) v} →
      RationalSameLeviGenericInductionIsoStatement.{u, max (u + 1) v} →
        RationalInducedK0WeylConjugacyStatement.{u, v}

/-- Proof of the reduction. -/
theorem rationalInducedK0WeylConjugacy_of_genericIso :
    RationalInducedK0WeylFromGenericIsoStatement.{u, v} := by
  intro hadmG hadmM hgen k _ _ _ _ G hG T i hi
  let _ := hG.isAffineHom
  let _ : TopologicalSpace (RationalPoint k G.X) := pointTopology
  intro _ _ _ ν hν hStandard hU hP hproj hUc hiFl hrFl I J n hIJ
  let dec := isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν
  let fl := standardParabolicFiniteLength.{u, v} i ν hStandard hG hi hν hU hP hproj hUc hiFl hrFl
  let _ : MeasurableSpace (RationalPoint k G.X) := borel _
  have _ : BorelSpace (RationalPoint k G.X) := ⟨rfl⟩
  have _ := compactSpace_leftQuotient_parabolic i ν
    BruhatTits.dynamicParabolicQuotientCompact hStandard hG hi hν I
  have _ := compactSpace_leftQuotient_parabolic i ν
    BruhatTits.dynamicParabolicQuotientCompact hStandard hG hi hν J
  have hLJ : IsConnectedReductive (Standard.leviScheme i ν (rootSet i ν J)) :=
    standardLeviScheme_isConnectedReductive i ν hStandard dynamicCentralizerReductive
      hG hi hν J
  have hAdm : ∀ (C : SmoothRep.{0, u, max (u + 1) v} ℂ (RationalPoint k G.X)),
      C.HasFiniteLength → C.IsAdmissible := fun C hC => hadmG k G hG C hC
  have hAdmJ : ∀ (A : SmoothRep.{0, u, max (u + 1) v} ℂ (levi i ν J)),
      A.HasFiniteLength → A.IsAdmissible := fun A hA =>
    standardLevi_isAdmissible_of_hasFiniteLength i ν hStandard hG hi hν hadmM J A hA
  exact inductionK0_comp_conjugationK0_of_rationalPrincipalOpen.{u, max (u + 1) v}
    i ν I J (dec I) (dec J) (n : RationalPoint k G.X) hIJ (hU I) (hU J) (hproj I) (hproj J)
    Measure.haar (hP I) (hP J) hAdm hAdmJ (fl I).1 (fl I).2.1 (fl J).1 (fl J).2.1 hLJ
    (exists_principalOpen_subset_comparisonLocus_of_genericIso.{u, max (u + 1) v}
      i ν I J (dec I) (dec J) (n : RationalPoint k G.X) hIJ (hU I) (hU J) (hproj I)
      (hproj J) Measure.haar hAdm hAdmJ (fl I).1 (fl I).2.1 (fl J).1 (fl J).2.1 hLJ
      (fun σ hσ hσadm => hgen k G hG T i hi ν hν hStandard hU I J n hIJ hLJ σ hσ hσadm))

end Langlands.Aubert.General.RationalPointFamily
