import Langlands.Representation.Families.InducedTwistPersistenceEndpoints
import Langlands.Representation.Exponents.LeviParabolicTransitivityProof
import Langlands.Representation.Exponents.ArbitraryParabolicInductionAdmissibility
import Langlands.Representation.Exponents.ArbitraryParabolicQuotientCompactProof
import Langlands.Representation.Derivative.DerivativeEquivTransport
import Mathlib.CategoryTheory.Adjunction.Additive

/-! # Transport of an exponent across one rank-one wall

Let `P₁ = M₁N₁` be an actual parabolic of `G`, and let `Q₁`, `Q₁'` be actual parabolics of
`M₁` with common Levi `L`. Let `R` and `R'` be actual parabolics of `G` with Levi `L`,
contained in `P₁`, with `R ∩ M₁ = Q₁` and `R' ∩ M₁ = Q₁'`. Let `Z` be admissible. Suppose that
`r_{R'}(Z)` has finite length and an `A_L`-exponent `χ`, that `i^{M₁}_{Q₁}(C)` is irreducible
for every irreducible subrepresentation `C` of `r_{R'}(Z)` with exponent `χ`, and that a
second adjunction `i_{Q₁} ⊣ r_{Q₁'}` is supplied. Then `χ` is an exponent of `r_R(Z)`.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.InducedTwistPersistence

open Langlands.Aubert.General Langlands.Aubert.General.RepresentedParabolic GroupScheme

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance persistenceWallAmbientTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]

/-- **Wall transport.** See the module docstring. -/
theorem isGeneralizedEigencharacter_wall (hG : IsConnectedReductive G)
    {P₁ M₁ N₁ Q₁ Q₁' V₁ V₁' L R R' NR NR' : GroupScheme (Spec (CommRingCat.of k))}
    (p₁ : P₁ ⟶ G) (m₁ : M₁ ⟶ P₁) (n₁ : N₁ ⟶ P₁) (hp₁ : IsParabolicSubgroup p₁)
    (hm₁ : IsRationalLeviSubgroup m₁) (hn₁ : LeviSubgroup.IsGeometricUnipotentRadical n₁)
    (hmul₁ : IsIso (subgroupMultiplication m₁ n₁))
    (q₁ : Q₁ ⟶ M₁) (l₁ : L ⟶ Q₁) (v₁ : V₁ ⟶ Q₁) (hq₁ : IsParabolicSubgroup q₁)
    (hl₁ : IsRationalLeviSubgroup l₁) (hv₁ : LeviSubgroup.IsGeometricUnipotentRadical v₁)
    (hmulQ₁ : IsIso (subgroupMultiplication l₁ v₁))
    (q₁' : Q₁' ⟶ M₁) (l₁' : L ⟶ Q₁') (v₁' : V₁' ⟶ Q₁') (hq₁' : IsParabolicSubgroup q₁')
    (hl₁' : IsRationalLeviSubgroup l₁') (hv₁' : LeviSubgroup.IsGeometricUnipotentRadical v₁')
    (hmulQ₁' : IsIso (subgroupMultiplication l₁' v₁'))
    (r : R ⟶ G) (lR : L ⟶ R) (nR : NR ⟶ R) (hr : IsParabolicSubgroup r)
    (hlR : IsRationalLeviSubgroup lR) (hnR : LeviSubgroup.IsGeometricUnipotentRadical nR)
    (hmulR : IsIso (subgroupMultiplication lR nR))
    (r' : R' ⟶ G) (lR' : L ⟶ R') (nR' : NR' ⟶ R') (hr' : IsParabolicSubgroup r')
    (hlR' : IsRationalLeviSubgroup lR') (hnR' : LeviSubgroup.IsGeometricUnipotentRadical nR')
    (hmulR' : IsIso (subgroupMultiplication lR' nR'))
    (hRP : pointImage r ≤ pointImage p₁) (hRL : l₁ ≫ q₁ ≫ m₁ ≫ p₁ = lR ≫ r)
    (hRQ : pointImage (q₁ ≫ m₁ ≫ p₁) = pointImage (m₁ ≫ p₁) ⊓ pointImage r)
    (hR'P : pointImage r' ≤ pointImage p₁) (hR'L : l₁' ≫ q₁' ≫ m₁ ≫ p₁ = lR' ≫ r')
    (hR'Q : pointImage (q₁' ≫ m₁ ≫ p₁) = pointImage (m₁ ≫ p₁) ⊓ pointImage r')
    (adj : haveI := hm₁.isConnectedReductive.isAffineHom
      letI : TopologicalSpace (rationalPoints M₁) := leviPointTopology m₁ hm₁
      haveI := leviPoints_locallyCompactSpace p₁ m₁ hp₁ hm₁
      haveI := leviPoints_nonarchimedeanGroup p₁ m₁ hp₁ hm₁
      letI := leviPointTopology l₁ hl₁
      leviInductionFunctor.{u, max u v} q₁ l₁ v₁ hq₁ hv₁ hl₁ hmulQ₁ ⊣
        leviJacquetFunctor.{u, max u v} q₁' l₁' v₁' hq₁' hv₁' hl₁' hmulQ₁')
    {B : CommGroupScheme (Spec (CommRingCat.of k))} {bL : B.toGrp ⟶ L} (hbL : IsCentral bL)
    (χ : rationalPoints B.toGrp →* ℂˣ)
    (Z : SmoothRep.{0, u, max u v} ℂ (rationalPoints G)) (hZ : Z.IsAdmissible)
    (hfl : letI := leviPointTopology lR' hlR'
      haveI := leviPoints_locallyCompactSpace r' lR' hr' hlR'
      haveI := leviPoints_nonarchimedeanGroup r' lR' hr' hlR'
      ((leviJacquetFunctor r' lR' nR' hr' hnR' hlR' hmulR').obj Z).HasFiniteLength)
    (hexp : letI := leviPointTopology lR' hlR'
      IsGeneralizedEigencharacter
        (((leviJacquetFunctor r' lR' nR' hr' hnR' hlR' hmulR').obj Z).representation.comp
          (rationalPoints.map bL)) χ)
    (hirr : haveI := hm₁.isConnectedReductive.isAffineHom
      letI : TopologicalSpace (rationalPoints M₁) := leviPointTopology m₁ hm₁
      haveI := leviPoints_locallyCompactSpace p₁ m₁ hp₁ hm₁
      haveI := leviPoints_nonarchimedeanGroup p₁ m₁ hp₁ hm₁
      letI := leviPointTopology l₁ hl₁
      ∀ C : SmoothRep.{0, u, max u v} ℂ (rationalPoints L), C.IsIrreducible →
        (∃ j : C ⟶ (leviJacquetFunctor r' lR' nR' hr' hnR' hlR' hmulR').obj Z,
          Function.Injective (SmoothRep.hom j)) →
        IsGeneralizedEigencharacter (C.representation.comp (rationalPoints.map bL)) χ →
        ((leviInductionFunctor q₁ l₁ v₁ hq₁ hv₁ hl₁ hmulQ₁).obj C).IsIrreducible) :
    letI := leviPointTopology lR hlR
    IsGeneralizedEigencharacter
      (((leviJacquetFunctor r lR nR hr hnR hlR hmulR).obj Z).representation.comp
        (rationalPoints.map bL)) χ := by
  have hM₁ := hm₁.isConnectedReductive
  have := hM₁.isAffineHom
  let : TopologicalSpace (rationalPoints M₁) := leviPointTopology m₁ hm₁
  have := leviPoints_locallyCompactSpace p₁ m₁ hp₁ hm₁
  have := leviPoints_nonarchimedeanGroup p₁ m₁ hp₁ hm₁
  let := leviPointTopology l₁ hl₁
  have := leviPoints_locallyCompactSpace q₁ l₁ hq₁ hl₁
  have := leviPoints_nonarchimedeanGroup q₁ l₁ hq₁ hl₁
  have hcen : ∀ t, rationalPoints.map bL t ∈ Subgroup.center (rationalPoints L) :=
    hbL.map_mem_center
  -- transitivity on both sides of the wall
  obtain ⟨-, ⟨eR⟩⟩ := leviParabolicTransitivity.{u, max u v} k G hG R L NR P₁ M₁ N₁ Q₁ V₁
    r lR nR hr hlR hnR hmulR p₁ m₁ n₁ hp₁ hm₁ hn₁ hmul₁ q₁ l₁ v₁ hq₁ hl₁ hv₁ hmulQ₁
    hRP hRL hRQ
  obtain ⟨-, ⟨eR'⟩⟩ := leviParabolicTransitivity.{u, max u v} k G hG R' L NR' P₁ M₁ N₁ Q₁' V₁'
    r' lR' nR' hr' hlR' hnR' hmulR' p₁ m₁ n₁ hp₁ hm₁ hn₁ hmul₁ q₁' l₁' v₁' hq₁' hl₁' hv₁'
    hmulQ₁' hR'P hR'L hR'Q
  let V := (leviJacquetFunctor p₁ m₁ n₁ hp₁ hn₁ hm₁ hmul₁).obj Z
  let W' := (leviJacquetFunctor q₁' l₁' v₁' hq₁' hv₁' hl₁' hmulQ₁').obj V
  let E' := eR'.app Z
  -- admissibility
  have hVadm : V.IsAdmissible :=
    isAdmissible_comp_continuousMulEquiv _ (leviPointsEquiv p₁ m₁ hp₁ hm₁)
      (arbitraryParabolicJacquetAdmissibility k G hG P₁ M₁ N₁ p₁ m₁ n₁ hp₁ hm₁ hn₁ hmul₁ Z hZ)
  have hW'adm : W'.IsAdmissible :=
    isAdmissible_comp_continuousMulEquiv _ (leviPointsEquiv q₁' l₁' hq₁' hl₁')
      (arbitraryParabolicJacquetAdmissibility k M₁ hM₁ Q₁' L V₁' q₁' l₁' v₁' hq₁' hl₁' hv₁'
        hmulQ₁' V hVadm)
  -- the opposite side
  have hW'fl : W'.HasFiniteLength :=
    Derivative.hasFiniteLength_of_equiv (SmoothRep.equivOfIso E') hfl
  have hW'exp : IsGeneralizedEigencharacter (W'.representation.comp (rationalPoints.map bL)) χ :=
    isGeneralizedEigencharacter_of_injective (rationalPoints.map bL)
      (SmoothRep.equivOfIso E').toIntertwiningMap (SmoothRep.equivOfIso E').injective χ hexp
  obtain ⟨C, hC, jC, hjC, hCχ⟩ :=
    exists_irreducible_sub_isGeneralizedEigencharacter (rationalPoints.map bL) hcen hW'fl χ hW'exp
  have hC' : C.representation.IsIrreducible := hC
  have : Nontrivial C := IsSimpleModule.nontrivial (MonoidAlgebra ℂ (rationalPoints L))
    C.representation.asModule
  have hiC : ((leviInductionFunctor q₁ l₁ v₁ hq₁ hv₁ hl₁ hmulQ₁).obj C).IsIrreducible :=
    hirr C hC ⟨jC ≫ E'.inv, ((SmoothRep.equivOfIso E').symm.injective).comp hjC⟩ hCχ
  have hiC' : ((leviInductionFunctor q₁ l₁ v₁ hq₁ hv₁ hl₁ hmulQ₁).obj C).representation.IsIrreducible :=
    hiC
  -- second adjointness: a nonzero map `i_{Q₁}(C) → V`
  let : (leviInductionFunctor.{u, max u v} q₁ l₁ v₁ hq₁ hv₁ hl₁ hmulQ₁).Additive :=
    { map_add := by
        intro A B f g
        apply ObjectProperty.hom_ext
        ext x
        rfl }
  let φ := (adj.homEquiv C V).symm jC
  have hjC0 : jC ≠ 0 := by
    intro h0
    obtain ⟨c, hc⟩ := exists_ne (0 : C)
    apply hc
    apply hjC
    rw [h0, map_zero]
    rfl
  have hφ0 : SmoothRep.hom φ ≠ 0 := by
    intro h0
    have hφ : φ = 0 := by
      apply ObjectProperty.hom_ext
      exact Rep.hom_ext h0
    apply hjC0
    have : jC = adj.homEquiv C V φ := by simp [φ]
    rw [this, hφ]
    simp only [Adjunction.homAddEquiv_zero]
  have hφinj : Function.Injective (SmoothRep.hom φ) :=
    (Representation.IsIrreducible.injective_or_eq_zero (SmoothRep.hom φ)).resolve_right hφ0
  -- the Jacquet module of `i_{Q₁}(C)` along `Q₁` has the exponent
  have hCadm : C.IsAdmissible :=
    isAdmissible_of_injective (SmoothRep.hom jC) hjC hW'adm
  have hiCadm : ((leviInductionFunctor q₁ l₁ v₁ hq₁ hv₁ hl₁ hmulQ₁).obj C).IsAdmissible :=
    leviInductionFunctor_obj_isAdmissible_of_quotientCompactStatement
      arbitraryParabolicQuotientCompact hM₁ q₁ l₁ v₁ hq₁ hl₁ hv₁ hmulQ₁ C hCadm
  have hid : SmoothRep.hom (𝟙 ((leviInductionFunctor q₁ l₁ v₁ hq₁ hv₁ hl₁ hmulQ₁).obj C)) ≠ 0 := by
    have : Nontrivial ((leviInductionFunctor q₁ l₁ v₁ hq₁ hv₁ hl₁ hmulQ₁).obj C) :=
      IsSimpleModule.nontrivial (MonoidAlgebra ℂ (rationalPoints M₁))
        ((leviInductionFunctor q₁ l₁ v₁ hq₁ hv₁ hl₁ hmulQ₁).obj C).representation.asModule
    obtain ⟨x, hx⟩ := exists_ne (0 : (leviInductionFunctor q₁ l₁ v₁ hq₁ hv₁ hl₁ hmulQ₁).obj C)
    intro h0
    apply hx
    have := congrArg (fun f => f x) h0
    simpa using this
  have hJiC := isGeneralizedEigencharacter_jacquet_of_ne_zero_induction q₁ l₁ v₁ hq₁ hl₁ hv₁
    hmulQ₁ hM₁ hbL _ hiCadm C hC _ hid χ hCχ
  -- push it into `r_{Q₁}(V)` and back to `r_R(Z)`
  have hJV := isGeneralizedEigencharacter_of_injective (rationalPoints.map bL)
    (SmoothRep.hom ((leviJacquetFunctor q₁ l₁ v₁ hq₁ hv₁ hl₁ hmulQ₁).map φ))
    (leviJacquetFunctor_map_injective q₁ l₁ v₁ hq₁ hl₁ hv₁ hmulQ₁ φ hφinj) χ hJiC
  exact isGeneralizedEigencharacter_of_injective (rationalPoints.map bL)
    (SmoothRep.equivOfIso (eR.app Z)).symm.toIntertwiningMap
    (SmoothRep.equivOfIso (eR.app Z)).symm.injective χ hJV

end Langlands.InducedTwistPersistence
