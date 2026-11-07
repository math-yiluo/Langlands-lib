import Langlands.Representation.Exponents.LeviJacquetContragredientStructure
import Langlands.Representation.Exponents.LeviSecondAdjointnessTransport
import Langlands.Representation.Exponents.LeviParabolicModulus
import Langlands.Representation.Exponents.ArbitraryParabolicQuotientCompactStatement
import Langlands.Representation.Aubert.General.SecondAdjointnessCell
import Langlands.Representation.Aubert.General.CompactQuotientNaturalDuality
import Langlands.Representation.Aubert.General.AlternatingOperator

/-! # Second adjointness from explicit structure statements

Renard 2026, VI.9.6 Theorem (VI.9.6.1) (printed p.201, PDF p.207), for arbitrary represented
parabolics `P = MN` and `P̄ = M N̄` as in `LeviSecondAdjointnessStatement`. The general
form is `nonempty_secondAdjunction_of_stableLift`. Its inputs on point images are:

* the stable-lift isomorphism `Ψ : r_{N̄}(V~) ≅ (r_N V)~` and the contracting element of
  `exists_isStableLiftDuality_of_dynamic`, when the point images of `N`, `M` and `N̄` are
  `N(χ)`, `M(χ)` and `N(χ⁻¹)`;
* the duality `C : (i_P τ)~ ≅ i_P(τ~)` of `exists_isNaturalIntegralDuality_of_compactSpace`,
  from compactness of `P(F) \ G(F)`, unimodularity of `G(F)` and the modular character of
  `P(F)`;
* exactness of `r_{N̄}` (`jacquetFunctor_map_isShortExact`), continuity of the Levi
  projection, unimodularity of `N(F)`, and `P(F) ∩ N̄(F) = 1`, which follows from
  `P(F) ∩ P̄(F) = M(F)`.

Unimodularity of `G(F)` and the modular character of `P(F)` come from the reductive
unimodularity statement through `rationalPoints_modularCharacter_eq_one` and
`modularCharacter_pointImage_of_unimodularity`. The cocharacter `χ` and the
identification of `N̄(F)` with `N(χ⁻¹)(F)` come from the same structure statements as in
`leviJacquetContragredient_of_structure`.
-/

noncomputable section

universe u v uG

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Aubert.General

/-- If `P̄ = M ⋉ O` and a subgroup `P` satisfies `P ∩ P̄ = M`, then `P ∩ O = 1`. -/
theorem IsSemidirectDecomposition.eq_one_of_inf_eq {G : Type uG} [Group G]
    {P Pbar M O : Subgroup G} (h : IsSemidirectDecomposition Pbar M O) (hPP : P ⊓ Pbar = M)
    {x : G} (hxP : x ∈ P) (hxO : x ∈ O) : x = 1 := by
  have hxM : x ∈ M := by
    rw [← hPP]
    exact Subgroup.mem_inf.mpr ⟨hxP, h.unipotent_le hxO⟩
  have e : (⟨x, hxM⟩ : M) = 1 :=
    (h.projection_levi ⟨x, hxM⟩).symm.trans (h.projection_unipotent ⟨x, hxO⟩)
  exact congrArg Subtype.val e

end Langlands.Aubert.General

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G P Pbar M N Nbar : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance secondAdjointnessStructurePointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]

/-- Renard VI.9.6 Theorem (VI.9.6.1) for represented parabolics realized by a cocharacter:
let `P = MN` and `P̄ = M N̄` have `mbar ≫ pbar = m ≫ p` and `P(F) ∩ P̄(F) = M(F)`, and let the
point images of `N`, `M` and `N̄` be `N(χ)`, `M(χ)` and `N(χ⁻¹)`. Assume the VI.9.1 uniform
stabilization statement, reciprocity of the Haar scaling characters of `N(χ⁻¹)` and `N(χ)`
on `M(χ)`, compactness of `P(F) \ G(F)`, unimodularity of `G(F)`, and that the modular
character of `P(F)` is the Haar modulus of conjugation on `N(F)`. Then `i_P` is left adjoint
to `r_{P̄}`. -/
theorem nonempty_leviSecondAdjunction_of_dynamic
    (hstab : RationalPointFamily.UniformCompressionStabilizationStatement.{u, max u v})
    (hG : IsConnectedReductive G)
    (p : P ⟶ G) (m : M ⟶ P) (n : N ⟶ P)
    (hp : IsParabolicSubgroup p) (hm : IsRationalLeviSubgroup m)
    (hn : LeviSubgroup.IsGeometricUnipotentRadical n)
    (hmul : IsIso (subgroupMultiplication m n))
    (pbar : Pbar ⟶ G) (mbar : M ⟶ Pbar) (nbar : Nbar ⟶ Pbar)
    (hpbar : IsParabolicSubgroup pbar) (hmbar : IsRationalLeviSubgroup mbar)
    (hnbar : LeviSubgroup.IsGeometricUnipotentRadical nbar)
    (hmulbar : IsIso (subgroupMultiplication mbar nbar))
    (hP : mbar ≫ pbar = m ≫ p)
    (hPP : pointImage p ⊓ pointImage pbar = pointImage (m ≫ p))
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (hN : pointImage (n ≫ p) = (Dynamic.unipotent χ).carrier (Over.mk (𝟙 _)))
    (hM : pointImage (m ≫ p) = (Dynamic.centralizer χ).carrier (Over.mk (𝟙 _)))
    (hNbar : pointImage (nbar ≫ pbar) =
      (Dynamic.unipotent (Dynamic.inverseCocharacter χ)).carrier (Over.mk (𝟙 _)))
    (hrec : ∀ (hU : IsClosed (pointImage (nbar ≫ pbar) : Set (rationalPoints G)))
      (hO : IsClosed (pointImage (n ≫ p) : Set (rationalPoints G)))
      (hMU : pointImage (m ≫ p) ≤
        Subgroup.normalizer (pointImage (nbar ≫ pbar) : Set (rationalPoints G)))
      (hMO : pointImage (m ≫ p) ≤
        Subgroup.normalizer (pointImage (n ≫ p) : Set (rationalPoints G)))
      (x : pointImage (m ≫ p)),
      HaarModulus.closedRestrictCharacter _ hU _ hMU x *
        HaarModulus.closedRestrictCharacter _ hO _ hMO x = 1)
    [CompactSpace (Induction.LeftQuotient (pointImage p))]
    (hmod : ∀ g : rationalPoints G, Measure.modularCharacter g = 1)
    (hδ :
      letI : LocallyCompactSpace (pointImage p) :=
        (isClosed_pointImage p hp.isClosedSubgroup).locallyCompactSpace
      ∀ q : pointImage p, Measure.modularCharacter q =
        (HaarModulus.closedRestrictCharacter (pointImage (n ≫ p))
          (isClosed_pointImage_comp p n hp.isClosedSubgroup hn.1.isClosedSubgroup)
          (pointImage p)
          (isSemidirectDecomposition_pointImage p m n hp.isClosedSubgroup hn hmul).le_normalizer
          q : ℝ≥0)) :
    letI := leviPointTopology m hm
    Nonempty (leviInductionFunctor.{u, max u v} p m n hp hn hm hmul ⊣
      leviJacquetFunctor.{u, max u v} pbar mbar nbar hpbar hnbar hmbar hmulbar) := by
  apply nonempty_leviSecondAdjunction_of_pointImage p m n hp hm hn hmul
    pbar mbar nbar hpbar hmbar hnbar hmulbar hP
  intro hUbar hMUbar
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : T2Space (rationalPoints G) := rationalPoint_t2Space k G
  let : MeasurableSpace (rationalPoints G) := borel _
  have : BorelSpace (rationalPoints G) := ⟨rfl⟩
  let : LocallyCompactSpace (pointImage p) :=
    (isClosed_pointImage p hp.isClosedSubgroup).locallyCompactSpace
  have h := isSemidirectDecomposition_pointImage p m n hp.isClosedSubgroup hn hmul
  have hU := isClosed_pointImage_comp p n hp.isClosedSubgroup hn.1.isClosedSubgroup
  have hproj := continuous_projection_pointImage p m n hp hm hn hmul
  have hdec : IsSemidirectDecomposition (pointImage pbar) (pointImage (m ≫ p))
      (pointImage (nbar ≫ pbar)) := by
    rw [← hP]
    exact isSemidirectDecomposition_pointImage pbar mbar nbar hpbar.isClosedSubgroup hnbar
      hmulbar
  obtain ⟨g, -, hB, Ψ, hΨ⟩ := RationalPointFamily.exists_isStableLiftDuality_of_dynamic hstab
    hG χ _ _ _ hNbar hM hN hUbar hU hMUbar h.levi_le_normalizer
    (hrec hUbar hU hMUbar h.levi_le_normalizer)
  obtain ⟨meas, C, hC⟩ := exists_isNaturalIntegralDuality_of_compactSpace.{u, max u v} h hU
    (isClosed_pointImage p hp.isClosedSubgroup) hproj hmod hδ
  exact nonempty_secondAdjunction_of_stableLift.{u, v} (h := h) (hU := hU)
    (isUnimodularModulus_pointImage_radical p n hp.isClosedSubgroup hn.1) hproj
    (fun x hxP hxO => hdec.eq_one_of_inf_eq hPP hxP hxO) hUbar hMUbar
    (fun f g hfg => jacquetFunctor_map_isShortExact hdec hUbar
      (isLimitOfCompactSubgroups_pointImage_radical pbar nbar hpbar.isClosedSubgroup hnbar.1)
      f g hfg)
    ⊤ meas C hC g hB Ψ hΨ

/-- Renard VI.9.6 Theorem (VI.9.6.1) for one pair of represented parabolics `P = MN` and
`P̄ = M N̄` with `mbar ≫ pbar = m ≫ p` and `P(F) ∩ P̄(F) = M(F)`, from the parabolic dynamic
statement, uniqueness of the opposite dynamic parabolic, the VI.9.1 uniform stabilization
statement, the adjoint determinant reciprocity statement, unimodularity of connected
reductive groups and compactness of parabolic quotients. -/
theorem nonempty_leviSecondAdjunction_of_structure
    (hPD : ParabolicDynamicStatement.{u})
    (hOpp : OppositeDynamicParabolicUniquenessStatement.{u})
    (hstab : RationalPointFamily.UniformCompressionStabilizationStatement.{u, max u v})
    (h2 : Dynamic.LeviAdjointDeterminantReciprocityStatement.{u})
    (hUnimod : RationalPointFamily.RationalReductiveUnimodularityStatement.{u})
    (hStandard : StandardCocharacterStatement.{u})
    (hCompact : ArbitraryParabolicQuotientCompactStatement.{u})
    (hG : IsConnectedReductive G)
    (p : P ⟶ G) (m : M ⟶ P) (n : N ⟶ P)
    (hp : IsParabolicSubgroup p) (hm : IsRationalLeviSubgroup m)
    (hn : LeviSubgroup.IsGeometricUnipotentRadical n)
    (hmul : IsIso (subgroupMultiplication m n))
    (pbar : Pbar ⟶ G) (mbar : M ⟶ Pbar) (nbar : Nbar ⟶ Pbar)
    (hpbar : IsParabolicSubgroup pbar) (hmbar : IsRationalLeviSubgroup mbar)
    (hnbar : LeviSubgroup.IsGeometricUnipotentRadical nbar)
    (hmulbar : IsIso (subgroupMultiplication mbar nbar))
    (hP : mbar ≫ pbar = m ≫ p)
    (hPP : pointImage p ⊓ pointImage pbar = pointImage (m ≫ p)) :
    letI := leviPointTopology m hm
    Nonempty (leviInductionFunctor.{u, max u v} p m n hp hn hm hmul ⊣
      leviJacquetFunctor.{u, max u v} pbar mbar nbar hpbar hnbar hmbar hmulbar) := by
  obtain ⟨χ, hPχ, hMχ⟩ :=
    DynamicLeviConjugacy.exists_cocharacter_parabolic_levi hPD dynamicGeometricUnipotentRadical hG
      hp hm
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : T2Space (rationalPoints G) := rationalPoint_t2Space k G
  have : CompactSpace (Induction.LeftQuotient (pointImage p)) := hCompact k G hG P p hp
  have hN := pointImage_radical_eq_dynamic dynamicGeometricUnipotentRadical hG χ hp hPχ hn
  have hM : pointImage (m ≫ p) = (Dynamic.centralizer χ).carrier (Over.mk (𝟙 _)) := by
    rw [pointImage_eq_range_carrier, hMχ]
  have hNbar := pointImage_opposite_radical_eq_dynamic hPD hOpp hG χ m hPχ hMχ hpbar
    hmbar hnbar hP hPP
  exact nonempty_leviSecondAdjunction_of_dynamic hstab hG p m n hp hm hn hmul
    pbar mbar nbar hpbar hmbar hnbar hmulbar hP hPP χ hN hM hNbar
    (fun hU hO hMU hMO x =>
      RationalPointFamily.dynamicOppositeHaarReciprocity_of_leviAdjoint h2 hG χ _ _ _
        hNbar hM hN hU hO hMU hMO x)
    (rationalPoints_modularCharacter_eq_one hUnimod hStandard hG)
    (modularCharacter_pointImage_of_unimodularity hUnimod hStandard hG p m n hp hm hn hmul)

omit [IsAffineHom G.X.hom] [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)] in
/-- `LeviSecondAdjointnessStatement` (Renard VI.9.6, (VI.9.6.1)) follows from the parabolic
dynamic statement, uniqueness of the opposite dynamic parabolic, the VI.9.1
uniform stabilization statement on carriers in `max u v`, the adjoint determinant
reciprocity statement, unimodularity of connected reductive groups (with the standard
cocharacter statement) and compactness of parabolic quotients. -/
theorem leviSecondAdjointness_of_structure
    (hPD : ParabolicDynamicStatement.{u})
    (hOpp : OppositeDynamicParabolicUniquenessStatement.{u})
    (hstab : RationalPointFamily.UniformCompressionStabilizationStatement.{u, max u v})
    (h2 : Dynamic.LeviAdjointDeterminantReciprocityStatement.{u})
    (hUnimod : RationalPointFamily.RationalReductiveUnimodularityStatement.{u})
    (hStandard : StandardCocharacterStatement.{u})
    (hCompact : ArbitraryParabolicQuotientCompactStatement.{u}) :
    LeviSecondAdjointnessStatement.{u, v} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P Pbar M N Nbar p m n hp hm hn hmul pbar mbar nbar hpbar hmbar hnbar hmulbar hP hPP
  exact nonempty_leviSecondAdjunction_of_structure hPD hOpp hstab h2 hUnimod hStandard
    hCompact hG p m n hp hm hn hmul pbar mbar nbar hpbar hmbar hnbar hmulbar hP hPP

/-- `LeviSecondAdjointnessStatement` with the adjoint determinant reciprocity input replaced
by the relative root reflection and central split torus character statements, through
`leviAdjointDeterminantReciprocity_of_structure` and the proved reductivity of dynamic
centralizers. -/
theorem leviSecondAdjointness_of_structure_of_reflection_centralSplitTorus
    (hPD : ParabolicDynamicStatement.{u})
    (hOpp : OppositeDynamicParabolicUniquenessStatement.{u})
    (hstab : RationalPointFamily.UniformCompressionStabilizationStatement.{u, max u v})
    (hRefl : RelativeRootReflectionExistenceStatement.{u})
    (hCST : CentralSplitTorusCharacterStatement.{u})
    (hUnimod : RationalPointFamily.RationalReductiveUnimodularityStatement.{u})
    (hStandard : StandardCocharacterStatement.{u})
    (hCompact : ArbitraryParabolicQuotientCompactStatement.{u}) :
    LeviSecondAdjointnessStatement.{u, v} :=
  leviSecondAdjointness_of_structure hPD hOpp hstab
    (leviAdjointDeterminantReciprocity_of_structure hRefl hCST dynamicCentralizerReductive)
    hUnimod hStandard hCompact

end Langlands.Aubert.General.RepresentedParabolic
