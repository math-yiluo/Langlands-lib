import Langlands.Representation.Exponents.LeviJacquetContragredientReciprocity
import Langlands.Representation.Exponents.ArbitraryParabolicJacquetAdmissibilityReduction
import Langlands.GroupScheme.Dynamic.OppositeParabolicUniquenessStatement
import Langlands.GroupScheme.Dynamic.GeometricUnipotentRadicalProof

/-! # Jacquet modules of contragredients from explicit structure statements

Renard 2026, VI.9.6 Theorem (VI.9.6.2) (printed p.201, PDF p.207), for arbitrary represented
parabolics `P = MN` and `P̄ = M N̄` as in `LeviJacquetContragredientStatement`. The cocharacters
of `P` and `P̄` come from `DynamicLeviConjugacy.exists_cocharacter_parabolic_levi`, and the
opposition hypothesis on rational points identifies `N̄(F)` with `N(χ⁻¹)(F)` through
`OppositeDynamicParabolicUniquenessStatement`. The dynamic case is
`nonempty_leviJacquetContragredient_iso_of_dynamic_of_leviAdjoint`.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- If `P` and `M` are the dynamic parabolic and centralizer of `χ`, then the radical of a
represented parabolic `P̄ = M N̄` with `P(F) ∩ P̄(F) = M(F)` has point image `N(χ⁻¹)(F)`. -/
theorem pointImage_opposite_radical_eq_dynamic
    (hPD : ParabolicDynamicStatement.{u})
    (hOpp : OppositeDynamicParabolicUniquenessStatement.{u})
    {k : Type u} [Field k] {G P Pbar M Nbar : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsConnectedReductive G) (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    {p : P ⟶ G} (m : M ⟶ P)
    (hPχ : SubgroupFunctor.range p = Dynamic.parabolic χ)
    (hMχ : SubgroupFunctor.range (m ≫ p) = Dynamic.centralizer χ)
    {pbar : Pbar ⟶ G} (hpbar : IsParabolicSubgroup pbar)
    {mbar : M ⟶ Pbar} (hmbar : IsRationalLeviSubgroup mbar)
    {nbar : Nbar ⟶ Pbar} (hnbar : LeviSubgroup.IsGeometricUnipotentRadical nbar)
    (hP : mbar ≫ pbar = m ≫ p)
    (hPP : pointImage p ⊓ pointImage pbar = pointImage (m ≫ p)) :
    pointImage (nbar ≫ pbar) =
      (Dynamic.unipotent (Dynamic.inverseCocharacter χ)).carrier (Over.mk (𝟙 _)) := by
  obtain ⟨χ', hPχ', hMχ'⟩ :=
    DynamicLeviConjugacy.exists_cocharacter_parabolic_levi hPD dynamicGeometricUnipotentRadical hG
      hpbar hmbar
  have hZ : Dynamic.centralizer χ' = Dynamic.centralizer χ := by
    rw [← hMχ', ← hMχ, hP]
  have hrat : (Dynamic.parabolic χ).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) ⊓
        (Dynamic.parabolic χ').carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) =
      (Dynamic.centralizer χ).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) := by
    simpa only [pointImage_eq_range_carrier, hPχ, hPχ', hMχ] using hPP
  obtain ⟨-, hU⟩ := hOpp k G hG χ χ' hZ hrat
  rw [pointImage_radical_eq_dynamic dynamicGeometricUnipotentRadical hG χ' hpbar hPχ' hnbar,
    hU]
  rfl

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G P Pbar M N Nbar : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance structureLeviJacquetContragredientPointTopology :
    TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]

/-- Renard VI.9.6 Theorem (VI.9.6.2) for one pair of represented parabolics `P = MN` and
`P̄ = M N̄` with `mbar ≫ pbar = m ≫ p` and `P(F) ∩ P̄(F) = M(F)`, from the parabolic dynamic
statement, uniqueness of the opposite dynamic parabolic, the VI.9.1 uniform stabilization
statement and the adjoint determinant reciprocity statement. -/
theorem nonempty_leviJacquetContragredient_iso_of_structure
    (hPD : ParabolicDynamicStatement.{u})
    (hOpp : OppositeDynamicParabolicUniquenessStatement.{u})
    (hstab : RationalPointFamily.UniformCompressionStabilizationStatement.{u, v})
    (h2 : Dynamic.LeviAdjointDeterminantReciprocityStatement.{u})
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
    haveI : NonarchimedeanGroup (rationalPoints M) :=
      leviPoints_nonarchimedeanGroup p m hp hm
    Nonempty
      (SmoothRep.contragredientFunctor.{0, u, v} ⋙
          leviJacquetFunctor.{u, v} pbar mbar nbar hpbar hnbar hmbar hmulbar ≅
        (leviJacquetFunctor.{u, v} p m n hp hn hm hmul).op ⋙
          SmoothRep.contragredientFunctor.{0, u, v}) := by
  obtain ⟨χ, hPχ, hMχ⟩ :=
    DynamicLeviConjugacy.exists_cocharacter_parabolic_levi hPD dynamicGeometricUnipotentRadical hG
      hp hm
  exact nonempty_leviJacquetContragredient_iso_of_dynamic_of_leviAdjoint hstab h2 hG
    p m n hp hm hn hmul pbar mbar nbar hpbar hmbar hnbar hmulbar hP χ
    (pointImage_radical_eq_dynamic dynamicGeometricUnipotentRadical hG χ hp hPχ hn)
    (by rw [pointImage_eq_range_carrier, hMχ])
    (pointImage_opposite_radical_eq_dynamic hPD hOpp hG χ m hPχ hMχ hpbar hmbar hnbar
      hP hPP)

omit [IsAffineHom G.X.hom] [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)] in
/-- `LeviJacquetContragredientStatement` (Renard VI.9.6, (VI.9.6.2)) follows from the parabolic
dynamic statement, uniqueness of the opposite dynamic parabolic, the VI.9.1
uniform stabilization statement and the adjoint determinant reciprocity statement. -/
theorem leviJacquetContragredient_of_structure
    (hPD : ParabolicDynamicStatement.{u})
    (hOpp : OppositeDynamicParabolicUniquenessStatement.{u})
    (hstab : RationalPointFamily.UniformCompressionStabilizationStatement.{u, v})
    (h2 : Dynamic.LeviAdjointDeterminantReciprocityStatement.{u}) :
    LeviJacquetContragredientStatement.{u, v} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P Pbar M N Nbar p m n hp hm hn hmul pbar mbar nbar hpbar hmbar hnbar hmulbar hP hPP
  exact nonempty_leviJacquetContragredient_iso_of_structure hPD hOpp hstab h2 hG
    p m n hp hm hn hmul pbar mbar nbar hpbar hmbar hnbar hmulbar hP hPP

/-- `LeviJacquetContragredientStatement` with the adjoint determinant reciprocity input
replaced by the relative root reflection and central split torus character statements,
through `leviAdjointDeterminantReciprocity_of_structure` and the proved reductivity of
dynamic centralizers. -/
theorem leviJacquetContragredient_of_structure_of_reflection_centralSplitTorus
    (hPD : ParabolicDynamicStatement.{u})
    (hOpp : OppositeDynamicParabolicUniquenessStatement.{u})
    (hstab : RationalPointFamily.UniformCompressionStabilizationStatement.{u, v})
    (hRefl : RelativeRootReflectionExistenceStatement.{u})
    (hCST : CentralSplitTorusCharacterStatement.{u}) :
    LeviJacquetContragredientStatement.{u, v} :=
  leviJacquetContragredient_of_structure hPD hOpp hstab
    (leviAdjointDeterminantReciprocity_of_structure hRefl hCST dynamicCentralizerReductive)

end Langlands.Aubert.General.RepresentedParabolic
