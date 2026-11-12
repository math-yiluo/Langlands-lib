import Langlands.Representation.Exponents.CasselmanDynamicNecessity
import Langlands.Representation.Exponents.CasselmanChamberBoundCone
import Langlands.Representation.CuspidalSupport.RationalNormKernelPositiveGenerators
import Langlands.GroupScheme.Rational.RelativeRootSignInclusionsProof
import Langlands.GroupScheme.Dynamic.GeometricUnipotentRadicalProof
import Langlands.GroupScheme.Rational.RootSubgroupRationalNontrivial
import Langlands.GroupScheme.Rational.RootSubgroupPositive
import Langlands.GroupScheme.Rational.RelativeTitsNondegeneracy

/-! # Necessity in Casselman's criterion for represented parabolics

Renard 2026, VII.1.2 (printed pp.221–224/PDF pp.227–230), necessity: every
normalized Jacquet exponent of a representation that is square integrable modulo
the center, at every represented parabolic with a compatible root presentation,
has normalized real part in the strictly positive restricted-root cone. No
Bruhat–Tits input is used: the Iwahori subgroups come from the dynamic open cell.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry Filter Topology TensorProduct
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.BruhatTits.DynamicUnipotentContainment

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme RealTorusSpace ParabolicRootPresentation

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G P M U : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [T2Space k]
  [IsAffineHom G.X.hom] in
/-- Evaluating a split-component cocharacter and mapping to the ambient group is
evaluating the composite ambient cocharacter. -/
theorem splitComponentPointsMap_cocharacterPoints (p : P ⟶ G) (l : M ⟶ P)
    {A : CommGroupScheme (Spec (CommRingCat.of k))} (a : A.toGrp ⟶ M)
    (m : cocharacterLattice A) (t : kˣ) :
    (splitComponentPointsMap (l ≫ p) a (CocharacterUniformizer.cocharacterPoints k A m t) :
        rationalPoints G) = cocharPoint (CommGroupScheme.groupHom m ≫ a ≫ l ≫ p) t := by
  rw [cocharPoint_eq, splitComponentPointsMap_val]
  simp only [CocharacterUniformizer.cocharacterPoints, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, rationalPoints.map_apply, Grp.comp_hom_hom, Category.assoc]

section Necessity

local instance casselmanNecessityAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  [MeasurableSpace (rationalPoints G ⧸ Subgroup.center (rationalPoints G))]
  [BorelSpace (rationalPoints G ⧸ Subgroup.center (rationalPoints G))]
  (haar : MeasureTheory.Measure (rationalPoints G ⧸ Subgroup.center (rationalPoints G)))
  [haar.IsHaarMeasure]

/-- The dynamic bound `norm_lt_one_of_squareIntegrable_dynamic`, for any closed
subgroup and normalizing subgroup equal to the dynamic radical and Levi. -/
theorem norm_lt_one_of_squareIntegrable_dynamic_of_eq (hG : IsConnectedReductive G)
    (χd ξ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (hUP : (Dynamic.unipotent χd).carrier (Over.mk (𝟙 _)) ≤
      (Dynamic.parabolic ξ).carrier (Over.mk (𝟙 _)))
    (hOP : (Dynamic.unipotent (Dynamic.inverseCocharacter χd)).carrier (Over.mk (𝟙 _)) ≤
      (Dynamic.parabolic (Dynamic.inverseCocharacter ξ)).carrier (Over.mk (𝟙 _)))
    (x : rationalPoints G) (hx1 : x ≠ 1)
    (hxU : x ∈ (Dynamic.unipotent χd).carrier (Over.mk (𝟙 _)))
    (hxL : x ∈ (Dynamic.unipotent ξ).carrier (Over.mk (𝟙 _)))
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))
    (hsq : IsSquareIntegrableModCenter π.representation haar)
    (N L : Subgroup (rationalPoints G)) (hN : IsClosed (N : Set (rationalPoints G)))
    (hLN : L ≤ Subgroup.normalizer (N : Set (rationalPoints G)))
    (eN : N = (Dynamic.unipotent χd).carrier (Over.mk (𝟙 _)))
    (eL : L = (Dynamic.centralizer χd).carrier (Over.mk (𝟙 _)))
    {B : Type u} [Group B] (incl : B →* L) (hι : ∀ s, incl s ∈ Subgroup.center L)
    (χB : B →* ℂˣ)
    (hχB : IsGeneralizedEigencharacter
      (((normalizedJacquetFunctor N L hN hLN).obj π).representation.comp incl) χB)
    (a0 b0 : B) (t : kˣ) (ht : Tendsto (fun n : ℕ => (t : k) ^ n) atTop (𝓝 0))
    (ha0 : ((incl a0 : L) : rationalPoints G) = cocharPoint ξ t)
    (hb0 : ((incl b0 : L) : rationalPoints G) = cocharPoint χd t) :
    ‖(χB a0 : ℂ)‖ < 1 := by
  subst eN eL
  exact RationalPointFamily.norm_lt_one_of_squareIntegrable_dynamic hG haar χd ξ hUP hOP
    x hx1 hxU hxL π hsq incl hι χB hχB a0 b0 t ht ha0 hb0

variable [LocallyOfFiniteType G.X.hom]
  (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
  (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
  (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
  (hmul : IsIso (subgroupMultiplication l r))
  {A : CommGroupScheme (Spec (CommRingCat.of k))} {a : A.toGrp ⟶ M}

/-- **Strict bound on the closed chamber.** For a representation square integrable
modulo the center and a normalized exponent `χ`, `|χ(m(ϖ))| < 1` for every
split-component cocharacter `m` with nonnegative pairings with all restricted
simple roots and a positive pairing with one of them. -/
theorem norm_latticeSection_lt_one_of_squareIntegrable (hG : IsConnectedReductive G)
    (ha : IsSplitComponent a) (pres : ParabolicRootPresentation p l a)
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))
    (hsq : IsSquareIntegrableModCenter π.representation haar)
    (χ : rationalPoints A.toGrp →* ℂˣ)
    (hχ : IsNormalizedJacquetExponent p l r hp hl hr hmul ha π χ)
    (m : cocharacterLattice A)
    (hnonneg : ∀ α ∈ simpleRelativeRoots pres.data.i pres.data.ν, α ∉ pres.data.J →
      0 ≤ latticePairing A (pres.data.f ≫ α) m)
    (hposm : ∃ α ∈ simpleRelativeRoots pres.data.i pres.data.ν, α ∉ pres.data.J ∧
      0 < latticePairing A (pres.data.f ≫ α) m) :
    ‖(χ (CocharacterUniformizer.latticeSection k A (Multiplicative.ofAdd m)) : ℂ)‖ < 1 := by
  have := hG.smooth
  obtain ⟨ζ, hζ, hP, hL⟩ := pres.isCompatible.realization
  have hi : IsMaximalSplitTorus pres.data.i := pres.isCompatible.maximalSplit
  let νm : cocharacterLattice pres.data.T := cocharacterMapInt pres.data.f m
  have hνmα : ∀ α : characterLattice pres.data.T,
      latticePairing pres.data.T α νm = latticePairing A (pres.data.f ≫ α) m :=
    fun α => (RelativeRoot.latticePairing_restrict_cocharacterMapInt pres.data.f α m).symm
  -- `νm` pairs nonnegatively with the positive roots, and trivially with those on
  -- which the standard cocharacter `ζ` vanishes
  have hposνm : ∀ α ∈ positiveRelativeRoots pres.data.i pres.data.ν,
      0 ≤ latticePairing pres.data.T α νm := by
    intro α hα
    exact positiveRelativeRoots_induction pres.data.i pres.data.ν
      (P := fun α => 0 ≤ latticePairing pres.data.T α νm)
      (fun β hβ => by
        rw [hνmα]
        by_cases hβJ : β ∈ pres.data.J
        · rw [pres.selectedRoot_restrict_eq_zero hβJ, map_zero, LinearMap.zero_apply]
        · exact hnonneg β hβ hβJ)
      (fun β _ β₂ _ hβ hβ₂ => by
        rw [map_add, LinearMap.add_apply]
        exact add_nonneg hβ hβ₂) hα
  have hzeroνm : ∀ α ∈ positiveRelativeRoots pres.data.i pres.data.ν,
      latticePairing pres.data.T α ζ = 0 → latticePairing pres.data.T α νm = 0 := by
    intro α hα h
    rw [hνmα, pres.restrict_eq_zero_of_mem_closure
      ((hζ.pairing_eq_zero_iff_mem_closure pres.data.i pres.data.ν hα).mp h),
      map_zero, LinearMap.zero_apply]
  have hsign : ∀ α ∈ relativeRoots pres.data.i,
      0 ≤ latticePairing pres.data.T α ζ → 0 ≤ latticePairing pres.data.T α νm := by
    intro α hα h
    rcases lt_or_gt_of_ne (pres.isCompatible.generic α hα) with hn | hp'
    · have hneg := relativeRootNegation k G hG pres.data.T pres.data.i hi α hα
      have hnegpos : -α ∈ positiveRelativeRoots pres.data.i pres.data.ν :=
        ⟨hneg, by rw [map_neg, LinearMap.neg_apply]; omega⟩
      have h1 := hζ.pairing_nonneg_of_positive pres.data.i pres.data.ν hnegpos
      rw [map_neg, LinearMap.neg_apply] at h1
      have h2 := hzeroνm (-α) hnegpos (by rw [map_neg, LinearMap.neg_apply]; omega)
      rw [map_neg, LinearMap.neg_apply, neg_eq_zero] at h2
      exact h2.ge
    · exact hposνm α ⟨hα, hp'⟩
  have hsign' : ∀ α ∈ relativeRoots pres.data.i,
      0 ≤ latticePairing pres.data.T α (-ζ) → 0 ≤ latticePairing pres.data.T α (-νm) := by
    intro α hα h
    have h' := hsign (-α) (relativeRootNegation k G hG pres.data.T pres.data.i hi α hα)
      (by simpa using h)
    simpa using h'
  -- the dynamic inclusions
  let χd := CommGroupScheme.groupHom ζ ≫ pres.data.i
  let ξ := CommGroupScheme.groupHom νm ≫ pres.data.i
  have hPP : Dynamic.parabolic χd ≤ Dynamic.parabolic ξ :=
    ((relativeRootSignInclusions k G hG pres.data.T pres.data.i hi ζ νm).1).mpr hsign
  have hPP' : Dynamic.parabolic (CommGroupScheme.groupHom (-ζ) ≫ pres.data.i) ≤
      Dynamic.parabolic (CommGroupScheme.groupHom (-νm) ≫ pres.data.i) :=
    ((relativeRootSignInclusions k G hG pres.data.T pres.data.i hi (-ζ) (-νm)).1).mpr hsign'
  have hinvd : Dynamic.inverseCocharacter χd = CommGroupScheme.groupHom (-ζ) ≫ pres.data.i :=
    (groupHom_neg_comp_eq_oppositeCocharacter pres.data.i ζ).symm
  have hinvξ : Dynamic.inverseCocharacter ξ = CommGroupScheme.groupHom (-νm) ≫ pres.data.i :=
    (groupHom_neg_comp_eq_oppositeCocharacter pres.data.i νm).symm
  have hUP : (Dynamic.unipotent χd).carrier (Over.mk (𝟙 _)) ≤
      (Dynamic.parabolic ξ).carrier (Over.mk (𝟙 _)) :=
    fun y hy => hPP _ (Dynamic.unipotent_le_parabolic χd _ hy)
  have hOP : (Dynamic.unipotent (Dynamic.inverseCocharacter χd)).carrier (Over.mk (𝟙 _)) ≤
      (Dynamic.parabolic (Dynamic.inverseCocharacter ξ)).carrier (Over.mk (𝟙 _)) := by
    rw [hinvd, hinvξ]
    exact fun y hy => hPP' _ (Dynamic.unipotent_le_parabolic _ _ hy)
  -- a nonidentity root point contracted by both cocharacters
  obtain ⟨α, hα, hJ, hαpos⟩ := hposm
  obtain ⟨x, hx, hx1⟩ := RelativeRoot.exists_rootPoint_actual hi.isSplitSubtorus.1
    pres.data.i hα.1.1
  have hxU : x ∈ (Dynamic.unipotent χd).carrier (Over.mk (𝟙 _)) :=
    RelativeRoot.subgroup_le_dynamicUnipotent pres.data.i ζ (hζ.2.2 α hα hJ) _ hx
  have hxL : x ∈ (Dynamic.unipotent ξ).carrier (Over.mk (𝟙 _)) :=
    RelativeRoot.subgroup_le_dynamicUnipotent pres.data.i νm (by rw [hνmα]; exact hαpos) _ hx
  -- the represented radical and Levi are the dynamic ones
  have eN : pointImage (r ≫ p) = (Dynamic.unipotent χd).carrier (Over.mk (𝟙 _)) :=
    pointImage_radical_eq_dynamic dynamicGeometricUnipotentRadical hG χd hp hP hr
  have eL : pointImage (l ≫ p) = (Dynamic.centralizer χd).carrier (Over.mk (𝟙 _)) :=
    congrArg (fun F : SubgroupFunctor G => F.carrier (Over.mk (𝟙 _))) hL
  have hχB := (isNormalizedJacquetExponent_iff p l r hp hl hr hmul ha π χ).mp hχ
  -- the two test points
  have hcomp : ∀ n : cocharacterLattice A, CommGroupScheme.groupHom n ≫ a ≫ l ≫ p =
      CommGroupScheme.groupHom (cocharacterMapInt pres.data.f n) ≫ pres.data.i := by
    intro n
    rw [← pres.isCompatible.factor_comp]
    rfl
  let ϖ := SplitTorusValuation.uniformizerUnit k
  let mb := pres.standardCocharacterLift hζ
  have ha0 : ((splitComponentPointsMap (l ≫ p) a
      (CocharacterUniformizer.latticeSection k A (Multiplicative.ofAdd m)) :
        pointImage (l ≫ p)) : rationalPoints G) = cocharPoint ξ ϖ := by
    change (splitComponentPointsMap (l ≫ p) a
      (CocharacterUniformizer.cocharacterPoints k A m ϖ) : rationalPoints G) = _
    rw [splitComponentPointsMap_cocharacterPoints, hcomp]
  have hb0 : ((splitComponentPointsMap (l ≫ p) a
      (CocharacterUniformizer.latticeSection k A (Multiplicative.ofAdd mb)) :
        pointImage (l ≫ p)) : rationalPoints G) = cocharPoint χd ϖ := by
    change (splitComponentPointsMap (l ≫ p) a
      (CocharacterUniformizer.cocharacterPoints k A mb ϖ) : rationalPoints G) = _
    rw [splitComponentPointsMap_cocharacterPoints, hcomp,
      pres.cocharacterMapInt_standardCocharacterLift hζ]
  exact norm_lt_one_of_squareIntegrable_dynamic_of_eq haar hG χd ξ hUP hOP x hx1 hxU hxL π hsq
    (pointImage (r ≫ p)) (pointImage (l ≫ p)) _ _ eN eL (splitComponentPointsMap (l ≫ p) a)
    (splitComponentPointsMap_mem_center (l ≫ p) ha) χ hχB _ _ ϖ
    (SplitTorusValuation.tendsto_uniformizerUnit_pow_zero k) ha0 hb0

/-- **Necessity in Casselman's criterion.** Every normalized Jacquet exponent of a
representation square integrable modulo the center has normalized real part in
the strictly positive restricted-root cone of every compatible presentation. -/
theorem normalizedRealPart_mem_positiveCone_of_squareIntegrable (hG : IsConnectedReductive G)
    (ha : IsSplitComponent a) (pres : ParabolicRootPresentation p l a)
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))
    (hsq : IsSquareIntegrableModCenter π.representation haar)
    (χ : rationalPoints A.toGrp →* ℂˣ)
    (hχ : IsNormalizedJacquetExponent p l r hp hl hr hmul ha π χ) :
    Plancherel.SplitTorus.normalizedRealPart ha.isCentralSplitTorus.1.1 χ ∈
      pres.positiveCone := by
  have := ha.isAffine
  let := RationalPointFamily.splitComponentPointTopology ha
  let hA := ha.isCentralSplitTorus.1.1
  obtain ⟨c, -⟩ := hsq.2
  apply pres.mem_positiveCone_of_latticePair (pres.linearIndependent_simpleRoots hG) hA
  · intro m hm
    have hc := pres.isCentral_of_pairing_eq_zero hG m hm
    have h0 := normalizedJacquetExponent_realPart_restrict_eq_zero p l r hp hl hr hmul ha
      isSplitTorus_gm m hc π c χ hχ
    rw [latticePair_apply]
    have hmap : cocharacterMapReal m ((1 : ℝ) ⊗ₜ[ℤ] (𝟙 (Gm (Spec (CommRingCat.of k))))) =
        (1 : ℝ) ⊗ₜ[ℤ] m := by
      rw [cocharacterMapReal_tmul, Category.id_comp]
    rw [← hmap, pair_cocharacterMapReal, h0, map_zero, LinearMap.zero_apply]
  · intro m hnonneg hposm
    have hlt := norm_latticeSection_lt_one_of_squareIntegrable haar p l r hp hl hr hmul hG ha
      pres π hsq χ hχ m hnonneg hposm
    have hval : (Plancherel.SplitTorus.valuation hA
        (CocharacterUniformizer.latticeSection k A (Multiplicative.ofAdd m))).toAdd =
          (1 : ℝ) ⊗ₜ[ℤ] m :=
      Plancherel.SplitTorus.valuation_latticeSection hA m
    rw [Plancherel.SplitTorus.norm_eq_rpow_normalizedRealPart hA χ hχ.1, hval] at hlt
    have hq : (1 : ℝ) < (LocalField.residueCardinality k : ℝ) := by
      exact_mod_cast LocalField.residueCardinality_gt_one k
    rcases (Real.rpow_lt_one_iff_of_pos (by linarith)).mp hlt with h | h
    · rw [latticePair_apply]
      linarith [h.2]
    · exact absurd h.1 (not_lt.mpr hq.le)

end Necessity

/-- The necessity half of Renard VII.1.2 for represented parabolics: for a
representation square integrable modulo the center, the normalized real part of
every normalized Jacquet exponent at every represented parabolic with a compatible
root presentation lies in the strictly positive root cone. Neither admissibility
nor a unitary central character is assumed separately: both are part of square
integrability. -/
def ArbitraryParabolicCasselmanNecessityStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    haveI := hG.smooth
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      [MeasurableSpace (rationalPoints G ⧸ Subgroup.center (rationalPoints G))]
      [BorelSpace (rationalPoints G ⧸ Subgroup.center (rationalPoints G))]
      (haar : MeasureTheory.Measure (rationalPoints G ⧸ Subgroup.center (rationalPoints G)))
      [haar.IsHaarMeasure] (π : SmoothRep.{0, u, v} ℂ (rationalPoints G)),
      IsSquareIntegrableModCenter π.representation haar →
        ∀ (P M U : GroupScheme (Spec (CommRingCat.of k)))
          (A : CommGroupScheme (Spec (CommRingCat.of k)))
          (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P) (a : A.toGrp ⟶ M)
          (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
          (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
          (hmul : IsIso (subgroupMultiplication l r)) (ha : IsSplitComponent a)
          (pres : ParabolicRootPresentation p l a) (χ : rationalPoints A.toGrp →* ℂˣ),
          IsNormalizedJacquetExponent p l r hp hl hr hmul ha π χ →
            Plancherel.SplitTorus.normalizedRealPart ha.isCentralSplitTorus.1.1 χ ∈
              pres.positiveCone

/-- Proof of the necessity half of Casselman's criterion. -/
theorem arbitraryParabolicCasselmanNecessity :
    ArbitraryParabolicCasselmanNecessityStatement.{u, v} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  have := hG.smooth
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ _ _ haar _ π hsq P M U A p l r a hp hl hr hmul ha pres χ hχ
  exact normalizedRealPart_mem_positiveCone_of_squareIntegrable haar p l r hp hl hr hmul hG ha
    pres π hsq χ hχ

end Langlands.Aubert.General.RepresentedParabolic
