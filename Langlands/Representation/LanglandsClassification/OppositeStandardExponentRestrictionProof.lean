import Langlands.Representation.LanglandsClassification.OppositeStandardExponentRestrictionStatement
import Langlands.Representation.LanglandsClassification.OppositeStandardNesting
import Langlands.Representation.LanglandsClassification.OppositeStandardExponentParameters
import Langlands.Representation.Exponents.NestedJacquetExponentProjection
import Langlands.Representation.Exponents.ArbitraryParabolicJacquetAdmissibilityProof
import Langlands.Representation.Exponents.MaximalLeviExponentTransport
import Langlands.GroupScheme.Rational.ParabolicRootPresentationSimpleRoots

/-! # Restriction of opposite standard exponents to a larger standard Levi: proof

An actual opposite standard Jacquet exponent on `J` restricts, along the chosen
morphism of split components `A_K → A_J`, to an actual opposite standard Jacquet
exponent on any `K ⊇ J`. Its full real parameter is the unique lift annihilating
the coroots of `K` of the restricted real part.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme RealTorusSpace

section Generic

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance exponentRestrictionProofAmbientTopology :
    TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)]

variable {P M N Q L U PL NL : GroupScheme (Spec (CommRingCat.of k))}
  (hG : IsConnectedReductive G)
  (p : P ⟶ G) (m : M ⟶ P) (n : N ⟶ P)
  (hp : IsParabolicSubgroup p) (hm : IsRationalLeviSubgroup m)
  (hn : LeviSubgroup.IsGeometricUnipotentRadical n)
  (hmul : IsIso (subgroupMultiplication m n))
  (q : Q ⟶ G) (l : L ⟶ Q) (r : U ⟶ Q)
  (hq : IsParabolicSubgroup q) (hl : IsRationalLeviSubgroup l)
  (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
  (hmulQ : IsIso (subgroupMultiplication l r))
  (pL : PL ⟶ L) (mL : M ⟶ PL) (nL : NL ⟶ PL)
  (hpL : IsParabolicSubgroup pL) (hmL : IsRationalLeviSubgroup mL)
  (hnL : LeviSubgroup.IsGeometricUnipotentRadical nL)
  (hmulL : IsIso (subgroupMultiplication mL nL))
  (hPQ : pointImage p ≤ pointImage q)
  (hM : mL ≫ pL ≫ l ≫ q = m ≫ p)
  (hPL : pointImage (pL ≫ l ≫ q) = pointImage (l ≫ q) ⊓ pointImage p)

variable (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))

variable {A B : CommGroupScheme (Spec (CommRingCat.of k))}
  {a : A.toGrp ⟶ L} {b : B.toGrp ⟶ M}
  (ha : IsSplitComponent a) (hb : IsSplitComponent b)

include hG hPQ hM hPL hpL hmL hnL hmulL in
/-- For an admissible source, a fine normalized Jacquet exponent restricts along
a morphism of split components to a normalized Jacquet exponent for the outer
parabolic. This is the admissible variant of
`isNormalizedJacquetExponent_outer_of_fine_scheme`: admissibility of the outer
Jacquet module comes from `arbitraryParabolicJacquetAdmissibility`. -/
theorem isNormalizedJacquetExponent_outer_of_fine_of_isAdmissible
    (hadm : π.IsAdmissible)
    (e : A ⟶ B) (he : CommGroupScheme.groupHom e ≫ b ≫ mL ≫ pL = a)
    (χ : rationalPoints B.toGrp →* ℂˣ)
    (hχ : IsNormalizedJacquetExponent p m n hp hm hn hmul hb π χ) :
    IsNormalizedJacquetExponent q l r hq hl hr hmulQ ha π
      (χ.comp (rationalPoints.map (CommGroupScheme.groupHom e))) := by
  have := hl.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints L) := leviPointTopology l hl
  have : LocallyCompactSpace (rationalPoints L) :=
    leviPoints_locallyCompactSpace q l hq hl
  have : NonarchimedeanGroup (rationalPoints L) :=
    leviPoints_nonarchimedeanGroup q l hq hl
  let σ := (leviJacquetFunctor q l r hq hr hl hmulQ).obj π
  have hσ : σ.IsAdmissible :=
    isAdmissible_comp_continuousMulEquiv
      ((jacquetFunctor q l r hq hr hl hmulQ).obj π).representation
      (leviPointsEquiv q l hq hl)
      (arbitraryParabolicJacquetAdmissibility.{u, v} k G hG Q L U q l r hq hl hr hmulQ
        π hadm)
  have hinner := isNormalizedJacquetExponent_nested_of_fine hG
    p m n hp hm hn hmul q l r hq hl hr hmulQ
    pL mL nL hpL hmL hnL hmulL hPQ hM hPL π hb χ hχ
  let eP := rationalPoints.map (CommGroupScheme.groupHom e)
  have hpts : ∀ t : rationalPoints A.toGrp,
      (splitComponentPointsMap (mL ≫ pL) b (eP t) : rationalPoints L) =
        rationalPoints.map a t := by
    intro t
    have h := congrArg (fun f : A.toGrp ⟶ L => rationalPoints.map f t) he
    change t ≫ (CommGroupScheme.groupHom e ≫ b ≫ mL ≫ pL).hom.hom =
      t ≫ a.hom.hom at h
    change ((t ≫ _ ) ≫ b.hom.hom) ≫ (mL ≫ pL).hom.hom = t ≫ a.hom.hom
    simpa only [Grp.comp_hom_hom, Category.assoc] using h
  have hres := normalizedJacquetExponent_restrict pL mL nL hpL hmL hnL hmulL
    hb ha eP hpts σ χ hσ hinner
  rw [isNormalizedJacquetExponent_iff_leviEigencharacter]
  exact (generalizedWeightSpace_ne_bot_iff _ (χ.comp eP) _ σ.isSmooth).mp
    ((isGroupExponent_iff_isOpen_ker_and ha σ (χ.comp eP)).mp hres).2

end Generic

namespace OppositeStandardJacquetFamily

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)

local instance restrictionProofPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
/-- The character of an element of the opposite family is a normalized Jacquet
exponent for the opposite datum of its label. -/
theorem isNormalizedJacquetExponent_val (x : exponents i ν hG hi hν π) :
    IsNormalizedJacquetExponent (datum i ν hG hi hν x.1).p (datum i ν hG hi hν x.1).l
      (datum i ν hG hi hν x.1).r (datum i ν hG hi hν x.1).hp (datum i ν hG hi hν x.1).hl
      (datum i ν hG hi hν x.1).hr (datum i ν hG hi hν x.1).hmul
      (component i ν hG hi hν x.1).ha π x.2.val :=
  x.2.property

/-- For an admissible representation, the restriction of an opposite standard
exponent on `J` to the chosen split component of a larger label `K`, along the
nesting morphism `A_K → A_J`, as an opposite standard exponent on `K`. -/
def restrictExponent (hadm : π.IsAdmissible) (z : exponents i ν hG hi hν π)
    {K : StandardJacquetFamily.Index i ν} (h : z.1.val ⊆ K.val) :
    exponents i ν hG hi hν π :=
  ⟨K, ⟨z.2.val.comp (rationalPoints.map
      (CommGroupScheme.groupHom (Nesting.nestedData i ν hG hi hν h).e)),
    isNormalizedJacquetExponent_outer_of_fine_of_isAdmissible hG
      (datum i ν hG hi hν z.1).p (datum i ν hG hi hν z.1).l (datum i ν hG hi hν z.1).r
      (datum i ν hG hi hν z.1).hp (datum i ν hG hi hν z.1).hl (datum i ν hG hi hν z.1).hr
      (datum i ν hG hi hν z.1).hmul
      (datum i ν hG hi hν K).p (datum i ν hG hi hν K).l (datum i ν hG hi hν K).r
      (datum i ν hG hi hν K).hp (datum i ν hG hi hν K).hl (datum i ν hG hi hν K).hr
      (datum i ν hG hi hν K).hmul
      (Nesting.nestedData i ν hG hi hν h).p (Nesting.nestedData i ν hG hi hν h).m
      (Nesting.nestedData i ν hG hi hν h).n (Nesting.nestedData i ν hG hi hν h).hp
      (Nesting.nestedData i ν hG hi hν h).hm (Nesting.nestedData i ν hG hi hν h).hn
      (Nesting.nestedData i ν hG hi hν h).hmul
      (Nesting.pointImage_opposite_p_le i ν hG hi hν h)
      (Nesting.nestedData i ν hG hi hν h).levi_comp
      (Nesting.nestedData i ν hG hi hν h).inner_eq π
      (component i ν hG hi hν K).ha (component i ν hG hi hν z.1).ha hadm
      (Nesting.nestedData i ν hG hi hν h).e
      (Nesting.nestedData i ν hG hi hν h).e_comp_inner z.2.val
      (isNormalizedJacquetExponent_val i ν hG hi hν π z)⟩⟩

@[simp] theorem restrictExponent_fst (hadm : π.IsAdmissible) (z : exponents i ν hG hi hν π)
    {K : StandardJacquetFamily.Index i ν} (h : z.1.val ⊆ K.val) :
    (restrictExponent i ν hG hi hν π hadm z h).1 = K :=
  rfl

/-- The real part of the restricted exponent is the restriction of the real
part along the nesting morphism of split components. -/
theorem realPart_restrictExponent (hadm : π.IsAdmissible) (z : exponents i ν hG hi hν π)
    {K : StandardJacquetFamily.Index i ν} (h : z.1.val ⊆ K.val) :
    realPart i ν hG hi hν π (restrictExponent i ν hG hi hν π hadm z h) =
      rationalCharacterRestrictReal
        (CommGroupScheme.groupHom (Nesting.nestedData i ν hG hi hν h).e)
        (realPart i ν hG hi hν π z) := by
  have : IsAffine (component i ν hG hi hν z.1).A.X.left :=
    (component i ν hG hi hν z.1).ha.isAffine
  have hopen := ((isNormalizedJacquetExponent_iff_isOpen_ker_and _ _ _ _ _ _ _
    (component i ν hG hi hν z.1).ha π z.2.val).mp
      (isNormalizedJacquetExponent_val i ν hG hi hν π z)).1
  exact Plancherel.SplitTorus.normalizedRealPart_comp_points
    (component i ν hG hi hν K).ha.isCentralSplitTorus.1.1
    (component i ν hG hi hν z.1).ha.isCentralSplitTorus.1.1
    (Nesting.nestedData i ν hG hi hν h).e z.2.val hopen

section FullParameter

variable [LocallyOfFiniteType G.X.hom] [Mono i.hom.hom.left]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [T2Space k]
  [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  [Mono i.hom.hom.left] in
/-- Restriction to the chosen split component of `K` kills the real span of the
roots in `K`. -/
theorem restrict_eq_zero_of_mem_span (K : StandardJacquetFamily.Index i ν) {y : Vstar T}
    (hy : y ∈ Submodule.span ℝ ((fun α : characterLattice T => (1 : ℝ) ⊗ₜ[ℤ] α) '' K.val)) :
    rationalCharacterRestrictReal (component i ν hG hi hν K).g y = 0 := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨α, hα, rfl⟩ := hy
    rw [rationalCharacterRestrictReal_tmul]
    change (1 : ℝ) ⊗ₜ[ℤ]
      ((rootPresentation i ν hG hi hν K).data.f ≫ α) = 0
    rw [(rootPresentation i ν hG hi hν K).selectedRoot_restrict_eq_zero (alpha := α) hα,
      tmul_zero]
  | zero => exact map_zero _
  | add y y' _ _ hy hy' => rw [map_add, hy, hy', add_zero]
  | smul c y _ hy => rw [map_smul, hy, smul_zero]

variable (D : RelativeRootReflectionData i)

/-- The full real parameter of the restricted exponent is the prescribed `w`
whenever `w` annihilates the coroots of `K` and is congruent to the original
full parameter modulo the real span of the roots of `K`. -/
theorem fullRealPart_restrictExponent (hadm : π.IsAdmissible) (z : exponents i ν hG hi hν π)
    {K : StandardJacquetFamily.Index i ν} (h : z.1.val ⊆ K.val) (w : Vstar T)
    (hw : ∀ α : relativeRoots i, α.1 ∈ K.val → pair T w ((1 : ℝ) ⊗ₜ[ℤ] D.coroot α) = 0)
    (hspan : fullRealPart i ν hG hi hν π D z - w ∈
      Submodule.span ℝ ((fun α : characterLattice T => (1 : ℝ) ⊗ₜ[ℤ] α) '' K.val)) :
    fullRealPart i ν hG hi hν π D (restrictExponent i ν hG hi hν π hadm z h) = w := by
  apply fullRealPart_eq_of_restrict_eq
  · have hdiff := restrict_eq_zero_of_mem_span i ν hG hi hν K hspan
    rw [map_sub, sub_eq_zero] at hdiff
    rw [realPart_restrictExponent, ← restrict_fullRealPart i ν hG hi hν π D z,
      rationalCharacterRestrictReal_comp_apply, (Nesting.nestedData i ν hG hi hν h).e_g]
    exact hdiff.symm
  · exact hw

end FullParameter

end OppositeStandardJacquetFamily

/-- Renard VII.4.2 (iii), restriction step: an actual opposite standard
exponent on `J` gives, for every standard `K ⊇ J`, an actual opposite standard
exponent on `K` whose full real parameter is any prescribed `w` annihilating the
coroots of `K` and congruent to the original full parameter modulo the roots
of `K`. -/
theorem oppositeStandardExponentRestriction :
    OppositeStandardExponentRestrictionStatement.{u, v} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  have := hG.smooth
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ T i _ ν D hi hν _hmin π hadm _hfl z K w hJK hw hspan
  exact ⟨OppositeStandardJacquetFamily.restrictExponent i ν hG hi hν π hadm z hJK, rfl,
    OppositeStandardJacquetFamily.fullRealPart_restrictExponent i ν hG hi hν π D hadm z hJK
      w hw hspan⟩

end Langlands.Aubert.General.RepresentedParabolic
