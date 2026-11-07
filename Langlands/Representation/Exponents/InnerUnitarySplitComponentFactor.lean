import Langlands.GroupScheme.Rational.NestedSplitComponentFactorization
import Langlands.Representation.Exponents.NestedLeviUnitaryRestriction
import Langlands.Representation.Plancherel.SplitTorusRealPartLaws

/-! # Actual split-component factors for inner unitary Jacquet exponents -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance innerFactorAmbientTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)]
  {Q L U PL M NL : GroupScheme (Spec (CommRingCat.of k))}
  (q : Q ⟶ G) (l : L ⟶ Q) (r : U ⟶ Q)
  (hq : IsParabolicSubgroup q) (hl : IsRationalLeviSubgroup l)
  (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
  (hmulQ : IsIso (subgroupMultiplication l r))
  (pL : PL ⟶ L) (mL : M ⟶ PL) (nL : NL ⟶ PL)
  (hpL : IsParabolicSubgroup pL) (hmL : IsRationalLeviSubgroup mL)
  (hnL : LeviSubgroup.IsGeometricUnipotentRadical nL)
  (hmulL : IsIso (subgroupMultiplication mL nL))
  {A B : CommGroupScheme (Spec (CommRingCat.of k))}
  {a : A.toGrp ⟶ L} {b : B.toGrp ⟶ M}
  (ha : IsSplitComponent a) (hb : IsSplitComponent b)
  (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))
  {hG : IsConnectedReductive G} (hπ : IsNormalizedExponentTempered hG π)

include hq hl hr hmulQ hpL hmL hnL hmulL ha hb hπ in
/-- Temperedness supplies the fine ambient presentation used to factor the
original outer split component through the original inner split component. -/
theorem exists_innerSplitComponentFactor :
    ∃ f : A ⟶ B, CommGroupScheme.groupHom f ≫ b ≫ mL ≫ pL = a := by
  obtain ⟨P, N, p, m, n, hp, hm, hn, hmul, hM, _, _⟩ :=
    leviParabolicExtension k G hG Q L U q l r hq hl hr hmulQ
      PL M NL pL mL nL hpL hmL hnL hmulL
  obtain ⟨pres⟩ := hπ.nonempty_presentation p m b hp hm hb
  have hM' : (mL ≫ pL) ≫ (l ≫ q) = m ≫ p := by
    simpa only [Category.assoc] using hM.symm
  let hj := hl.isClosedSubgroup.comp hq.isClosedSubgroup
  refine ⟨pres.intermediateSplitComponentFactor (l ≫ q) hj
    (mL ≫ pL) hM' a ha.isCentralSplitTorus.isCentral ha.isCentralSplitTorus.1.1, ?_⟩
  exact pres.intermediateSplitComponentFactor_comp (l ≫ q) hj
    (mL ≫ pL) hM' a ha.isCentralSplitTorus.isCentral ha.isCentralSplitTorus.1.1

/-- A chosen actual factor between the two original split components. -/
def innerSplitComponentFactor : A ⟶ B :=
  (exists_innerSplitComponentFactor q l r hq hl hr hmulQ
    pL mL nL hpL hmL hnL hmulL ha hb π hπ).choose

/-- The chosen factor commutes with the original inner Levi inclusion into
the actual outer Levi. -/
theorem innerSplitComponentFactor_comp :
    CommGroupScheme.groupHom
        (innerSplitComponentFactor q l r hq hl hr hmulQ
          pL mL nL hpL hmL hnL hmulL ha hb π hπ) ≫ b ≫ mL ≫ pL = a :=
  (exists_innerSplitComponentFactor q l r hq hl hr hmulQ
    pL mL nL hpL hmL hnL hmulL ha hb π hπ).choose_spec

/-- Its rational-point factor has exactly the compatibility used by the
published central coinvariant quotient. -/
theorem innerSplitComponentFactor_points (t : rationalPoints A.toGrp) :
    (splitComponentPointsMap (mL ≫ pL) b
      (rationalPoints.map (CommGroupScheme.groupHom
        (innerSplitComponentFactor q l r hq hl hr hmulQ
          pL mL nL hpL hmL hnL hmulL ha hb π hπ)) t) : rationalPoints L) =
      rationalPoints.map a t := by
  have h := congrArg (fun f : A.toGrp ⟶ L => rationalPoints.map f t)
    (innerSplitComponentFactor_comp q l r hq hl hr hmulQ
      pL mL nL hpL hmL hnL hmulL ha hb π hπ)
  change t ≫ (CommGroupScheme.groupHom
    (innerSplitComponentFactor q l r hq hl hr hmulQ
      pL mL nL hpL hmL hnL hmulL ha hb π hπ) ≫ b ≫ mL ≫ pL).hom.hom =
        t ≫ a.hom.hom at h
  change ((t ≫ _ ) ≫ b.hom.hom) ≫ (mL ≫ pL).hom.hom = t ≫ a.hom.hom
  simpa only [Grp.comp_hom_hom, Category.assoc] using h

/-- An inner exponent of the outer unitary Jacquet part has zero restriction
to the original outer split component, along the constructed actual map. -/
theorem rationalCharacterRestrictReal_eq_zero_of_innerUnitaryExponent
    (χ : rationalPoints B.toGrp →* ℂˣ) :
    haveI := hl.isConnectedReductive.isAffineHom
    letI : TopologicalSpace (rationalPoints L) := leviPointTopology l hl
    haveI : LocallyCompactSpace (rationalPoints L) :=
      leviPoints_locallyCompactSpace q l hq hl
    haveI : NonarchimedeanGroup (rationalPoints L) :=
      leviPoints_nonarchimedeanGroup q l hq hl
    IsNormalizedJacquetExponent pL mL nL hpL hmL hnL hmulL hb
      (leviUnitaryJacquetModule q l r hq hl hr hmulQ ha π) χ →
      rationalCharacterRestrictReal
        (CommGroupScheme.groupHom
          (innerSplitComponentFactor q l r hq hl hr hmulQ
            pL mL nL hpL hmL hnL hmulL ha hb π hπ))
        (Plancherel.SplitTorus.normalizedRealPart hb.isCentralSplitTorus.1.1 χ) = 0 := by
  have := hl.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints L) := leviPointTopology l hl
  have : LocallyCompactSpace (rationalPoints L) :=
    leviPoints_locallyCompactSpace q l hq hl
  have : NonarchimedeanGroup (rationalPoints L) :=
    leviPoints_nonarchimedeanGroup q l hq hl
  intro hχ
  let f := innerSplitComponentFactor q l r hq hl hr hmulQ
    pL mL nL hpL hmL hnL hmulL ha hb π hπ
  have he := innerSplitComponentFactor_points q l r hq hl hr hmulQ
    pL mL nL hpL hmL hnL hmulL ha hb π hπ
  have hz := (normalizedRealPart_comp_eq_zero_of_innerUnitaryExponent
    q l r hq hl hr hmulQ pL mL nL hpL hmL hnL hmulL ha hb
    (rationalPoints.map (CommGroupScheme.groupHom f)) he π hπ χ hχ).2
  have : IsAffine B.X.left := hb.isAffine
  have hopen := ((isNormalizedJacquetExponent_iff_isOpen_ker_and
    pL mL nL hpL hmL hnL hmulL hb _ χ).mp hχ).1
  rw [Plancherel.SplitTorus.normalizedRealPart_comp_points
    ha.isCentralSplitTorus.1.1 hb.isCentralSplitTorus.1.1 f χ hopen] at hz
  exact hz

end Langlands.Aubert.General.RepresentedParabolic
