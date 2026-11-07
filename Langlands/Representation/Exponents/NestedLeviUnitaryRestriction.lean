import Langlands.Representation.Exponents.NestedLeviJacquetExponents
import Langlands.Representation.Exponents.TemperedLeviJacquetDecomposition
import Langlands.Representation.Exponents.TemperedGeometricPiece
import Langlands.Representation.Exponents.JacquetExponentRestriction

/-! # Central restriction of inner exponents of an outer unitary Jacquet part -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance nestedRestrictionAmbientTopology : TopologicalSpace (rationalPoints G) :=
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
  (e : rationalPoints A.toGrp →* rationalPoints B.toGrp)
  (he : ∀ t : rationalPoints A.toGrp,
    (splitComponentPointsMap (mL ≫ pL) b (e t) : rationalPoints L) =
      rationalPoints.map a t)
  (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))

/-- The ordinary inner coinvariant quotient of the outer unitary Jacquet module,
intertwining the outer split-component action. The factor is supplied on points. -/
def innerUnitaryJacquetCentralQuotient :
    haveI := hl.isConnectedReductive.isAffineHom
    letI : TopologicalSpace (rationalPoints L) := leviPointTopology l hl
    haveI : LocallyCompactSpace (rationalPoints L) :=
      leviPoints_locallyCompactSpace q l hq hl
    haveI : NonarchimedeanGroup (rationalPoints L) :=
      leviPoints_nonarchimedeanGroup q l hq hl
    Representation.IntertwiningMap
      ((leviUnitaryJacquetModule q l r hq hl hr hmulQ ha π).representation.comp
        (rationalPoints.map a))
      (((jacquetFunctor pL mL nL hpL hnL hmL hmulL).obj
        (leviUnitaryJacquetModule q l r hq hl hr hmulQ ha π)).representation.comp
          ((splitComponentPointsMap (mL ≫ pL) b).comp e)) := by
  have := hl.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints L) := leviPointTopology l hl
  have : LocallyCompactSpace (rationalPoints L) :=
    leviPoints_locallyCompactSpace q l hq hl
  have : NonarchimedeanGroup (rationalPoints L) :=
    leviPoints_nonarchimedeanGroup q l hq hl
  exact normalizedJacquetCentralQuotient
    (pointImage (nL ≫ pL)) (pointImage (mL ≫ pL))
    (isClosed_pointImage_comp pL nL hpL.isClosedSubgroup hnL.1.isClosedSubgroup)
    (pointImage_le_normalizer pL mL nL hnL)
    (leviUnitaryJacquetModule q l r hq hl hr hmulQ ha π) (rationalPoints.map a)
    ((splitComponentPointsMap (mL ≫ pL) b).comp e) he
    ha.isCentralSplitTorus.isCentral.map_mem_center

/-- This central intertwiner is surjective, as the actual coinvariant projection. -/
theorem innerUnitaryJacquetCentralQuotient_surjective :
    haveI := hl.isConnectedReductive.isAffineHom
    letI : TopologicalSpace (rationalPoints L) := leviPointTopology l hl
    haveI : LocallyCompactSpace (rationalPoints L) :=
      leviPoints_locallyCompactSpace q l hq hl
    haveI : NonarchimedeanGroup (rationalPoints L) :=
      leviPoints_nonarchimedeanGroup q l hq hl
    Function.Surjective
      (innerUnitaryJacquetCentralQuotient q l r hq hl hr hmulQ
        pL mL nL hpL hmL hnL hmulL ha e he π) := by
  have := hl.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints L) := leviPointTopology l hl
  have : LocallyCompactSpace (rationalPoints L) :=
    leviPoints_locallyCompactSpace q l hq hl
  have : NonarchimedeanGroup (rationalPoints L) :=
    leviPoints_nonarchimedeanGroup q l hq hl
  exact Jacquet.Localization.mk_surjective
    (leviUnitaryJacquetModule q l r hq hl hr hmulQ ha π).representation
    (pointImage (nL ≫ pL)) 1

/-- Each outer split-component exponent on the actual outer unitary module
has zero real part, independently of temperedness or admissibility. -/
theorem normalizedRealPart_eq_zero_of_leviUnitaryGroupExponent
    (ψ : rationalPoints A.toGrp →* ℂˣ) :
    haveI := hl.isConnectedReductive.isAffineHom
    letI : TopologicalSpace (rationalPoints L) := leviPointTopology l hl
    haveI : LocallyCompactSpace (rationalPoints L) :=
      leviPoints_locallyCompactSpace q l hq hl
    haveI : NonarchimedeanGroup (rationalPoints L) :=
      leviPoints_nonarchimedeanGroup q l hq hl
    IsGroupExponent ha (leviUnitaryJacquetModule q l r hq hl hr hmulQ ha π) ψ →
      Plancherel.SplitTorus.normalizedRealPart ha.isCentralSplitTorus.1.1 ψ = 0 := by
  have := hl.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints L) := leviPointTopology l hl
  have : LocallyCompactSpace (rationalPoints L) :=
    leviPoints_locallyCompactSpace q l hq hl
  have : NonarchimedeanGroup (rationalPoints L) :=
    leviPoints_nonarchimedeanGroup q l hq hl
  intro hψ
  have hgen := (generalizedWeightSpace_ne_bot_iff _ ψ _
    (leviUnitaryJacquetModule q l r hq hl hr hmulQ ha π).isSmooth).mp
      ((isGroupExponent_iff_isOpen_ker_and ha _ ψ).mp hψ).2
  exact (normalizedRealPart_eq_zero_of_unitaryJacquetPart q l r hq hl hr hmulQ
    ha π hgen).2

include hb he in
/-- For a tempered source, every inner normalized Jacquet exponent of the
outer unitary module restricts to an exponent with zero real part on the outer
split component, along every compatible supplied point factor. -/
theorem normalizedRealPart_comp_eq_zero_of_innerUnitaryExponent
    {hG : IsConnectedReductive G} (hπ : IsNormalizedExponentTempered hG π)
    (χ : rationalPoints B.toGrp →* ℂˣ) :
    haveI := hl.isConnectedReductive.isAffineHom
    letI : TopologicalSpace (rationalPoints L) := leviPointTopology l hl
    haveI : LocallyCompactSpace (rationalPoints L) :=
      leviPoints_locallyCompactSpace q l hq hl
    haveI : NonarchimedeanGroup (rationalPoints L) :=
      leviPoints_nonarchimedeanGroup q l hq hl
    IsNormalizedJacquetExponent pL mL nL hpL hmL hnL hmulL hb
      (leviUnitaryJacquetModule q l r hq hl hr hmulQ ha π) χ →
      IsGroupExponent ha (leviUnitaryJacquetModule q l r hq hl hr hmulQ ha π) (χ.comp e) ∧
        Plancherel.SplitTorus.normalizedRealPart ha.isCentralSplitTorus.1.1 (χ.comp e) = 0 := by
  have := hl.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints L) := leviPointTopology l hl
  have : LocallyCompactSpace (rationalPoints L) :=
    leviPoints_locallyCompactSpace q l hq hl
  have : NonarchimedeanGroup (rationalPoints L) :=
    leviPoints_nonarchimedeanGroup q l hq hl
  intro hχ
  have hres := normalizedJacquetExponent_restrict pL mL nL hpL hmL hnL hmulL hb ha e he
    (leviUnitaryJacquetModule q l r hq hl hr hmulQ ha π) χ
    (hπ.isAdmissible_leviUnitaryJacquetModule q l r hq hl hr hmulQ ha) hχ
  exact ⟨hres, normalizedRealPart_eq_zero_of_leviUnitaryGroupExponent
    q l r hq hl hr hmulQ ha π (χ.comp e) hres⟩

end Langlands.Aubert.General.RepresentedParabolic
