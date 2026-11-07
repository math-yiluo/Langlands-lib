import Langlands.GroupScheme.Rational.ParabolicBoundaryRootSupport
import Langlands.Representation.Exponents.NestedJacquetExponentProjection

/-! # Actual unitary outer exponents from a supplied boundary face -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance boundaryExponentAmbientTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)]
  {P M N Q L U PL NL : GroupScheme (Spec (CommRingCat.of k))}
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
  (hP : SubgroupFunctor.range p ≤ SubgroupFunctor.range q)
  (hM : (mL ≫ pL) ≫ l ≫ q = m ≫ p)
  (hPL : SubgroupFunctor.range (pL ≫ l ≫ q) =
    SubgroupFunctor.range (l ≫ q) ⊓ SubgroupFunctor.range p)
  {A B : CommGroupScheme (Spec (CommRingCat.of k))}
  {a : A.toGrp ⟶ L} {b : B.toGrp ⟶ M}
  (ha : IsSplitComponent a) (hb : IsSplitComponent b)
  (fine : ParabolicRootPresentation p m b)
  (outer : ParabolicRootPresentation q l a)
  (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))
  (hπ : IsNormalizedExponentTempered hG π)
  (χ : rationalPoints B.toGrp →* ℂˣ)
  (hχ : IsNormalizedJacquetExponent p m n hp hm hn hmul hb π χ)

/-- The actual outer exponent obtained by restricting the given fine exponent
along the constructed split-component factor, certified unitary by the supplied
boundary-support containment in the original outer Levi face. -/
def boundaryUnitaryJacquetExponent
    (hx : haveI := hG.smooth
      Plancherel.SplitTorus.normalizedRealPart hb.isCentralSplitTorus.1.1 χ ∈
        fine.nonnegCone)
    (hface : haveI := hG.smooth
      fine.boundaryRootIndex hx ⊆ fine.outerSimpleRootFace outer (mL ≫ pL) hM) :
    unitaryJacquetExponents q l r hq hl hr hmulQ ha π := by
  have := hG.smooth
  have := hl.isConnectedReductive.isAffineHom
  have := hl.isConnectedReductive.smooth
  let e := fine.intermediateSplitComponentFactor (l ≫ q)
    (hl.isClosedSubgroup.comp hq.isClosedSubgroup) (mL ≫ pL) hM a
    ha.isCentralSplitTorus.isCentral ha.isCentralSplitTorus.1.1
  have he : CommGroupScheme.groupHom e ≫ b ≫ mL ≫ pL = a := by
    exact fine.intermediateSplitComponentFactor_comp (l ≫ q)
      (hl.isClosedSubgroup.comp hq.isClosedSubgroup) (mL ≫ pL) hM a
      ha.isCentralSplitTorus.isCentral ha.isCentralSplitTorus.1.1
  have hM' : mL ≫ pL ≫ l ≫ q = m ≫ p := by
    simpa only [Category.assoc] using hM
  have hPL' : pointImage (pL ≫ l ≫ q) =
      pointImage (l ≫ q) ⊓ pointImage p :=
    congrArg (fun F : SubgroupFunctor G =>
      F.carrier (Over.mk (𝟙 (Spec (CommRingCat.of k))))) hPL
  have houter := isNormalizedJacquetExponent_outer_of_fine_scheme hG
    p m n hp hm hn hmul q l r hq hl hr hmulQ
    pL mL nL hpL hmL hnL hmulL (hP _) hM' hPL' π ha hb hπ e he χ hχ
  refine ⟨χ.comp (rationalPoints.map (CommGroupScheme.groupHom e)), houter, ?_⟩
  have : IsAffine B.X.left := hb.isAffine
  have hopen := ((isNormalizedJacquetExponent_iff_isOpen_ker_and
    p m n hp hm hn hmul hb π χ).mp hχ).1
  rw [Plancherel.SplitTorus.normalizedRealPart_comp_points
    ha.isCentralSplitTorus.1.1 hb.isCentralSplitTorus.1.1 e χ hopen]
  change fine.outerComponentRestriction outer (mL ≫ pL) hM _ = 0
  exact fine.outerComponentRestriction_eq_zero_of_boundaryRootIndex
    outer (mL ≫ pL) hM hG hP hx hface

include hp hm hn hmul hpL hmL hnL hmulL hP hPL hπ hχ in
/-- The constructed unitary exponent witnesses nonvanishing of the original
outer unitary Jacquet part. -/
theorem unitaryJacquetPart_ne_bot_of_boundaryRootIndex
    (hx : haveI := hG.smooth
      Plancherel.SplitTorus.normalizedRealPart hb.isCentralSplitTorus.1.1 χ ∈
        fine.nonnegCone)
    (hface : haveI := hG.smooth
      fine.boundaryRootIndex hx ⊆ fine.outerSimpleRootFace outer (mL ≫ pL) hM) :
    unitaryJacquetPart q l r hq hl hr hmulQ ha π ≠ ⊥ := by
  apply (unitaryJacquetExponents_nonempty_iff q l r hq hl hr hmulQ ha π).mp
  let ψ := boundaryUnitaryJacquetExponent hG p m n hp hm hn hmul
    q l r hq hl hr hmulQ pL mL nL hpL hmL hnL hmulL hP hM hPL
    ha hb fine outer π hπ χ hχ hx hface
  exact ⟨ψ.val, ψ.property⟩

end Langlands.Aubert.General.RepresentedParabolic
