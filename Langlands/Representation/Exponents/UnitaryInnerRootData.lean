import Langlands.GroupScheme.Rational.NestedParabolicInnerCone
import Langlands.Representation.Exponents.InnerUnitarySplitComponentFactor

/-! # Actual ambient root data for inner unitary Jacquet exponents -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance unitaryRootDataAmbientTopology : TopologicalSpace (rationalPoints G) :=
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

/-- Ambient fine parabolic geometry and compatible fine and outer root
presentations for the original inner parabolic and common Levi. -/
structure UnitaryInnerRootData where
  P : GroupScheme (Spec (CommRingCat.of k))
  N : GroupScheme (Spec (CommRingCat.of k))
  p : P ⟶ G
  m : M ⟶ P
  n : N ⟶ P
  parabolic : IsParabolicSubgroup p
  levi : IsRationalLeviSubgroup m
  radical : LeviSubgroup.IsGeometricUnipotentRadical n
  multiplication : IsIso (subgroupMultiplication m n)
  commonLevi : (mL ≫ pL) ≫ (l ≫ q) = m ≫ p
  nested : SubgroupFunctor.range p ≤ SubgroupFunctor.range q
  intersection : SubgroupFunctor.range (pL ≫ (l ≫ q)) =
    SubgroupFunctor.range (l ≫ q) ⊓ SubgroupFunctor.range p
  fine : ParabolicRootPresentation p m b
  outer : ParabolicRootPresentation q l a

variable (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))
  {hG : IsConnectedReductive G} (hπ : IsNormalizedExponentTempered hG π)

include hq hl hr hmulQ hpL hmL hnL hmulL ha hb hπ in
/-- Temperedness supplies both ambient presentations after actual extension
from the original outer Levi. -/
theorem nonempty_unitaryInnerRootData :
    Nonempty (UnitaryInnerRootData q l pL mL (a := a) (b := b)) := by
  obtain ⟨P, N, p, m, n, hp, hm, hn, hmul, hM, hPQ, hPL⟩ :=
    leviParabolicExtension k G hG Q L U q l r hq hl hr hmulQ
      PL M NL pL mL nL hpL hmL hnL hmulL
  obtain ⟨fine⟩ := hπ.nonempty_presentation p m b hp hm hb
  obtain ⟨outer⟩ := hπ.nonempty_presentation q l a hq hl ha
  exact ⟨⟨P, N, p, m, n, hp, hm, hn, hmul,
    by simpa only [Category.assoc] using hM.symm, hPQ,
    by simpa only [Category.assoc] using hPL, fine, outer⟩⟩

/-- Choose actual ambient root data for the original inner maps, without an
inner-presentation existence assumption. -/
def unitaryInnerRootData : UnitaryInnerRootData q l pL mL (a := a) (b := b) :=
  Classical.choice (nonempty_unitaryInnerRootData q l r hq hl hr hmulQ
    pL mL nL hpL hmL hnL hmulL ha hb π hπ)

include hπ in
/-- Every exponent of the inner Jacquet module of the outer unitary part lies
in the nonnegative cone of every supplied compatible inner presentation. -/
theorem normalizedRealPart_mem_innerNonnegCone_of_unitary
    (inner : haveI := hl.isConnectedReductive.isAffineHom
      ParabolicRootPresentation pL mL b)
    (χ : rationalPoints B.toGrp →* ℂˣ) :
    haveI := hl.isConnectedReductive.isAffineHom
    haveI := hl.isConnectedReductive.smooth
    letI : TopologicalSpace (rationalPoints L) := leviPointTopology l hl
    haveI : LocallyCompactSpace (rationalPoints L) :=
      leviPoints_locallyCompactSpace q l hq hl
    haveI : NonarchimedeanGroup (rationalPoints L) :=
      leviPoints_nonarchimedeanGroup q l hq hl
    IsNormalizedJacquetExponent pL mL nL hpL hmL hnL hmulL hb
      (leviUnitaryJacquetModule q l r hq hl hr hmulQ ha π) χ →
      Plancherel.SplitTorus.normalizedRealPart hb.isCentralSplitTorus.1.1 χ ∈
        inner.nonnegCone := by
  have := hG.smooth
  have := hl.isConnectedReductive.isAffineHom
  have := hl.isConnectedReductive.smooth
  let : TopologicalSpace (rationalPoints L) := leviPointTopology l hl
  have : LocallyCompactSpace (rationalPoints L) :=
    leviPoints_locallyCompactSpace q l hq hl
  have : NonarchimedeanGroup (rationalPoints L) :=
    leviPoints_nonarchimedeanGroup q l hq hl
  intro hχ
  let d := unitaryInnerRootData q l r hq hl hr hmulQ
    pL mL nL hpL hmL hnL hmulL ha hb π hπ
  have hM : mL ≫ pL ≫ l ≫ q = d.m ≫ d.p := by
    simpa only [Category.assoc] using d.commonLevi
  have hPL : pointImage (pL ≫ l ≫ q) =
      pointImage (l ≫ q) ⊓ pointImage d.p := by
    exact congrArg (fun F : SubgroupFunctor G =>
      F.carrier (Over.mk (𝟙 (Spec (CommRingCat.of k))))) d.intersection
  have hχfine := isNormalizedJacquetExponent_of_nestedUnitary hG
    d.p d.m d.n d.parabolic d.levi d.radical d.multiplication
    q l r hq hl hr hmulQ pL mL nL hpL hmL hnL hmulL
    (d.nested _) hM hPL ha π hb χ hχ
  have hfine := SatisfiesNormalizedExponentConeCondition.normalizedRealPart_mem_nonnegCone
    d.p d.m b d.parabolic d.levi hb π
    (hπ.parabolic d.p d.m b d.parabolic d.levi hb)
    d.fine d.n d.radical d.multiplication χ hχfine
  have hz := rationalCharacterRestrictReal_eq_zero_of_innerUnitaryExponent
    q l r hq hl hr hmulQ pL mL nL hpL hmL hnL hmulL ha hb π hπ χ hχ
  let f := innerSplitComponentFactor q l r hq hl hr hmulQ
    pL mL nL hpL hmL hnL hmulL ha hb π hπ
  let g := d.fine.intermediateSplitComponentFactor (l ≫ q)
    (hl.isClosedSubgroup.comp hq.isClosedSubgroup) (mL ≫ pL) d.commonLevi
    a ha.isCentralSplitTorus.isCentral ha.isCentralSplitTorus.1.1
  have hfactor : CommGroupScheme.groupHom f = CommGroupScheme.groupHom g := by
    have hclosed := hmL.isClosedSubgroup.comp hpL.isClosedSubgroup
    have hbclosed := hb.isCentralSplitTorus.1.2
    let := (hbclosed.comp hclosed).mono
    have : Mono (b ≫ (mL ≫ pL)).hom.hom := Over.mono_of_mono_left _
    apply Grp.hom_ext
    apply (cancel_mono (b ≫ (mL ≫ pL)).hom.hom).mp
    change (CommGroupScheme.groupHom f ≫ (b ≫ (mL ≫ pL))).hom.hom =
      (CommGroupScheme.groupHom g ≫ (b ≫ (mL ≫ pL))).hom.hom
    apply congrArg (fun t : A.toGrp ⟶ L => t.hom.hom)
    calc
      CommGroupScheme.groupHom f ≫ (b ≫ (mL ≫ pL)) = a := by
        simpa only [f, Category.assoc] using innerSplitComponentFactor_comp
          q l r hq hl hr hmulQ pL mL nL hpL hmL hnL hmulL ha hb π hπ
      _ = CommGroupScheme.groupHom g ≫ (b ≫ (mL ≫ pL)) :=
        (d.fine.intermediateSplitComponentFactor_comp (l ≫ q)
          (hl.isClosedSubgroup.comp hq.isClosedSubgroup) (mL ≫ pL) d.commonLevi
          a ha.isCentralSplitTorus.isCentral ha.isCentralSplitTorus.1.1).symm
  have hzero : d.fine.outerComponentRestriction d.outer (mL ≫ pL) d.commonLevi
      (Plancherel.SplitTorus.normalizedRealPart hb.isCentralSplitTorus.1.1 χ) = 0 := by
    change rationalCharacterRestrictReal (CommGroupScheme.groupHom g) _ = 0
    rw [← hfactor]
    exact hz
  exact d.fine.mem_innerNonnegCone_of_fine_mem_of_outerRestriction_eq_zero
    d.outer pL mL d.commonLevi d.intersection hG d.nested inner hfine hzero

end Langlands.Aubert.General.RepresentedParabolic
