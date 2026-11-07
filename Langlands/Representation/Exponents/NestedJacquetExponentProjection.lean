import Langlands.Representation.Exponents.NestedLeviJacquetExponents
import Langlands.Representation.Exponents.TemperedLeviJacquetDecomposition
import Langlands.Representation.Exponents.JacquetExponentRestriction
import Langlands.Representation.Exponents.UnitaryJacquetExponents
import Langlands.Representation.Plancherel.SplitTorusRealPartLaws

/-! # Projection of actual fine Jacquet exponents to an outer parabolic -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance exponentProjectionAmbientTopology : TopologicalSpace (rationalPoints G) :=
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

/-- The actual forward map from the fine Jacquet module to the iterated
outer-then-inner module, chosen from normalized transitivity. -/
def fineToNestedLeviJacquetMap :
    haveI := hl.isConnectedReductive.isAffineHom
    letI : TopologicalSpace (rationalPoints L) := leviPointTopology l hl
    haveI : LocallyCompactSpace (rationalPoints L) :=
      leviPoints_locallyCompactSpace q l hq hl
    haveI : NonarchimedeanGroup (rationalPoints L) :=
      leviPoints_nonarchimedeanGroup q l hq hl
    letI : TopologicalSpace (rationalPoints M) := leviPointTopology m hm
    (leviJacquetFunctor p m n hp hn hm hmul).obj π ⟶
      (leviJacquetFunctor pL mL nL hpL hnL hmL hmulL).obj
        ((leviJacquetFunctor q l r hq hr hl hmulQ).obj π) := by
  have := hl.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints L) := leviPointTopology l hl
  have : LocallyCompactSpace (rationalPoints L) :=
    leviPoints_locallyCompactSpace q l hq hl
  have : NonarchimedeanGroup (rationalPoints L) :=
    leviPoints_nonarchimedeanGroup q l hq hl
  let : TopologicalSpace (rationalPoints M) := leviPointTopology m hm
  let E := Classical.choice
    (leviParabolicTransitivity k G hG P M N Q L U PL NL
      p m n hp hm hn hmul q l r hq hl hr hmulQ
      pL mL nL hpL hmL hnL hmulL hPQ hM hPL).2
  exact E.hom.app π

/-- The forward transitivity map is injective. -/
theorem fineToNestedLeviJacquetMap_injective :
    haveI := hl.isConnectedReductive.isAffineHom
    letI : TopologicalSpace (rationalPoints L) := leviPointTopology l hl
    haveI : LocallyCompactSpace (rationalPoints L) :=
      leviPoints_locallyCompactSpace q l hq hl
    haveI : NonarchimedeanGroup (rationalPoints L) :=
      leviPoints_nonarchimedeanGroup q l hq hl
    letI : TopologicalSpace (rationalPoints M) := leviPointTopology m hm
    Function.Injective (SmoothRep.hom
      (fineToNestedLeviJacquetMap hG p m n hp hm hn hmul q l r hq hl hr hmulQ
        pL mL nL hpL hmL hnL hmulL hPQ hM hPL π)) := by
  have := hl.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints L) := leviPointTopology l hl
  have : LocallyCompactSpace (rationalPoints L) :=
    leviPoints_locallyCompactSpace q l hq hl
  have : NonarchimedeanGroup (rationalPoints L) :=
    leviPoints_nonarchimedeanGroup q l hq hl
  let : TopologicalSpace (rationalPoints M) := leviPointTopology m hm
  let E := Classical.choice
    (leviParabolicTransitivity k G hG P M N Q L U PL NL
      p m n hp hm hn hmul q l r hq hl hr hmulQ
      pL mL nL hpL hmL hnL hmulL hPQ hM hPL).2
  exact (SmoothRep.equivOfIso (E.app π)).injective

variable {A B : CommGroupScheme (Spec (CommRingCat.of k))}
  {a : A.toGrp ⟶ L} {b : B.toGrp ⟶ M}
  (ha : IsSplitComponent a) (hb : IsSplitComponent b)

include hG hPQ hM hPL in
/-- A fine exponent occurs in the iterated actual Jacquet module, on the
same original common-Levi split component and with the same character. -/
theorem isNormalizedJacquetExponent_nested_of_fine
    (χ : rationalPoints B.toGrp →* ℂˣ)
    (hχ : IsNormalizedJacquetExponent p m n hp hm hn hmul hb π χ) :
    haveI := hl.isConnectedReductive.isAffineHom
    letI : TopologicalSpace (rationalPoints L) := leviPointTopology l hl
    haveI : LocallyCompactSpace (rationalPoints L) :=
      leviPoints_locallyCompactSpace q l hq hl
    haveI : NonarchimedeanGroup (rationalPoints L) :=
      leviPoints_nonarchimedeanGroup q l hq hl
    IsNormalizedJacquetExponent pL mL nL hpL hmL hnL hmulL hb
      ((leviJacquetFunctor q l r hq hr hl hmulQ).obj π) χ := by
  have := hl.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints L) := leviPointTopology l hl
  have : LocallyCompactSpace (rationalPoints L) :=
    leviPoints_locallyCompactSpace q l hq hl
  have : NonarchimedeanGroup (rationalPoints L) :=
    leviPoints_nonarchimedeanGroup q l hq hl
  let : TopologicalSpace (rationalPoints M) := leviPointTopology m hm
  rw [isNormalizedJacquetExponent_iff_leviEigencharacter] at hχ ⊢
  let F := SmoothRep.hom
    (fineToNestedLeviJacquetMap hG p m n hp hm hn hmul q l r hq hl hr hmulQ
      pL mL nL hpL hmL hnL hmulL hPQ hM hPL π)
  let FB : Representation.IntertwiningMap
      (((leviJacquetFunctor p m n hp hn hm hmul).obj π).representation.comp
        (rationalPoints.map b))
      (((leviJacquetFunctor pL mL nL hpL hnL hmL hmulL).obj
        ((leviJacquetFunctor q l r hq hr hl hmulQ).obj π)).representation.comp
          (rationalPoints.map b)) :=
    { toLinearMap := F.toLinearMap
      isIntertwining' t := F.isIntertwining' (rationalPoints.map b t) }
  obtain ⟨d, hd⟩ := hχ
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).mp hd
  apply isGeneralizedEigencharacter_of_map_ne_zero FB χ d hx
  intro h
  change F x = 0 at h
  apply hx0
  exact (fineToNestedLeviJacquetMap_injective hG p m n hp hm hn hmul
    q l r hq hl hr hmulQ pL mL nL hpL hmL hnL hmulL hPQ hM hPL π)
      (by simpa only [map_zero] using h)

include hG hPQ hM hPL hpL hmL hnL hmulL in
/-- For a tempered source, a fine exponent restricts to an actual exponent
of the outer normalized Jacquet module along every compatible point factor. -/
theorem isNormalizedJacquetExponent_outer_of_fine
    (hπ : IsNormalizedExponentTempered hG π)
    (e : rationalPoints A.toGrp →* rationalPoints B.toGrp)
    (he : ∀ t : rationalPoints A.toGrp,
      (splitComponentPointsMap (mL ≫ pL) b (e t) : rationalPoints L) =
        rationalPoints.map a t)
    (χ : rationalPoints B.toGrp →* ℂˣ)
    (hχ : IsNormalizedJacquetExponent p m n hp hm hn hmul hb π χ) :
    IsNormalizedJacquetExponent q l r hq hl hr hmulQ ha π (χ.comp e) := by
  have := hl.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints L) := leviPointTopology l hl
  have : LocallyCompactSpace (rationalPoints L) :=
    leviPoints_locallyCompactSpace q l hq hl
  have : NonarchimedeanGroup (rationalPoints L) :=
    leviPoints_nonarchimedeanGroup q l hq hl
  let σ := (leviJacquetFunctor q l r hq hr hl hmulQ).obj π
  have hinner := isNormalizedJacquetExponent_nested_of_fine hG
    p m n hp hm hn hmul q l r hq hl hr hmulQ
    pL mL nL hpL hmL hnL hmulL hPQ hM hPL π hb χ hχ
  have hres := normalizedJacquetExponent_restrict pL mL nL hpL hmL hnL hmulL
    hb ha e he σ χ
    (hπ.isAdmissible_leviJacquetFunctor_obj q l r hq hl hr hmulQ ha) hinner
  rw [isNormalizedJacquetExponent_iff_leviEigencharacter]
  exact (generalizedWeightSpace_ne_bot_iff _ (χ.comp e) _ σ.isSmooth).mp
    ((isGroupExponent_iff_isOpen_ker_and ha σ (χ.comp e)).mp hres).2

include hG hPQ hM hPL hpL hmL hnL hmulL in
/-- A genuine morphism of the original split components gives the point
compatibility needed for projection of a fine Jacquet exponent. -/
theorem isNormalizedJacquetExponent_outer_of_fine_scheme
    (hπ : IsNormalizedExponentTempered hG π)
    (e : A ⟶ B) (he : CommGroupScheme.groupHom e ≫ b ≫ mL ≫ pL = a)
    (χ : rationalPoints B.toGrp →* ℂˣ)
    (hχ : IsNormalizedJacquetExponent p m n hp hm hn hmul hb π χ) :
    IsNormalizedJacquetExponent q l r hq hl hr hmulQ ha π
      (χ.comp (rationalPoints.map (CommGroupScheme.groupHom e))) := by
  apply isNormalizedJacquetExponent_outer_of_fine hG
    p m n hp hm hn hmul q l r hq hl hr hmulQ
    pL mL nL hpL hmL hnL hmulL hPQ hM hPL π ha hb hπ
    (rationalPoints.map (CommGroupScheme.groupHom e)) _ χ hχ
  intro t
  have h := congrArg (fun f : A.toGrp ⟶ L => rationalPoints.map f t) he
  change t ≫ (CommGroupScheme.groupHom e ≫ b ≫ mL ≫ pL).hom.hom =
    t ≫ a.hom.hom at h
  change ((t ≫ _ ) ≫ b.hom.hom) ≫ (mL ≫ pL).hom.hom = t ≫ a.hom.hom
  simpa only [Grp.comp_hom_hom, Category.assoc] using h

include hG hPQ hM hPL hpL hmL hnL hmulL in
/-- A fine exponent whose real parameter restricts to zero witnesses a
nonzero unitary part for the supplied outer parabolic. -/
theorem unitaryJacquetPart_ne_bot_of_fine_exponent_restrict_zero
    (hπ : IsNormalizedExponentTempered hG π)
    (e : A ⟶ B) (he : CommGroupScheme.groupHom e ≫ b ≫ mL ≫ pL = a)
    (χ : rationalPoints B.toGrp →* ℂˣ)
    (hχ : IsNormalizedJacquetExponent p m n hp hm hn hmul hb π χ)
    (hzero : rationalCharacterRestrictReal (CommGroupScheme.groupHom e)
      (Plancherel.SplitTorus.normalizedRealPart hb.isCentralSplitTorus.1.1 χ) = 0) :
    unitaryJacquetPart q l r hq hl hr hmulQ ha π ≠ ⊥ := by
  have houter := isNormalizedJacquetExponent_outer_of_fine_scheme hG
    p m n hp hm hn hmul q l r hq hl hr hmulQ
    pL mL nL hpL hmL hnL hmulL hPQ hM hPL π ha hb hπ e he χ hχ
  have : IsAffine B.X.left := hb.isAffine
  have hopen := ((isNormalizedJacquetExponent_iff_isOpen_ker_and
    p m n hp hm hn hmul hb π χ).mp hχ).1
  have hreal : Plancherel.SplitTorus.normalizedRealPart ha.isCentralSplitTorus.1.1
      (χ.comp (rationalPoints.map (CommGroupScheme.groupHom e))) = 0 := by
    rw [Plancherel.SplitTorus.normalizedRealPart_comp_points
      ha.isCentralSplitTorus.1.1 hb.isCentralSplitTorus.1.1 e χ hopen]
    exact hzero
  intro hbot
  exact ((unitaryJacquetPart_eq_bot_iff q l r hq hl hr hmulQ ha π).mp hbot)
    _ houter hreal

end Langlands.Aubert.General.RepresentedParabolic
