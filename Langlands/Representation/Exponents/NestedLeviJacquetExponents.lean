import Langlands.Representation.Exponents.LeviParabolicTransitivityProof
import Langlands.Representation.Exponents.LeviParabolicExtensionProof
import Langlands.Representation.Exponents.ArbitraryParabolicUnitaryJacquetPart
import Langlands.Representation.Exponents.LeviRadicalCompactSubgroups
import Langlands.Representation.Aubert.General.DirectedUnions
import Langlands.Representation.Filtration.GeneralizedEigencharacterProof

/-! # Actual nested Jacquet maps and exponent inheritance -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance nestedExponentAmbientTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)]

section ActualLevi

variable {P M N : GroupScheme (Spec (CommRingCat.of k))}
  (p : P ⟶ G) (m : M ⟶ P) (n : N ⟶ P)
  (hp : IsParabolicSubgroup p) (hm : IsRationalLeviSubgroup m)
  (hn : LeviSubgroup.IsGeometricUnipotentRadical n)
  (hmul : IsIso (subgroupMultiplication m n))
  {A : CommGroupScheme (Spec (CommRingCat.of k))} {a : A.toGrp ⟶ M}

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
/-- Normalized exponents may be tested on the actual Levi-point module,
with the original split-component point map. -/
theorem isNormalizedJacquetExponent_iff_leviEigencharacter
    (ha : IsSplitComponent a) (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))
    (χ : rationalPoints A.toGrp →* ℂˣ) :
    letI := leviPointTopology m hm
    IsNormalizedJacquetExponent p m n hp hm hn hmul ha π χ ↔
      IsGeneralizedEigencharacter
        (((leviJacquetFunctor p m n hp hn hm hmul).obj π).representation.comp
          (rationalPoints.map a)) χ := by
  rw [isNormalizedJacquetExponent_iff]
  rfl

/-- The actual normalized Jacquet functor on Levi points preserves injectivity.
The radical's compact-subgroup exhaustion follows from the original local-field
and geometric-radical data. -/
theorem leviJacquetFunctor_map_injective
    {π τ : SmoothRep.{0, u, v} ℂ (rationalPoints G)}
    (f : π ⟶ τ) (hf : Function.Injective (SmoothRep.hom f)) :
    letI := leviPointTopology m hm
    Function.Injective
      (SmoothRep.hom ((leviJacquetFunctor p m n hp hn hm hmul).map f)) :=
  normalizedJacquetFunctor_map_injective (pointImage (n ≫ p)) (pointImage (m ≫ p))
    (isClosed_pointImage_comp p n hp.isClosedSubgroup hn.1.isClosedSubgroup)
    (pointImage_le_normalizer p m n hn)
    (isLimitOfCompactSubgroups_pointImage_radical p n hp.isClosedSubgroup hn.1) f hf

end ActualLevi

section Nested

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

variable {A : CommGroupScheme (Spec (CommRingCat.of k))} {a : A.toGrp ⟶ L}
  (ha : IsSplitComponent a) (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))

/-- Apply inner normalized Jacquet restriction to the literal inclusion of the
outer unitary part, then use actual normalized transitivity to land in the
original fine ambient Jacquet module. -/
def nestedLeviUnitaryJacquetMap :
    haveI := hl.isConnectedReductive.isAffineHom
    letI : TopologicalSpace (rationalPoints L) := leviPointTopology l hl
    haveI : LocallyCompactSpace (rationalPoints L) :=
      leviPoints_locallyCompactSpace q l hq hl
    haveI : NonarchimedeanGroup (rationalPoints L) :=
      leviPoints_nonarchimedeanGroup q l hq hl
    letI : TopologicalSpace (rationalPoints M) := leviPointTopology m hm
    (leviJacquetFunctor pL mL nL hpL hnL hmL hmulL).obj
        (leviUnitaryJacquetModule q l r hq hl hr hmulQ ha π) ⟶
      (leviJacquetFunctor p m n hp hn hm hmul).obj π := by
  haveI := hl.isConnectedReductive.isAffineHom
  letI : TopologicalSpace (rationalPoints L) := leviPointTopology l hl
  haveI : LocallyCompactSpace (rationalPoints L) :=
    leviPoints_locallyCompactSpace q l hq hl
  haveI : NonarchimedeanGroup (rationalPoints L) :=
    leviPoints_nonarchimedeanGroup q l hq hl
  letI : TopologicalSpace (rationalPoints M) := leviPointTopology m hm
  let e := Classical.choice
    (leviParabolicTransitivity k G hG P M N Q L U PL NL
      p m n hp hm hn hmul q l r hq hl hr hmulQ
      pL mL nL hpL hmL hnL hmulL hPQ hM hPL).2
  exact (leviJacquetFunctor pL mL nL hpL hnL hmL hmulL).map
    (leviUnitaryJacquetModuleι q l r hq hl hr hmulQ ha π) ≫ e.inv.app π

/-- The inner Jacquet module of the outer unitary part embeds in the fine
ambient Jacquet module. No temperedness or presentation premise is required. -/
theorem nestedLeviUnitaryJacquetMap_injective :
    haveI := hl.isConnectedReductive.isAffineHom
    letI : TopologicalSpace (rationalPoints L) := leviPointTopology l hl
    haveI : LocallyCompactSpace (rationalPoints L) :=
      leviPoints_locallyCompactSpace q l hq hl
    haveI : NonarchimedeanGroup (rationalPoints L) :=
      leviPoints_nonarchimedeanGroup q l hq hl
    letI : TopologicalSpace (rationalPoints M) := leviPointTopology m hm
    Function.Injective (SmoothRep.hom
      (nestedLeviUnitaryJacquetMap hG p m n hp hm hn hmul q l r hq hl hr hmulQ
        pL mL nL hpL hmL hnL hmulL hPQ hM hPL ha π)) := by
  have := hl.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints L) := leviPointTopology l hl
  have : LocallyCompactSpace (rationalPoints L) :=
    leviPoints_locallyCompactSpace q l hq hl
  have : NonarchimedeanGroup (rationalPoints L) :=
    leviPoints_nonarchimedeanGroup q l hq hl
  let : TopologicalSpace (rationalPoints M) := leviPointTopology m hm
  let e := Classical.choice
    (leviParabolicTransitivity k G hG P M N Q L U PL NL
      p m n hp hm hn hmul q l r hq hl hr hmulQ
      pL mL nL hpL hmL hnL hmulL hPQ hM hPL).2
  exact (SmoothRep.equivOfIso (e.app π).symm).injective.comp
    (leviJacquetFunctor_map_injective pL mL nL hpL hmL hnL hmulL
      (leviUnitaryJacquetModuleι q l r hq hl hr hmulQ ha π)
      (leviUnitaryJacquetModuleι_injective q l r hq hl hr hmulQ ha π))

include hG hPQ hM hPL in
/-- Every exponent of the inner Jacquet module of the outer unitary part is
an exponent of the fine ambient Jacquet module, on the exact same split component
of the original common Levi. -/
theorem isNormalizedJacquetExponent_of_nestedUnitary
    {B : CommGroupScheme (Spec (CommRingCat.of k))} {b : B.toGrp ⟶ M}
    (hb : IsSplitComponent b) (χ : rationalPoints B.toGrp →* ℂˣ) :
    haveI := hl.isConnectedReductive.isAffineHom
    letI : TopologicalSpace (rationalPoints L) := leviPointTopology l hl
    haveI : LocallyCompactSpace (rationalPoints L) :=
      leviPoints_locallyCompactSpace q l hq hl
    haveI : NonarchimedeanGroup (rationalPoints L) :=
      leviPoints_nonarchimedeanGroup q l hq hl
    letI : TopologicalSpace (rationalPoints M) := leviPointTopology m hm
    IsNormalizedJacquetExponent pL mL nL hpL hmL hnL hmulL hb
      (leviUnitaryJacquetModule q l r hq hl hr hmulQ ha π) χ →
    IsNormalizedJacquetExponent p m n hp hm hn hmul hb π χ := by
  have := hl.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints L) := leviPointTopology l hl
  have : LocallyCompactSpace (rationalPoints L) :=
    leviPoints_locallyCompactSpace q l hq hl
  have : NonarchimedeanGroup (rationalPoints L) :=
    leviPoints_nonarchimedeanGroup q l hq hl
  let : TopologicalSpace (rationalPoints M) := leviPointTopology m hm
  intro hχ
  rw [isNormalizedJacquetExponent_iff_leviEigencharacter] at hχ ⊢
  let f := SmoothRep.hom
    (nestedLeviUnitaryJacquetMap hG p m n hp hm hn hmul q l r hq hl hr hmulQ
      pL mL nL hpL hmL hnL hmulL hPQ hM hPL ha π)
  let fB : Representation.IntertwiningMap
      (((leviJacquetFunctor pL mL nL hpL hnL hmL hmulL).obj
        (leviUnitaryJacquetModule q l r hq hl hr hmulQ ha π)).representation.comp
          (rationalPoints.map b))
      (((leviJacquetFunctor p m n hp hn hm hmul).obj π).representation.comp
        (rationalPoints.map b)) :=
    { toLinearMap := f.toLinearMap
      isIntertwining' t := f.isIntertwining' (rationalPoints.map b t) }
  obtain ⟨d, hd⟩ := hχ
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).mp hd
  apply isGeneralizedEigencharacter_of_map_ne_zero fB χ d hx
  intro h
  change f x = 0 at h
  apply hx0
  exact (nestedLeviUnitaryJacquetMap_injective hG p m n hp hm hn hmul
    q l r hq hl hr hmulQ pL mL nL hpL hmL hnL hmulL hPQ hM hPL ha π)
      (by simpa only [map_zero] using h)

end Nested

section ArbitraryInner

variable {Q L U PL M NL : GroupScheme (Spec (CommRingCat.of k))}
  (hG : IsConnectedReductive G)
  (q : Q ⟶ G) (l : L ⟶ Q) (r : U ⟶ Q)
  (hq : IsParabolicSubgroup q) (hl : IsRationalLeviSubgroup l)
  (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
  (hmulQ : IsIso (subgroupMultiplication l r))
  (pL : PL ⟶ L) (mL : M ⟶ PL) (nL : NL ⟶ PL)
  (hpL : IsParabolicSubgroup pL) (hmL : IsRationalLeviSubgroup mL)
  (hnL : LeviSubgroup.IsGeometricUnipotentRadical nL)
  (hmulL : IsIso (subgroupMultiplication mL nL))
  {A : CommGroupScheme (Spec (CommRingCat.of k))} {a : A.toGrp ⟶ L}
  (ha : IsSplitComponent a) (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))

include hG in
/-- For every actual inner parabolic of the outer Levi, each exponent of its
Jacquet module on the outer unitary part occurs in an actual ambient Jacquet
module with the same original inner Levi and split component. -/
theorem exists_ambient_isNormalizedJacquetExponent_of_unitary
    {B : CommGroupScheme (Spec (CommRingCat.of k))} {b : B.toGrp ⟶ M}
    (hb : IsSplitComponent b) (χ : rationalPoints B.toGrp →* ℂˣ) :
    haveI := hl.isConnectedReductive.isAffineHom
    letI : TopologicalSpace (rationalPoints L) := leviPointTopology l hl
    haveI : LocallyCompactSpace (rationalPoints L) :=
      leviPoints_locallyCompactSpace q l hq hl
    haveI : NonarchimedeanGroup (rationalPoints L) :=
      leviPoints_nonarchimedeanGroup q l hq hl
    IsNormalizedJacquetExponent pL mL nL hpL hmL hnL hmulL hb
      (leviUnitaryJacquetModule q l r hq hl hr hmulQ ha π) χ →
    ∃ (P N : GroupScheme (Spec (CommRingCat.of k)))
      (p : P ⟶ G) (m : M ⟶ P) (n : N ⟶ P)
      (hp : IsParabolicSubgroup p) (hm : IsRationalLeviSubgroup m)
      (hn : LeviSubgroup.IsGeometricUnipotentRadical n)
      (hmul : IsIso (subgroupMultiplication m n)),
      pointImage p ≤ pointImage q ∧
      mL ≫ pL ≫ l ≫ q = m ≫ p ∧
      pointImage (pL ≫ l ≫ q) = pointImage (l ≫ q) ⊓ pointImage p ∧
      IsNormalizedJacquetExponent p m n hp hm hn hmul hb π χ := by
  have := hl.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints L) := leviPointTopology l hl
  have : LocallyCompactSpace (rationalPoints L) :=
    leviPoints_locallyCompactSpace q l hq hl
  have : NonarchimedeanGroup (rationalPoints L) :=
    leviPoints_nonarchimedeanGroup q l hq hl
  intro hχ
  obtain ⟨P, N, p, m, n, hp, hm, hn, hmul, hM, hPQ, hPL⟩ :=
    leviParabolicExtension k G hG Q L U q l r hq hl hr hmulQ
      PL M NL pL mL nL hpL hmL hnL hmulL
  have hPQ' : pointImage p ≤ pointImage q := hPQ _
  have hPL' : pointImage (pL ≫ l ≫ q) = pointImage (l ≫ q) ⊓ pointImage p :=
    congrArg (fun F : SubgroupFunctor G =>
      F.carrier (Over.mk (𝟙 (Spec (CommRingCat.of k))))) hPL
  exact ⟨P, N, p, m, n, hp, hm, hn, hmul, hPQ', hM.symm, hPL',
    isNormalizedJacquetExponent_of_nestedUnitary hG p m n hp hm hn hmul
      q l r hq hl hr hmulQ pL mL nL hpL hmL hnL hmulL hPQ' hM.symm hPL'
      ha π hb χ hχ⟩

end ArbitraryInner

end Langlands.Aubert.General.RepresentedParabolic
