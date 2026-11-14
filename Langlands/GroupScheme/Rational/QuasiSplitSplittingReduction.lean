import Langlands.GroupScheme.Rational.RationalRestrictionSplitting
import Langlands.GroupScheme.Rational.RelativeRootSystemProof
import Langlands.GroupScheme.Rational.RelativeRootSystemIrreducibleStatement
import Langlands.GroupScheme.Rational.MaximalTorusFiniteType
import Langlands.GroupScheme.Reductive.SplitRankZeroIsomorphism
import Langlands.GroupScheme.SimplyConnected.AlmostSimpleFactorDescentProperties
import Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof
import Langlands.GroupScheme.Torus.MaximalSplitComparison

/-! # Reducing quasi-split splitting to actual relative-root irreducibility -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj
open Langlands.LinearAlgebra.RationalSpan

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

section AlgebraicExtension

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  [Algebra.IsAlgebraic k K]
  {G : GroupScheme (Spec (CommRingCat.of k))}

/-- Absolute almost-simplicity persists along algebraic field extensions. -/
theorem IsAbsolutelyAlmostSimple.baseChange_of_algebraicExtension
    (hG : IsAbsolutelyAlmostSimple G) :
    IsAbsolutelyAlmostSimple
      ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) := by
  let b := algebraBaseMap k K
  let r := Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure K)))
  let e := IsAlgClosure.equiv k (AlgebraicClosure K) (AlgebraicClosure k)
  let d := Spec.map (CommRingCat.ofHom e.symm.toRingHom)
  have hr : toAlgebraicClosure K ≫ b = r := by
    dsimp [b, r, toAlgebraicClosure, algebraBaseMap]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← IsScalarTower.algebraMap_eq k K (AlgebraicClosure K)]
  have hd : d ≫ toAlgebraicClosure k = r := by
    dsimp [d, r, toAlgebraicClosure]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun f => Spec.map (CommRingCat.ofHom f))
      (RingHom.ext fun x => e.symm.commutes x)
  let : IsIso d := isIso_SpecMap_iff.mpr e.symm.bijective
  have hD := hG.2.baseChange_of_isIso d
  have hR : IsAlmostSimple ((GroupScheme.baseChange r).obj G) :=
    hD.of_iso (Descent.pullbackComparison (toAlgebraicClosure k) d r hd G).symm
  have hbar : IsAlmostSimple
      ((GroupScheme.baseChange (toAlgebraicClosure K)).obj
        ((GroupScheme.baseChange b).obj G)) :=
    hR.of_iso (Descent.pullbackComparison b (toAlgebraicClosure K) r hr G)
  exact ⟨IsAlmostSimple.of_fieldExtension (K := AlgebraicClosure K) hbar, hbar⟩

end AlgebraicExtension

section SplitMaximalRoots

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom]

/-- A split maximal torus of an almost-simple group has at least one actual root. -/
theorem IsAlmostSimple.relativeRoots_nonempty_of_split_maximalTorus
    (hG : IsAlmostSimple G) (j : T.toGrp ⟶ G)
    (hT : IsSplitTorus T.toGrp) (hj : IsMaximalTorus j) :
    (relativeRoots j).Nonempty := by
  by_contra hne
  have hempty : roots j = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
  let : IsIso j := hG.isSemisimple.isConnectedReductive.isIso_of_roots_eq_empty hT hj hempty
  apply hG.noncommutative
  intro Z x y
  apply (commute_iff_eq x y).mpr
  apply (cancel_mono (inv j).hom.hom).mp
  simp only [MonObj.mul_comp]
  exact mul_comm _ _

end SplitMaximalRoots

namespace IsQuasiSplit

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
  [hfin : FiniteDimensional k L] [hgal : IsGalois k L]
  {S T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (hG : IsQuasiSplit G) (habs : IsAbsolutelyAlmostSimple G)
  (a : S.toGrp ⟶ G) (j : T.toGrp ⟶ G) (f : S ⟶ T)
  (ha : IsMaximalSplitTorus a) (hj : IsMaximalTorus j)
  (hf : CommGroupScheme.groupHom f ≫ j = a)
  (hTL : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T).toGrp)

local notation "b" => algebraBaseMap k L
local notation "T_L" => Functor.obj (CommGroupScheme.baseChange b) T
local notation "G_L" => Functor.obj (GroupScheme.baseChange b) G
local notation "j_L" => CategoryTheory.Functor.map (GroupScheme.baseChange b) j

include hG habs a j f ha hj hf hTL hfin hgal

omit hfin in
/-- The published actual-root irreducibility statement supplies the only
unresolved source-system premise in rational-restriction injectivity. -/
theorem rationalRootRestriction_injective_of_relativeRootSystemIrreducible
    (hirr : RelativeRootSystemIrreducibleStatement.{u})
    (hroot : HasReducedSimplyLacedRelativeRootSystem a) :
    Function.Injective (hG.rationalRootRestriction (L := L) a j f ha hj hf hTL) := by
  let : Smooth G.X.hom := habs.1.isSemisimple.isConnectedReductive.smooth
  have hGL : IsAlmostSimple G_L :=
    (habs.baseChange_of_algebraicExtension (K := L)).1
  let : IsAffineHom (G_L).X.hom := hGL.isSemisimple.isConnectedReductive.isAffineHom
  have hjL : IsMaximalTorus (T := T_L) (G := G_L) j_L :=
    (maximalTorusBaseChange k L G T j hj.1 hj.2.1).mp hj
  have hmax := hjL.isMaximalSplitTorus hTL
  obtain ⟨J, _, Q, hQsys, _, hQeval, hQ, _, _⟩ :=
    relativeRootSystem L G_L hGL.isSemisimple.isConnectedReductive T_L j_L hmax
  let := hQsys
  have hne := hGL.relativeRoots_nonempty_of_split_maximalTorus j_L hTL hjL
  let := hirr L G_L hGL T_L j_L hmax hne J Q hQeval hQ
  obtain ⟨I, _, P, hPsys, _, _, _, hP, hs⟩ := hroot
  let := hPsys
  exact hG.rationalRootRestriction_injective_of_rootSystems
    (L := L) a j f ha hj hf hTL P Q hP hQ hs

/-- Along the supplied factor, the original maximal split torus is
isomorphic to its containing maximal torus, conditional only on the
published relative-root irreducibility statement. -/
def torusFactorIsoOfRelativeRootSystemIrreducible
    (hirr : RelativeRootSystemIrreducibleStatement.{u})
    (hroot : HasReducedSimplyLacedRelativeRootSystem a) :
    S.toGrp ≅ T.toGrp :=
  hG.torusFactorIsoOfRationalRootRestriction habs.1.isSemisimple a j f ha hj hf hTL
    (hG.rationalRootRestriction_injective_of_relativeRootSystemIrreducible
      habs a j f ha hj hf hTL hirr hroot)

@[simp]
theorem torusFactorIsoOfRelativeRootSystemIrreducible_hom
    (hirr : RelativeRootSystemIrreducibleStatement.{u})
    (hroot : HasReducedSimplyLacedRelativeRootSystem a) :
    (hG.torusFactorIsoOfRelativeRootSystemIrreducible
      habs a j f ha hj hf hTL hirr hroot).hom = CommGroupScheme.groupHom f := rfl

/-- Constructing the source system removes every extra root-system datum
from the split-maximality conclusion. -/
theorem isMaximalTorus_of_relativeRootSystemIrreducible
    (hirr : RelativeRootSystemIrreducibleStatement.{u})
    (hroot : HasReducedSimplyLacedRelativeRootSystem a) :
    IsMaximalTorus a :=
  hG.isMaximalTorus_of_rationalRootRestriction_injective habs.1.isSemisimple
    a j f ha hj hf hTL
    (hG.rationalRootRestriction_injective_of_relativeRootSystemIrreducible
      habs a j f ha hj hf hTL hirr hroot)

end IsQuasiSplit

/-- The quasi-split simply-laced splitting target follows from the published
relative-root irreducibility target. The containing torus, splitting field
and actual source root system are all constructed in the proof. -/
theorem quasiSplitSimplyLacedSplitting_of_relativeRootSystemIrreducible
    (hirr : RelativeRootSystemIrreducibleStatement.{u}) :
    QuasiSplitSimplyLacedSplittingStatement.{u} := by
  intro k _ G hG habs S a ha hroot
  let : IsAffineHom G.X.hom := hG.isConnectedReductive.isAffineHom
  let : Smooth G.X.hom := hG.isConnectedReductive.smooth
  obtain ⟨T, j, hj, f, hf⟩ :=
    exists_maximalTorus_extension_of_finiteType G a ha.1.1.isTorus ha.1.2
  obtain ⟨L, hL, hA, hfin, hgal, hTL⟩ := torusFiniteGaloisSplitting k T.toGrp hj.1
  let := hL
  let := hA
  let := hfin
  let := hgal
  exact hG.isMaximalTorus_of_relativeRootSystemIrreducible
    habs a j (Additive.ofMul f) ha hj hf hTL hirr hroot

end Langlands.GroupScheme
