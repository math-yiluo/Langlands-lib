import Langlands.BruhatTits.SpecialCompact.IwahoriHaarProductStatement
import Langlands.BruhatTits.SpecialCompact.StandardBasisProperty
import Langlands.Representation.Aubert.General.RationalOppositeHaarReciprocityStatement
import Langlands.GroupScheme.Rational.Statement
import Mathlib.MeasureTheory.Group.ModularCharacter

/-! # Reduction of the torus modular character to actual structural inputs -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme Langlands.BruhatTits.SpecialCompact
open Langlands.AlgebraicGeometry.PointTopology

/-- The empty-face Iwahori basis, generic centralizer identification and
opposite Haar reciprocity make the ambient modular character trivial on the
actual torus image. The structural inputs remain explicit. -/
def RationalTorusModularReductionStatement : Prop :=
  IwahoriHaarProductStatement.{u} →
  RationalOppositeHaarReciprocityStatement.{u} →
  GenericCentralizerStatement.{u} →
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i),
    haveI := hG.isAffineHom
    haveI := hi.isSplitSubtorus.mono
    letI : TopologicalSpace (RationalPoint k G.X) := pointTopology
    ∀ [LocallyCompactSpace (RationalPoint k G.X)]
      [NonarchimedeanGroup (RationalPoint k G.X)] [T2Space (RationalPoint k G.X)]
      (ν : cocharacterLattice T) (_hν : IsGenericCocharacter i ν)
      (_hStandard : StandardCocharacterStatement.{u})
      (K0 : Subgroup (RationalPoint k G.X)),
      SimultaneousStandardBasisAt i ν K0 →
      ∀ t ∈ torusPoints i, MeasureTheory.Measure.modularCharacter t = 1

end Langlands.Aubert.General.RationalPointFamily
