import Langlands.Representation.Plancherel.ParabolicPointIntertwiningRegion
import Langlands.Representation.Plancherel.CompactIntertwiningFamilies
import Langlands.Representation.Plancherel.UnramifiedRationalNormalizedModels
import Langlands.Representation.Category.Subquotients

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel

open RationalNormalized

universe u uV

/-- A common detector and actual rational structural data give openness for
positive Levi-normalized induction on the full complex character space. -/
def RationalLeviInductionOpennessStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      [T2Space (rationalPoints G)]
      (A : CommGroupScheme (Spec (CommRingCat.of F)))
      (M P U : GroupScheme (Spec (CommRingCat.of F))) [IsAffine M.X.left]
      (p : P ⟶ G) (l : M ⟶ P) (a : A.toGrp ⟶ M)
      (r : ParabolicRootPresentation p l a) (n : U ⟶ P)
      (_hn : LeviSubgroup.IsGeometricUnipotentRadical n)
      (h : Aubert.General.IsSemidirectDecomposition (ParabolicPoints p)
        (parabolicLeviPointSubgroup p l) (UnipotentPoints (p := p) n))
      (hU : IsClosed (UnipotentPoints (p := p) n : Set (rationalPoints G))),
      Continuous h.projection → CompactSpace (Induction.LeftQuotient (ParabolicPoints p)) →
      ∀ (π : SmoothRep.{0, u, uV} ℂ (parabolicLeviPointSubgroup p l)),
        π.IsAdmissible → Nontrivial π →
        ∀ (K : OpenSubgroup (rationalPoints G)), IsCompact (K : Set (rationalPoints G)) →
          (∀ (χ : unramifiedCharacters (parabolicLeviRationalNormCharacters r))
            (D : SmoothRep.{0, u, max u uV} ℂ (rationalPoints G)),
            D.IsIrreducible →
            SmoothRep.IsSubquotient D
              (UnramifiedLeviInduction h hU (parabolicLeviRationalNormCharacters r) χ π) →
            ∃ v : D, v ∈ fixedVectors D.representation K.toSubgroup ∧ v ≠ 0) →
          IsOpen {χ : unramifiedCharacters (parabolicLeviRationalNormCharacters r) |
            (UnramifiedLeviInduction h hU (parabolicLeviRationalNormCharacters r) χ π).IsIrreducible}

end Langlands.Plancherel
