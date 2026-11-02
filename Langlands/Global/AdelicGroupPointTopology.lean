import Langlands.Global.AdelicGroupPoints
import Langlands.GroupScheme.AffinePointFiniteCoordinates
import Langlands.GroupScheme.GeneralLinearPointTopology
import Langlands.Global.AdelesLocallyCompactProof

/-! # Topology on actual adelic group-scheme points -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain
open scoped CategoryTheory.MonObj RestrictedProduct

namespace Langlands.Global

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))

namespace FiniteAdelicGroupPoints

/-- The global-function evaluation topology on the actual finite adelic points. -/
instance topologicalSpace : TopologicalSpace (FiniteAdelicGroupPoints F G) :=
  G.affinePointsTopologicalSpace (CommAlgCat.of F (FiniteAdeleRing (𝓞 F) F))

variable [IsAffine G.X.left]

/-- The inherited finite adelic point group has continuous group operations. -/
instance isTopologicalGroup : IsTopologicalGroup (FiniteAdelicGroupPoints F G) :=
  G.affinePointsIsTopologicalGroup (CommAlgCat.of F (FiniteAdeleRing (𝓞 F) F))

/-- Actual finite adelic points of an affine group scheme are Hausdorff. -/
instance t2Space : T2Space (FiniteAdelicGroupPoints F G) := by
  let : T2Space (FiniteAdeleRing (𝓞 F) F) :=
    inferInstanceAs (T2Space (Πʳ v : FinitePlace F,
      [FiniteCompletion F v, v.adicCompletionIntegers F]))
  exact G.affinePointsT2Space (CommAlgCat.of F (FiniteAdeleRing (𝓞 F) F))

/-- Finite-type affine group schemes have locally compact finite adelic points. -/
instance locallyCompactSpace [LocallyOfFiniteType G.X.hom] :
    LocallyCompactSpace (FiniteAdelicGroupPoints F G) := by
  let : T2Space (FiniteAdeleRing (𝓞 F) F) :=
    inferInstanceAs (T2Space (Πʳ v : FinitePlace F,
      [FiniteCompletion F v, v.adicCompletionIntegers F]))
  let : LocallyCompactSpace (FiniteAdeleRing (𝓞 F) F) :=
    finiteAdeles_locallyCompactSpace F
  exact G.affinePointsLocallyCompactSpace (CommAlgCat.of F (FiniteAdeleRing (𝓞 F) F))

end FiniteAdelicGroupPoints

namespace InfiniteAdelicGroupPoints

/-- The global-function evaluation topology on the actual archimedean points. -/
instance topologicalSpace : TopologicalSpace (InfiniteAdelicGroupPoints F G) :=
  G.affinePointsTopologicalSpace (CommAlgCat.of F (InfiniteAdeleRing F))

variable [IsAffine G.X.left]

/-- The inherited archimedean point group has continuous group operations. -/
instance isTopologicalGroup : IsTopologicalGroup (InfiniteAdelicGroupPoints F G) :=
  G.affinePointsIsTopologicalGroup (CommAlgCat.of F (InfiniteAdeleRing F))

/-- Actual archimedean points of an affine group scheme are Hausdorff. -/
instance t2Space : T2Space (InfiniteAdelicGroupPoints F G) := by
  let : T2Space (InfiniteAdeleRing F) :=
    inferInstanceAs (T2Space ((v : NumberField.InfinitePlace F) → v.Completion))
  exact G.affinePointsT2Space (CommAlgCat.of F (InfiniteAdeleRing F))

/-- Finite-type affine group schemes have locally compact archimedean points. -/
instance locallyCompactSpace [LocallyOfFiniteType G.X.hom] :
    LocallyCompactSpace (InfiniteAdelicGroupPoints F G) := by
  let : T2Space (InfiniteAdeleRing F) :=
    inferInstanceAs (T2Space ((v : NumberField.InfinitePlace F) → v.Completion))
  let : LocallyCompactSpace (InfiniteAdeleRing F) :=
    inferInstanceAs (LocallyCompactSpace ((v : NumberField.InfinitePlace F) → v.Completion))
  exact G.affinePointsLocallyCompactSpace (CommAlgCat.of F (InfiniteAdeleRing F))

end InfiniteAdelicGroupPoints

namespace AdelicGroupPoints

/-- The global-function evaluation topology on the actual full adelic points. -/
instance topologicalSpace : TopologicalSpace (AdelicGroupPoints F G) :=
  G.affinePointsTopologicalSpace (CommAlgCat.of F (AdeleRing (𝓞 F) F))

variable [IsAffine G.X.left]

/-- The inherited full adelic point group has continuous group operations. -/
instance isTopologicalGroup : IsTopologicalGroup (AdelicGroupPoints F G) :=
  G.affinePointsIsTopologicalGroup (CommAlgCat.of F (AdeleRing (𝓞 F) F))

/-- Actual full adelic points of an affine group scheme are Hausdorff. -/
instance t2Space : T2Space (AdelicGroupPoints F G) := by
  let : T2Space (InfiniteAdeleRing F) :=
    inferInstanceAs (T2Space ((v : NumberField.InfinitePlace F) → v.Completion))
  let : T2Space (FiniteAdeleRing (𝓞 F) F) :=
    inferInstanceAs (T2Space (Πʳ v : FinitePlace F,
      [FiniteCompletion F v, v.adicCompletionIntegers F]))
  let : T2Space (AdeleRing (𝓞 F) F) :=
    inferInstanceAs (T2Space (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))
  exact G.affinePointsT2Space (CommAlgCat.of F (AdeleRing (𝓞 F) F))

/-- Finite-type affine group schemes have locally compact full adelic points. -/
instance locallyCompactSpace [LocallyOfFiniteType G.X.hom] :
    LocallyCompactSpace (AdelicGroupPoints F G) := by
  let : T2Space (InfiniteAdeleRing F) :=
    inferInstanceAs (T2Space ((v : NumberField.InfinitePlace F) → v.Completion))
  let : T2Space (FiniteAdeleRing (𝓞 F) F) :=
    inferInstanceAs (T2Space (Πʳ v : FinitePlace F,
      [FiniteCompletion F v, v.adicCompletionIntegers F]))
  let : T2Space (AdeleRing (𝓞 F) F) :=
    inferInstanceAs (T2Space (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))
  let : LocallyCompactSpace (AdeleRing (𝓞 F) F) := adeles_locallyCompactSpace F
  exact G.affinePointsLocallyCompactSpace (CommAlgCat.of F (AdeleRing (𝓞 F) F))

end AdelicGroupPoints

namespace GeneralLinearGroupPoints

variable (n : ℕ)

/-- The existing full adelic general-linear comparison is a multiplicative homeomorphism. -/
def adelicHomeomorph :
    AdelicGroupPoints F (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F))
      ≃ₜ* AdelicGL F n :=
  GroupScheme.GeneralLinear.affinePointsHomeomorph (Fin n) (CommRingCat.of F)
    (CommAlgCat.of F (AdeleRing (𝓞 F) F))

/-- The finite adelic comparison retains the existing multiplicative equivalence. -/
def finiteHomeomorph :
    FiniteAdelicGroupPoints F
      (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F))
      ≃ₜ* FiniteAdelicGL F n :=
  GroupScheme.GeneralLinear.affinePointsHomeomorph (Fin n) (CommRingCat.of F)
    (CommAlgCat.of F (FiniteAdeleRing (𝓞 F) F))

/-- The archimedean comparison retains the existing multiplicative equivalence. -/
def infiniteHomeomorph :
    InfiniteAdelicGroupPoints F
      (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F))
      ≃ₜ* InfiniteAdelicGL F n :=
  GroupScheme.GeneralLinear.affinePointsHomeomorph (Fin n) (CommRingCat.of F)
    (CommAlgCat.of F (InfiniteAdeleRing F))

@[simp] theorem adelicHomeomorph_toMulEquiv :
    (adelicHomeomorph F n).toMulEquiv = adelicEquiv F n := rfl

@[simp] theorem finiteHomeomorph_toMulEquiv :
    (finiteHomeomorph F n).toMulEquiv = finiteEquiv F n := rfl

omit [NumberField F] in
@[simp] theorem infiniteHomeomorph_toMulEquiv :
    (infiniteHomeomorph F n).toMulEquiv = infiniteEquiv F n := rfl

/-- The topological comparison preserves the actual principal rational-point map. -/
theorem adelicHomeomorph_rational
    (x : RationalGroupPoints F
      (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F))) :
    adelicHomeomorph F n (AdelicGroupPoints.rational F
      (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)) x) =
      AdelicGL.rational F n (rationalEquiv F n x) :=
  adelicEquiv_rational F n x

end GeneralLinearGroupPoints

end Langlands.Global
