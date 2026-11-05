import Langlands.Representation.Aubert.General.RationalCuspidalExtractionGeometry
import Langlands.Representation.Aubert.General.RationalProperTargetGeometricTerm
import Langlands.Representation.Aubert.General.CuspidalJacquetFiltrationExtraction
import Langlands.Representation.Aubert.General.SharpSupportRetentionReduction

/-! # Cuspidal extraction from supplied actual rational geometric filtrations -/

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false

universe u v

open Classical CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme SmoothRep Group.RelativeWeylIndexing
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]
  (ν : cocharacterLattice T) [Fintype (SimpleRoot i ν)]
  (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)
  {C : CoxeterMatrix (SimpleRoot i ν)}
  (cs : ActualCoxeterSystem (torusPoints i) C)
  [TopologicalSpace k]

local instance rationalCuspidalGeometricExtractionPointTopology :
    TopologicalSpace (RationalPoint k G.X) := pointTopology

variable [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)]
  (hInter : StandardLeviIntersectionStatement.{u})
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)
  (hM : ∀ A, IsClosed (levi i ν A : Set (RationalPoint k G.X)))
  (hU : ∀ A, IsClosed (unipotent i ν A : Set (RationalPoint k G.X)))

/-- The actual geometric term on a cuspidal datum either excludes every
irreducible inside-Levi cuspidal factor or is the associated conjugate along
the supplied normalizer lift. This predicate supplies no filtration. -/
def PointGeometricCuspidalGradeDichotomy : Prop :=
  ∀ (I J : Finset (SimpleRoot i ν)) (w : Weyl i), IsMinimal cs J I w →
    ∀ (n : Group.RelativeWeyl.normalizer (torusPoints i)), QuotientGroup.mk n = w →
      ∀ (hs : GeometricSourceDecomposition
          (parabolic i ν) (levi i ν) (unipotent i ν) J I n)
        (ht : GeometricTargetDecomposition
          (parabolic i ν) (levi i ν) (unipotent i ν) J I n)
        (σ : SmoothRep.{0, u, max (u + 1) v} ℂ (levi i ν I)),
        IsLeviCuspidal (parabolic i ν) (levi i ν) (unipotent i ν) hU I (hM I)
          (isSemidirectDecomposition_in_levi i ν hInter hG hi hν I) σ →
        (∀ τ : SmoothRep.{0, u, max (u + 1) v} ℂ (levi i ν J),
          τ.IsIrreducible →
          IsLeviCuspidal (parabolic i ν) (levi i ν) (unipotent i ν) hU J (hM J)
            (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J) τ →
          ¬ SmoothRep.IsSubquotient τ
            ((geometricTermFunctor.{u, u, max (u + 1) v}
              (parabolic i ν) (levi i ν) (unipotent i ν) hM hU J I n hs ht).obj σ)) ∨
        ∃ hConj : ∀ x : RationalPoint k G.X,
            x ∈ levi i ν J ↔
              (n : RationalPoint k G.X)⁻¹ * x * (n : RationalPoint k G.X) ∈ levi i ν I,
          rootAssociation i ν hN hZ I J (n : RationalPoint k G.X) ∧
          Nonempty
            ((geometricTermFunctor.{u, u, max (u + 1) v}
              (parabolic i ν) (levi i ν) (unipotent i ν) hM hU J I n hs ht).obj σ ≅
              (conjugationFunctor (n : RationalPoint k G.X) hConj).obj σ)

/-- Source vanishing, proper-target exclusion, and full-intersection geometry
give the actual grade dichotomy. Proper-target exclusion remains an input. -/
theorem pointGeometricCuspidalGradeDichotomy_of_geometry_exclusion
    (hGeom : PointCuspidalExtractionGeometry.{u, v}
      i ν hN hZ cs hG hi hν hInter hM hU)
    (hExclude : PointProperTargetGeometricTermExclusion.{u, v}
      i ν cs hInter hG hi hν hM hU) :
    PointGeometricCuspidalGradeDichotomy.{u, v}
      i ν hN hZ cs hInter hG hi hν hM hU := by
  intro I J w hw n hn hs ht σ hcσ
  by_cases hS : intersectionSubset cs J I w = I
  · by_cases hT : intersectionSubset cs I J w⁻¹ = J
    · exact Or.inr (hGeom.2.2.2 I J w hw n hn hs ht hS hT σ)
    · exact Or.inl (hExclude I J w hw n hn hs ht hT σ)
  · left
    intro τ hτ _hcτ
    let _ := hGeom.2.2.1 J I w hw n hn hs ht σ
      ((isCorollaryLeviCuspidal_iff_isLeviCuspidal.{u, u, max (u + 1) v}
        I (hM I) (isSemidirectDecomposition_in_levi i ν hInter hG hi hν I) σ).mpr hcσ) hS
    exact SmoothRep.not_isSubquotient_of_subsingleton hτ

omit [Fintype (SimpleRoot i ν)] in
/-- Transport the actual geometric-term dichotomy through actual grade
isomorphisms. All filtration and grade witnesses remain supplied inputs. -/
theorem pointCuspidalJacquetGradedPieces_of_geometricTerms
    (hDichotomy : PointGeometricCuspidalGradeDichotomy.{u, v}
      i ν hN hZ cs hInter hG hi hν hM hU)
    (I J : Finset (SimpleRoot i ν))
    (σ : SmoothRep.{0, u, max (u + 1) v} ℂ (levi i ν I))
    (hcσ : IsLeviCuspidal (parabolic i ν) (levi i ν) (unipotent i ν) hU I (hM I)
      (isSemidirectDecomposition_in_levi i ν hInter hG hi hν I) σ)
    {A : SmoothRep.{0, u, max (u + 1) v} ℂ (levi i ν J)}
    {r : ℕ} (s : ObjectRepFiltration A.obj r)
    (hgrades : ∀ q : Fin r,
      ∃ (w : Weyl i) (_hw : IsMinimal cs J I w)
        (n : Group.RelativeWeyl.normalizer (torusPoints i)) (_hn : QuotientGroup.mk n = w)
        (hs : GeometricSourceDecomposition
          (parabolic i ν) (levi i ν) (unipotent i ν) J I n)
        (ht : GeometricTargetDecomposition
          (parabolic i ν) (levi i ν) (unipotent i ν) J I n),
        Nonempty
          (s.smoothGradedObject q ≅
            (geometricTermFunctor.{u, u, max (u + 1) v}
              (parabolic i ν) (levi i ν) (unipotent i ν) hM hU J I n hs ht).obj σ)) :
    CuspidalJacquetGradedPieces.{u, u, max (u + 1) v}
      (parabolic i ν) (levi i ν) (unipotent i ν) hU hM
      (isSemidirectDecomposition_in_levi i ν hInter hG hi hν)
      (rootAssociation i ν hN hZ) I J σ s := by
  intro q
  obtain ⟨w, hw, n, hn, hs, ht, ⟨e⟩⟩ := hgrades q
  rcases hDichotomy I J w hw n hn hs ht σ hcσ with hno | ⟨hConj, hA, ⟨eConj⟩⟩
  · left
    intro τ hτ hcτ hsub
    exact hno τ hτ hcτ (hsub.of_iso_right e)
  · exact Or.inr ⟨(n : RationalPoint k G.X), hConj, hA, ⟨e ≪≫ eConj⟩⟩

/-- A supplied actual rational geometric filtration extracts the required
cuspidal conjugate under proper-target exclusion. No finite-length assumption
on the ambient representation or its grades is used. -/
theorem pointCuspidalJacquetFactor_of_geometricFiltration
    (hGeom : PointCuspidalExtractionGeometry.{u, v}
      i ν hN hZ cs hG hi hν hInter hM hU)
    (hExclude : PointProperTargetGeometricTermExclusion.{u, v}
      i ν cs hInter hG hi hν hM hU)
    (I J : Finset (SimpleRoot i ν))
    (σ : SmoothRep.{0, u, max (u + 1) v} ℂ (levi i ν I))
    (τ A : SmoothRep.{0, u, max (u + 1) v} ℂ (levi i ν J))
    {r : ℕ} (s : ObjectRepFiltration A.obj r)
    (hσ : σ.IsIrreducible)
    (hcσ : IsLeviCuspidal (parabolic i ν) (levi i ν) (unipotent i ν) hU I (hM I)
      (isSemidirectDecomposition_in_levi i ν hInter hG hi hν I) σ)
    (hτ : τ.IsIrreducible)
    (hcτ : IsLeviCuspidal (parabolic i ν) (levi i ν) (unipotent i ν) hU J (hM J)
      (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J) τ)
    (hτA : SmoothRep.IsSubquotient τ A)
    (hgrades : ∀ q : Fin r,
      ∃ (w : Weyl i) (_hw : IsMinimal cs J I w)
        (n : Group.RelativeWeyl.normalizer (torusPoints i)) (_hn : QuotientGroup.mk n = w)
        (hs : GeometricSourceDecomposition
          (parabolic i ν) (levi i ν) (unipotent i ν) J I n)
        (ht : GeometricTargetDecomposition
          (parabolic i ν) (levi i ν) (unipotent i ν) J I n),
        Nonempty
          (s.smoothGradedObject q ≅
            (geometricTermFunctor.{u, u, max (u + 1) v}
              (parabolic i ν) (levi i ν) (unipotent i ν) hM hU J I n hs ht).obj σ)) :
    ∃ (n : RationalPoint k G.X)
      (hn : ∀ x : RationalPoint k G.X, x ∈ levi i ν J ↔ n⁻¹ * x * n ∈ levi i ν I),
      rootAssociation i ν hN hZ I J n ∧
      Nonempty (τ ≅ (conjugationFunctor n hn).obj σ) := by
  exact cuspidalJacquetFactor_of_finiteFiltration s hσ hτ hcτ hτA
    (pointCuspidalJacquetGradedPieces_of_geometricTerms
      i ν hN hZ cs hInter hG hi hν hM hU
      (pointGeometricCuspidalGradeDichotomy_of_geometry_exclusion
        i ν hN hZ cs hInter hG hi hν hM hU hGeom hExclude)
      I J σ hcσ s hgrades)

end Langlands.Aubert.General.RationalPointFamily
