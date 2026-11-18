import Langlands.AlgebraicGeometry.Picard.ArtinianChartVersalityDescentStatement
import Langlands.CategoryTheory.Sites.PseudofunctorPointFiberAtlasRestriction
import Langlands.CategoryTheory.Sites.PseudofunctorPointFiberObjectIso

/-! # Proof of pointed Picard versality descent -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.AlgebraicGeometry.Deformation
open Langlands.CategoryTheory

namespace PicardGroupoid.ArtinianChartVersality

variable {R K : Type u} [CommRing R] [Field K] [Algebra R K]
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
  {U : Over (Spec (CommRingCat.of R))}
  {L L' : LineBundle ((relativeSpace f).obj U)}
  (p : ArtinianTest.residueBase R K ⟶ U)

/-- An actual isomorphism of families preserves formal versality at the
same specified residue map, including all prescribed fibre isomorphisms. -/
theorem isFormallyVersalAt_of_iso (e : L ≅ L')
    (h : IsFormallyVersalAt f L p) : IsFormallyVersalAt f L' p := by
  intro A B q hq T N a b w y hy
  let y₀ := PseudofunctorPointFiberObjectIso.mapPoints (relative f)
    (Core.isoMk e).symm (Core.mk N) (Over.mk b) y
  have hy₀ : ArtinianTest.reduction B ≫ y₀.1 = p := hy
  obtain ⟨x, hx⟩ := h q hq T N a b w y₀ hy₀
  refine ⟨PseudofunctorPointFiberObjectIso.mapPoints (relative f)
    (Core.isoMk e) (Core.mk N) (Over.mk a) x, ?_⟩
  change PseudofunctorPointFiber.restrict (relative f) (Core.mk L') (Core.mk N)
    (ArtinianChartLifting.testArrow q w) _ = y
  rw [← PseudofunctorPointFiberObjectIso.mapPoints_restrict]
  change PseudofunctorPointFiberObjectIso.mapPoints (relative f)
    (Core.isoMk e) (Core.mk N) (Over.mk b)
    (ArtinianChartLifting.restrict f L q N w x) = y
  rw [hx]
  exact PseudofunctorPointFiberObjectIso.mapPoints_symm (relative f)
    (Core.isoMk e).symm (Core.mk N) (Over.mk b) y

/-- Versality descends through a pointed Artinian factorization condition
for the chart map, without uniqueness of factorizations. -/
theorem isFormallyVersalAt_of_pointed_factorization
    {V : Over (Spec (CommRingCat.of R))} (i : V ⟶ U)
    (pV : ArtinianTest.residueBase R K ⟶ V)
    (hfactor : ∀ (A : ArtinianTest R K) (a : ArtinianTest.base A ⟶ U),
      ArtinianTest.reduction A ≫ a = pV ≫ i →
        ∃ b : ArtinianTest.base A ⟶ V,
          ArtinianTest.reduction A ≫ b = pV ∧ b ≫ i = a)
    (h : IsFormallyVersalAt f
      ((LineBundle.pullback ((relativeSpace f).map i)).obj L) pV) :
    IsFormallyVersalAt f L (pV ≫ i) := by
  intro A B q hq T N a b w y hy
  obtain ⟨c, hcp, hc⟩ := hfactor B y.1 hy
  rcases y with ⟨d, δ⟩
  dsimp only at hc
  subst d
  let yV : FiberPoints f
      ((LineBundle.pullback ((relativeSpace f).map i)).obj L) N (Over.mk b) :=
    ⟨c, (PseudofunctorPointFiberAtlasRestriction.atlasComparison
      (relative f) i (Core.mk L) c).symm ≪≫ δ⟩
  obtain ⟨x, hx⟩ := h q hq T N a b w yV hcp
  refine ⟨PseudofunctorPointFiberAtlasRestriction.mapPoints (relative f) i
    (Core.mk L) (Core.mk N) (Over.mk a) x, ?_⟩
  change PseudofunctorPointFiber.restrict (relative f) (Core.mk L) (Core.mk N)
    (ArtinianChartLifting.testArrow q w) _ = ⟨c ≫ i, δ⟩
  rw [← PseudofunctorPointFiberAtlasRestriction.mapPoints_restrict]
  change PseudofunctorPointFiberAtlasRestriction.mapPoints (relative f) i
    (Core.mk L) (Core.mk N) (Over.mk b)
    (ArtinianChartLifting.restrict f
      ((LineBundle.pullback ((relativeSpace f).map i)).obj L) q N w x) = _
  rw [hx]
  simp [yV, PseudofunctorPointFiberAtlasRestriction.mapPoints]

end PicardGroupoid.ArtinianChartVersality

/-- Pointed Artinian factorizations descend formal versality of an actual
family identified with a pullback. -/
theorem artinianChartVersalityDescent : ArtinianChartVersalityDescentStatement.{u} := by
  intro R _ X f U V i L M K _ _ p ⟨e⟩ hfactor h
  apply PicardGroupoid.ArtinianChartVersality.isFormallyVersalAt_of_pointed_factorization
    f i p hfactor
  exact PicardGroupoid.ArtinianChartVersality.isFormallyVersalAt_of_iso f p e h

end Langlands.AlgebraicGeometry.Picard
