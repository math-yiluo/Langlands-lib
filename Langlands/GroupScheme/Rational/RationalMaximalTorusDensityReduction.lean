import Langlands.GroupScheme.Rational.RationalMaximalTorusDensityStatement
import Langlands.GroupScheme.SchemeActionRationalOrbit
import Langlands.AlgebraicGeometry.PointTopology.GeometricRationalPoints

/-! # Pulling rational parameter density back to conjugators -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Along an open locally finite type morphism over an algebraically closed field,
rational points lying above a dense set of rational points are dense. -/
theorem dense_rationalPoints_over_dense_parameters
    {K : Type u} [Field K] [IsAlgClosed K]
    {X Y : Over (Spec (CommRingCat.of K))} (q : X ⟶ Y)
    [LocallyOfFiniteType q.left] (hq : IsOpenMap q.left)
    (P : Set (RationalPoint K Y))
    (hP : Dense (⋃ p ∈ P, Set.range p.left)) :
    Dense (⋃ (g : RationalPoint K X) (_ : g ≫ q ∈ P), Set.range g.left) := by
  rw [dense_iff_inter_open]
  rintro U hU ⟨x, hx⟩
  obtain ⟨y, hyp, hy⟩ := hP.exists_mem_open (hq U hU) ⟨q.left x, x, hx, rfl⟩
  obtain ⟨p, hp'⟩ := Set.mem_iUnion.mp hyp
  obtain ⟨hp, a, ha⟩ := Set.mem_iUnion.mp hp'
  let V : X.left.Opens := ⟨U, hU⟩
  have hprange : p.left (IsLocalRing.closedPoint K) ∈ Set.range (V.ι ≫ q.left) := by
    obtain ⟨z, hz, hzy⟩ := hy
    refine ⟨⟨z, hz⟩, ?_⟩
    change q.left z = p.left (IsLocalRing.closedPoint K)
    rw [hzy, ← ha]
    congr 1
    exact Subsingleton.elim (α := PrimeSpectrum K) _ _
  obtain ⟨z, hz⟩ := exists_rationalPoint_lift_of_mem_range (V.ι ≫ q.left) p.left hprange
  have hz' : (z ≫ V.ι) ≫ q.left = p.left := by
    simpa only [Category.assoc] using hz
  let g : RationalPoint K X := Over.homMk (z ≫ V.ι) (by
    rw [← Over.w q, ← Category.assoc, hz', Over.w p])
  have hg : g ≫ q = p := Over.OverMorphism.ext hz'
  refine ⟨g.left (IsLocalRing.closedPoint K), ?_, ?_⟩
  · exact (z (IsLocalRing.closedPoint K)).2
  · exact Set.mem_iUnion.mpr ⟨g,
      Set.mem_iUnion.mpr ⟨hg ▸ hp, ⟨IsLocalRing.closedPoint K, rfl⟩⟩⟩

/-- The compatibility needed from a ground-field parameter map for conjugate tori:
each rational parameter specifies one actual closed ground-field torus, and every
geometric lift conjugates the fixed torus onto that torus on all scheme tests. -/
def TorusParameterConjugationCompatible
    {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {T₀ : CommGroupScheme (Spec (CommRingCat.of k))} (j₀ : T₀.toGrp ⟶ G)
    {Q : Over (Spec (CommRingCat.of k))} (q : G.X ⟶ Q) : Prop :=
  ∀ x : RationalPoint k Q,
    ∃ (T : CommGroupScheme (Spec (CommRingCat.of k))) (j : T.toGrp ⟶ G),
      IsTorus T.toGrp ∧ IsClosedSubgroup j ∧
        ∀ g : RationalPoint (AlgebraicClosure k)
            ((GroupScheme.baseChange (toAlgebraicClosure k)).obj G).X,
          g ≫ (Over.pullback (toAlgebraicClosure k)).map q =
              geometricRationalPoint (K := AlgebraicClosure k) Q x →
            SubgroupFunctor.range
                ((GroupScheme.baseChange (toAlgebraicClosure k)).map j₀ ≫
                  (((GroupScheme.baseChange (toAlgebraicClosure k)).obj G).innerIso g).hom) =
              SubgroupFunctor.range ((GroupScheme.baseChange (toAlgebraicClosure k)).map j)

/-- An open parameter map, compatible with actual closed tori and having geometrically
dense ground-field parameters, gives the required density of conjugators. -/
theorem dense_torusConjugators_of_parameters
    {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {T₀ : CommGroupScheme (Spec (CommRingCat.of k))} (j₀ : T₀.toGrp ⟶ G)
    {Q : Over (Spec (CommRingCat.of k))} (q : G.X ⟶ Q)
    [LocallyOfFiniteType ((Over.pullback (toAlgebraicClosure k)).map q).left]
    (hq : IsOpenMap ((Over.pullback (toAlgebraicClosure k)).map q).left)
    (hcompatible : TorusParameterConjugationCompatible j₀ q)
    (hdense : HasDenseGeometricRationalPoints k (AlgebraicClosure k) Q) :
    Dense (⋃ (g : RationalPoint (AlgebraicClosure k)
          ((GroupScheme.baseChange (toAlgebraicClosure k)).obj G).X)
        (_ : ∃ (T : CommGroupScheme (Spec (CommRingCat.of k))) (j : T.toGrp ⟶ G),
          IsTorus T.toGrp ∧ IsClosedSubgroup j ∧
            SubgroupFunctor.range ((GroupScheme.baseChange (toAlgebraicClosure k)).map j₀ ≫
                (((GroupScheme.baseChange (toAlgebraicClosure k)).obj G).innerIso g).hom) =
              SubgroupFunctor.range ((GroupScheme.baseChange (toAlgebraicClosure k)).map j)),
        Set.range g.left) := by
  let P : Set (RationalPoint (AlgebraicClosure k)
      ((Over.pullback (toAlgebraicClosure k)).obj Q)) :=
    Set.range (geometricRationalPoint (K := AlgebraicClosure k) Q)
  have hP : Dense (⋃ p ∈ P, Set.range p.left) := by
    apply hdense.mono
    rintro z hz
    simp only [Set.mem_iUnion, Set.mem_range] at hz ⊢
    obtain ⟨x, a, rfl⟩ := hz
    exact ⟨_, ⟨x, rfl⟩, a, rfl⟩
  apply (dense_rationalPoints_over_dense_parameters
    ((Over.pullback (toAlgebraicClosure k)).map q) hq P hP).mono
  rintro z hz
  simp only [Set.mem_iUnion, Set.mem_range] at hz ⊢
  obtain ⟨g, ⟨x, hx⟩, a, rfl⟩ := hz
  obtain ⟨T, j, hT, hj, hconj⟩ := hcompatible x
  exact Set.mem_iUnion.mpr ⟨g, Set.mem_iUnion.mpr
    ⟨⟨T, j, hT, hj, hconj g hx.symm⟩, a, rfl⟩⟩

end Langlands.GroupScheme
