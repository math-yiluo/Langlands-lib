import Langlands.GroupScheme.Rational.SemigroupSolvableIntersection
import Langlands.GroupScheme.Rational.SemigroupZeroExcludedIntersection
import Langlands.GroupScheme.Rational.UnipotentSemigroupProduct
import Langlands.GroupScheme.Rational.SemigroupRealizationProof
import Langlands.GroupScheme.Rational.SemigroupSmoothQuotientProof
import Langlands.GroupScheme.Rational.SolvableSchemeComparison

/-! # Ordered products from solvable semigroup intersections -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

section Intersection

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
    [Smooth G.X.hom] [Smooth H.X.hom] [ConnectedSpace H.X.left]

/-- Solvable-source inverse images need only the independent fixed-containment
connectedness criterion; realization and coordinate containment are published. -/
theorem semigroup_comap_eq_of_solvable
    (hConn : Torus.SolvableFixedContainmentConnectedStatement.{u})
    (hsolv : IsSolvableScheme H) (hS : IsSplitTorus S.toGrp)
    (b : AutomorphicAction S.toGrp G) (c : AutomorphicAction S.toGrp H)
    (j : H ⟶ G) (hjc : IsClosedSubgroup j)
    (heq : ∀ (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ S.X) (x : T ⟶ H.X),
      c.act s x ≫ j.hom.hom = b.act s (x ≫ j.hom.hom))
    (A : AddSubsemigroup (characterLattice S)) :
    (semigroupSubgroup b A).comap j = semigroupSubgroup c A := by
  by_cases h0 : 0 ∈ A
  · exact semigroup_comap_eq_of_solvable_of_zero_mem c hS hConn hsolv b j heq
      semigroupRealization hjc A h0
  · exact semigroup_comap_eq_of_zero_not_mem b c j heq semigroupRealization
      CoordinateWeights.coordinateSemigroupComparison.2 hS hjc A h0

end Intersection

/-- The actual point equivalences supplied by vector coordinates give the
common derived-series bound one on every test scheme. -/
theorem isSolvableScheme_of_vectorCoordinates
    {k : Type u} [Field k] {Z : GroupScheme (Spec (CommRingCat.of k))} {n : ℕ}
    (e : ∀ T : Over (Spec (CommRingCat.of k)),
      (T ⟶ Z.X) ≃* Multiplicative (Fin n → Γ(T.left, ⊤))) :
    IsSolvableScheme Z := by
  refine ⟨1, fun T => ?_⟩
  exact UniformSolvability.bound_of_injective (e T).toMonoidHom (e T).injective 1
    (by rw [derivedSeries_one, commutator_eq_bot])

/-- Central-vector induction for the exact unipotent target uses only the
solvable-source intersection case. Both remaining structural inputs are explicit. -/
theorem unipotentSemigroupOrderedProduct_of_solvableIntersection
    (hConn : Torus.SolvableFixedContainmentConnectedStatement.{u})
    (hCentral : CentralStableVectorSubgroupStatement.{u}) :
    UnipotentSemigroupOrderedProductStatement.{u} := by
  intro k _ _ G hG hAff hconn hunip S hS b
  let := hAff
  have hind : ∀ (d : ℕ) (H : GroupScheme (Spec (CommRingCat.of k)))
      (hAffH : IsAffineHom H.X.hom),
      letI := hAffH
      Smooth H.X.hom → ConnectedSpace H.X.left → IsUnipotent H →
      SmoothOfRelativeDimension d H.X.hom →
      ∀ bH : AutomorphicAction S.toGrp H, HasOrderedSemigroupProducts bH := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro H hAffH hH hconnH hunipH hd bH
      let := hAffH
      let : Smooth H.X.hom := hH
      let : ConnectedSpace H.X.left := hconnH
      by_cases htriv : SubgroupFunctor.range (𝟙 H) = ⊥
      · exact hasOrderedSemigroupProducts_of_range_id_eq_bot bH hH hconnH htriv
      obtain ⟨Z, z, bZ, n, e, hzClosed, hZ, hAffZ, hconnZ, hunipZ, hzCentral,
        hzStable, hzNontrivial, hn, hdZ, hlinear, hzEq⟩ :=
        hCentral k H hH hAffH hconnH hunipH htriv S hS bH
      let := hAffZ
      let : Smooth Z.X.hom := hZ
      let : ConnectedSpace Z.X.left := hconnZ
      obtain ⟨Q, q, bQ, m, hAffQ, hQ, hconnQ, hunipQ, hq, hqSmooth, hqdim,
        hdQ, hsum, hm, hqEq⟩ :=
        Chevalley.exists_unipotentNormalQuotient unipotentAffineOrbitClosed
          k H Z S.toGrp hunipH z hzClosed hunipZ hzCentral.range_isNormal
          bH hzStable hd hdZ hn
      let := hAffQ
      have hZprod : HasOrderedSemigroupProducts bZ :=
        hlinear.semigroupOrderedProduct CoordinateWeights.coordinateSemigroupComparison.2 hS
      have hQprod : HasOrderedSemigroupProducts bQ :=
        ih m hm Q hAffQ hQ hconnQ hunipQ hdQ bQ
      exact hasOrderedSemigroupProducts_of_centralExtension_of_comap
        semigroupRealization semigroupSmoothQuotient hH hQ hS bH bZ bQ z q
        hzClosed hzCentral hq hqSmooth hzEq
        (fun T s g => (hqEq T s g).symm)
        (fun A => semigroup_comap_eq_of_solvable hConn
          (isSolvableScheme_of_vectorCoordinates e) hS bH bZ z hzClosed hzEq A)
        hZprod hQprod
  obtain ⟨d, hd⟩ := Langlands.AlgebraicGeometry.smoothConnectedRelativeDimension
    G.X.left _ G.X.hom hG hconn
  exact hind d G hAff hG hconn hunip hd b

section Data

variable {k : Type u} [Field k] [IsAlgClosed k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    (b : AutomorphicAction S.toGrp G) {n : ℕ}
    (Ψ : Fin n → Set (characterLattice S))

/-- Actual smooth connected closed factors and their original ordered
multiplication isomorphism, using the narrowed unipotent induction. -/
def solvableUnipotentOrderedSemigroupProduct
    (hConn : Torus.SolvableFixedContainmentConnectedStatement.{u})
    (hCentral : CentralStableVectorSubgroupStatement.{u})
    (hG : Smooth G.X.hom) (hconn : ConnectedSpace G.X.left)
    (hunip : IsUnipotent G) (hS : IsSplitTorus S.toGrp)
    (hcover : (⋃ r, Ψ r) = actionWeightSupport b ⊤)
    (hdisj : ∀ r s, r ≠ s → Disjoint (Ψ r) (Ψ s))
    (hcross : ∀ r s, r ≠ s →
      Disjoint (Ψ r) (AddSubsemigroup.closure (Ψ s) : Set (characterLattice S))) :
    OrderedSemigroupProductData b Ψ :=
  Classical.choice (by
    obtain ⟨H, j, hj, hp⟩ :=
      unipotentSemigroupOrderedProduct_of_solvableIntersection hConn hCentral
        k G hG inferInstance hconn hunip S hS b n Ψ hcover hdisj hcross
    let := hp
    exact ⟨⟨H, j, hj, asIso (orderedMultiplication j), rfl⟩⟩)

end Data

end Langlands.GroupScheme.RelativeRoot
