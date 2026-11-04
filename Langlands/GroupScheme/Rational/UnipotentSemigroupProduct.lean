import Langlands.GroupScheme.Rational.UnipotentSemigroupInduction
import Langlands.GroupScheme.Rational.CoordinateSemigroupProof
import Langlands.GroupScheme.Chevalley.UnipotentNormalQuotient
import Langlands.GroupScheme.UnipotentAffineOrbitClosedProof

/-! # Unipotent semigroup products using the actual central quotient -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

/-- Central-vector existence and the three semigroup comparisons suffice for
the exact algebraically closed unipotent target. The actual affine quotient
and augmentation/Lie containment are supplied by published proofs. -/
theorem unipotentSemigroupOrderedProduct_of_centralVector
    (hReal : SemigroupRealizationStatement.{u})
    (hSmoothQuotient : SemigroupSmoothQuotientStatement.{u})
    (hIntersection : SemigroupIntersectionStatement.{u})
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
      let : ConnectedSpace H.X.left := hconnH
      by_cases htriv : SubgroupFunctor.range (𝟙 H) = ⊥
      · exact hasOrderedSemigroupProducts_of_range_id_eq_bot bH hH hconnH htriv
      obtain ⟨Z, z, bZ, n, e, hzClosed, hZ, hAffZ, hconnZ, hunipZ, hzCentral,
        hzStable, hzNontrivial, hn, hdZ, hlinear, hzEq⟩ :=
        hCentral k H hH hAffH hconnH hunipH htriv S hS bH
      let := hAffZ
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
      exact hasOrderedSemigroupProducts_of_centralExtension
        hReal hSmoothQuotient hIntersection hH hZ hQ hconnZ hS bH bZ bQ z q
        hzClosed hzCentral hq hqSmooth hzEq
        (fun T s g => (hqEq T s g).symm) hZprod hQprod
  obtain ⟨d, hd⟩ := Langlands.AlgebraicGeometry.smoothConnectedRelativeDimension
    G.X.left _ G.X.hom hG hconn
  exact hind d G hAff hG hconn hunip hd b

section Data

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    (b : AutomorphicAction S.toGrp G) {n : ℕ}
    (Ψ : Fin n → Set (characterLattice S))

/-- Actual representatives and the original multiplication isomorphism for
one ordered family of semigroup blocks. -/
structure OrderedSemigroupProductData where
  factor : Fin n → GroupScheme (Spec (CommRingCat.of k))
  inclusion : ∀ r, factor r ⟶ G
  geometry : ∀ r,
    (semigroupSubgroup b (AddSubsemigroup.closure (Ψ r))).IsRepresentedBy (inclusion r) ∧
      IsClosedSubgroup (inclusion r) ∧ Smooth (factor r).X.hom ∧
      ConnectedSpace (factor r).X.left
  productIso : (∏ᶜ factor).X ≅ G.X
  productIso_hom : productIso.hom = orderedMultiplication inclusion

/-- Choose the actual factors from the strengthened unipotent induction.
The four remaining structural premises are explicit. -/
def unipotentOrderedSemigroupProduct
    (hReal : SemigroupRealizationStatement.{u})
    (hSmoothQuotient : SemigroupSmoothQuotientStatement.{u})
    (hIntersection : SemigroupIntersectionStatement.{u})
    (hCentral : CentralStableVectorSubgroupStatement.{u})
    [IsAlgClosed k] (hG : Smooth G.X.hom) (hconn : ConnectedSpace G.X.left)
    (hunip : IsUnipotent G) (hS : IsSplitTorus S.toGrp)
    (hcover : (⋃ r, Ψ r) = actionWeightSupport b ⊤)
    (hdisj : ∀ r s, r ≠ s → Disjoint (Ψ r) (Ψ s))
    (hcross : ∀ r s, r ≠ s →
      Disjoint (Ψ r) (AddSubsemigroup.closure (Ψ s) : Set (characterLattice S))) :
    OrderedSemigroupProductData b Ψ :=
  Classical.choice (by
    obtain ⟨H, j, hj, hp⟩ :=
      unipotentSemigroupOrderedProduct_of_centralVector
        hReal hSmoothQuotient hIntersection hCentral
        k G hG inferInstance hconn hunip S hS b n Ψ hcover hdisj hcross
    let := hp
    exact ⟨⟨H, j, hj, asIso (orderedMultiplication j), rfl⟩⟩)

end Data

end Langlands.GroupScheme.RelativeRoot
