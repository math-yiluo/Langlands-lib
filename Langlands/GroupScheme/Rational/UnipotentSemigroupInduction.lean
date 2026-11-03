import Langlands.GroupScheme.Rational.CentralSemigroupProduct
import Langlands.GroupScheme.Rational.VectorSemigroupProduct
import Langlands.GroupScheme.Rational.SemigroupSolvableReductionStatement
import Langlands.GroupScheme.Derived.Basic
import Langlands.AlgebraicGeometry.SmoothConnectedRelativeDimensionProof

/-! # Central dimension induction for exact unipotent semigroup products -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

section Trivial

variable {B : Scheme.{u}} (G : GroupScheme B)

/-- Triviality of the identity range gives triviality on every scheme test. -/
theorem points_eq_one_of_range_id_eq_bot
    (hG : SubgroupFunctor.range (𝟙 G) = ⊥)
    (T : Over B) (x : T ⟶ G.X) : x = 1 := by
  have hx : x ∈ (⊥ : SubgroupFunctor G).carrier T := by
    rw [← hG]
    exact ⟨x, by simp⟩
  exact hx

private theorem trivial_orderedMultiplication_isIso
    (hG : SubgroupFunctor.range (𝟙 G) = ⊥) (n : ℕ) :
    IsIso (orderedMultiplication (fun _ : Fin n => 𝟙 G)) := by
  apply (isIso_orderedMultiplication_iff _).mpr
  intro T
  let : Subsingleton (T ⟶ G.X) :=
    ⟨fun x y => (points_eq_one_of_range_id_eq_bot G hG T x).trans
      (points_eq_one_of_range_id_eq_bot G hG T y).symm⟩
  exact Function.bijective_of_subsingleton' _

/-- The original ordered product of any number of copies of an all-test
trivial group is canonically that group, including the empty product. -/
def trivialOrderedProductIso
    (hG : SubgroupFunctor.range (𝟙 G) = ⊥) (n : ℕ) :
    (∏ᶜ fun _ : Fin n => G).X ≅ G.X :=
  letI := trivial_orderedMultiplication_isIso G hG n
  asIso (orderedMultiplication (fun _ : Fin n => 𝟙 G))

@[simp]
theorem trivialOrderedProductIso_hom
    (hG : SubgroupFunctor.range (𝟙 G) = ⊥) (n : ℕ) :
    (trivialOrderedProductIso G hG n).hom =
      orderedMultiplication (fun _ : Fin n => 𝟙 G) := rfl

end Trivial

section Field

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}

/-- A smooth connected all-test trivial ambient group satisfies the exact
product property, without any condition on its supplied action. -/
theorem hasOrderedSemigroupProducts_of_range_id_eq_bot
    (b : AutomorphicAction S.toGrp G)
    (hG : Smooth G.X.hom) (hconn : ConnectedSpace G.X.left)
    (htriv : SubgroupFunctor.range (𝟙 G) = ⊥) :
    HasOrderedSemigroupProducts b := by
  intro n Ψ _ _ _
  refine ⟨fun _ => G, fun _ => 𝟙 G, ?_,
    (trivialOrderedProductIso G htriv n).isIso_hom⟩
  intro r
  have heq : semigroupSubgroup b (AddSubsemigroup.closure (Ψ r)) = ⊤ := by
    apply le_antisymm
    · exact fun _ _ _ => Subgroup.mem_top _
    · intro T x _
      rw [points_eq_one_of_range_id_eq_bot G htriv T x]
      exact Subgroup.one_mem _
  rw [heq]
  refine ⟨⟨?_, SubgroupFunctor.range_id G⟩,
    IsClosedSubgroup.of_iso (Iso.refl G), hG, hconn⟩
  change Mono (𝟙 G.X)
  infer_instance

end Field

/-- The exact algebraically closed unipotent core follows by dimension
induction from the stated geometric inputs and augmentation/Lie comparison. -/
theorem unipotentSemigroupOrderedProduct_of_centralStatements
    (hContain : CoordinateWeights.AugmentationLieContainmentStatement.{u})
    (hReal : SemigroupRealizationStatement.{u})
    (hSmoothQuotient : SemigroupSmoothQuotientStatement.{u})
    (hIntersection : SemigroupIntersectionStatement.{u})
    (hCentral : CentralStableVectorSubgroupStatement.{u})
    (hQuotient : CentralSmoothQuotientStatement.{u}) :
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
      by_cases htriv : SubgroupFunctor.range (𝟙 H) = ⊥
      · exact hasOrderedSemigroupProducts_of_range_id_eq_bot bH hH hconnH htriv
      obtain ⟨Z, z, bZ, n, e, hzClosed, hZ, hAffZ, hconnZ, hunipZ, hzCentral,
        hzStable, hzNontrivial, hn, hdZ, hlinear, hzEq⟩ :=
        hCentral k H hH hAffH hconnH hunipH htriv S hS bH
      let := hAffZ
      obtain ⟨Q, q, bQ, m, hAffQ, hQ, hconnQ, hunipQ, hq, hqSmooth, hqdim,
        hdQ, hsum, hm, hqEq⟩ :=
        hQuotient k H Z z hH hAffH hconnH hunipH hzClosed hZ hconnZ hzCentral
          S hS bH bZ hzEq d n hd hdZ hn
      let := hAffQ
      have hZprod : HasOrderedSemigroupProducts bZ :=
        hlinear.semigroupOrderedProduct hContain hS
      have hQprod : HasOrderedSemigroupProducts bQ :=
        ih m hm Q hAffQ hQ hconnQ hunipQ hdQ bQ
      exact hasOrderedSemigroupProducts_of_centralExtension
        hReal hSmoothQuotient hIntersection hH hZ hQ hconnZ hS bH bZ bQ z q
        hzClosed hzCentral hq hqSmooth hzEq
        (fun T s g => (hqEq T s g).symm) hZprod hQprod
  obtain ⟨d, hd⟩ := Langlands.AlgebraicGeometry.smoothConnectedRelativeDimension
    G.X.left _ G.X.hom hG hconn
  exact hind d G hAff hG hconn hunip hd b

end Langlands.GroupScheme.RelativeRoot
