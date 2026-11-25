import Langlands.GroupScheme.OddOrthogonalMatrix.NumberedBase
import Langlands.LinearAlgebra.TypeBBasedAutomorphism
import Langlands.GroupScheme.Reductive.RootPinningFromSplitTorus
import Langlands.GroupScheme.Reductive.PinnedAutomorphismGroupProof
import Langlands.GroupScheme.Adjoint.ExistenceProof
import Langlands.GroupScheme.Absolute.QuotientNormalizer

/-! # Innerness of automorphisms of the split odd identity component -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.OddOrthogonalMatrix.TypeBNumbering

variable {K : Type u} [Field K] {n : ℕ}

/-- An actual pinning with a numbered type-B base and full integral root span. -/
structure NumberedPinning (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffineHom G.X.hom]
    (n : ℕ) where
  pinning : SplitPinning G
  numbering : pinning.base.support ≃ Fin n
  cartan : ∀ a b : pinning.base.support,
    pinning.rootDatum.pairing a.val b.val = CartanMatrix.B n (numbering a) (numbering b)
  rootSpan : pinning.rootDatum.rootSpan ℤ = ⊤

/-- The actual odd identity component has a pinning with its exact type-B numbering. -/
def numberedPinning (hn : 2 ≤ n) : NumberedPinning (identityComponent (groupScheme (Fin n) K)) n := by
  apply Classical.choice
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  obtain ⟨J, hJ, Q, hQ, hred, B, e, hcartan, _, _⟩ := exists_numberedRootDatum (K := K) hn
  have : Finite J := hJ
  let p : SplitPinning (identityComponent (groupScheme (Fin n) K)) :=
    { isConnectedReductive := identityReductive (Fin n) K
      torus := splitTorus.commGroupScheme (Spec (CommRingCat.of K)) (ULift (Fin n))
      inclusion := identityTorus (Fin n) K
      isSplitTorus := SymplecticMatrix.isSplitTorus_diagonalTorus (Fin n) K
      isMaximalTorus := isMaximalTorus_identityTorus (Fin n) K
      rootIndex := J
      rootDatum := Q
      isRootDatum := hQ
      isReduced := hred
      base := B
      pinning := RootPinning.ofSplitMaximalTorus (identityReductive (Fin n) K)
        (SymplecticMatrix.isSplitTorus_diagonalTorus (Fin n) K)
        (identityTorus (Fin n) K) (isMaximalTorus_identityTorus (Fin n) K) Q hQ B }
  exact ⟨⟨p, e, hcartan, rootSpan_eq_top Q hQ.2.1⟩⟩

variable {G : GroupScheme (Spec (CommRingCat.of K))} [IsAffineHom G.X.hom]

/-- Every based automorphism of this full-root type-B pinning is trivial. -/
theorem NumberedPinning.basedRootDatumAut_eq_one (p : NumberedPinning G n) (hn : 2 ≤ n)
    (θ : p.pinning.basedRootDatumAut) : θ = 1 := by
  apply Subtype.ext
  exact TypeBBasedAutomorphism.eq_one_of_full_rootSpan p.pinning.rootDatum p.pinning.base hn
    p.numbering p.cartan p.rootSpan θ.val θ.property

/-- Over an algebraically closed field, all automorphisms of a full-root
pinned type-B group are conjugation by its own rational points. -/
theorem NumberedPinning.exists_innerIso [IsAlgClosed K] (p : NumberedPinning G n)
    (hn : 2 ≤ n) (σ : G ≅ G) :
    ∃ g : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X, G.innerIso g = σ := by
  obtain ⟨A, q, hq⟩ := adjointQuotientExistence K G p.pinning.isConnectedReductive
  obtain ⟨x, θ, hσ⟩ := PinnedAutomorphismGroup.exists_eq_innerHom_mul_lift hq p.pinning (Aut.of σ)
  rw [p.basedRootDatumAut_eq_one hn θ, map_one, mul_one] at hσ
  have : Surjective q.hom.hom.left := hq.surjective
  have : LocallyOfFinitePresentation q.hom.hom.left := hq.locallyOfFinitePresentation
  obtain ⟨g, hg⟩ := exists_rationalPointLift q x
  refine ⟨g, ?_⟩
  rw [← hg, PinnedAutomorphismGroup.innerHom_apply,
    SplitPinning.innerAction_basePointIso_lift hq g] at hσ
  exact (congrArg Aut.asIso hσ).symm

/-- Every automorphism of the actual split odd identity component is inner
over an algebraically closed field. -/
theorem exists_innerIso_identityComponent [IsAlgClosed K] (hn : 2 ≤ n)
    (σ : identityComponent (groupScheme (Fin n) K) ≅ identityComponent (groupScheme (Fin n) K)) :
    ∃ g : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ (identityComponent (groupScheme (Fin n) K)).X,
      (identityComponent (groupScheme (Fin n) K)).innerIso g = σ :=
  (numberedPinning (K := K) hn).exists_innerIso hn σ

end Langlands.GroupScheme.OddOrthogonalMatrix.TypeBNumbering
