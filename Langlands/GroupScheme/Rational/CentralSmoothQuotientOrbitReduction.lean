import Langlands.GroupScheme.Rational.CentralSmoothQuotientReduction
import Langlands.GroupScheme.Reductive.UnipotentFieldExtensionProof
import Langlands.GroupScheme.UnipotentAffineOrbitClosedProof

/-! # Actual unipotent quotients using the published closed-orbit theorem -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace Chevalley

/-- An actual affine homogeneous quotient over any field by a smooth closed
subgroup, when both groups are unipotent. -/
def unipotentAffineQuotientOfUnipotentSubgroup
    (k : Type u) [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [Smooth G.X.hom] (hG : IsUnipotent G)
    (H : GroupScheme (Spec (CommRingCat.of k))) (i : H ⟶ G)
    (hi : IsClosedSubgroup i) (hsm : Smooth H.X.hom) (hH : IsUnipotent H) :
    HomogeneousQuotientFromEmbedding.AffineHomogeneousQuotient i := by
  let : IsClosedImmersion i.hom.hom.left := hi
  let : IsAffineHom H.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  exact unipotentAffineQuotientOfFieldExtension unipotentAffineOrbitClosed
    k (AlgebraicClosure k) G H i hi hsm
    (IsUnipotent.baseChange hG) (IsUnipotent.baseChange hH)

/-- A smooth normal unipotent subgroup of positive dimension gives an actual
equivariant affine quotient over any field, with strict dimension decrease. -/
theorem exists_unipotentNormalQuotient_overField
    (k : Type u) [Field k]
    (G Z A : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (hG : IsUnipotent G) (i : Z ⟶ G)
    (hi : IsClosedSubgroup i) (hZ : IsUnipotent Z)
    (hnormal : (SubgroupFunctor.range i).IsNormal)
    (a : AutomorphicAction A G) (hstable : a.IsStable (SubgroupFunctor.range i))
    {d n : ℕ} (hd : SmoothOfRelativeDimension d G.X.hom)
    (hn : SmoothOfRelativeDimension n Z.X.hom) (hpos : 0 < n) :
    ∃ (Q : GroupScheme (Spec (CommRingCat.of k))) (q : G ⟶ Q)
      (b : AutomorphicAction A Q) (m : ℕ),
      IsAffineHom Q.X.hom ∧ Smooth Q.X.hom ∧ ConnectedSpace Q.X.left ∧
      IsUnipotent Q ∧ RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q ∧
      Smooth q.hom.hom.left ∧ SmoothOfRelativeDimension n q.hom.hom.left ∧
      SmoothOfRelativeDimension m Q.X.hom ∧ d = n + m ∧ m < d ∧
      ∀ (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ A.X) (g : T ⟶ G.X),
        b.act s (g ≫ q.hom.hom) = a.act s g ≫ q.hom.hom := by
  let : SmoothOfRelativeDimension d G.X.hom := hd
  let : SmoothOfRelativeDimension n Z.X.hom := hn
  let : Smooth G.X.hom := SmoothOfRelativeDimension.smooth d G.X.hom
  let : IsClosedImmersion i.hom.hom.left := hi
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  let D := unipotentAffineQuotientOfUnipotentSubgroup k G hG Z i hi
    (SmoothOfRelativeDimension.smooth n Z.X.hom) hZ
  exact D.quotient.exists_action_relativeDimension D.affine hnormal hG a hstable hd hn hpos

end Chevalley

namespace RelativeRoot

/-- Only closed-subgroup unipotence remains as a structural proposition
premise for the exact central smooth quotient target. -/
theorem centralSmoothQuotient_of_closedSubgroup
    (hsub : UnipotentClosedSubgroupStatement.{u}) :
    CentralSmoothQuotientStatement.{u} :=
  centralSmoothQuotient_of_structuralStatements
    unipotentAffineOrbitClosed unipotentFieldExtensionStatement hsub

end RelativeRoot

end Langlands.GroupScheme
