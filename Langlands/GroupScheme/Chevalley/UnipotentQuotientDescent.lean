import Langlands.GroupScheme.Chevalley.UnipotentAffineQuotient
import Langlands.GroupScheme.HomogeneousQuotientAffineDescent
import Langlands.GroupScheme.HomogeneousQuotientProof
import Langlands.GroupScheme.HomogeneousQuotientGroup

/-! # Actual affine unipotent quotients by field-extension descent -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Chevalley

/-- An affine homogeneous quotient over an arbitrary field, given unipotence of
the ambient group and subgroup after an algebraically closed extension. The
closed-orbit proposition remains an explicit input. -/
def unipotentAffineQuotientOfFieldExtension
    (hclosed : UnipotentAffineOrbitClosedStatement.{u})
    (k K : Type u) [Field k] [Field K] [Algebra k K] [IsAlgClosed K]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [Smooth G.X.hom]
    (H : GroupScheme (Spec (CommRingCat.of k))) (i : H ⟶ G)
    (hi : IsClosedSubgroup i) (hsm : Smooth H.X.hom)
    (hGK : IsUnipotent ((GroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G))
    (hHK : IsUnipotent ((GroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj H)) :
    HomogeneousQuotientFromEmbedding.AffineHomogeneousQuotient i :=
  Classical.choice (by
    obtain ⟨Q, q, hsep, hft, hqc, hqsm, hsurj, hqqc, hfib⟩ :=
      smoothSubgroupQuotientExistence k G H i hi hsm
    let D : HomogeneousQuotientFromEmbedding.HomogeneousQuotient i :=
      ⟨Q, q, hsep, hft, hqc, hqsm, hsurj, hqqc, hfib⟩
    let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
    let GK := (GroupScheme.baseChange b).obj G
    let HK := (GroupScheme.baseChange b).obj H
    let iK := (GroupScheme.baseChange b).map i
    let : IsAffineHom GK.X.hom := by
      change IsAffineHom (pullback.snd G.X.hom b)
      infer_instance
    let : Smooth GK.X.hom := by
      change Smooth (pullback.snd G.X.hom b)
      infer_instance
    have hsmK : Smooth HK.X.hom := by
      let : Smooth H.X.hom := hsm
      change Smooth (pullback.snd H.X.hom b)
      infer_instance
    let E := unipotentAffineQuotient hclosed K GK hGK HK iK (hi.baseChange b) hsmK hHK
    exact ⟨⟨D, D.isAffine_of_fieldExtension E.quotient E.affine⟩⟩)

/-- The descended affine quotient gives the actual equivariant normal quotient
over the original field, with exact fppf kernel and strict dimension decrease. -/
theorem exists_unipotentNormalQuotientOfFieldExtension
    (hclosed : UnipotentAffineOrbitClosedStatement.{u})
    (k K : Type u) [Field k] [Field K] [Algebra k K] [IsAlgClosed K]
    (G Z A : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (hG : IsUnipotent G) (i : Z ⟶ G) (hi : IsClosedSubgroup i)
    (hGK : IsUnipotent ((GroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G))
    (hZK : IsUnipotent ((GroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj Z))
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
  let D := unipotentAffineQuotientOfFieldExtension hclosed k K G Z i hi
    (SmoothOfRelativeDimension.smooth n Z.X.hom) hGK hZK
  exact D.quotient.exists_action_relativeDimension D.affine hnormal hG a hstable hd hn hpos

end Langlands.GroupScheme.Chevalley
