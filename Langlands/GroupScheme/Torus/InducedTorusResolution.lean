import Langlands.GroupScheme.Torus.InducedEmbedding
import Langlands.GroupScheme.Torus.MultiplicativeTypeMonoClosedImmersionProof
import Langlands.GroupScheme.Torus.RelativeMultiplicativeTypeClosedQuotient
import Langlands.GroupScheme.Torus.RelativeMultiplicativeTypeFieldComparison
import Langlands.GroupScheme.Torus.RelativeTorusMultiplicativeType
import Langlands.GroupScheme.Torus.RelativeFieldComparison
import Langlands.GroupScheme.Torus.DiagonalizableSmoothConnectedCriteriaProof
import Langlands.GroupScheme.CentralIsogeny.FpqcReflection

/-! # A torus as the kernel of a quotient of an induced torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Over a characteristic-zero field every torus embeds as the kernel of an
fppf quotient from an induced torus to a torus. -/
def InducedTorusResolutionStatement : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (T : CommGroupScheme (Spec (CommRingCat.of k))),
    IsTorus T.toGrp →
    ∃ (P Q : CommGroupScheme (Spec (CommRingCat.of k)))
      (i : T.toGrp ⟶ P.toGrp) (q : P.toGrp ⟶ Q.toGrp),
      IsInducedTorus P ∧ IsTorus Q.toGrp ∧ IsClosedSubgroup i ∧
        RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q

private theorem isTorus_of_torus_surjection {k : Type u} [Field k] [CharZero k]
    {P Q : GroupScheme (Spec (CommRingCat.of k))} (q : P ⟶ Q) (hP : IsTorus P)
    (hQ : RelativeMultiplicativeType.IsMultiplicativeType Q)
    [Surjective q.hom.hom.left] : IsTorus Q := by
  let d := hQ.fieldDiagonalization
  let E := d.extensionField
  let Λ := d.characterGroup
  let b := algebraBaseMap k E
  let F := GroupScheme.baseChange b
  let D := (Diagonalizable.groupScheme (CommRingCat.of E) Λ).toGrp
  let e : F.obj Q ≅ D := d.iso
  let : ConnectedSpace (F.obj P).X.left := (hP.baseChange (K := E)).connectedSpace
  have hf : Surjective (F.map q).hom.hom.left :=
    MorphismProperty.of_isPullback (baseChange_map_isPullback b q).flip inferInstance
  let : ConnectedSpace (F.obj Q).X.left :=
    hf.surj.connectedSpace (F.map q).hom.hom.left.continuous
  have he : Surjective e.hom.hom.hom.left := inferInstanceAs
    (Surjective ((Grp.forget _ ⋙ Over.forget _).map e.hom))
  have hc : ConnectedSpace D.X.left := he.surj.connectedSpace e.hom.hom.hom.left.continuous
  let : CharZero E := charZero_of_injective_algebraMap (algebraMap k E).injective
  have hcriteria := Diagonalizable.diagonalizableSmoothConnectedCriteria E 1 Λ
  have hs : Smooth D.X.hom := hcriteria.2.1.mpr (fun x hx => by simpa using hx)
  let : Module.Free ℤ Λ := hcriteria.2.2.mp ⟨hs, hc⟩
  let : Module.Finite ℤ Λ := Module.Finite.iff_addGroup_fg.mpr inferInstance
  let basis := Module.Free.chooseBasis ℤ Λ
  exact ⟨E, inferInstance, inferInstance, _, inferInstance,
    ⟨e ≪≫ Diagonalizable.splitIso (CommRingCat.of E) basis.equivFun.toAddEquiv⟩⟩

/-- Embed into an induced torus and form the multiplicative-type quotient.
Connectedness on a diagonalizing extension makes its character group free. -/
theorem inducedTorusResolution : InducedTorusResolutionStatement.{u} := by
  intro k _ _ T hT
  obtain ⟨P, i, hP, hi⟩ := hT.exists_mono_inducedTorus T
  let j := CommGroupScheme.groupHom i
  let : IsAffineHom P.X.hom := hP.isTorus.isRelativeTorus.isAffineHom
  let : Smooth P.X.hom := hP.isTorus.smooth
  have hTm := hT.isRelativeTorus.isMultiplicativeType
  have hPm := hP.isTorus.isRelativeTorus.isMultiplicativeType
  have hj : IsClosedSubgroup j := multiplicativeTypeMonoClosedImmersion _ _ _ j hTm hi
  obtain ⟨Q, q, hQ, hq, _⟩ :=
    RelativeMultiplicativeType.exists_quotient_of_multiplicativeType hPm hTm j hj
  have hQT : IsTorus Q := @isTorus_of_torus_surjection k _ _ P.toGrp Q q
    hP.isTorus hQ hq.2.1
  exact ⟨P, hQ.commGroupScheme, j, q, hP, hQT, hj, hq⟩

end Langlands.GroupScheme
