import Langlands.GroupScheme.Rational.CentralSurjectionMaximalSplitTorusImageProof
import Langlands.GroupScheme.Torus.MaximalSplitComparison
import Langlands.GroupScheme.Torus.SplitReflection
import Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof
import Langlands.GroupScheme.Torus.MaximalBaseChangeProof
import Langlands.GroupScheme.Torus.FieldPointMaximality
import Langlands.GroupScheme.Torus.RelativeFieldComparison
import Langlands.GroupScheme.Reductive.BaseChange
import Langlands.GroupScheme.CentralIsogeny.BaseChange

/-! # Maximality of supplied torus images under central fppf surjections -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme

section Field

variable {k : Type u} [Field k]
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    {T T' : CommGroupScheme (Spec (CommRingCat.of k))}

/-- A supplied fppf image of a maximal torus under a central fppf surjection
of connected reductive field groups is maximal among all closed tori. -/
theorem IsMaximalTorus.image_of_centralFppfHom
    {i : T.toGrp ⟶ G} (hi : IsMaximalTorus i)
    (q : G ⟶ H) (hG : IsConnectedReductive G) (hH : IsConnectedReductive H)
    [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    [LocallyOfFinitePresentation q.hom.hom.left]
    (hq : IsCentral (kernelι q))
    (j : T'.toGrp ⟶ H) (hj : IsClosedSubgroup j) (hT' : IsTorus T'.toGrp)
    (p : T ⟶ T')
    [Flat (CommGroupScheme.groupHom p).hom.hom.left]
    [Surjective (CommGroupScheme.groupHom p).hom.hom.left]
    [LocallyOfFinitePresentation (CommGroupScheme.groupHom p).hom.hom.left]
    (hsq : CommGroupScheme.groupHom p ≫ j = i ≫ q) :
    IsMaximalTorus j := by
  let K := AlgebraicClosure k
  let b := toAlgebraicClosure k
  let F := GroupScheme.baseChange b
  let Fc := CommGroupScheme.baseChange b
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  have hiK : IsMaximalTorus (T := Fc.obj T) (F.map i) :=
    (maximalTorusBaseChange k K G T i hi.1 hi.2.1).mp hi
  have hTK : IsSplitTorus (F.obj T.toGrp) :=
    hiK.1.isSplitTorus_of_finiteGaloisSplitting torusFiniteGaloisSplitting
  have hT'K : IsSplitTorus (F.obj T'.toGrp) :=
    hT'.baseChange.isSplitTorus_of_finiteGaloisSplitting torusFiniteGaloisSplitting
  have hqK : IsCentral (kernelι (F.map q)) := by
    have hc := (hq.baseChange b).comp (kernelBaseChangeIso b q).inv
    simpa only [kernelBaseChangeIso_inv_ι] using hc
  have hsplit : IsMaximalSplitTorus (T := Fc.obj T') (F.map j) := by
    apply centralSurjectionMaximalSplitTorusImage K (F.obj G) (F.obj H) (F.map q)
      (connectedReductiveFieldExtensionStatement k K G hG)
      (connectedReductiveFieldExtensionStatement k K H hH)
      (MorphismProperty.overPullbackMap (P := @Flat) b q.hom.hom inferInstance)
      (MorphismProperty.overPullbackMap (P := @Surjective) b q.hom.hom inferInstance)
      (MorphismProperty.overPullbackMap (P := @LocallyOfFinitePresentation)
        b q.hom.hom inferInstance)
      hqK (Fc.obj T) (Fc.obj T') (F.map i) (F.map j) (Fc.map p)
      (hiK.isMaximalSplitTorus hTK) ⟨hT'K, hj.baseChange b⟩
    · exact MorphismProperty.overPullbackMap (P := @Flat) b
        (CommGroupScheme.groupHom p).hom.hom inferInstance
    · exact MorphismProperty.overPullbackMap (P := @Surjective) b
        (CommGroupScheme.groupHom p).hom.hom inferInstance
    · exact MorphismProperty.overPullbackMap (P := @LocallyOfFinitePresentation) b
        (CommGroupScheme.groupHom p).hom.hom inferInstance
    · exact (F.map_comp _ _).symm.trans
        ((congrArg F.map hsq).trans (F.map_comp _ _))
  apply IsMaximalTorus.of_baseChange (K := K) hj
  exact hsplit.isMaximalTorus fun U hU =>
    hU.isSplitTorus_of_finiteGaloisSplitting torusFiniteGaloisSplitting

end Field

section GeneralBase

variable {S : Scheme.{u}} {G H : GroupScheme S}
    {T T' : CommGroupScheme S}

/-- A supplied fppf torus image under a central fppf homomorphism of
reductive group schemes is maximal on every residue-field fibre. -/
theorem IsFibrewiseMaximalTorus.image_of_centralFppfHom
    {i : T.toGrp ⟶ G} (hi : IsFibrewiseMaximalTorus i)
    (q : G ⟶ H) (hG : IsReductive G) (hH : IsReductive H)
    [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    [LocallyOfFinitePresentation q.hom.hom.left]
    (hq : IsCentral (kernelι q))
    (j : T'.toGrp ⟶ H) (hj : IsClosedSubgroup j)
    (hT' : RelativeTorus.IsTorus T'.toGrp)
    (p : T ⟶ T')
    [Flat (CommGroupScheme.groupHom p).hom.hom.left]
    [Surjective (CommGroupScheme.groupHom p).hom.hom.left]
    [LocallyOfFinitePresentation (CommGroupScheme.groupHom p).hom.hom.left]
    (hsq : CommGroupScheme.groupHom p ≫ j = i ≫ q) :
    IsFibrewiseMaximalTorus j := by
  intro s
  let b := S.fromSpecResidueField s
  let F := GroupScheme.baseChange b
  let Fc := CommGroupScheme.baseChange b
  let : Flat (F.map q).hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @Flat) b q.hom.hom inferInstance
  let : Surjective (F.map q).hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @Surjective) b q.hom.hom inferInstance
  let : LocallyOfFinitePresentation (F.map q).hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @LocallyOfFinitePresentation)
      b q.hom.hom inferInstance
  let : Flat (CommGroupScheme.groupHom (Fc.map p)).hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @Flat) b
      (CommGroupScheme.groupHom p).hom.hom inferInstance
  let : Surjective (CommGroupScheme.groupHom (Fc.map p)).hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @Surjective) b
      (CommGroupScheme.groupHom p).hom.hom inferInstance
  let : LocallyOfFinitePresentation (CommGroupScheme.groupHom (Fc.map p)).hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @LocallyOfFinitePresentation) b
      (CommGroupScheme.groupHom p).hom.hom inferInstance
  have hqK : IsCentral (kernelι (F.map q)) := by
    have hc := (hq.baseChange b).comp (kernelBaseChangeIso b q).inv
    simpa only [kernelBaseChangeIso_inv_ι] using hc
  change IsMaximalTorus (T := Fc.obj T') (F.map j)
  exact IsMaximalTorus.image_of_centralFppfHom
    (k := S.residueField s) (G := F.obj G) (H := F.obj H)
    (T := Fc.obj T) (T' := Fc.obj T') (i := F.map i) (hi s) (F.map q)
    (hG.isConnectedReductive_residueFiber s) (hH.isConnectedReductive_residueFiber s)
    hqK (F.map j) (hj.baseChange b) (hT'.baseChange b).isTorus (Fc.map p)
    ((F.map_comp _ _).symm.trans ((congrArg F.map hsq).trans (F.map_comp _ _)))

end GeneralBase


/-- The complete proposition proved by the supplied helper, with every hypothesis explicit. -/
def RelativeCentralSurjectionMaximalImageStatement : Prop :=
  ∀
    {S : Scheme.{u}} {G H : GroupScheme S}
    {T T' : CommGroupScheme S}

    {i : T.toGrp ⟶ G} (_hi : IsFibrewiseMaximalTorus i)
    (q : G ⟶ H) (_hG : IsReductive G) (_hH : IsReductive H)
    [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    [LocallyOfFinitePresentation q.hom.hom.left]
    (_hq : IsCentral (kernelι q))
    (j : T'.toGrp ⟶ H) (_hj : IsClosedSubgroup j)
    (_hT' : RelativeTorus.IsTorus T'.toGrp)
    (p : T ⟶ T')
    [Flat (CommGroupScheme.groupHom p).hom.hom.left]
    [Surjective (CommGroupScheme.groupHom p).hom.hom.left]
    [LocallyOfFinitePresentation (CommGroupScheme.groupHom p).hom.hom.left]
    (_hsq : CommGroupScheme.groupHom p ≫ j = i ≫ q),
    IsFibrewiseMaximalTorus j

/-- The retained helper proof establishes the named proposition. -/
theorem relativeCentralSurjectionMaximalImage : RelativeCentralSurjectionMaximalImageStatement.{u} := by
  unfold RelativeCentralSurjectionMaximalImageStatement
  exact @IsFibrewiseMaximalTorus.image_of_centralFppfHom.{u}

end Langlands.GroupScheme
