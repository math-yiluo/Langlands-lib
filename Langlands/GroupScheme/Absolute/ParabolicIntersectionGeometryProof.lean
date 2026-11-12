import Langlands.GroupScheme.Absolute.ParabolicIntersectionCommonTorus
import Langlands.GroupScheme.Absolute.TwoBorelCommonMaximalTorusProof
import Langlands.GroupScheme.Absolute.BorelOvergroupCocharacterProof
import Langlands.GroupScheme.Dynamic.ConnectedProof
import Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof
import Langlands.GroupScheme.Torus.SplitReflection
import Langlands.GroupScheme.Reductive.AlgebraicExtensionAscent

/-! # The geometry of the intersection of two rational parabolics -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme

/-- Over an algebraically closed field, a smooth closed overgroup of a Borel pair is,
on every test scheme, the dynamic parabolic of an integral cocharacter of the pair's
torus. -/
theorem exists_range_eq_dynamicParabolic_of_isBorelPair
    {k : Type u} [Field k] [IsAlgClosed k]
    {G : GroupScheme (Spec (CommRingCat.of k))} (hG : IsConnectedReductive G)
    {T : CommGroupScheme (Spec (CommRingCat.of k))} (hT : IsSplitTorus T.toGrp)
    (j : T.toGrp ⟶ G) {P : GroupScheme (Spec (CommRingCat.of k))} [Smooth P.X.hom]
    (i : P ⟶ G) (hi : IsClosedSubgroup i)
    {B : GroupScheme (Spec (CommRingCat.of k))} (b : B ⟶ P)
    (hpair : IsBorelPair (b ≫ i) j) :
    ∃ ζ : cocharacterLattice T,
      SubgroupFunctor.range i = Dynamic.parabolic (CommGroupScheme.groupHom ζ ≫ j) := by
  have : IsAffineHom G.X.hom := hG.isAffineHom
  let := hpair.2.1.2.1.mono
  obtain ⟨ν, hν, hpos, hflip⟩ :=
    AbsoluteBorelOvergroup.exists_regularCocharacter_support_and_inverters
      hG hT j i hi b hpair
  obtain ⟨ζ, hζ⟩ :=
    AbsoluteBorelOvergroup.exists_cocharacter_of_rootSupport_negators
      j hG hT hpair.2.1
      (RelativeRoot.actionWeightSupport (AutomorphicAction.conjugation j)
        (SubgroupFunctor.range i))
      ν hν hpos (by
        intro α hα hplus hminus
        obtain ⟨w, hwα, hw⟩ := hflip α hα hplus hminus
        exact ⟨w, hwα, fun β _ => hw β⟩)
  exact ⟨ζ, borelOvergroup_eq_dynamicParabolic_of_rootSupport hG hT j i hi b hpair ζ hζ⟩

/-- Over an algebraically closed field, two smooth closed subgroups of a connected
reductive group through which Borel subgroups factor form a common-torus parabolic
pair. -/
theorem isCommonTorusParabolicPair_of_borel
    {K : Type u} [Field K] [IsAlgClosed K]
    {G P P' B B' : GroupScheme (Spec (CommRingCat.of K))} (hG : IsConnectedReductive G)
    [Smooth P.X.hom] [Smooth P'.X.hom]
    (j : P ⟶ G) (j' : P' ⟶ G) (hj : IsClosedSubgroup j) (hj' : IsClosedSubgroup j')
    (f : B ⟶ P) (f' : B' ⟶ P')
    (hB : IsBorelSubgroup (f ≫ j)) (hB' : IsBorelSubgroup (f' ≫ j')) :
    IsCommonTorusParabolicPair j j' := by
  obtain ⟨T, t, g, g', ht, hg, hg'⟩ :=
    twoBorelCommonMaximalTorus K G hG B B' (f ≫ j) (f' ≫ j') hB hB'
  have hT : IsSplitTorus T.toGrp :=
    ht.1.isSplitTorus_of_finiteGaloisSplitting torusFiniteGaloisSplitting
  obtain ⟨ν, hν⟩ :=
    exists_range_eq_dynamicParabolic_of_isBorelPair hG hT t j hj f ⟨hB, ht, g, hg⟩
  obtain ⟨ν', hν'⟩ :=
    exists_range_eq_dynamicParabolic_of_isBorelPair hG hT t j' hj' f' ⟨hB', ht, g', hg'⟩
  exact ⟨T, t, ν, ν', ht, hν, hν'⟩

/-- The base changes to the algebraic closure of two rational parabolics of a connected
reductive group form a common-torus parabolic pair. -/
theorem isCommonTorusParabolicPair_baseChange
    {k : Type u} [Field k] {G P P' : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsConnectedReductive G) (j : P ⟶ G) (j' : P' ⟶ G)
    (hj : IsParabolicSubgroup j) (hj' : IsParabolicSubgroup j') :
    IsCommonTorusParabolicPair ((GroupScheme.baseChange (toAlgebraicClosure k)).map j)
      ((GroupScheme.baseChange (toAlgebraicClosure k)).map j') := by
  let F := GroupScheme.baseChange (toAlgebraicClosure k)
  have hGc : IsConnectedReductive (F.obj G) := hG.baseChange_of_algebraicExtension
  have := hj.smooth
  have := hj'.smooth
  have : Smooth (F.obj P).X.hom := by
    change Smooth (pullback.snd P.X.hom (toAlgebraicClosure k))
    infer_instance
  have : Smooth (F.obj P').X.hom := by
    change Smooth (pullback.snd P'.X.hom (toAlgebraicClosure k))
    infer_instance
  obtain ⟨B, jB, f, hB, hf⟩ := hj.exists_isBorelSubgroup
  obtain ⟨B', jB', f', hB', hf'⟩ := hj'.exists_isBorelSubgroup
  subst hf hf'
  exact isCommonTorusParabolicPair_of_borel hGc (F.map j) (F.map j')
    (hj.isClosedSubgroup.baseChange _) (hj'.isClosedSubgroup.baseChange _) f f' hB hB'

/-- **Geometry of two-parabolic intersections.** The actual intersection of two rational
parabolics of a connected reductive group over any field is smooth, geometrically
connected, and geometrically contains an ambient maximal torus. -/
theorem parabolicIntersectionGeometry : ParabolicIntersectionGeometryStatement.{u} :=
  parabolicIntersectionGeometry_of_commonTorus dynamicConnected
    fun _ _ _ hG _ _ j j' hj hj' => isCommonTorusParabolicPair_baseChange hG j j' hj hj'

end Langlands.GroupScheme
