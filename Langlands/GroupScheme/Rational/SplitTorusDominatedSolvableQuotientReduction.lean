import Langlands.GroupScheme.Rational.SplitTorusTargetDescent
import Langlands.GroupScheme.Rational.TorusQuotientKernelDescent
import Langlands.GroupScheme.Rational.SplitTorusDominatedSolvableQuotientStatement
import Langlands.GroupScheme.Absolute.SolvableTorusQuotientStatement
import Langlands.GroupScheme.Absolute.SolvableFieldExtensionProof

/-! # Reducing split-torus-dominated quotient existence to the absolute case -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj CategoryTheory.Obj

namespace Langlands.GroupScheme

section Descent

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsReduced G.X.left] [IsAffineHom G.X.hom]
    {U D : GroupScheme (Spec (CommRingCat.of K))}

/-- Descend an actual split-torus quotient, retaining the target and source
recovery isomorphisms and the geometric radical on its full ground kernel. -/
def HasPointedSplitTorusDomination.descendSplitTorusQuotient
    (hG : HasPointedSplitTorusDomination G)
    (i : U ⟶ (GroupScheme.baseChange (algebraBaseMap k K)).obj G)
    (hi : IsClosedSubgroup i) (hs : Smooth U.X.hom)
    (hc : ConnectedSpace U.X.left) (hu : IsUnipotent U)
    (q : (GroupScheme.baseChange (algebraBaseMap k K)).obj G ⟶ D)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q)
    (hD : IsSplitTorus D) :
    Σ r : SplitTorusHomDescentData G D q, TorusQuotientKernelDescent r.hom i q :=
  let r := hG.descendSplitTorusHom hD q
  ⟨r, torusQuotientKernelDescent r.hom i hi hs hc hu q hq hD.isTorus
    r.recovery r.baseChange_hom⟩

end Descent

/-- Quotient existence over algebraically closed fields suffices for the
initial quotient of every smooth connected affine split-torus-dominated
solvable group, over an arbitrary ground field. -/
theorem splitTorusDominatedSolvableQuotient_of_solvableTorusQuotient
    (hquot : SolvableTorusQuotientStatement.{u}) :
    SplitTorusDominatedSolvableQuotientStatement.{u} := by
  intro k _ H _ _ _ hsolv hdom
  have : GeometricallyIntegral H.X.hom :=
    smoothConnectedAffineGeometry.1 k H inferInstance inferInstance inferInstance
  have : IsReduced H.X.left :=
    GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian H.X.hom
  let K := AlgebraicClosure k
  let b := algebraBaseMap k K
  let HK := (GroupScheme.baseChange b).obj H
  have : Smooth HK.X.hom :=
    inferInstanceAs (Smooth (pullback.snd H.X.hom b))
  have : IsAffineHom HK.X.hom :=
    inferInstanceAs (IsAffineHom (pullback.snd H.X.hom b))
  have : ConnectedSpace HK.X.left :=
    H.connectedSpace_baseChange_of_smooth_affine b
  have hsolvK : IsSolvableGroupScheme HK :=
    solvableFieldExtensionStatement k K b H inferInstance hsolv
  obtain ⟨U, D, i, q, hi, hs, hc, hu, _, hq, hD⟩ := hquot K HK hsolvK
  let d := hdom.descendSplitTorusQuotient i hi hs hc hu q hq hD
  let r := d.fst
  have hrad := d.snd.isGeometricUnipotentRadical.1
  exact ⟨kernel r.hom, r.target, kernelι r.hom, r.hom,
    hrad.isClosedSubgroup, hrad.smooth, hrad.connectedSpace, hrad.isUnipotent,
    d.snd.isFppfQuotient, r.isSplitTorus.isTorus⟩

end Langlands.GroupScheme
