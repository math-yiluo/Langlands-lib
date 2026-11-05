import Langlands.GroupScheme.Rational.TorusGeneratedSplitGeometricRadicalAssembly

/-! # The torus quotient retained with a split geometric radical -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]

/-- An actual ground-field split geometric radical, with an actual smooth
torus quotient whose full represented kernel is that same inclusion. -/
structure SplitGeometricRadicalTorusQuotient
    (G : GroupScheme (Spec (CommRingCat.of k))) where
  radical : GroupScheme (Spec (CommRingCat.of k))
  inclusion : radical ⟶ G
  isGeometricUnipotentRadical : LeviSubgroup.IsGeometricUnipotentRadical inclusion
  isSplitUnipotent : RelativeRoot.IsSplitUnipotent radical
  quotientData : SmoothNormalQuotient inclusion
  isTorus : IsTorus quotientData.quotient

/-- Retain the descended quotient as well as the radical, conditional on the
same three structural statements as the radical-only assembly. -/
def IsTorusGenerated.splitGeometricRadicalTorusQuotientOfStructuralStatements
    (hquot : SplitTorusDominatedSolvableQuotientStatement.{u})
    (hsplit : UnipotentSplitTorusDominationStatement.{u})
    (hstable : RelativeRoot.SplitUnipotentStableVectorSubgroupStatement.{u})
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (hG : IsTorusGenerated G) (hsolv : IsSolvableGroupScheme G) :
    SplitGeometricRadicalTorusQuotient G :=
  Classical.choice (by
    let d := hG.finiteGaloisSplitDomination
    let b := algebraBaseMap k d.carrier
    let H := (GroupScheme.baseChange b).obj G
    have : Smooth H.X.hom :=
      inferInstanceAs (Smooth (pullback.snd G.X.hom b))
    have : IsAffineHom H.X.hom :=
      inferInstanceAs (IsAffineHom (pullback.snd G.X.hom b))
    have : ConnectedSpace H.X.left :=
      G.connectedSpace_baseChange_of_smooth_affine b
    have hsolvH : IsSolvableGroupScheme H :=
      solvableFieldExtensionStatement k d.carrier b G inferInstance hsolv
    have hdom : HasPointedSplitTorusDomination H :=
      ⟨d.torus, d.parametrization, d.isSplitTorus, d.dominant, d.pointed⟩
    obtain ⟨U, D, i, q, hi, hs, hc, hu, hq, hD⟩ :=
      hquot d.carrier H hsolvH hdom
    have hsU := TorusKernelDomination.representative_isSplitUnipotent_of_stableVector
      hsplit hstable i hi hs hc hu q hq hD hdom
    let r := finiteGaloisSplitTorusQuotientDescent hstable
      i hi hs hc hu hsU q hq hD
    exact ⟨{
      radical := r.val.radical
      inclusion := r.val.inclusion
      isGeometricUnipotentRadical := r.val.isGeometricUnipotentRadical
      isSplitUnipotent := r.property
      quotientData := r.val.quotientData
      isTorus := r.val.isTorus
    }⟩)

end Langlands.GroupScheme
