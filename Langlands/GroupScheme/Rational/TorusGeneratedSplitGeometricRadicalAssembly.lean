import Langlands.GroupScheme.Rational.TorusGeneratedSplitGeometricRadicalStatement
import Langlands.GroupScheme.Rational.SplitTorusDominatedSolvableQuotientStatement
import Langlands.GroupScheme.Absolute.SolvableFieldExtensionProof
import Langlands.GroupScheme.KernelRepresentativeTransport
import Langlands.GroupScheme.Rational.TorusQuotientKernelSplitDescent
import Langlands.GroupScheme.Rational.FiniteGaloisSplitRadicalDescent

/-! # Conditional assembly of the split geometric radical -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace TorusKernelDomination

/-- Splitness of the full categorical kernel transfers to its specified
closed representative, retaining both structural splitness inputs. -/
theorem representative_isSplitUnipotent_of_stableVector
    (hsplit : UnipotentSplitTorusDominationStatement.{u})
    (hstable : RelativeRoot.SplitUnipotentStableVectorSubgroupStatement.{u})
    {k : Type u} [Field k]
    {H U D : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth H.X.hom] [IsAffineHom H.X.hom]
    (i : U ⟶ H) (hi : IsClosedSubgroup i)
    (hs : Smooth U.X.hom) (hc : ConnectedSpace U.X.left)
    (hu : IsUnipotent U) (q : H ⟶ D)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q)
    (hD : IsTorus D) (hH : HasPointedSplitTorusDomination H) :
    RelativeRoot.IsSplitUnipotent U := by
  have : IsClosedImmersion i.hom.hom.left := hi
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  have : Smooth U.X.hom := hs
  have : ConnectedSpace U.X.left := hc
  have : Smooth (kernel q).X.hom := KernelRepresentative.smooth q i hq.2.2.2
  have : ConnectedSpace (kernel q).X.left :=
    KernelRepresentative.connectedSpace q i hq.2.2.2
  have : Surjective q.hom.hom.left := hq.2.1
  have : IsDominant q.hom.hom.left := inferInstance
  have hkernel := kernel_isSplitUnipotent_of_stableVector
    hsplit hstable hD q hH (KernelRepresentative.isUnipotent q i hq.2.2.2 hu)
  exact hkernel.of_iso (KernelRepresentative.iso q i hq.2.2.2)

end TorusKernelDomination

/-- Choose an actual split geometric radical of a torus-generated solvable
group, conditional on the initial quotient and the two splitness statements. -/
def IsTorusGenerated.splitGeometricRadicalOfStructuralStatements
    (hquot : SplitTorusDominatedSolvableQuotientStatement.{u})
    (hsplit : UnipotentSplitTorusDominationStatement.{u})
    (hstable : RelativeRoot.SplitUnipotentStableVectorSubgroupStatement.{u})
    {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (hG : IsTorusGenerated G) (hsolv : IsSolvableGroupScheme G) :
    Σ U : GroupScheme (Spec (CommRingCat.of k)),
      {i : U ⟶ G // LeviSubgroup.IsGeometricUnipotentRadical i ∧
        RelativeRoot.IsSplitUnipotent U} :=
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
    exact ⟨⟨r.val.radical, r.val.inclusion,
      r.val.isGeometricUnipotentRadical, r.property⟩⟩)

/-- The exact torus-generated split geometric radical proposition follows
from these three explicitly retained structural statements. -/
theorem torusGeneratedSplitGeometricRadical_of_structuralStatements
    (hquot : SplitTorusDominatedSolvableQuotientStatement.{u})
    (hsplit : UnipotentSplitTorusDominationStatement.{u})
    (hstable : RelativeRoot.SplitUnipotentStableVectorSubgroupStatement.{u}) :
    TorusGeneratedSplitGeometricRadicalStatement.{u} := by
  intro k _ G _ _ _ hsolv hG
  let r := hG.splitGeometricRadicalOfStructuralStatements hquot hsplit hstable hsolv
  exact ⟨r.fst, r.snd.val, r.snd.property⟩

end Langlands.GroupScheme
