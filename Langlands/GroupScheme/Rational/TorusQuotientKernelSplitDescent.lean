import Langlands.GroupScheme.Rational.TorusQuotientKernelSplitDomination
import Langlands.GroupScheme.Rational.SplitTorusDominationRefinement
import Langlands.GroupScheme.Rational.UnipotentSplitTorusDominationStatement
import Langlands.GroupScheme.Rational.FiniteSeparableSplitDescent
import Langlands.GroupScheme.Unipotent.BaseChange

/-! # Finite-Galois domination and conditional split series on full quotient kernels -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace RelativeRoot

/-- Split-torus domination after a finite separable extension gives split
unipotence over the original field, retaining both structural premises. -/
theorem IsSplitUnipotent.of_finiteSeparable_splitTorusDomination
    (hsplit : UnipotentSplitTorusDominationStatement.{u})
    (hstable : SplitUnipotentStableVectorSubgroupStatement.{u})
    {k : Type u} [Field k] (L : Type u) [Field L] [Algebra k L]
    [FiniteDimensional k L] [Algebra.IsSeparable k L]
    (H : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth H.X.hom] [IsAffineHom H.X.hom] [ConnectedSpace H.X.left]
    (hU : IsUnipotent H)
    (hdom : HasPointedSplitTorusDomination
      ((GroupScheme.baseChange (algebraBaseMap k L)).obj H)) :
    IsSplitUnipotent H := by
  let HL := (GroupScheme.baseChange (algebraBaseMap k L)).obj H
  have hs : Smooth HL.X.hom := by
    change Smooth (pullback.snd H.X.hom (algebraBaseMap k L))
    infer_instance
  have ha : IsAffineHom HL.X.hom := by
    change IsAffineHom (pullback.snd H.X.hom (algebraBaseMap k L))
    infer_instance
  have hc : ConnectedSpace HL.X.left :=
    H.connectedSpace_baseChange_of_smooth_affine (algebraBaseMap k L)
  have hu : IsUnipotent HL := hU.baseChange
  have hseries : IsSplitUnipotent HL := hsplit L HL hs ha hc hu hdom
  exact IsSplitUnipotent.of_finiteSeparable_of_stableVector
    hstable L H hU hseries

end RelativeRoot

namespace TorusKernelDomination

variable {k : Type u} [Field k]
    {H Q : GroupScheme (Spec (CommRingCat.of k))}

private theorem kernel_isAffineHom
    [IsAffineHom H.X.hom] (hQ : IsTorus Q) (q : H ⟶ Q) :
    IsAffineHom (kernel q).X.hom := by
  have : IsAffine Q.X.left := SplittingAssembly.isAffine_of_isTorus Q hQ
  have : IsAffineHom Q.X.hom := inferInstance
  rw [← Over.w (kernelι q).hom.hom]
  infer_instance

/-- Choose a finite Galois domination field and an actual pointed split-torus
parametrization of the full smooth connected kernel of a torus quotient. -/
def finiteGaloisKernelDomination
    [Smooth H.X.hom] [IsAffineHom H.X.hom]
    (hQ : IsTorus Q) (q : H ⟶ Q) [IsDominant q.hom.hom.left]
    [Smooth (kernel q).X.hom] [ConnectedSpace (kernel q).X.left]
    (hH : HasPointedSplitTorusDomination H) :
    FiniteGaloisSplitTorusDomination (kernel q) :=
  Classical.choice (by
    obtain ⟨D, p, hD, hd, hp⟩ := hH
    obtain ⟨L, hL, hA, hfin, hsep, hdom⟩ :=
      exists_finiteSeparable_kernel_hasPointedSplitTorusDomination
        hD hQ q p hp hd
    let : Field L := hL
    let : Algebra k L := hA
    let : Module.Finite k L := hfin
    let : Algebra.IsSeparable k L := hsep
    have : IsAffineHom (kernel q).X.hom := kernel_isAffineHom hQ q
    exact ⟨hdom.finiteGaloisRefinement k L (kernel q)⟩)

/-- The full unipotent kernel of a torus quotient of a split-torus-dominated
group is split over the original field, conditional on the exact domination
criterion and stable-vector proposition. -/
theorem kernel_isSplitUnipotent_of_stableVector
    (hsplit : UnipotentSplitTorusDominationStatement.{u})
    (hstable : RelativeRoot.SplitUnipotentStableVectorSubgroupStatement.{u})
    [Smooth H.X.hom] [IsAffineHom H.X.hom]
    (hQ : IsTorus Q) (q : H ⟶ Q) [IsDominant q.hom.hom.left]
    [Smooth (kernel q).X.hom] [ConnectedSpace (kernel q).X.left]
    (hH : HasPointedSplitTorusDomination H)
    (hU : IsUnipotent (kernel q)) :
    RelativeRoot.IsSplitUnipotent (kernel q) := by
  let d := finiteGaloisKernelDomination hQ q hH
  have : IsAffineHom (kernel q).X.hom := kernel_isAffineHom hQ q
  exact RelativeRoot.IsSplitUnipotent.of_finiteSeparable_splitTorusDomination
    hsplit hstable d.carrier (kernel q) hU
    ⟨d.torus, d.parametrization, d.isSplitTorus, d.dominant, d.pointed⟩

/-- Choose a represented split series on the same original full quotient
kernel, retaining both unproved structural propositions as explicit inputs. -/
def kernelSplitSeriesOfStableVector
    (hsplit : UnipotentSplitTorusDominationStatement.{u})
    (hstable : RelativeRoot.SplitUnipotentStableVectorSubgroupStatement.{u})
    [Smooth H.X.hom] [IsAffineHom H.X.hom]
    (hQ : IsTorus Q) (q : H ⟶ Q) [IsDominant q.hom.hom.left]
    [Smooth (kernel q).X.hom] [ConnectedSpace (kernel q).X.left]
    (hH : HasPointedSplitTorusDomination H)
    (hU : IsUnipotent (kernel q)) :
    {n : ℕ // RelativeRoot.HasSplitSeries n (kernel q)} :=
  let h := kernel_isSplitUnipotent_of_stableVector hsplit hstable hQ q hH hU
  ⟨h.choose, h.choose_spec⟩

end TorusKernelDomination

end Langlands.GroupScheme
