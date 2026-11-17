import Langlands.GroupScheme.SubgroupPreimageQuotient
import Langlands.GroupScheme.Torus.RelativeMultiplicativeTypeFlat
import Langlands.GroupScheme.Torus.MultiplicativeTypeFpqcExtensionStatement
import Langlands.GroupScheme.Rational.CentralSubgroupGeometry

/-! # Reduction of multiplicative-type preimages to the extension theorem -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.SubgroupPreimage

variable {S : Scheme.{u}} {G Q H K : GroupScheme S}
    (q : G ⟶ Q) (j : K ⟶ Q) (h : H ⟶ G)
    [IsAffineHom G.X.hom]
    [LocallyOfFinitePresentation H.X.hom]
    [LocallyOfFinitePresentation K.X.hom] [IsAffineHom K.X.hom]

/-- A central actual preimage of multiplicative-type groups is of multiplicative
type, conditional on the published extension statement. -/
theorem isMultiplicativeType_of_isCentral_inclusion
    (hExt : MultiplicativeTypeFpqcExtensionStatement.{u})
    (hh : IsClosedSubgroup h) (hj : IsClosedSubgroup j)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range h) q)
    (hH : RelativeMultiplicativeType.IsMultiplicativeType H)
    (hK : RelativeMultiplicativeType.IsMultiplicativeType K)
    (hC : IsCentral (inclusion q j)) :
    RelativeMultiplicativeType.IsMultiplicativeType (groupScheme q j) := by
  let : IsClosedImmersion h.hom.hom.left := hh
  let : Mono h.hom.hom := Over.mono_of_mono_left _
  let : IsClosedImmersion j.hom.hom.left := hj
  let : Mono j.hom.hom := Over.mono_of_mono_left _
  let : Mono (inclusion q j).hom.hom := (isRepresentedBy_inclusion q j).1
  let : IsAffineHom H.X.hom := by
    rw [← Over.w h.hom.hom]
    infer_instance
  let : Flat H.X.hom := hH.flat
  let : Flat K.X.hom := hK.flat
  let : Flat q.hom.hom.left := hq.1
  let : LocallyOfFinitePresentation q.hom.hom.left := hq.2.2.1
  let : Flat (groupScheme q j).X.hom := flat q j
  let : LocallyOfFinitePresentation (groupScheme q j).X.hom :=
    locallyOfFinitePresentation q j
  let : IsAffineHom (groupScheme q j).X.hom := isAffineHom q j hj
  let : IsCommMonObj (groupScheme q j).X := hC.isCommMonObj
  apply (hExt S).2 H (groupScheme q j) K
    (quotientKernelInclusion q j h hq) (projection q j)
    (by infer_instance) (isFppfQuotient_projection_of_kernel q j h hq) hH hK
  intro s
  exact Or.inr (Functor.isCommMonObj_obj
    (F := Over.pullback (S.fromSpecResidueField s)) (M := (groupScheme q j).X))

/-- The same reduction applies to every representative of the inverse-image
subgroup, using its comparison with the actual preimage. -/
theorem isMultiplicativeType_represented_of_isCentral_inclusion
    (hExt : MultiplicativeTypeFpqcExtensionStatement.{u})
    (hh : IsClosedSubgroup h) (hj : IsClosedSubgroup j)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range h) q)
    (hH : RelativeMultiplicativeType.IsMultiplicativeType H)
    (hK : RelativeMultiplicativeType.IsMultiplicativeType K)
    (hC : IsCentral (inclusion q j))
    {P : GroupScheme S} {p : P ⟶ G}
    (hp : ((SubgroupFunctor.range j).comap q).IsRepresentedBy p) :
    RelativeMultiplicativeType.IsMultiplicativeType P := by
  let : IsClosedImmersion j.hom.hom.left := hj
  let : Mono j.hom.hom := Over.mono_of_mono_left _
  exact RelativeMultiplicativeType.IsMultiplicativeType.of_iso
    (representedIso q j hp)
    (isMultiplicativeType_of_isCentral_inclusion q j h hExt hh hj hq hH hK hC)

end Langlands.GroupScheme.SubgroupPreimage
