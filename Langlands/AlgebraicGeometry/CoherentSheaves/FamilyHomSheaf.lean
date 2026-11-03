import Langlands.AlgebraicGeometry.CoherentSheaves.IntrinsicModuleHomDescent

/-! # The sheaf of all actual coherent-family morphisms -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.CoherentSheaves.FamilyGroupoid

set_option backward.isDefEq.respectTransparency false

variable {S X : Scheme.{u}} (f : X ⟶ S) {T : Over S}
    (M N : FamilyGroupoid f T)

/-- All morphisms of actual coherent families form an fpqc sheaf on the
entire slice over the test scheme. -/
theorem homPresheaf_isSheaf_fpqc :
    Presheaf.IsSheaf (Scheme.fpqcTopology.over T.left) (homPresheaf f M N) :=
  (Presheaf.isSheaf_of_iso_iff (homPresheafIntrinsicIso f T M N)).mpr
    ((isSheaf_iff_isSheaf_of_type _ _).2
      (isSheaf_intrinsicModuleHomPresheaf_fpqc
        ((Picard.relativeProjection f).app T) M.of.obj N.of.obj))

/-- The actual family Hom presheaf is an fppf sheaf without any
additional geometric hypotheses. -/
theorem homPresheaf_isSheaf_fppf :
    Presheaf.IsSheaf (AlgebraicSpace.fppfTopology T.left) (homPresheaf f M N) :=
  (Presheaf.isSheaf_of_iso_iff (homPresheafIntrinsicIso f T M N)).mpr
    ((isSheaf_iff_isSheaf_of_type _ _).2
      (isSheaf_intrinsicModuleHomPresheaf_fppf
        ((Picard.relativeProjection f).app T) M.of.obj N.of.obj))

/-- The fppf sheaf whose underlying presheaf consists of all actual
coherent-family module maps after base change. -/
def homSheaf : AlgebraicSpace.FppfSheaf T.left :=
  ⟨homPresheaf f M N, homPresheaf_isSheaf_fppf f M N⟩

end Langlands.AlgebraicGeometry.CoherentSheaves.FamilyGroupoid
