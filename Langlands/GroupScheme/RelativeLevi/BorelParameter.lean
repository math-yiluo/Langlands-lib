import Langlands.GroupScheme.RelativeLevi.BorelLocusStatement
import Langlands.GroupScheme.Reductive.BaseChange
import Langlands.GroupScheme.HomScheme.OpenParameterFamily

/-! # The actual Borel parameter scheme inside a parabolic parameter scheme -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

open TorusSubgroupModuli

namespace RelativeLevi

variable {S : Scheme.{u}} {G : GroupScheme S} {M : Over S}
variable {P : GroupScheme M.left}

/-- The open subset of a parabolic parameter scheme consisting of Borel fibres,
using the clopen Borel-locus theorem as an explicit premise. -/
def borelParameterOpens
    (hcl : RelativeBorelLocusClopenStatement.{u}) (hG : IsReductive G)
    (j : P ⟶ (baseChange M.hom).obj G) (hj : IsRelativeParabolicSubgroup j) :
    M.left.Opens :=
  ⟨{m | IsGeometricBorelSubgroup (residueFiberHom j m)},
    (hcl M.left ((baseChange M.hom).obj G) P j (hG.baseChange M.hom) hj).isOpen⟩

/-- The actual open and closed Borel part of a supplied parabolic parameter scheme. -/
def borelParameter
    (hcl : RelativeBorelLocusClopenStatement.{u}) (hG : IsReductive G)
    (j : P ⟶ (baseChange M.hom).obj G) (hj : IsRelativeParabolicSubgroup j) :
    Over S :=
  openParameter (borelParameterOpens hcl hG j hj)

/-- The Borel part of a smooth parabolic parameter scheme is smooth. -/
theorem smooth_borelParameter
    (hcl : RelativeBorelLocusClopenStatement.{u}) (hG : IsReductive G)
    (j : P ⟶ (baseChange M.hom).obj G) (hj : IsRelativeParabolicSubgroup j)
    [Smooth M.hom] : Smooth (borelParameter hcl hG j hj).hom :=
  smooth_openParameter _

/-- The Borel part of a proper parabolic parameter scheme is proper. -/
theorem isProper_borelParameter
    (hcl : RelativeBorelLocusClopenStatement.{u}) (hG : IsReductive G)
    (j : P ⟶ (baseChange M.hom).obj G) (hj : IsRelativeParabolicSubgroup j)
    [IsProper M.hom] : IsProper (borelParameter hcl hG j hj).hom :=
  isProper_openParameter (borelParameterOpens hcl hG j hj)
    (hcl M.left ((baseChange M.hom).obj G) P j (hG.baseChange M.hom) hj).isClosed

end RelativeLevi

end Langlands.GroupScheme
