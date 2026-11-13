import Langlands.GroupScheme.RelativeLevi.Basic
import Langlands.GroupScheme.Reductive.QuasiSplit

/-! # Borel subgroups and quasi-split reductive group schemes over a base scheme

These predicates transcribe Conrad, *Reductive group schemes* (2014), Definition 5.2.10.
They neither construct a Borel subgroup nor assert that one exists.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {S : Scheme.{u}}

open RelativeLevi

/-- A **Borel subgroup** over a base scheme (Conrad 2014, Definition 5.2.10): a parabolic
subgroup `i : B ⟶ G` over `S` in the sense of `IsRelativeParabolicSubgroup` whose fibre
`i_s : B_s ⟶ G_s` over the residue field `κ(s)` is, for every point `s` of `S`, a Borel
subgroup in the sense of `IsGeometricBorelSubgroup`: a Borel subgroup over `κ(s)` whose
base change to the algebraic closure of `κ(s)` is again a Borel subgroup. -/
structure IsRelativeBorelSubgroup {B G : GroupScheme S} (i : B ⟶ G) : Prop where
  isRelativeParabolicSubgroup : IsRelativeParabolicSubgroup i
  residueFiber : ∀ s : S, IsGeometricBorelSubgroup (residueFiberHom i s)

/-- A **quasi-split** reductive group scheme over a base scheme (Conrad 2014,
Definition 5.2.10): `G` is reductive over `S` and has a Borel subgroup over `S`. -/
structure IsRelativeQuasiSplit (G : GroupScheme S) : Prop where
  isReductive : IsReductive G
  exists_isRelativeBorelSubgroup :
    ∃ (B : GroupScheme S) (i : B ⟶ G), IsRelativeBorelSubgroup i

end Langlands.GroupScheme
