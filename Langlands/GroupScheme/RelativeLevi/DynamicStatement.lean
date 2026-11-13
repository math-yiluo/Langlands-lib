import Langlands.GroupScheme.RelativeLevi.Basic
import Langlands.GroupScheme.Dynamic.Basic

/-! # Statement: dynamic parabolic, unipotent and centralizer subgroups over a base -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Dynamic parabolic subgroups and their Levi subgroups** (Conrad, *Reductive group
schemes* (2014), Example 5.2.2 and the paragraph after Definition 5.4.2). For every scheme
`S`, reductive group scheme `G` over `S` and cocharacter `χ : 𝔾_m ⟶ G`, let `iP : P ⟶ G`,
`iU : U ⟶ G` and `iZ : Z ⟶ G` represent `P_G(χ)`, `U_G(χ)` and `Z_G(χ)`. Then `iP` is a
parabolic subgroup, every factorization `r : U ⟶ P` of `iU` through `iP` is a unipotent
radical of `P`, and every factorization `l : Z ⟶ P` of `iZ` through `iP` is a Levi
subgroup of `P`. -/
def DynamicRelativeLeviStatement : Prop :=
  ∀ (S : Scheme.{u}) (G P U Z : GroupScheme S) (χ : (Gm S).toGrp ⟶ G)
    (iP : P ⟶ G) (iU : U ⟶ G) (iZ : Z ⟶ G),
    IsReductive G →
    (Dynamic.parabolic χ).IsRepresentedBy iP →
    (Dynamic.unipotent χ).IsRepresentedBy iU →
    (Dynamic.centralizer χ).IsRepresentedBy iZ →
    IsRelativeParabolicSubgroup iP ∧
      (∀ r : U ⟶ P, r ≫ iP = iU → IsRelativeUnipotentRadical r) ∧
      (∀ l : Z ⟶ P, l ≫ iP = iZ → IsRelativeLeviSubgroup l)

end Langlands.GroupScheme
