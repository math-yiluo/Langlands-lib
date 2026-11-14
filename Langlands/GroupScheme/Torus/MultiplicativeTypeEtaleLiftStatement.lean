import Langlands.GroupScheme.Torus.RelativeMultiplicativeType
import Langlands.AbelianScheme.Tate.BaseChangeCoherence
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Statement: lifting a multiplicative-type subgroup of a fibre to an étale neighbourhood -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

open RelativeMultiplicativeType in
/-- **Lifting subgroups of multiplicative type from a fibre** (Conrad, *Reductive group
schemes* (2014), Proposition 3.1.6, with the remark after it; SGA3 XI 5.8(a)). Let `G → S`
be a smooth affine group scheme, `s ∈ S`, and `i₀ : H₀ ⟶ G_s` a closed subgroup of
multiplicative type of the fibre over `κ(s)`. There are an étale morphism `p : U ⟶ S` and a
point `b : Spec κ(s) ⟶ U` over `s` (an étale neighbourhood of `s` with trivial residue-field
extension), a group `H` of multiplicative type over `U` and a closed subgroup
`i : H ⟶ G_U`, whose fibre at `b` is identified with `i₀`. -/
def MultiplicativeTypeEtaleLiftStatement : Prop :=
  ∀ (S : Scheme.{u}) (G : GroupScheme S) [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (s : S) (H₀ : GroupScheme (Spec (S.residueField s))),
    IsMultiplicativeType H₀ →
    ∀ (i₀ : H₀ ⟶ (baseChange (S.fromSpecResidueField s)).obj G),
      IsClosedImmersion i₀.hom.hom.left →
      ∃ (U : Scheme.{u}) (p : U ⟶ S), Etale p ∧
        ∃ (b : Spec (S.residueField s) ⟶ U)
          (hb : b ≫ p = S.fromSpecResidueField s)
          (H : GroupScheme U),
          IsMultiplicativeType H ∧
          ∃ (i : H ⟶ (baseChange p).obj G), IsClosedImmersion i.hom.hom.left ∧
            ∃ (e : (baseChange b).obj H ≅ H₀),
              (baseChange b).map i ≫ (baseChangeCompIso p b G).inv ≫
                (eqToIso (congrArg (fun f => (baseChange f).obj G) hb)).hom =
                  e.hom ≫ i₀

end Langlands.GroupScheme
