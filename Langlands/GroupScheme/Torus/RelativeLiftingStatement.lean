import Langlands.GroupScheme.Torus.Split
import Langlands.AbelianScheme.Tate.BaseChangeCoherence
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Lifting an actual split torus from a residue fibre -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- A closed split torus in a residue fibre of a smooth affine group lifts to a
split torus over an etale neighbourhood with a residue-field-valued point.
The lifted inclusion recovers the specified inclusion under the actual
base-change composition and equality comparisons. -/
def RelativeSplitTorusLiftingStatement : Prop :=
  ∀ (S : Scheme.{u}) (G : GroupScheme S) [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (s : S) (T₀ : GroupScheme (Spec (S.residueField s))),
    IsSplitTorus T₀ →
    ∀ (i₀ : T₀ ⟶ (baseChange (S.fromSpecResidueField s)).obj G),
      IsClosedImmersion i₀.hom.hom.left →
      ∃ (U : Scheme.{u}) (p : U ⟶ S), Etale p ∧
        ∃ (b : Spec (S.residueField s) ⟶ U)
          (hb : b ≫ p = S.fromSpecResidueField s)
          (T : GroupScheme U),
          IsSplitTorus T ∧
          ∃ (i : T ⟶ (baseChange p).obj G), IsClosedImmersion i.hom.hom.left ∧
            ∃ (e : (baseChange b).obj T ≅ T₀),
              (baseChange b).map i ≫ (baseChangeCompIso p b G).inv ≫
                (eqToIso (congrArg (fun f => (baseChange f).obj G) hb)).hom =
                  e.hom ≫ i₀

end Langlands.GroupScheme
