import Langlands.GroupScheme.RelativeLevi.ModuliRepresentation
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-! # Statement: the relative Levi moduli is a unipotent-radical torsor -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **The torsor of relative Levi subgroups** (Conrad, *Reductive group schemes*
(2014), Corollary 5.4.6). For a parabolic subgroup of a reductive group over an
arbitrary base, its actual Levi subgroup images are represented, compatibly
with conjugation, by an fpqc torsor under the supplied relative unipotent
radical. No global Levi subgroup or section is assumed. -/
def RelativeLeviTorsorStatement : Prop :=
  ∀ (S : Scheme.{u}) (G P U : GroupScheme S) (i : P ⟶ G) (r : U ⟶ P),
    IsReductive G → IsRelativeParabolicSubgroup i →
      IsRelativeUnipotentRadical r →
        ∃ (X : Over S) (_ : ModObj U.X X)
          (ρ : RelativeLevi.ModuliRepresentation P X),
          ρ.IsEquivariant r ∧ Flat X.hom ∧ Surjective X.hom ∧
            QuasiCompact X.hom ∧ IsIso (ModObj.leftSMul U.X X)

end Langlands.GroupScheme
