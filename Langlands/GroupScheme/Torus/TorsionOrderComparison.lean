import Langlands.AbelianScheme.TorsionFunctor
import Langlands.AlgebraicGeometry.FiniteEtale.GeometricCardinality
import Langlands.GroupScheme.Torus.IsomorphismLocus
import Mathlib.LinearAlgebra.Dimension.Free

/-! # Torsion comparisons from equality of coordinate orders -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.TorsionOrderComparison

open Langlands.AlgebraicGeometry.FiniteEtale

/-- A closed immersion between finite schemes over a field is an isomorphism
when their coordinate algebras have the same dimension. -/
def finiteFieldClosedImmersionIso {k : Type u} [Field k]
    {X Y : Over (Spec (CommRingCat.of k))}
    [IsFinite X.hom] [IsFinite Y.hom] (f : X ⟶ Y) [IsClosedImmersion f.left]
    (hdim :
      letI := coordinateAlgebra X.hom
      letI := coordinateAlgebra Y.hom
      Module.finrank k Γ(X.left, ⊤) = Module.finrank k Γ(Y.left, ⊤)) : X ≅ Y := by
  let := coordinateAlgebra X.hom
  let := coordinateAlgebra Y.hom
  have : IsAffine X.left := isAffine_of_isAffineHom X.hom
  have : IsAffine Y.left := isAffine_of_isAffineHom Y.hom
  have : Module.Finite k Γ(X.left, ⊤) := by
    exact RingHom.Finite.comp X.hom.finite_appTop
      (RingHom.Finite.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).inv).2)
  have : Module.Finite k Γ(Y.left, ⊤) := by
    exact RingHom.Finite.comp Y.hom.finite_appTop
      (RingHom.Finite.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).inv).2)
  let φ : Γ(Y.left, ⊤) →ₐ[k] Γ(X.left, ⊤) :=
    (((algΓ (CommRingCat.of k)).map f).unop).hom
  have hs : Function.Surjective φ :=
    (IsClosedImmersion.isAffine_surjective_of_isAffine f.left).2
  have hb : Function.Bijective φ :=
    OrzechProperty.bijective_of_surjective_of_finrank_le φ.toLinearMap hs hdim.symm.le
  have : IsIso f.left := IsClosedImmersion.isIso_of_injective_of_isAffine hb.1
  have : IsIso ((Over.forget _).map f) := inferInstanceAs (IsIso f.left)
  have : IsIso f := isIso_of_reflects_iso f (Over.forget _)
  exact asIso f

/-- Restricting a closed group embedding to integer torsion is still a closed
embedding, whenever both groups are separated over their base. -/
theorem torsionMap_isClosedImmersion {S : Scheme.{u}} {G H : GroupScheme S}
    [IsCommMonObj G.X] [IsCommMonObj H.X]
    [IsSeparated G.X.hom] [IsSeparated H.X.hom]
    (j : G ⟶ H) [IsClosedImmersion j.hom.hom.left] (n : ℤ) :
    IsClosedImmersion (torsionMap j n).hom.hom.left := by
  have : IsClosedImmersion
      ((torsionMap j n).hom.hom.left ≫ (torsionι H n).hom.hom.left) := by
    change IsClosedImmersion ((torsionMap j n ≫ torsionι H n).hom.hom.left)
    rw [torsionMap_ι]
    change IsClosedImmersion ((torsionι G n).hom.hom.left ≫ j.hom.hom.left)
    infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion
    (torsionMap j n).hom.hom.left (torsionι H n).hom.hom.left

/-- The canonical map on finite torsion is an isomorphism when a closed
group embedding has equal torsion coordinate dimensions over a field. -/
def torsionIsoOfFinrankEq {k : Type u} [Field k]
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    [IsCommMonObj G.X] [IsCommMonObj H.X]
    [IsSeparated G.X.hom] [IsSeparated H.X.hom]
    (j : G ⟶ H) [IsClosedImmersion j.hom.hom.left] (n : ℤ)
    [IsFinite (torsion G n).X.hom] [IsFinite (torsion H n).X.hom]
    (hdim :
      letI := coordinateAlgebra (torsion G n).X.hom
      letI := coordinateAlgebra (torsion H n).X.hom
      Module.finrank k Γ((torsion G n).X.left, ⊤) =
        Module.finrank k Γ((torsion H n).X.left, ⊤)) :
    torsion G n ≅ torsion H n := by
  have := torsionMap_isClosedImmersion j n
  let E := finiteFieldClosedImmersionIso (torsionMap j n).hom.hom hdim
  have : IsIso (torsionMap j n).hom.hom := by
    change IsIso E.hom
    infer_instance
  have : IsIso (torsionMap j n).hom.hom.left :=
    (Over.forget _).map_isIso (torsionMap j n).hom.hom
  let := TorusIsomorphismLocus.isIso_of_underlying (torsionMap j n)
  exact asIso (torsionMap j n)

end Langlands.GroupScheme.TorsionOrderComparison
