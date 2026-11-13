import Langlands.GroupScheme.IntegralModel.ClosedSubgroupIntegralPoints
import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-! # Schematic closure of a generic subgroup in an integral model -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IntegralModel

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G H : GroupScheme (Spec (CommRingCat.of K))}
  {M : IntegralModel R K H} {N : IntegralModel R K G} {j : H ⟶ G}

/-- The underlying map from the specified generic group into its integral model. -/
def genericToModel (N : IntegralModel R K G) : G.X.left ⟶ N.group.X.left :=
  N.genericIso.inv.hom.hom.left ≫
    pullback.fst N.group.X.hom (Spec.algebraMap R K)

/-- A compatible integral homomorphism realizes the schematic closure when it is a
closed immersion whose ideal-sheaf kernel is the kernel of the original generic map
`H → G → N.group`. -/
def Hom.IsSchematicClosure (φ : M.Hom N j) : Prop :=
  IsClosedSubgroup φ.hom ∧
    φ.hom.hom.hom.left.ker = (j.hom.hom.left ≫ N.genericToModel).ker

/-- Integral points of a compatible closed integral subgroup are the preimage
of the ambient integral-point subgroup under the originally specified generic map. -/
theorem Hom.integralPoints_eq_comap (φ : M.Hom N j)
    (hφ : IsClosedSubgroup φ.hom) :
    M.integralPoints = N.integralPoints.comap (rationalPoints.map j) := by
  ext g
  constructor
  · exact φ.map_mem_integralPoints
  · intro hg
    obtain ⟨x, hx⟩ := hg
    let y : rationalPoints M.genericFibre := rationalPoints.map M.genericIso.inv g
    have hy :
        rationalPoints.map (N.genericHom φ.hom) y = rationalPoints.map j g := by
      change (g ≫ M.genericIso.inv.hom.hom) ≫
        ((baseChange (Spec.algebraMap R K)).map φ.hom ≫
          N.genericIso.hom).hom.hom = g ≫ j.hom.hom
      rw [φ.generic_comm]
      calc
        _ = g ≫ (M.genericIso.inv ≫ (M.genericIso.hom ≫ j)).hom.hom := by
          simp only [Grp.comp_hom_hom, Category.assoc]
        _ = _ := by rw [Iso.inv_hom_id_assoc]
    obtain ⟨h, _, hgen⟩ :=
      N.exists_eq_of_integralPointMap_eq φ.hom hφ x y (hx.trans hy.symm)
    refine ⟨h, ?_⟩
    change baseChangeSectionHom (Spec.algebraMap R K) M.group h ≫
      M.genericIso.hom.hom.hom = g
    rw [hgen]
    change (g ≫ M.genericIso.inv.hom.hom) ≫ M.genericIso.hom.hom.hom = g
    simp only [Category.assoc, ← Grp.comp_hom_hom, Iso.inv_hom_id,
      Grp.id_hom_hom, Category.comp_id]

/-- The closure's integral-point subgroup uses the original generic inclusion. -/
theorem Hom.IsSchematicClosure.integralPoints_eq_comap {φ : M.Hom N j}
    (hφ : φ.IsSchematicClosure) :
    M.integralPoints = N.integralPoints.comap (rationalPoints.map j) :=
  φ.integralPoints_eq_comap hφ.1

end Langlands.GroupScheme.IntegralModel

namespace Langlands.GroupScheme

/-- Schematic closure constructs an actual integral model of a closed generic
subgroup inside a supplied integral model over a discrete valuation ring. -/
def IntegralModelSchematicClosureStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (G : GroupScheme (Spec (CommRingCat.of K))) (N : IntegralModel R K G)
    (H : GroupScheme (Spec (CommRingCat.of K))) (j : H ⟶ G),
    IsClosedSubgroup j →
      ∃ (M : IntegralModel R K H) (φ : M.Hom N j), φ.IsSchematicClosure

end Langlands.GroupScheme
