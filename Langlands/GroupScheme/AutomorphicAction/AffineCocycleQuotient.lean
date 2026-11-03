import Langlands.GroupScheme.AutomorphicAction.CocycleModel

/-! # Actual affine homogeneous quotients from cocycle orbits -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.AutomorphicAction.CocycleModel

variable {S : Scheme.{u}} {H G C : GroupScheme S} {a : AutomorphicAction H G}
variable (M : a.CocycleModel)

/-- An actual affine orbit with smooth surjective projection is the homogeneous
quotient of any representative of the all-test fixed subgroup. -/
def affineHomogeneousQuotientOfOrbit
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (j : C ⟶ G) (hrep : a.fixedSubgroup.IsRepresentedBy j)
    (O : Over S) [IsAffineHom O.hom]
    (p : G.X ⟶ O) (e : O ⟶ M.scheme) [Mono e]
    (he : p ≫ e = M.orbit) (hp : Smooth p.left) (hs : Surjective p.left) :
    HomogeneousQuotientFromEmbedding.HomogeneousQuotient j := by
  let : Smooth p.left := hp
  let : Surjective p.left := hs
  have hcomp : LocallyOfFinitePresentation (p.left ≫ O.hom) := by
    rw [Over.w p]
    infer_instance
  let : LocallyOfFinitePresentation (p.left ≫ O.hom) := hcomp
  have hfp : LocallyOfFinitePresentation O.hom :=
    Langlands.AlgebraicGeometry.locallyOfFinitePresentation_of_surjective_flat_comp
      p.left O.hom
  let : LocallyOfFinitePresentation O.hom := hfp
  have hqc : QuasiCompact (p.left ≫ O.hom) := by
    rw [Over.w p]
    infer_instance
  let : QuasiCompact (p.left ≫ O.hom) := hqc
  refine
    { scheme := O
      projection := p
      separated := inferInstance
      locallyOfFiniteType := inferInstance
      quasiCompact := inferInstance
      smooth_projection := hp
      surjective_projection := hs
      quasiCompact_projection := QuasiCompact.of_comp p.left O.hom
      fibers := ?_ }
  intro T g g'
  rw [← cancel_mono e, Category.assoc, Category.assoc, he, M.orbit_fibers, hrep.2]

/-- The constructed quotient uses the supplied affine orbit itself. -/
theorem affineHomogeneousQuotientOfOrbit_isAffineHom
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (j : C ⟶ G) (hrep : a.fixedSubgroup.IsRepresentedBy j)
    (O : Over S) [IsAffineHom O.hom]
    (p : G.X ⟶ O) (e : O ⟶ M.scheme) [Mono e]
    (he : p ≫ e = M.orbit) (hp : Smooth p.left) (hs : Surjective p.left) :
    IsAffineHom (M.affineHomogeneousQuotientOfOrbit j hrep O p e he hp hs).scheme.hom :=
  inferInstanceAs (IsAffineHom O.hom)

end Langlands.GroupScheme.AutomorphicAction.CocycleModel
