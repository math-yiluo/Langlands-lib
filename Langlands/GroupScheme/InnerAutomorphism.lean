import Langlands.GroupScheme.Multiplicative

noncomputable section
open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

universe u
variable {S : Scheme.{u}} (G : GroupScheme S)

/-- Pull a point over the base back to any test scheme. -/
def constantPoint (g : Over.mk (𝟙 S) ⟶ G.X) (T : Over S) : T ⟶ G.X :=
  Over.homMk T.hom (by simp) ≫ g

/-- Base points give natural families of points. -/
theorem constantPoint_naturality (g : Over.mk (𝟙 S) ⟶ G.X)
    {T T' : Over S} (a : T' ⟶ T) :
    a ≫ G.constantPoint g T = G.constantPoint g T' := by
  unfold constantPoint
  rw [← Category.assoc]
  congr 1
  apply Over.OverMorphism.ext
  exact a.w

set_option backward.isDefEq.respectTransparency false in
/-- Inner conjugation by a base point is natural on groups of points. -/
theorem constantPoint_conj_naturality (g : Over.mk (𝟙 S) ⟶ G.X)
    {T T' : Over S} (a : T' ⟶ T) (x : T ⟶ G.X) :
    MulAut.conj (G.constantPoint g T') (a ≫ x) =
      a ≫ MulAut.conj (G.constantPoint g T) x := by
  change MulAut.conj (G.constantPoint g T') (a ≫ x) =
    (G.points.map a.op).hom (MulAut.conj (G.constantPoint g T) x)
  rw [MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]
  change _ = (a ≫ G.constantPoint g T) * (a ≫ x) * (a ≫ G.constantPoint g T)⁻¹
  rw [G.constantPoint_naturality]

/-- The group-scheme inner automorphism induced by a point over the base. -/
def innerIso (g : Over.mk (𝟙 S) ⟶ G.X) : G ≅ G :=
  isoOfPoints (fun T => MulAut.conj (G.constantPoint g T))
    (fun a x => G.constantPoint_conj_naturality g a x)

/-- Inner automorphisms act by the prescribed conjugation on every test scheme. -/
theorem comp_innerIso_hom (g : Over.mk (𝟙 S) ⟶ G.X)
    (T : Over S) (x : T ⟶ G.X) :
    x ≫ (G.innerIso g).hom.hom.hom =
      G.constantPoint g T * x * (G.constantPoint g T)⁻¹ := by
  exact comp_isoOfPoints_hom _ _ T x

end Langlands.GroupScheme
