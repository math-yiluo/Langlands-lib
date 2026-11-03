import Langlands.GroupScheme.Reductive.CenterStructureStatement
import Langlands.GroupScheme.SubgroupBaseChange

/-! # Scheme-theoretic centre field base change: proof -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {S S' : Scheme.{u}} (b : S' ⟶ S)

/-- Restriction along a morphism of test schemes preserves commuting points. -/
theorem commute_comp {G : GroupScheme S} {U V : Over S} (c : U ⟶ V) {x y : V ⟶ G.X}
    (h : Commute x y) : Commute (c ≫ x) (c ≫ y) := by
  change (c ≫ x) * (c ≫ y) = (c ≫ y) * (c ≫ x)
  rw [← MonObj.comp_mul, ← MonObj.comp_mul, h.eq]

/-- The all-test centre functor commutes with arbitrary base change. -/
theorem center_baseChange (G : GroupScheme S) :
    center ((GroupScheme.baseChange b).obj G) = (center G).baseChange b := by
  ext T x
  rw [SubgroupFunctor.mem_baseChange, mem_center, mem_center]
  constructor
  · intro hx U c h
    let U' : Over S' := Over.mk (c.left ≫ T.hom)
    let a : U' ⟶ T := Over.homMk c.left rfl
    let e : U ≅ (Over.map b).obj U' := Over.isoMk (Iso.refl _) (by
      simpa [U'] using Over.w c)
    have hc : e.hom ≫ (Over.map b).map a = c := by
      ext
      simp [e, a]
    have h1 := (hx U' a ((baseChangePointsEquiv b G U').symm (e.inv ≫ h))).map
      (baseChangePointsEquiv b G U').toMonoidHom
    simp only [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply,
      baseChangePointsEquiv_naturality] at h1
    have h2 := commute_comp e.hom h1
    rwa [← Category.assoc, hc, Iso.hom_inv_id_assoc] at h2
  · intro hx T' a h
    have h1 := hx ((Over.map b).obj T') ((Over.map b).map a) (baseChangePointsEquiv b G T' h)
    rw [← baseChangePointsEquiv_naturality] at h1
    simpa using h1.map (baseChangePointsEquiv b G T').symm.toMonoidHom

/-- Every scheme-theoretic centre inclusion of a connected reductive group remains one after
an arbitrary field extension. -/
theorem schemeTheoreticCenterBaseChangeStatement :
    SchemeTheoreticCenterBaseChangeStatement.{u} := by
  intro k K _ _ _ G Z z _ hz
  refine ⟨hz.1.baseChange (algebraBaseMap k K), ?_⟩
  rw [SubgroupFunctor.range_baseChangeHom, hz.2, center_baseChange]

end Langlands.GroupScheme
