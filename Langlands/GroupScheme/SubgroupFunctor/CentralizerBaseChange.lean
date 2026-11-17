import Langlands.GroupScheme.Derived.CentralIntersectionReduction
import Langlands.GroupScheme.SubgroupFunctor.NormalizerBaseChange
import Langlands.GroupScheme.Dynamic.Functoriality

/-! # Base change of all-test centralizers and represented preimages -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SubgroupFunctor

variable {S S' : Scheme.{u}} {G H C : GroupScheme S}

/-- Centralizing points remain centralizing after arbitrary base change. -/
theorem centralizer_baseChange_le (b : S' ⟶ S) (F : SubgroupFunctor G) :
    F.centralizer.baseChange b ≤ (F.baseChange b).centralizer := by
  intro U g hg V a x hx
  change baseChangePointsEquiv b G U g ∈ F.centralizer.carrier _ at hg
  have h := hg ((Over.map b).obj V) ((Over.map b).map a)
    (baseChangePointsEquiv b G V x) hx
  apply (baseChangePointsEquiv b G V).injective
  simpa only [map_mul, baseChangePointsEquiv_naturality] using h.eq

/-- Centralization after base change still tests every refinement over the
original base. -/
theorem centralizer_le_baseChange (b : S' ⟶ S) (F : SubgroupFunctor G) :
    (F.baseChange b).centralizer ≤ F.centralizer.baseChange b := by
  intro U g hg
  change baseChangePointsEquiv b G U g ∈ F.centralizer.carrier _
  intro V a x hx
  let W : Over S' := Over.mk (a.left ≫ U.hom)
  let e : (Over.map b).obj W ≅ V := Over.isoMk (Iso.refl _) (by
    change (𝟙 V.left) ≫ V.hom = (a.left ≫ U.hom) ≫ b
    have hw : a.left ≫ (U.hom ≫ b) = V.hom := a.w
    simpa only [Category.id_comp, Category.assoc] using hw.symm)
  let a' : W ⟶ U := Over.homMk a.left rfl
  let y := (baseChangePointsEquiv b G W).symm (e.hom ≫ x)
  have hy : y ∈ (F.baseChange b).carrier W := by
    change baseChangePointsEquiv b G W
      ((baseChangePointsEquiv b G W).symm (e.hom ≫ x)) ∈ F.carrier _
    rw [MulEquiv.apply_symm_apply]
    exact F.comp_mem e.hom hx
  have h := hg W a' y hy
  have ha : (Over.map b).map a' = e.hom ≫ a := by
    apply Over.OverMorphism.ext
    change a.left = (𝟙 V.left) ≫ a.left
    simp only [Category.id_comp]
  have he : e.hom ≫ ((a ≫ baseChangePointsEquiv b G U g) * x) =
      e.hom ≫ (x * (a ≫ baseChangePointsEquiv b G U g)) := by
    simpa only [map_mul, baseChangePointsEquiv_naturality, y,
      MulEquiv.apply_symm_apply, ha, MonObj.comp_mul, Category.assoc] using
        congrArg (baseChangePointsEquiv b G W) h.eq
  have he' := congrArg (fun z => e.inv ≫ z) he
  simpa only [Commute, SemiconjBy, Iso.inv_hom_id_assoc] using he'

/-- All-test centralizers of arbitrary subgroup functors commute with every
change of base. -/
theorem centralizer_baseChange (b : S' ⟶ S) (F : SubgroupFunctor G) :
    F.centralizer.baseChange b = (F.baseChange b).centralizer :=
  le_antisymm (centralizer_baseChange_le b F) (centralizer_le_baseChange b F)

/-- The base-change point equivalence restricted to all-test centralizers. -/
def centralizerBaseChangeEquiv (b : S' ⟶ S) (F : SubgroupFunctor G) (U : Over S') :
    (F.baseChange b).centralizer.carrier U ≃*
      F.centralizer.carrier ((Over.map b).obj U) := by
  rw [← centralizer_baseChange]
  exact baseChangeCarrierEquiv b F.centralizer U

/-- Given monic representatives and a commuting inclusion, the smaller
representative is the preimage of its ambient subgroup functor. -/
theorem IsRepresentedBy.comap_of_comp {E F : SubgroupFunctor G}
    {n : H ⟶ G} {c : C ⟶ G}
    (hn : E.IsRepresentedBy n) (hc : F.IsRepresentedBy c)
    (f : C ⟶ H) (hfc : f ≫ n = c) :
    (F.comap n).IsRepresentedBy f := by
  have hfc' : f.hom.hom ≫ n.hom.hom = c.hom.hom :=
    congrArg (fun a => a.hom.hom) hfc
  let : Mono c.hom.hom := hc.1
  refine ⟨mono_of_mono_fac hfc', ?_⟩
  ext U x
  rw [mem_range, mem_comap, ← hc.2, mem_range]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y, by rw [Category.assoc, hfc']⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, hn.1.right_cancellation _ _
      (by rw [Category.assoc, hfc']; exact hy)⟩

end Langlands.GroupScheme.SubgroupFunctor
