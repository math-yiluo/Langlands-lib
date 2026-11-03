import Langlands.GroupScheme.Reductive.CenterBaseChangeProof
import Langlands.GroupScheme.Reductive.Semisimple
import Langlands.AbelianScheme.KernelBaseChange

/-! # Geometric centre transport for actual adjoint quotients -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {S S' : Scheme.{u}} (b : S' ⟶ S)
variable {G H Z Z' : GroupScheme S}

/-- Changing the source presentation of a centre preserves its full subgroup functor. -/
theorem IsSchemeTheoreticCenter.iso_comp {z : Z ⟶ G}
    (hz : IsSchemeTheoreticCenter z) (e : Z' ≅ Z) :
    IsSchemeTheoreticCenter (e.hom ≫ z) := by
  refine ⟨?_, ?_⟩
  · have : IsClosedImmersion z.hom.hom.left := hz.1
    have : IsIso e.hom.hom.hom.left :=
      (inferInstance : IsIso ((Over.forget _).mapIso ((Grp.forget _).mapIso e)).hom)
    change IsClosedImmersion (e.hom.hom.hom.left ≫ z.hom.hom.left)
    infer_instance
  · rw [← hz.2]
    ext T x
    constructor
    · rintro ⟨y, rfl⟩
      change T ⟶ Z'.X at y
      refine ⟨y ≫ e.hom.hom.hom, ?_⟩
      change (y ≫ e.hom.hom.hom) ≫ z.hom.hom =
        y ≫ (e.hom.hom.hom ≫ z.hom.hom)
      exact Category.assoc _ _ _
    · rintro ⟨y, hy⟩
      change T ⟶ Z.X at y
      change y ≫ z.hom.hom = x at hy
      refine ⟨y ≫ e.inv.hom.hom, ?_⟩
      change (y ≫ e.inv.hom.hom) ≫ (e.hom.hom.hom ≫ z.hom.hom) = x
      rw [← Category.assoc, Category.assoc y, ← Grp.comp_hom_hom,
        e.inv_hom_id, Grp.id_hom_hom, Category.comp_id]
      exact hy

/-- The actual kernel after pullback is the full centre when the original kernel is. -/
theorem kernelCenter_baseChange {q : G ⟶ H}
    (hq : IsSchemeTheoreticCenter (kernelι q)) :
    IsSchemeTheoreticCenter (kernelι ((GroupScheme.baseChange b).map q)) := by
  have hbc : IsSchemeTheoreticCenter ((GroupScheme.baseChange b).map (kernelι q)) := by
    refine ⟨hq.1.baseChange b, ?_⟩
    rw [SubgroupFunctor.range_baseChangeHom, hq.2, center_baseChange]
  have h := hbc.iso_comp (kernelBaseChangeIso b q).symm
  change IsSchemeTheoreticCenter
    ((kernelBaseChangeIso b q).inv ≫ (GroupScheme.baseChange b).map (kernelι q)) at h
  rwa [kernelBaseChangeIso_inv_ι] at h

/-- Points of the actual pulled-back kernel are the points of the full centre. -/
def kernelCenterBaseChangePointsEquiv {q : G ⟶ H}
    (hq : IsSchemeTheoreticCenter (kernelι q)) (T : Over S') :
    (T ⟶ (kernel ((GroupScheme.baseChange b).map q)).X) ≃*
      (center ((GroupScheme.baseChange b).obj G)).carrier T :=
  (kernelCenter_baseChange b hq).isRepresentedBy.pointsEquiv T

/-- The point identification retains the actual kernel inclusion. -/
theorem kernelCenterBaseChangePointsEquiv_val {q : G ⟶ H}
    (hq : IsSchemeTheoreticCenter (kernelι q)) {T : Over S'}
    (x : T ⟶ (kernel ((GroupScheme.baseChange b).map q)).X) :
    (kernelCenterBaseChangePointsEquiv b hq T x :
      T ⟶ ((GroupScheme.baseChange b).obj G).X) =
      x ≫ (kernelι ((GroupScheme.baseChange b).map q)).hom.hom := rfl

/-- The point identification is natural under every morphism of test schemes. -/
theorem kernelCenterBaseChangePointsEquiv_naturality {q : G ⟶ H}
    (hq : IsSchemeTheoreticCenter (kernelι q)) {T T' : Over S'} (a : T' ⟶ T)
    (x : T ⟶ (kernel ((GroupScheme.baseChange b).map q)).X) :
    (kernelCenterBaseChangePointsEquiv b hq T' (a ≫ x) :
      T' ⟶ ((GroupScheme.baseChange b).obj G).X) =
      a ≫ (kernelCenterBaseChangePointsEquiv b hq T x :
        T ⟶ ((GroupScheme.baseChange b).obj G).X) :=
  Category.assoc _ _ _

/-- Triviality of the full centre survives arbitrary base change. -/
theorem center_eq_bot_baseChange (hG : center G = ⊥) :
    center ((GroupScheme.baseChange b).obj G) = ⊥ := by
  rw [center_baseChange, hG, SubgroupFunctor.bot_baseChange]

end Langlands.GroupScheme
