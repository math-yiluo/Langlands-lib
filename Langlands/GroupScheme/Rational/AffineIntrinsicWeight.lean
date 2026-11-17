import Langlands.GroupScheme.Chevalley.ActualLineStabilizer
import Langlands.GroupScheme.Rational.TorusWeightFunctoriality
import Langlands.GroupScheme.AffineLinearEmbeddingCorepresentedProof
import Langlands.GroupScheme.Dynamic.Functoriality

/-! # Intrinsic weights for actual affine group homomorphisms -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

variable {R : CommRingCat.{u}} {G H : GroupScheme (Spec R)}

/-- The actual coefficient-point natural transformation of a group-scheme map. -/
abbrev affinePointsTransformation (f : G ⟶ H) : G.affinePointFunctor ⟶ H.affinePointFunctor :=
  Chevalley.affineMapNat f

@[simp] theorem affinePointsTransformation_apply (f : G ⟶ H)
    (A : CommAlgCat.{u} R) (x : G.affinePoints A) :
    (affinePointsTransformation f).app A x = x ≫ f.hom.hom := rfl

/-- The natural isomorphism on actual coefficient points induced by a group
isomorphism. -/
def affinePointsTransformationIso (eG : G ≅ H) :
    G.affinePointFunctor ≅ H.affinePointFunctor :=
  Functor.isoWhiskerLeft (algSpec R).rightOp (yonedaGrp.mapIso eG)

namespace AffineCorepresentation

open Corepresented

variable {B B' : CommAlgCat.{u} R}
  (ψ : (algSpec R).obj (op B) ≅ G.X)
  (ψ' : (algSpec R).obj (op B') ≅ H.X)

/-- The actual map and its induced polynomial/affine model map form a commuting
square. The coordinate charts need not respect addition. -/
theorem toModel_map (f : G ⟶ H) :
    toModel G ψ ≫ groupSchemeMap (corep G ψ) (corep H ψ')
      (affinePointsTransformation f) = f ≫ toModel H ψ' := by
  apply Grp.hom_ext
  apply (cancel_epi ψ.hom).mp
  apply (affinePointsEquiv H.affinePointFunctor (corep H ψ') B).injective
  change affinePointsEquiv _ _ B
    ((ψ.hom ≫ (toModel G ψ).hom.hom) ≫
      (groupSchemeMap (corep G ψ) (corep H ψ') (affinePointsTransformation f)).hom.hom) = _
  rw [groupSchemeMap_affinePoints, affinePointsEquiv_eq, affinePointsTransformation_apply,
    affinePointsEquiv_eq]
  change ((ψ.hom ≫ ψ.inv) ≫ ψ.hom) ≫ f.hom.hom =
    ((ψ.hom ≫ f.hom.hom) ≫ ψ'.inv) ≫ ψ'.hom
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

variable {I : Type u} [Fintype I] [DecidableEq I]

/-- Intrinsic weight subgroup of an actual affine group, computed in any supplied
affine presentation with any split-torus action on its actual coefficient points. -/
def intrinsicWeightSubgroup (σ : TorusAction G.affinePointFunctor I)
    (P : AddSubsemigroup (I → ℤ)) : SubgroupFunctor G :=
  (cutSubgroupFunctor (isCutOutBy_weightIdeal (corep G ψ) σ P)).comap (toModel G ψ)

/-- An actual group-scheme map equivariant on every coefficient algebra preserves
the intrinsic subgroup on every scheme test. -/
theorem map_mem_intrinsicWeightSubgroup (f : G ⟶ H)
    (σ : TorusAction G.affinePointFunctor I) (σ' : TorusAction H.affinePointFunctor I)
    (hf : TorusAction.IsEquivariant σ σ' (affinePointsTransformation f))
    (P : AddSubsemigroup (I → ℤ)) {T : Over (Spec R)} {x : T ⟶ G.X}
    (hx : x ∈ (intrinsicWeightSubgroup ψ σ P).carrier T) :
    x ≫ f.hom.hom ∈ (intrinsicWeightSubgroup ψ' σ' P).carrier T := by
  have h := groupSchemeMap_mem_weightSubgroup (corep G ψ) (corep H ψ')
    σ σ' (affinePointsTransformation f) hf P hx
  change (x ≫ (toModel G ψ).hom.hom) ≫
    (groupSchemeMap (corep G ψ) (corep H ψ') (affinePointsTransformation f)).hom.hom ∈ _ at h
  rw [Category.assoc, ← Grp.comp_hom_hom, toModel_map ψ ψ' f,
    Grp.comp_hom_hom, ← Category.assoc] at h
  exact h

/-- Forward equivariance of an actual group isomorphism identifies the intrinsic
subgroup functors on all scheme tests; inverse equivariance is derived. -/
theorem mem_intrinsicWeightSubgroup_iso_iff (eG : G ≅ H)
    (σ : TorusAction G.affinePointFunctor I) (σ' : TorusAction H.affinePointFunctor I)
    (heG : TorusAction.IsEquivariant σ σ' (affinePointsTransformation eG.hom))
    (P : AddSubsemigroup (I → ℤ)) {T : Over (Spec R)} (x : T ⟶ G.X) :
    x ≫ eG.hom.hom.hom ∈ (intrinsicWeightSubgroup ψ' σ' P).carrier T ↔
      x ∈ (intrinsicWeightSubgroup ψ σ P).carrier T := by
  constructor
  · intro hx
    have hinv : TorusAction.IsEquivariant σ' σ (affinePointsTransformation eG.inv) :=
      TorusAction.IsEquivariant.inverse σ σ' (affinePointsTransformationIso eG) heG
    have h := map_mem_intrinsicWeightSubgroup ψ' ψ eG.inv σ' σ hinv P hx
    rw [Category.assoc, ← Grp.comp_hom_hom, eG.hom_inv_id,
      Grp.id_hom_hom, Category.comp_id] at h
    exact h
  · exact map_mem_intrinsicWeightSubgroup ψ ψ' eG.hom σ σ' heG P

/-- The intrinsic subgroup of a fixed actual affine group and action is
independent of the chosen affine coordinate presentation. -/
theorem intrinsicWeightSubgroup_independent {B' : CommAlgCat.{u} R}
    (ψ' : (algSpec R).obj (op B') ≅ G.X)
    (σ : TorusAction G.affinePointFunctor I) (P : AddSubsemigroup (I → ℤ)) :
    intrinsicWeightSubgroup ψ σ P = intrinsicWeightSubgroup ψ' σ P := by
  have hid : TorusAction.IsEquivariant σ σ (affinePointsTransformation (𝟙 G)) := by
    intro A s x
    simp only [affinePointsTransformation_apply, Grp.id_hom_hom, Category.comp_id]
  apply SubgroupFunctor.ext
  intro T
  apply Subgroup.ext
  intro x
  have h := mem_intrinsicWeightSubgroup_iso_iff ψ ψ' (Iso.refl G) σ σ hid P x
  simpa only [Iso.refl_hom, Grp.id_hom_hom, Category.comp_id] using h.symm

end AffineCorepresentation

end Langlands.GroupScheme
