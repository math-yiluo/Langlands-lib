import Langlands.GroupScheme.IdentityComponentRationalTransport
import Langlands.GroupScheme.IntegralModel

/-! # Extension of the field on rational identity-component quotients -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IdentityComponent

variable {k L : Type u} [Field k] [Field L]
  (H : GroupScheme (Spec (CommRingCat.of k)))
  [Smooth H.X.hom] [IsAffineHom H.X.hom] (φ : k →+* L)

/-- Extension of the ground field preserves the actual identity-component subgroup. -/
theorem baseChangeSectionHom_mem_rationalIdentitySubgroup
    {x : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ H.X}
    (hx : x ∈ rationalIdentitySubgroup H) :
    baseChangeSectionHom (specMap φ) H x ∈
      rationalIdentitySubgroup ((GroupScheme.baseChange (specMap φ)).obj H) := by
  rcases (mem_rationalIdentitySubgroup H x).mp hx with ⟨y, rfl⟩
  apply (mem_rationalIdentitySubgroup _ _).mpr
  refine ⟨baseChangeSectionHom (specMap φ) (identityComponent H) y ≫
    (baseChangeIso H φ).hom.hom.hom, ?_⟩
  rw [Category.assoc, ← Grp.comp_hom_hom, baseChangeIso_hom_identityComponentι]
  exact (baseChangeSectionHom_naturality (specMap φ) (identityComponentι H) y).symm

/-- The induced homomorphism on ordinary rational-component quotient groups. -/
def rationalComponentBaseChange :
    RationalComponentQuotient H →*
      RationalComponentQuotient ((GroupScheme.baseChange (specMap φ)).obj H) :=
  rationalComponentLift H
    ((rationalComponentProjection _).comp (baseChangeSectionHom (specMap φ) H))
    (by
      intro x hx
      change rationalComponentProjection _
        (baseChangeSectionHom (specMap φ) H x) = 1
      apply MonoidHom.mem_ker.mp
      rw [ker_rationalComponentProjection]
      exact baseChangeSectionHom_mem_rationalIdentitySubgroup H φ hx)

@[simp]
theorem rationalComponentBaseChange_projection
    (x : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ H.X) :
    rationalComponentBaseChange H φ (rationalComponentProjection H x) =
      rationalComponentProjection _ (baseChangeSectionHom (specMap φ) H x) :=
  rfl

/-- Projection of the changed scheme sends the changed rational component to the original
one. No reverse map on all rational-component quotients is asserted. -/
theorem rationalComponentEmbedding_baseChange
    (c : RationalComponentQuotient H) :
    (pullback.fst H.X.hom (specMap φ)).continuous.connectedComponentsMap
        (rationalComponentEmbedding _ (rationalComponentBaseChange H φ c)) =
      rationalComponentEmbedding H c := by
  obtain ⟨x, rfl⟩ := rationalComponentProjection_surjective H c
  change _root_.ConnectedComponents.mk
      ((pullback.fst H.X.hom (specMap φ))
        ((baseChangeSectionHom (specMap φ) H x).left (basePoint L))) =
    _root_.ConnectedComponents.mk (x.left (basePoint k))
  have h := congrArg (fun f : Spec (CommRingCat.of L) ⟶ H.X.left =>
    f (basePoint L)) (baseChangeSectionHom_fst (specMap φ) H x)
  have hb : specMap φ (basePoint L) = basePoint k := Subsingleton.elim _ _
  change (pullback.fst H.X.hom (specMap φ))
      ((baseChangeSectionHom (specMap φ) H x).left (basePoint L)) =
    x.left (specMap φ (basePoint L)) at h
  rw [hb] at h
  exact congrArg _root_.ConnectedComponents.mk h

/-- Distinct rational identity components remain distinct after any field extension. -/
theorem rationalComponentBaseChange_injective :
    Function.Injective (rationalComponentBaseChange H φ) := by
  intro c d h
  apply (rationalComponentEmbedding H).injective
  rw [← rationalComponentEmbedding_baseChange H φ c,
    ← rationalComponentEmbedding_baseChange H φ d, h]

/-- Pulling back a rational section detects its original identity-component membership. -/
theorem baseChangeSectionHom_mem_rationalIdentitySubgroup_iff
    (x : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ H.X) :
    baseChangeSectionHom (specMap φ) H x ∈
        rationalIdentitySubgroup ((GroupScheme.baseChange (specMap φ)).obj H) ↔
      x ∈ rationalIdentitySubgroup H := by
  constructor
  · intro hx
    have he : rationalComponentBaseChange H φ (rationalComponentProjection H x) =
        rationalComponentBaseChange H φ 1 := by
      rw [rationalComponentBaseChange_projection, map_one]
      apply MonoidHom.mem_ker.mp
      rw [ker_rationalComponentProjection]
      exact hx
    have hx' := rationalComponentBaseChange_injective H φ he
    have hm : x ∈ (rationalComponentProjection H).ker := hx'
    rwa [ker_rationalComponentProjection] at hm
  · exact baseChangeSectionHom_mem_rationalIdentitySubgroup H φ

variable {H}
  {H' : GroupScheme (Spec (CommRingCat.of k))}
  [Smooth H'.X.hom] [IsAffineHom H'.X.hom]

/-- Extension of the field commutes with actual homomorphisms on rational components. -/
theorem rationalComponentBaseChange_naturality (f : H ⟶ H') :
    (rationalComponentMap ((GroupScheme.baseChange (specMap φ)).map f)).comp
        (rationalComponentBaseChange H φ) =
      (rationalComponentBaseChange H' φ).comp (rationalComponentMap f) := by
  apply rationalComponentHom_ext
  intro x
  simp only [MonoidHom.comp_apply, rationalComponentBaseChange_projection,
    rationalComponentMap_projection, baseChangeSectionHom_naturality]

end Langlands.GroupScheme.IdentityComponent
