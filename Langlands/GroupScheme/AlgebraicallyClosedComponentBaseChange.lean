import Langlands.GroupScheme.AlgebraicallyClosedComponents

/-! # Field extension on the full actual component groups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IdentityComponent

variable {k L : Type u} [Field k] [Field L] [IsAlgClosed k] [IsAlgClosed L]
  (H : GroupScheme (Spec (CommRingCat.of k)))
  [Smooth H.X.hom] [IsAffineHom H.X.hom] (φ : k →+* L)

/-- Field extension on all actual components, transported from the ordinary
rational-component quotient through the published comparison equivalences. -/
def allComponentBaseChange :
    AlgebraicallyClosedComponents H →*
      AlgebraicallyClosedComponents ((GroupScheme.baseChange (specMap φ)).obj H) :=
  (allComponentQuotientEquiv _).toMonoidHom.comp
    ((rationalComponentBaseChange H φ).comp (allComponentQuotientEquiv H).symm.toMonoidHom)

@[simp]
theorem allComponentBaseChange_quotient (q : RationalComponentQuotient H) :
    allComponentBaseChange H φ (allComponentQuotientEquiv H q) =
      allComponentQuotientEquiv _ (rationalComponentBaseChange H φ q) := by
  change allComponentQuotientEquiv _
      (rationalComponentBaseChange H φ
        ((allComponentQuotientEquiv H).symm (allComponentQuotientEquiv H q))) = _
  rw [MulEquiv.symm_apply_apply]

/-- On rational sections this is the component of the actual pulled-back section. -/
@[simp]
theorem allComponentBaseChange_ofPoint (x : rationalPoints H) :
    allComponentBaseChange H φ (allComponentOfPoint H x) =
      allComponentOfPoint _ (baseChangeSectionHom (specMap φ) H x) := by
  change allComponentBaseChange H φ
      (allComponentQuotientEquiv H (rationalComponentProjection H x)) = _
  rw [allComponentBaseChange_quotient, rationalComponentBaseChange_projection]
  rfl

/-- The actual pullback projection sends the extended component to its source. -/
theorem allComponentBaseChange_fst (c : AlgebraicallyClosedComponents H) :
    (pullback.fst H.X.hom (specMap φ)).continuous.connectedComponentsMap
        (allComponentBaseChange H φ c) = c := by
  obtain ⟨q, rfl⟩ := (allComponentQuotientEquiv H).surjective c
  rw [allComponentBaseChange_quotient, allComponentQuotientEquiv_apply,
    allComponentQuotientEquiv_apply]
  exact rationalComponentEmbedding_baseChange H φ q

/-- The extension homomorphism has the actual projection on components as a
left inverse, so distinct source components remain distinct. -/
theorem allComponentBaseChange_injective :
    Function.Injective (allComponentBaseChange H φ) := by
  intro c d h
  rw [← allComponentBaseChange_fst H φ c, ← allComponentBaseChange_fst H φ d, h]

/-- Every source component is the image of a component under the actual
pullback projection. -/
theorem componentProjection_surjective_of_isAlgClosed :
    Function.Surjective
      (pullback.fst H.X.hom (specMap φ)).continuous.connectedComponentsMap := by
  intro c
  exact ⟨allComponentBaseChange H φ c, allComponentBaseChange_fst H φ c⟩

variable {H}
  {H' : GroupScheme (Spec (CommRingCat.of k))}
  [Smooth H'.X.hom] [IsAffineHom H'.X.hom]

/-- The actual-map homomorphism agrees with the ordinary quotient map under
the full-component comparison. -/
@[simp]
theorem allComponentMap_quotient (f : H ⟶ H') (q : RationalComponentQuotient H) :
    allComponentMap f (allComponentQuotientEquiv H q) =
      allComponentQuotientEquiv H' (rationalComponentMap f q) := by
  rw [allComponentMap_apply, allComponentQuotientEquiv_apply,
    allComponentQuotientEquiv_apply, rationalComponentEmbedding_naturality]

/-- Extending the field commutes with homomorphisms of the actual group schemes. -/
theorem allComponentBaseChange_naturality (f : H ⟶ H') :
    (allComponentMap ((GroupScheme.baseChange (specMap φ)).map f)).comp
        (allComponentBaseChange H φ) =
      (allComponentBaseChange H' φ).comp (allComponentMap f) := by
  ext c
  obtain ⟨q, rfl⟩ := (allComponentQuotientEquiv H).surjective c
  simp only [MonoidHom.comp_apply, allComponentBaseChange_quotient,
    allComponentMap_quotient]
  exact congrArg (allComponentQuotientEquiv _)
    (congrArg (fun m => m q) (rationalComponentBaseChange_naturality φ f))

end Langlands.GroupScheme.IdentityComponent
