/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralCoefficientData
import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralPointRingMap

/-!
# Lifting the integral representation comparison to rings

(auxiliary; not a blueprint node).
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Lift the normalized comparison on the point through the monoidal adjunction.

proof.md`, Steps 3--4
(auxiliary; not a blueprint node).

Proof: the point ring-map lemma supplies the sectionwise ring map into the continuous
direct image of the completion. Transpose it through the monoidal point adjunction.
Its transpose is an additive, multiplicative, unital map. To identify its underlying
natural transformation, precompose with p.inv and apply Yoneda at the identity of
X[O_E]. The unit equation for p identifies the universal section with the adjunction
unit applied to the identity continuous function. The lifted adjunction's unit equation
and the point map's defining value identify its image with d.inv at that identity.
Yoneda gives equality on every section. The assembly proves invertibility and all
normalized projections from this specified underlying-map equation.
-/
theorem sfb_integral_ring_comparison_exists (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) (a : sfbFiniteConstantSets X ≅ sfbFiniteRepresentables X)
    (c : Cone (sfbIntegralFiniteTower l E ⋙ FintypeCat.toProfinite))
    (j : sfbIntegralProfinite l E ≅ c.pt)
    (hq : ∀ (n : ℕ) (x : Padic.coefficientExtensionIntegers l E),
      (j.hom ≫ c.π.app (op n)) x =
        Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)) x)
    (hc : IsLimit c)
    (p : ((sfbPullbackFromPoint X).obj (sfbCondensedIntegers l E).X).obj ⋙
      forget Ab.{u + 1} ≅
        uliftYoneda.{u + 1}.obj ((profiniteToProEtOf X).obj (sfbIntegralProfinite l E)))
    (d : (completedIntegralCoefficientSheafUnrestricted l E X).obj ⋙
      forget RingCat.{u + 1} ≅
        uliftYoneda.{u + 1}.obj ((profiniteToProEtOf X).obj (sfbIntegralProfinite l E)))
    (hp : ∀ (S : Profinite.{u}) (f : S ⟶ sfbIntegralProfinite l E),
      p.hom.app (op ((profiniteToProEtOf X).obj S))
        ((((sfbIntegralPointAdjunction X).unit.app (sfbCondensedIntegers l E).X).hom.app
          (op S)) (ULift.up f.hom.hom)) = ULift.up ((profiniteToProEtOf X).map f))
    (hd : ∀ (V : X.ProEtᵒᵖ)
        (f : V.unop ⟶ (profiniteToProEtOf X).obj (sfbIntegralProfinite l E)) (n : ℕ),
      (sfbIntegralFiniteRepresentation l E X a n).hom.app V
        ((limit.π (integralCoefficientSheafSystem l E X) (op n)).hom.app V
          (d.inv.app V (ULift.up f))) =
        ULift.up (f ≫ (profiniteToProEtOf X).map (j.hom ≫ c.π.app (op n)))) :
    ∃ f : (coefficientRing X (sfbCondensedIntegers l E)).X ⟶
        sfbCompletedIntegersAb l E X,
      IsMonHom f ∧ Functor.whiskerRight f.hom (forget Ab.{u + 1}) = p.hom ≫ d.inv := by
  obtain ⟨t, ht⟩ := sfb_integral_point_ring_map_exists l E X a c j hq hc d hd
  let adj := sfbIntegralPointAdjunction X
  let : adj.IsMonoidal := by
    dsimp [adj, sfbIntegralPointAdjunction]
    infer_instance
  let g := (adj.mapMon.homEquiv _ _).symm t
  refine ⟨g.hom, inferInstance, ?_⟩
  have hg : adj.unit.app (sfbCondensedIntegers l E).X ≫
      (sfbPullbackFromPointRightAdjoint X).map g.hom = t.hom := by
    have h := (adj.mapMon.homEquiv _ _).apply_symm_apply t
    exact congrArg Mon.Hom.hom h
  apply (cancel_epi p.inv).mp
  rw [← Category.assoc, p.inv_hom_id, Category.id_comp]
  apply uliftYonedaEquiv.{u + 1}.injective
  have hmap := (profiniteToProEtOf X).map_id (sfbIntegralProfinite l E)
  have hp0 := (hp (sfbIntegralProfinite l E) (𝟙 (sfbIntegralProfinite l E))).trans
    (congrArg ULift.up hmap)
  have hpi : p.inv.app (op ((profiniteToProEtOf X).obj (sfbIntegralProfinite l E)))
      (ULift.up (𝟙 _)) =
      ((adj.unit.app (sfbCondensedIntegers l E).X).hom.app (op (sfbIntegralProfinite l E)))
        (ULift.up (𝟙 (sfbIntegralProfinite l E) :
          sfbIntegralProfinite l E ⟶ sfbIntegralProfinite l E).hom.hom) := by
    exact (congrArg (fun z ↦ p.inv.app _ z) hp0.symm).trans
      (p.hom_inv_id_app_apply _ _)
  change g.hom.hom.app _ (p.inv.app _ (ULift.up (𝟙 _))) =
    d.inv.app _ (ULift.up (𝟙 _))
  rw [hpi]
  have hunit := congrArg (fun h ↦ h.hom.app (op (sfbIntegralProfinite l E))
    (ULift.up (𝟙 (sfbIntegralProfinite l E) :
      sfbIntegralProfinite l E ⟶ sfbIntegralProfinite l E).hom.hom)) hg
  change g.hom.hom.app _ _ = t.hom.hom.app _ _ at hunit
  exact hunit.trans ((ht (sfbIntegralProfinite l E) (𝟙 (sfbIntegralProfinite l E))).trans
    (congrArg (fun z ↦ d.inv.app _ (ULift.up z)) hmap))

end AlgebraicGeometry.ProEtale
