import Langlands.AlgebraicGeometry.ComponentDenseOpenGeometry
import Langlands.AlgebraicGeometry.FiniteSeparableComponentSplittingStatement
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Reduction of finite separable component splitting to compact schemes -/

universe u

open Set Topology TopologicalSpace CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.SchemeFiberGeometry

variable {X S T : Scheme.{u}}

/-- The scalar extension of an open subscheme is the inverse-image open
in the scalar extension of the ambient scheme. -/
noncomputable def baseChangeOpenIso (f : X ⟶ S) (e : T ⟶ S) (V : X.Opens) :
    pullback (V.ι ≫ f) e ≅ (pullback.fst f e ⁻¹ᵁ V).toScheme :=
  (pullbackRightPullbackFstIso f e V.ι).symm ≪≫
    pullbackSymmetry V.ι (pullback.fst f e) ≪≫
      pullbackRestrictIsoRestrict (pullback.fst f e) V

@[reassoc (attr := simp)]
theorem baseChangeOpenIso_hom_ι (f : X ⟶ S) (e : T ⟶ S) (V : X.Opens) :
    (baseChangeOpenIso f e V).hom ≫ (pullback.fst f e ⁻¹ᵁ V).ι =
      (pullbackRightPullbackFstIso f e V.ι).inv ≫
        pullback.snd V.ι (pullback.fst f e) := by
  simp [baseChangeOpenIso, Category.assoc]

@[reassoc (attr := simp)]
theorem baseChangeOpenIso_hom_ι_snd (f : X ⟶ S) (e : T ⟶ S) (V : X.Opens) :
    (baseChangeOpenIso f e V).hom ≫
        (pullback.fst f e ⁻¹ᵁ V).ι ≫ pullback.snd f e =
      pullback.snd (V.ι ≫ f) e := by
  rw [baseChangeOpenIso_hom_ι_assoc]
  simp

/-- Splitting on a generic-point open suffices after a flat field base change. -/
theorem componentsGeometricallyIrreducible_of_open_baseChange
    {K L : Type u} [Field K] [Field L]
    (f : X ⟶ Spec (.of K)) (e : Spec (.of L) ⟶ Spec (.of K))
    (V : X.Opens) (hV : genericPoints X ⊆ V)
    (h : ComponentsGeometricallyIrreducible (pullback.snd (V.ι ≫ f) e)) :
    ComponentsGeometricallyIrreducible (pullback.snd f e) := by
  apply ComponentsGeometricallyIrreducible.of_open_containing_genericPoints
    (pullback.snd f e) (pullback.fst f e ⁻¹ᵁ V)
    (genericPoints_subset_preimage_of_flat (pullback.fst f e) V hV)
  exact h.of_iso (baseChangeOpenIso f e V) (baseChangeOpenIso_hom_ι_snd f e V)

/-- The exact unrestricted splitting proposition follows from its compact-scheme case. -/
theorem finiteSeparableComponentSplitting_of_compactSpace
    (hqc : ∀ (K : Type u) [Field K] {Y : Scheme.{u}}
      (g : Y ⟶ Spec (.of K)) [LocallyOfFiniteType g]
      [CompactSpace Y] [Finite (irreducibleComponents Y)],
      ∃ (L : Type u) (_ : Field L) (_ : Algebra K L),
        FiniteDimensional K L ∧ Algebra.IsSeparable K L ∧
        ComponentsGeometricallyIrreducible
          (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap K L))))) :
    FiniteSeparableComponentSplitting.{u} := by
  intro K _ X f _ _
  let V := genericPointCompactOpen X
  have : CompactSpace V.val.toScheme :=
    isCompact_iff_compactSpace.mp V.property.1
  have : IsLocallyNoetherian V.val.toScheme :=
    LocallyOfFiniteType.isLocallyNoetherian (V.val.ι ≫ f)
  have : IsNoetherian V.val.toScheme := ⟨⟩
  have : Finite (irreducibleComponents V.val.toScheme) :=
    (finite_irreducibleComponents_of_isNoetherian).to_subtype
  obtain ⟨L, hL, aL, hfin, hsep, hsplit⟩ := hqc K (V.val.ι ≫ f)
  exact ⟨L, hL, aL, hfin, hsep,
    componentsGeometricallyIrreducible_of_open_baseChange f
      (Spec.map (CommRingCat.ofHom (algebraMap K L))) V.val V.property.2 hsplit⟩

end Langlands.AlgebraicGeometry.SchemeFiberGeometry
