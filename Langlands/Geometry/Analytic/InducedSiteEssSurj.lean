import Langlands.Geometry.Analytic.InducedSiteBase

/-! # Induction on equivariant quasi-étale sites is essentially surjective -/

noncomputable section

universe u v z

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Analytic.SaturatedAtlasPresentation.InducedSpace

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {G : Type z} [Group G] {H : Subgroup G}

section QuasiEtale

variable {X : Action (LocalizedCategory.{u, max z v, max z v} (K := K)) H}
  {Y : Action (LocalizedCategory.{u, max z v, max z v} (K := K)) G}
  (π : Y ⟶ inducedAction H X)

theorem map_mem_copyDomain_of_mem_preimageDomain (c : G ⧸ H) :
    ∀ y ∈ (preimageDomain π c).carrier,
      localizedSpaceFunctor.map π.hom y ∈ (copyDomain H X c).carrier :=
  fun _ hy => hy

theorem baseHomV_eq_domainRestrict :
    baseHomV π = domainRestrict (preimageDomain π (baseCoset H)) (copyDomain H X (baseCoset H))
        π.hom (map_mem_copyDomain_of_mem_preimageDomain π (baseCoset H)) ≫
      (domainι _ (copyDomain H X (baseCoset H)) ≫ foldHom H X ≫ X.ρ (baseRep H)) :=
  (domainRestrict_comp_assoc _ _ _ _ _).symm

variable (hP : OpenPartitionCoproductStatement.{u, v, z})
  (hR : QuasiEtaleOpenRestrictionStatement.{u, max z v})

include hP hR in
/-- If `π` is quasi-étale and `Y` is Hausdorff, the morphism `π⁻¹(X_H) → X` is quasi-étale. -/
theorem quasiEtale_baseHomV [T2Space (localizedSpaceFunctor.obj Y.V)]
    (hπ : quasiEtale π.hom) : quasiEtale (baseHomV π) := by
  have := isIso_copyDomain_foldHom H X hP
  rw [baseHomV_eq_domainRestrict]
  exact MorphismProperty.RespectsIso.postcomp quasiEtale _ _
    (hR K π.hom hπ _ (isOpen_range_copy_space H X (baseCoset H)))

end QuasiEtale

/-- The inclusion of a subgroup `H` into `G`, as a continuous homomorphism; `H` carries the
subspace topology. -/
def subgroupContinuousHom [TopologicalSpace G] (H : Subgroup G) : H →ₜ* G :=
  { H.subtype with continuous_toFun := continuous_subtype_val }

section Site

variable [TopologicalSpace G] [IsTopologicalGroup G] (hH : IsOpen (H : Set G))
  (hC : ContinuityStatement.{u, v, z}) (hQ : MorphismPropertyStatement.{u, v, z})
  {X : GSpace.{u, max z v, max z v} K H}
  (W : EquivariantQuasiEtaleSite ((gSpaceInduction hH hC).obj X))

/-- The structure morphism `π : W → X_{G/H}` of an object of `Qét(X_{G/H}(G))`, as a morphism
of `G`-objects. -/
abbrev siteHom : W.left.obj ⟶ inducedAction H X.obj := W.hom.hom

/-- The `H`-space `π⁻¹(X_H)` of an object `π : W → X_{G/H}` of `Qét(X_{G/H}(G))`: the
`H`-object `baseAction π`, which is Hausdorff as a subspace of the Hausdorff space `W`, with
continuous action as an invariant domain of the restriction of `W` to `H`. -/
def baseSpace : GSpace.{u, max z v, max z v} K H :=
  ⟨baseAction (siteHom hH hC W), by
    have : T2Space (presentationOf W.left.obj.V).presentation.space := W.left.property.1
    exact ⟨inferInstanceAs (T2Space (preimageDomain (siteHom hH hC W) (baseCoset H)).carrier),
      IsContinuousAction.invariantDomainAction
        (X := (Action.res _ H.subtype).obj W.left.obj)
        (W.left.property.2.comp (subgroupContinuousHom H)) _ _⟩⟩

theorem baseSpace_obj : (baseSpace hH hC W).obj = baseAction (siteHom hH hC W) := rfl

variable (hP : OpenPartitionCoproductStatement.{u, v, z})

/-- The `H`-morphism `π⁻¹(X_H) → X`. -/
def baseSpaceHom : baseSpace hH hC W ⟶ X :=
  ObjectProperty.homMk (baseActionHom (siteHom hH hC W) hP)

variable (hR : QuasiEtaleOpenRestrictionStatement.{u, max z v})

/-- The object `π⁻¹(X_H) → X` of `Qét(X(H))` attached to an object `π : W → X_{G/H}` of
`Qét(X_{G/H}(G))`. -/
def baseObj : EquivariantQuasiEtaleSite X :=
  MorphismProperty.Over.mk ⊤ (baseSpaceHom hH hC W hP) (by
    have : T2Space (localizedSpaceFunctor.obj W.left.obj.V) := W.left.property.1
    exact (GSpace.quasiEtale_iff _).2
      (quasiEtale_baseHomV (siteHom hH hC W) hP hR ((GSpace.quasiEtale_iff _).1 W.prop)))

/-- Induction sends `π⁻¹(X_H) → X` back to `π : W → X_{G/H}`, given that the comparison
morphism `Ind(π⁻¹(X_H)) → W` is an isomorphism. -/
def baseObjIso (hI : IsIso (lift H (baseInclusion (siteHom hH hC W)))) :
    (quasiEtaleSiteInduction hH hC hQ X).obj (baseObj hH hC W hP hR) ≅ W :=
  MorphismProperty.Over.isoMk
    (ObjectProperty.isoMk _ (@asIso _ _ _ _ (lift H (baseInclusion (siteHom hH hC W))) hI))
    (ObjectProperty.hom_ext _ (lift_baseInclusion_comp (siteHom hH hC W) hP))

include hP hR in
/-- Induction on equivariant quasi-étale sites is essentially surjective, given that the
comparison morphisms `Ind(π⁻¹(X_H)) → W` are isomorphisms. -/
theorem essSurj_quasiEtaleSiteInduction_of_isIso
    (hI : ∀ {Y : Action (LocalizedCategory.{u, max z v, max z v} (K := K)) G}
      (π : Y ⟶ inducedAction H X.obj), IsIso (lift H (baseInclusion π))) :
    (quasiEtaleSiteInduction hH hC hQ X).EssSurj :=
  ⟨fun W => ⟨baseObj hH hC W hP hR, ⟨baseObjIso hH hC hQ W hP hR (hI _)⟩⟩⟩

end Site

end Langlands.Analytic.SaturatedAtlasPresentation.InducedSpace
