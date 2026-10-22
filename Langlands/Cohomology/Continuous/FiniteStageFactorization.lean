import Langlands.Cohomology.Continuous.FiniteQuotientComparison

noncomputable section

open CategoryTheory

universe u

namespace Langlands.Continuous

variable {k G H : Type u} [CommRing k] [TopologicalSpace k]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [DiscreteTopology H]

attribute [local instance] continuousToOrdinaryCochains_isIso continuousToOrdinary_isIso

set_option backward.isDefEq.respectTransparency false in
/-- Lift an ordinary finite-stage factorization to actual continuous cochains. -/
theorem finiteStageCochainMap_eq_of_factorization (A : DiscreteModule k G)
    (N : OpenNormalSubgroup G) (B : TopRep.{u} k H)
    (φ : G →ₜ* H) (f : TopRep.res φ B ⟶ A.toTopRep)
    (c : groupCohomology.inhomogeneousCochains (finiteQuotientRep A.toRep N) ⟶
      groupCohomology.inhomogeneousCochains (Rep.of B.ρ.toRepresentation))
    (hc : c ≫ groupCohomology.cochainsMap (φ : G →* H)
      (Rep.ofHom f.hom.toIntertwiningMap) = ordinaryInflationCochains A N) :
    finiteStageCochainMap A N = c ≫ inv (continuousToOrdinaryCochains B) ≫
      ((forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k)).mapHomologicalComplex
        (ComplexShape.up ℕ)).map (ContinuousCohomology.cochainsMap φ f) := by
  apply (cancel_mono (continuousToOrdinaryCochains A.toTopRep)).mp
  rw [finiteStageCochainMap_comp_comparison, Category.assoc, Category.assoc,
    continuousToOrdinaryCochains_naturality, ← Category.assoc
      (inv (continuousToOrdinaryCochains B)), IsIso.inv_hom_id, Category.id_comp]
  exact hc.symm

set_option backward.isDefEq.respectTransparency false in
/-- The factorization at continuous cohomology, with the actual inverse discrete comparison. -/
theorem finiteStageToContinuous_eq_of_factorization (A : DiscreteModule k G)
    (N : OpenNormalSubgroup G) (B : TopRep.{u} k H)
    (φ : G →ₜ* H) (f : TopRep.res φ B ⟶ A.toTopRep)
    (c : groupCohomology.inhomogeneousCochains (finiteQuotientRep A.toRep N) ⟶
      groupCohomology.inhomogeneousCochains (Rep.of B.ρ.toRepresentation))
    (hc : c ≫ groupCohomology.cochainsMap (φ : G →* H)
      (Rep.ofHom f.hom.toIntertwiningMap) = ordinaryInflationCochains A N) (q : ℕ) :
    finiteStageToContinuous A N q = HomologicalComplex.homologyMap c q ≫
      inv (continuousToOrdinary B q) ≫
      (forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k)).map
        (ContinuousCohomology.map φ f q) := by
  have hn := ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor (TopModuleCat.{u} k) (ComplexShape.up ℕ) q).map
      (ContinuousCohomology.cochainsMap φ f))
    (forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k))
  change HomologicalComplex.homologyMap
      (((forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k)).mapHomologicalComplex
        (ComplexShape.up ℕ)).map (ContinuousCohomology.cochainsMap φ f)) q ≫
      (((TopRep.homogeneousCochains A.toTopRep).sc q).mapHomologyIso
        (forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k))).hom =
    (((TopRep.homogeneousCochains B).sc q).mapHomologyIso
      (forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k))).hom ≫
      (forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k)).map
        (ContinuousCohomology.map φ f q) at hn
  unfold finiteStageToContinuous
  rw [finiteStageCochainMap_eq_of_factorization A N B φ f c hc,
    HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp]
  simp only [Category.assoc]
  rw [hn]
  simp only [continuousToOrdinary, IsIso.inv_comp, IsIso.Iso.inv_inv,
    HomologicalComplex.homologyMap_inv, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- The actual ordinary-cochain isomorphism induced by a quotient-group and
invariant-coefficient identification. -/
def finiteStageCochainIso (A : DiscreteModule k G)
    (N : OpenNormalSubgroup G) (B : TopRep.{u} k H)
    (e : (G ⧸ N.toSubgroup) ≃* H)
    (e' : (finiteQuotientRep A.toRep N).V ≃ₗ[k] B.V)
    (he : ∀ g, e' ∘ₗ (finiteQuotientRep A.toRep N).ρ g =
      (B.ρ (e g)).toLinearMap ∘ₗ e') :
    groupCohomology.inhomogeneousCochains (finiteQuotientRep A.toRep N) ≅
      groupCohomology.inhomogeneousCochains (Rep.of B.ρ.toRepresentation) where
  hom := groupCohomology.cochainsMap e.symm
    (Rep.ofHom ⟨e', fun h ↦ by simp [he]; rfl⟩)
  inv := groupCohomology.cochainsMap e
    (Rep.ofHom ⟨e'.symm, fun g ↦ by
      rw [e'.toLinearMap_symm_comp_eq, ← LinearMap.comp_assoc]
      simp [he, LinearMap.comp_assoc]
      rfl⟩)
  hom_inv_id := by
    rw [← groupCohomology.cochainsMap_comp, ← groupCohomology.cochainsMap_id]
    exact groupCohomology.cochainsMap_congr (by simp) (by simp [Rep.res_id])
  inv_hom_id := by
    rw [← groupCohomology.cochainsMap_comp, ← groupCohomology.cochainsMap_id]
    exact groupCohomology.cochainsMap_congr (by simp) e'.comp_symm

omit [IsTopologicalGroup G] [TopologicalSpace H] [IsTopologicalGroup H] [DiscreteTopology H] in
/-- Homology of the explicit cochain isomorphism is the existing cohomology map. -/
theorem finiteStageCochainIso_homologyMap (A : DiscreteModule k G)
    (N : OpenNormalSubgroup G) (B : TopRep.{u} k H)
    (e : (G ⧸ N.toSubgroup) ≃* H)
    (e' : (finiteQuotientRep A.toRep N).V ≃ₗ[k] B.V)
    (he : ∀ g, e' ∘ₗ (finiteQuotientRep A.toRep N).ρ g =
      (B.ρ (e g)).toLinearMap ∘ₗ e') (q : ℕ) :
    HomologicalComplex.homologyMap (finiteStageCochainIso A N B e e' he).hom q =
      (groupCohomology.mapIso e e' he q).hom := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Group and coefficient formulas identify a finite stage with inflation through a
cohomology isomorphism. -/
theorem finiteStageToContinuous_eq_mapIso (A : DiscreteModule k G)
    (N : OpenNormalSubgroup G) (B : TopRep.{u} k H)
    (e : (G ⧸ N.toSubgroup) ≃* H)
    (e' : (finiteQuotientRep A.toRep N).V ≃ₗ[k] B.V)
    (he : ∀ g, e' ∘ₗ (finiteQuotientRep A.toRep N).ρ g =
      (B.ρ (e g)).toLinearMap ∘ₗ e')
    (φ : G →ₜ* H) (f : TopRep.res φ B ⟶ A.toTopRep)
    (hφ : ∀ g, e (QuotientGroup.mk g) = φ g)
    (hf : ∀ x, f.hom (e' x) = x.val) (q : ℕ) :
    finiteStageToContinuous A N q =
      (groupCohomology.mapIso e e' he q).hom ≫
      inv (continuousToOrdinary B q) ≫
      (forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k)).map
        (ContinuousCohomology.map φ f q) := by
  apply finiteStageToContinuous_eq_of_factorization
  rw [← groupCohomology.cochainsMap_comp]
  apply groupCohomology.cochainsMap_congr
  · ext g
    exact e.symm_apply_eq.mpr (hφ g).symm
  · ext x
    exact hf x

end Langlands.Continuous
