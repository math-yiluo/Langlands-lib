import Mathlib.RepresentationTheory.Homological.ContCohomology.Functoriality

universe u

open CategoryTheory

namespace Langlands.Continuous

variable {k G H : Type u} [CommRing k] [TopologicalSpace k]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  {X : TopRep.{u} k G} {Y : TopRep.{u} k H}

/-- Equality of group maps and pointwise equality of coefficient maps give equal cochain maps. -/
theorem continuousCochainsMap_congr {φ ψ : H →ₜ* G} (h : φ = ψ)
    (f : TopRep.res φ X ⟶ Y) (g : TopRep.res ψ X ⟶ Y)
    (hfg : ∀ x : X, f.hom x = g.hom x) :
    ContinuousCohomology.cochainsMap φ f = ContinuousCohomology.cochainsMap ψ g := by
  subst ψ
  have hfg' : f = g := by
    ext x
    exact hfg x
  subst g
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The inverse coefficient morphism, equivariant for the inverse group equivalence. -/
def transportInverseCoefficient (e : H ≃ₜ* G)
    (f : TopRep.res (e : H →ₜ* G) X ≅ Y) :
    TopRep.res (e.symm : G →ₜ* H) Y ⟶ X :=
  TopRep.ofHom
    { toContinuousLinearMap := f.inv.hom.toContinuousLinearMap
      isIntertwining' g := by
        ext y
        simpa [ContIntertwiningMap.toContinuousLinearMap_apply] using
          TopRep.hom_comm_apply f.inv (e.symm g) y }

omit [IsTopologicalGroup G] [IsTopologicalGroup H] in
@[simp]
theorem transportInverseCoefficient_apply (e : H ≃ₜ* G)
    (f : TopRep.res (e : H →ₜ* G) X ≅ Y) (y : Y) :
    (transportInverseCoefficient e f).hom y = f.inv.hom y := rfl

/-- Forward transport followed by inverse transport is the identity on cochains. -/
theorem transportCochains_hom_inv_id (e : H ≃ₜ* G)
    (f : TopRep.res (e : H →ₜ* G) X ≅ Y) :
    ContinuousCohomology.cochainsMap (e : H →ₜ* G) f.hom ≫
      ContinuousCohomology.cochainsMap (e.symm : G →ₜ* H)
        (transportInverseCoefficient e f) = 𝟙 (TopRep.homogeneousCochains X) := by
  rw [← ContinuousCohomology.cochainsMap_comp]
  trans ContinuousCohomology.cochainsMap (ContinuousMonoidHom.id G) (𝟙 X)
  · apply continuousCochainsMap_congr
    · ext g
      exact e.apply_symm_apply g
    · intro x
      exact congrArg (fun t => t.hom x) f.hom_inv_id
  · exact ContinuousCohomology.cochainsMap_id X

/-- Inverse transport followed by forward transport is the identity on cochains. -/
theorem transportCochains_inv_hom_id (e : H ≃ₜ* G)
    (f : TopRep.res (e : H →ₜ* G) X ≅ Y) :
    ContinuousCohomology.cochainsMap (e.symm : G →ₜ* H)
        (transportInverseCoefficient e f) ≫
      ContinuousCohomology.cochainsMap (e : H →ₜ* G) f.hom =
        𝟙 (TopRep.homogeneousCochains Y) := by
  rw [← ContinuousCohomology.cochainsMap_comp]
  trans ContinuousCohomology.cochainsMap (ContinuousMonoidHom.id H) (𝟙 Y)
  · apply continuousCochainsMap_congr
    · ext h
      exact e.symm_apply_apply h
    · intro y
      exact congrArg (fun t => t.hom y) f.inv_hom_id
  · exact ContinuousCohomology.cochainsMap_id Y

/-- The cochain isomorphism induced by simultaneous group and coefficient equivalences. -/
def continuousCochainsIso (e : H ≃ₜ* G)
    (f : TopRep.res (e : H →ₜ* G) X ≅ Y) :
    TopRep.homogeneousCochains X ≅ TopRep.homogeneousCochains Y where
  hom := ContinuousCohomology.cochainsMap (e : H →ₜ* G) f.hom
  inv := ContinuousCohomology.cochainsMap (e.symm : G →ₜ* H)
    (transportInverseCoefficient e f)
  hom_inv_id := transportCochains_hom_inv_id e f
  inv_hom_id := transportCochains_inv_hom_id e f

/-- The isomorphism of actual continuous cohomology objects in every natural degree. -/
noncomputable def continuousCohomologyIso (e : H ≃ₜ* G)
    (f : TopRep.res (e : H →ₜ* G) X ≅ Y) (q : ℕ) :
    continuousCohomology q X ≅ continuousCohomology q Y where
  hom := ContinuousCohomology.map (e : H →ₜ* G) f.hom q
  inv := ContinuousCohomology.map (e.symm : G →ₜ* H)
    (transportInverseCoefficient e f) q
  hom_inv_id := by
    rw [ContinuousCohomology.map, ContinuousCohomology.map,
      ← HomologicalComplex.homologyMap_comp, transportCochains_hom_inv_id]
    exact HomologicalComplex.homologyMap_id _ _
  inv_hom_id := by
    rw [ContinuousCohomology.map, ContinuousCohomology.map,
      ← HomologicalComplex.homologyMap_comp, transportCochains_inv_hom_id]
    exact HomologicalComplex.homologyMap_id _ _

@[simp]
theorem continuousCohomologyIso_hom (e : H ≃ₜ* G)
    (f : TopRep.res (e : H →ₜ* G) X ≅ Y) (q : ℕ) :
    (continuousCohomologyIso e f q).hom =
      ContinuousCohomology.map (e : H →ₜ* G) f.hom q := rfl

@[simp]
theorem continuousCohomologyIso_inv (e : H ≃ₜ* G)
    (f : TopRep.res (e : H →ₜ* G) X ≅ Y) (q : ℕ) :
    (continuousCohomologyIso e f q).inv =
      ContinuousCohomology.map (e.symm : G →ₜ* H)
        (transportInverseCoefficient e f) q := rfl

end Langlands.Continuous
