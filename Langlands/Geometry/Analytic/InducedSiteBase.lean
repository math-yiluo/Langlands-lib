import Langlands.Geometry.Analytic.InducedSiteFold
import Langlands.Geometry.Analytic.QuasiEtaleOpenRestrictionStatement
import Langlands.Geometry.Analytic.InducedEquivariantSite
import Langlands.Geometry.Analytic.ContinuousInvariantDomain

/-! # The base of an object over an induced space

For a morphism `π : Y ⟶ Ind_H^G X` of `G`-objects, the open domain `π⁻¹(X_H)` of `Y` over the
copy of `X` indexed by the coset `H` is an `H`-object `baseAction π` with an `H`-morphism
`baseActionHom π hP : baseAction π ⟶ X`, and the counit-type comparison
`lift H (baseInclusion π) : Ind_H^G (π⁻¹(X_H)) ⟶ Y` lies over `π`. This is the construction
behind the essential surjectivity of induction on equivariant quasi-étale sites. -/

noncomputable section

universe u v z

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Analytic.SaturatedAtlasPresentation.InducedSpace

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {G : Type z} [Group G] {H : Subgroup G}

theorem out_inv_smul (c : G ⧸ H) : c.out⁻¹ • c = baseCoset H :=
  calc c.out⁻¹ • c = c.out⁻¹ • (c.out • baseCoset H) := by rw [out_smul_baseCoset]
    _ = baseCoset H := inv_smul_smul _ _

section Copy

variable (H) (X : Action (LocalizedCategory.{u, max z v, max z v} (K := K)) H)

theorem unitHom_mem_copyDomain (x : localizedSpaceFunctor.obj X.V) :
    localizedSpaceFunctor.map (unitHom H X) x ∈ (copyDomain H X (baseCoset H)).carrier :=
  (mem_copyDomain_iff H X _ _).2 (pointCoset_unitHom H X x)

variable (hP : OpenPartitionCoproductStatement.{u, v, z})

include hP in
/-- The domain of the copy indexed by the coset `H` is identified with `X` by the fold
morphism followed by the action of the chosen representative `r` of that coset. -/
theorem isIso_copyDomain_foldHom :
    IsIso (domainι _ (copyDomain H X (baseCoset H)) ≫ foldHom H X ≫ (X.ρ (baseRep H)).asHom) := by
  refine ⟨⟨domainLift (copyDomain H X (baseCoset H)) (unitHom H X)
    (unitHom_mem_copyDomain H X), ?_, ?_⟩⟩
  · apply (cancel_mono (domainι _ (copyDomain H X (baseCoset H)))).1
    rw [Category.assoc, Category.assoc, Category.assoc, domainLift_comp, Category.id_comp,
      unitHom, ρ_comp_assoc, inv_mul_cancel, Action.ρ_one, End.one_asHom, Category.id_comp,
      domainι_copyDomain_foldHom_copy H X hP]
  · rw [domainLift_comp_assoc, unitHom_foldHom]

end Copy

section Points

variable {X : Action (LocalizedCategory.{u, max z v, max z v} (K := K)) H}
  {Y : Action (LocalizedCategory.{u, max z v, max z v} (K := K)) G}
  (π : Y ⟶ inducedAction H X)

/-- The open domain `π⁻¹(X_c)` of `Y` lying over the copy `X_c` of `X` indexed by `c`. -/
def preimageDomain (c : G ⧸ H) : (presentationOf Y.V).AnalyticDomain :=
  (presentationOf Y.V).openDomain
    (localizedSpaceFunctor.map π.hom ⁻¹' Set.range (localizedSpaceFunctor.map (copy H X c)))
    ((isOpen_range_copy_space H X c).preimage (localizedSpaceFunctor.map π.hom).hom.continuous)

theorem mem_preimageDomain_iff (c : G ⧸ H) (y : localizedSpaceFunctor.obj Y.V) :
    y ∈ (preimageDomain π c).carrier ↔
      pointCoset H X (localizedSpaceFunctor.map π.hom y) = c :=
  mem_range_copy_space_iff H X c _

theorem map_hom_ρ_apply (g : G) (y : localizedSpaceFunctor.obj Y.V) :
    localizedSpaceFunctor.map π.hom (localizedSpaceFunctor.map (Y.ρ g).asHom y) =
      localizedSpaceFunctor.map (actionMap H X g) (localizedSpaceFunctor.map π.hom y) := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, π.comm g, Functor.map_comp,
    ConcreteCategory.comp_apply]
  rfl

theorem ρ_mem_preimageDomain (g : G) {c : G ⧸ H} (y : localizedSpaceFunctor.obj Y.V)
    (hy : y ∈ (preimageDomain π c).carrier) :
    localizedSpaceFunctor.map (Y.ρ g).asHom y ∈ (preimageDomain π (g • c)).carrier := by
  rw [mem_preimageDomain_iff] at hy ⊢
  rw [map_hom_ρ_apply, pointCoset_actionMap, hy]

theorem ρ_mem_preimageDomain_baseCoset (h : H) :
    ∀ y ∈ (preimageDomain π (baseCoset H)).carrier,
      localizedSpaceFunctor.map (Y.ρ (h : G)).asHom y ∈ (preimageDomain π (baseCoset H)).carrier :=
  fun y hy => by
    have := ρ_mem_preimageDomain π (h : G) y hy
    rwa [smul_baseCoset] at this

/-- The domain over the copy indexed by the coset `H` is invariant under `H`. -/
theorem isInvariantDomain_preimageDomain :
    IsInvariantDomain ((Action.res _ H.subtype).obj Y) (preimageDomain (Y := Y) π (baseCoset H)) :=
  fun h y hy => ρ_mem_preimageDomain_baseCoset π h y hy

/-- The `H`-object `π⁻¹(X_H)`: the domain of `Y` over the copy indexed by the coset `H`, with
the restricted action of `H`. -/
abbrev baseAction : Action (LocalizedCategory.{u, max z v, max z v} (K := K)) H :=
  invariantDomainAction ((Action.res _ H.subtype).obj Y) (preimageDomain (Y := Y) π (baseCoset H))
    (isInvariantDomain_preimageDomain π)

/-- The inclusion `π⁻¹(X_H) → Y` as a morphism of `H`-objects. -/
abbrev baseInclusion : baseAction π ⟶ (Action.res _ H.subtype).obj Y :=
  invariantDomainInclusion _ _ (isInvariantDomain_preimageDomain π)

/-- The morphism `π⁻¹(X_H) → X`: the restriction of `π`, followed by the fold morphism and the
action of the chosen representative `r` of the coset `H`. -/
def baseHomV : domainObj Y.V (preimageDomain π (baseCoset H)) ⟶ X.V :=
  domainι Y.V (preimageDomain π (baseCoset H)) ≫ π.hom ≫ foldHom H X ≫ (X.ρ (baseRep H)).asHom

variable (hP : OpenPartitionCoproductStatement.{u, v, z})

include hP in
theorem baseHomV_unitHom :
    baseHomV π ≫ unitHom H X = domainι Y.V (preimageDomain π (baseCoset H)) ≫ π.hom := by
  have hf : ∀ t, pointCoset H X (localizedSpaceFunctor.map
      (domainι Y.V (preimageDomain π (baseCoset H)) ≫ π.hom) t) = baseCoset H := fun t => by
    rw [Functor.map_comp, ConcreteCategory.comp_apply, domainι_apply]
    exact (mem_preimageDomain_iff π _ _).1 t.2
  have h := foldHom_copy_of_pointCoset H X hP _ _ hf
  rw [Category.assoc] at h
  rw [baseHomV, unitHom, Category.assoc, Category.assoc, Category.assoc, ρ_comp_assoc,
    inv_mul_cancel, Action.ρ_one, End.one_asHom, Category.id_comp, h]

include hP in
theorem baseHomV_comm (h : H) :
    domainRestrict (preimageDomain π (baseCoset H)) (preimageDomain π (baseCoset H))
        (Y.ρ (h : G)).asHom (ρ_mem_preimageDomain_baseCoset π h) ≫ baseHomV π =
      baseHomV π ≫ (X.ρ h).asHom := by
  apply (cancel_mono (unitHom H X)).1
  rw [Category.assoc, baseHomV_unitHom π hP, Category.assoc, unitHom_comm,
    ← Category.assoc (baseHomV π), baseHomV_unitHom π hP, domainRestrict_comp_assoc, π.comm,
    Category.assoc]
  rfl

/-- The morphism `π⁻¹(X_H) → X` of `H`-objects. -/
def baseActionHom : baseAction π ⟶ X where
  hom := baseHomV π
  comm h := baseHomV_comm π hP h

include hP in
@[simp]
theorem baseActionHom_hom : (baseActionHom π hP).hom = baseHomV π := rfl

include hP in
theorem lift_baseInclusion_comp :
    lift H (baseInclusion π) ≫ π = (inductionFunctor H).map (baseActionHom π hP) := by
  rw [inductionFunctor_map]
  apply (homEquiv H).injective
  rw [homEquiv_naturality, ← homEquiv_symm_apply, ← homEquiv_symm_apply, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply]
  exact Action.Hom.ext (baseHomV_unitHom π hP).symm

end Points

end Langlands.Analytic.SaturatedAtlasPresentation.InducedSpace
