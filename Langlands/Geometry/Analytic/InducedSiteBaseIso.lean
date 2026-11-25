import Langlands.Geometry.Analytic.InducedSiteBase
import Langlands.Geometry.Analytic.QuasiEtaleDomains

/-! # A `G`-space over an induced space is induced from the domain over the base copy -/

noncomputable section

universe u v z

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Analytic.SaturatedAtlasPresentation.InducedSpace

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {G : Type z} [Group G] {H : Subgroup G}
  {X : Action (LocalizedCategory.{u, max z v, max z v} (K := K)) H}
  {Y : Action (LocalizedCategory.{u, max z v, max z v} (K := K)) G}
  (π : Y ⟶ inducedAction H X)

/-- The action of the representative `c.out` identifies the domain `π⁻¹(X_H)` over the copy
indexed by `H` with the domain `π⁻¹(X_c)` over the copy indexed by `c`. -/
def preimageDomainIso (c : G ⧸ H) : (baseAction π).V ≅ domainObj Y.V (preimageDomain π c) :=
  domainRestrictIso (Y.ρAut c.out).asIso (preimageDomain π (baseCoset H)) (preimageDomain π c)
    (fun y hy => by
      have h := ρ_mem_preimageDomain π c.out y hy
      rw [out_smul_baseCoset] at h
      exact h)
    (fun y hy => by
      have h := ρ_mem_preimageDomain π c.out⁻¹ y hy
      rw [out_inv_smul] at h
      exact h)

/-- On the copy indexed by `c`, the extension of the inclusion `π⁻¹(X_H) → Y` is the
identification of `π⁻¹(X_H)` with `π⁻¹(X_c)` followed by the inclusion of `π⁻¹(X_c)`. -/
theorem copy_lift_baseInclusion_hom (c : G ⧸ H) :
    copy H (baseAction π) c ≫ (lift H (baseInclusion π)).hom =
      (preimageDomainIso π c).hom ≫ domainι Y.V (preimageDomain π c) :=
  (copy_liftHom (Y := Y) H (baseInclusion π).hom c).trans
    (domainRestrictIso_hom_inclusion (Y.ρAut c.out).asIso (preimageDomain π (baseCoset H))
      (preimageDomain π c) _ _).symm

variable (hP : OpenPartitionCoproductStatement.{u, v, z})

include hP in
/-- The domains `π⁻¹(X_c)` over the copies exhibit `Y` as their coproduct. -/
theorem nonempty_isColimit_preimageDomain :
    Nonempty (IsColimit (Cofan.mk Y.V fun c => domainι Y.V (preimageDomain π c))) :=
  hP K Y.V
    (fun c => localizedSpaceFunctor.map π.hom ⁻¹'
      Set.range (localizedSpaceFunctor.map (copy H X c)))
    (fun c => (isOpen_range_copy_space H X c).preimage
      (localizedSpaceFunctor.map π.hom).hom.continuous)
    (fun i j hij => Set.disjoint_left.2 fun y hi hj =>
      hij (((mem_preimageDomain_iff π i y).1 hi).symm.trans
        ((mem_preimageDomain_iff π j y).1 hj)))
    (fun y => ⟨pointCoset H X (localizedSpaceFunctor.map π.hom y),
      (mem_preimageDomain_iff π _ y).2 rfl⟩)

include hP in
/-- The underlying morphism of the extension `(π⁻¹(X_H))_{G/H} → Y` of the inclusion is an
isomorphism. -/
theorem isIso_lift_baseInclusion_hom : IsIso (lift H (baseInclusion π)).hom := by
  obtain ⟨hc⟩ := nonempty_isColimit_preimageDomain π hP
  have hfac : ∀ c, domainι Y.V (preimageDomain π c) ≫ Cofan.IsColimit.desc hc
      (fun d => (preimageDomainIso π d).inv ≫ copy H (baseAction π) d) =
        (preimageDomainIso π c).inv ≫ copy H (baseAction π) c :=
    fun c => Cofan.IsColimit.fac hc _ c
  refine ⟨⟨Cofan.IsColimit.desc hc
    (fun d => (preimageDomainIso π d).inv ≫ copy H (baseAction π) d), ?_, ?_⟩⟩
  · refine copies_hom_ext H (baseAction π) fun c => ?_
    rw [← Category.assoc, copy_lift_baseInclusion_hom, Category.assoc, hfac,
      Iso.hom_inv_id_assoc, Category.comp_id]
  · refine Cofan.IsColimit.hom_ext hc _ _ fun c => ?_
    change domainι Y.V (preimageDomain π c) ≫ _ = domainι Y.V (preimageDomain π c) ≫ _
    rw [← Category.assoc, hfac, Category.assoc, copy_lift_baseInclusion_hom,
      Iso.inv_hom_id_assoc, Category.comp_id]

include hP in
/-- **A `G`-object over `X_{G/H}` is induced.** For a `G`-morphism `π : Y → X_{G/H}`, the
extension `(π⁻¹(X_H))_{G/H} → Y` of the inclusion of the domain over the copy indexed by `H`
is an isomorphism of `G`-objects. -/
theorem isIso_lift_baseInclusion : IsIso (lift H (baseInclusion π)) := by
  have := isIso_lift_baseInclusion_hom π hP
  exact Action.isIso_of_hom_isIso _

end Langlands.Analytic.SaturatedAtlasPresentation.InducedSpace
