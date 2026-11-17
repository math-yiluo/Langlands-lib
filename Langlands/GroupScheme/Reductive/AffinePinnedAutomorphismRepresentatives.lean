import Langlands.GroupScheme.Reductive.AffinePinnedAutomorphismPredicate
import Langlands.GroupScheme.Reductive.AffinePinnedIsomorphismTheoremStatement

/-! # Exact pinned representatives from supplied pinned full faithfulness -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.AffinePinnedModel

variable (M : AffinePinnedModel.{u})

/-- Specializing supplied full faithfulness at the inverse root-datum label
gives the covariant pinned predicate used by the automorphism-group target. -/
theorem existsUnique_pinnedAutomorphism
    (hiso : AffinePinnedIsomorphismTheoremStatement.{u})
    (θ : RootPairing.Aut M.rootDatum) (hθ : θ ∈ M.basedAutomorphisms) :
    ∃! σ : CategoryTheory.Aut M.group, M.IsPinnedAutomorphism σ θ := by
  have hθinv : θ⁻¹ ∈ M.basedAutomorphisms := M.basedAutomorphisms.inv_mem hθ
  obtain ⟨σ, ⟨⟨τ, hτ, hτχ⟩, hσX⟩, hσunique⟩ :=
    hiso M.ring M.group M.group M.reductive M.reductive
      M.coordinates M.coordinates M.inclusion M.inclusion
      M.rootIndex M.rootIndex M.rootDatum M.rootDatum
      M.closed M.maximal M.fibrewiseRootDatum M.rootLines
      M.closed M.maximal M.fibrewiseRootDatum M.rootLines
      M.basis M.basis M.pinning M.pinning θ⁻¹ hθinv
  refine ⟨σ, ⟨hθ, ⟨τ, hτ, ?_⟩, ?_⟩, ?_⟩
  · intro U x m
    have h := hτχ U x (θ.weightMap m)
    change
      (∏ j, splitTorus.pointsEquiv M.coordinates U
        (x ≫ τ.hom.hom.hom) j ^ θ.weightMap m j) =
      ∏ j, splitTorus.pointsEquiv M.coordinates U x j ^
        θ.weightEquiv.symm (θ.weightMap m) j at h
    simpa only [RootPairing.Equiv.weightEquiv_symm_weightMap] using h
  · intro a
    have h := hσX ⟨θ.indexEquiv a, (hθ a).mp a.property⟩
    have ha : (⟨(θ⁻¹).indexEquiv (θ.indexEquiv a),
        (hθinv _).mp ((hθ a).mp a.property)⟩ : M.basis.support) = a :=
      Subtype.ext (θ.indexEquiv.symm_apply_apply a)
    rwa [ha] at h
  · intro ρ hρ
    apply hσunique ρ
    obtain ⟨hθ', ⟨υ, hυ, hυχ⟩, hρX⟩ := hρ
    refine ⟨⟨υ, hυ, ?_⟩, ?_⟩
    · intro U x m
      have h := hυχ U x (θ.weightEquiv.symm m)
      change
        (∏ j, splitTorus.pointsEquiv M.coordinates U
          (x ≫ υ.hom.hom.hom) j ^ m j) =
        ∏ j, splitTorus.pointsEquiv M.coordinates U x j ^ θ.weightEquiv.symm m j
      simpa only [RootPairing.Equiv.weightMap_weightEquiv_symm] using h
    · intro a
      have h := hρX ⟨θ.indexEquiv.symm a, (hθinv a).mp a.property⟩
      have ha : (⟨θ.indexEquiv (θ.indexEquiv.symm a),
          (hθ _).mp ((hθinv a).mp a.property)⟩ : M.basis.support) = a :=
        Subtype.ext (θ.indexEquiv.apply_symm_apply a)
      rwa [ha] at h

/-- The unique exact pinned representatives form a homomorphism, conditional
on the published pinned full-faithfulness statement. -/
def pinnedAutomorphismHom
    (hiso : AffinePinnedIsomorphismTheoremStatement.{u}) :
    M.basedAutomorphisms →* CategoryTheory.Aut M.group where
  toFun θ := (M.existsUnique_pinnedAutomorphism hiso θ θ.property).choose
  map_one' :=
    ((M.existsUnique_pinnedAutomorphism hiso 1 M.basedAutomorphisms.one_mem).choose_spec.2
      1 M.isPinnedAutomorphism_one).symm
  map_mul' θ ψ :=
    ((M.existsUnique_pinnedAutomorphism hiso (θ * ψ) (θ * ψ).property).choose_spec.2
      ((M.existsUnique_pinnedAutomorphism hiso θ θ.property).choose *
        (M.existsUnique_pinnedAutomorphism hiso ψ ψ.property).choose)
      (IsPinnedAutomorphism.mul M
        (M.existsUnique_pinnedAutomorphism hiso θ θ.property).choose_spec.1
        (M.existsUnique_pinnedAutomorphism hiso ψ ψ.property).choose_spec.1)).symm

theorem pinnedAutomorphismHom_pinned
    (hiso : AffinePinnedIsomorphismTheoremStatement.{u})
    (θ : M.basedAutomorphisms) :
    M.IsPinnedAutomorphism (M.pinnedAutomorphismHom hiso θ) θ :=
  (M.existsUnique_pinnedAutomorphism hiso θ θ.property).choose_spec.1

theorem eq_pinnedAutomorphismHom
    (hiso : AffinePinnedIsomorphismTheoremStatement.{u})
    {σ : CategoryTheory.Aut M.group} {θ : RootPairing.Aut M.rootDatum}
    (hσ : M.IsPinnedAutomorphism σ θ) :
    σ = M.pinnedAutomorphismHom hiso ⟨θ, hσ.based⟩ :=
  (M.existsUnique_pinnedAutomorphism hiso θ hσ.based).choose_spec.2 σ hσ

end Langlands.GroupScheme.AffinePinnedModel
