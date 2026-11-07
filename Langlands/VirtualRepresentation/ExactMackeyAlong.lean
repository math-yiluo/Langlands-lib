import Langlands.VirtualRepresentation.ExactMackey
import Langlands.VirtualRepresentation.Global.RelativeWeilLocalRestrictionStatement

/-!
# Mackey's formula for induction along open embeddings

The form of Mackey's formula used by the local restriction formula for relative
Weil groups: the restriction along `ι : L → G` of a representation induced along
an open embedding `j : M → G` is the sum over double-coset representatives `x u`
of representations induced along open embeddings `φ u : N u → L`, through maps
`ιu u : N u → M` with `j (ιu u n) = x u * ι (φ u n) * (x u)⁻¹`.
-/

noncomputable section

set_option autoImplicit false

universe uG uH uJ uM uN uV

namespace Langlands.VirtualRepresentation.ExactGrothendieckGroup

open FiniteRepresentation

/-- Successive continuous restrictions are restriction along the composite. -/
theorem continuousRestrict_continuousRestrict {G : Type uG} {H : Type uH} {J : Type uJ}
    [Group G] [Group H] [Group J] [TopologicalSpace G] [TopologicalSpace H]
    [TopologicalSpace J] (φ : H →ₜ* G) (ψ : J →ₜ* H)
    (y : ExactGrothendieckGroup
      (fun A : FiniteRepresentation.{0, uG, uV} ℂ G => A.IsContinuous)) :
    continuousRestrict ψ (continuousRestrict φ y) = continuousRestrict (φ.comp ψ) y :=
  LinearMap.congr_fun (restrict_comp φ.toMonoidHom _ _ ψ.toMonoidHom _ _ _
    (fun _ hA => FiniteRepresentation.isContinuous_restrict (φ.comp ψ).toMonoidHom
      (φ.comp ψ).continuous hA)) y

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type uM} [Group M] [TopologicalSpace M]
  (j : M →ₜ* G) (hj : Topology.IsOpenEmbedding j) [j.toMonoidHom.range.FiniteIndex]
  {L : Type uG} [Group L] [TopologicalSpace L] [IsTopologicalGroup L] (ι : L →ₜ* G)
  {U : Type*} [Fintype U] {N : U → Type uN} [∀ u, Group (N u)]
  [∀ u, TopologicalSpace (N u)]
  (φ : ∀ u, N u →ₜ* L) (hφ : ∀ u, Topology.IsOpenEmbedding (φ u))
  [∀ u, (φ u).toMonoidHom.range.FiniteIndex]
  (ιu : ∀ u, N u →ₜ* M) (x : U → G)
  (hι : ∀ u n, j (ιu u n) = x u * ι (φ u n) * (x u)⁻¹)
  (hS : ∀ u (ℓ : L), x u * ι ℓ * (x u)⁻¹ ∈ j.toMonoidHom.range →
    ℓ ∈ (φ u).toMonoidHom.range)
  (hcover : ∀ g : G, ∃ (m : M) (u : U) (ℓ : L), g = j m * (x u * ι ℓ))
  (hdisj : ∀ (m m' : M) (u u' : U) (ℓ ℓ' : L),
    j m * (x u * ι ℓ) = j m' * (x u' * ι ℓ') → u = u')

include hι hS hcover hdisj in
/-- Mackey's formula along open embeddings with finite-index ranges, on continuous
exact virtual groups. The double cosets `j(M) x u ι(L)` cover `G` and are
distinct for distinct `u`; the subgroup `ι⁻¹(x u⁻¹ j(M) x u)` is the range of
`φ u`, on which conjugation by `x u` is given by `ιu u`. -/
theorem continuousRestrict_continuousInduceAlong
    (y : ExactGrothendieckGroup
      (fun A : FiniteRepresentation.{0, uM, uV} ℂ M => A.IsContinuous)) :
    continuousRestrict ι (continuousInduceAlong j hj y) =
      ∑ u, continuousInduceAlong (φ u) (hφ u) (continuousRestrict (ιu u) y) := by
  let rj : j.toMonoidHom.range →ₜ* M :=
    ⟨InductionAlong.rangeInverse j.toMonoidHom hj.injective,
      InductionAlong.continuous_rangeInverse j.toMonoidHom hj.isEmbedding⟩
  let rφ : ∀ u, (φ u).toMonoidHom.range →ₜ* N u := fun u =>
    ⟨InductionAlong.rangeInverse (φ u).toMonoidHom (hφ u).injective,
      InductionAlong.continuous_rangeInverse (φ u).toMonoidHom (hφ u).isEmbedding⟩
  let κ : ∀ u, (φ u).toMonoidHom.range →ₜ* j.toMonoidHom.range := fun u =>
    ⟨j.toMonoidHom.rangeRestrict.comp ((ιu u).toMonoidHom.comp (rφ u).toMonoidHom),
      (j.continuous.comp ((ιu u).continuous.comp (rφ u).continuous)).subtype_mk _⟩
  have hφr : ∀ u (s : (φ u).toMonoidHom.range), φ u (rφ u s) = s := fun u s =>
    InductionAlong.apply_rangeInverse (φ u).toMonoidHom (hφ u).injective s
  have hκ : ∀ u (s : (φ u).toMonoidHom.range),
      (κ u s : G) = x u * ι s * (x u)⁻¹ := by
    intro u s
    change j (ιu u (rφ u s)) = _
    rw [hι, hφr]
  have hcover' : ∀ g : G, ∃ (h : j.toMonoidHom.range) (u : U) (ℓ : L),
      g = h * (x u * ι ℓ) := by
    intro g
    obtain ⟨m, u, ℓ, hg⟩ := hcover g
    exact ⟨⟨j m, m, rfl⟩, u, ℓ, hg⟩
  have hdisj' : ∀ (h h' : j.toMonoidHom.range) (u u' : U) (ℓ ℓ' : L),
      (h : G) * (x u * ι ℓ) = h' * (x u' * ι ℓ') → u = u' := by
    rintro ⟨_, m, rfl⟩ ⟨_, m', rfl⟩ u u' ℓ ℓ' e
    exact hdisj m m' u u' ℓ ℓ' e
  have hcomp : ∀ u, rj.comp (κ u) = (ιu u).comp (rφ u) := by
    intro u
    ext s
    exact InductionAlong.rangeInverse_apply j.toMonoidHom hj.injective (ιu u (rφ u s))
  have hmackey := continuousRestrict_continuousInduce j.toMonoidHom.range
    (InductionAlong.isOpen_range j.toMonoidHom hj) ι x
    (fun u => (φ u).toMonoidHom.range)
    (fun u => InductionAlong.isOpen_range (φ u).toMonoidHom (hφ u)) κ hκ hS hcover' hdisj'
    (continuousRestrict rj y)
  change continuousRestrict ι (continuousInduce j.toMonoidHom.range
      (InductionAlong.isOpen_range j.toMonoidHom hj) (continuousRestrict rj y)) =
    ∑ u, continuousInduce (φ u).toMonoidHom.range
      (InductionAlong.isOpen_range (φ u).toMonoidHom (hφ u))
      (continuousRestrict (rφ u) (continuousRestrict (ιu u) y))
  rw [hmackey]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [continuousRestrict_continuousRestrict, continuousRestrict_continuousRestrict, hcomp]

end Langlands.VirtualRepresentation.ExactGrothendieckGroup
