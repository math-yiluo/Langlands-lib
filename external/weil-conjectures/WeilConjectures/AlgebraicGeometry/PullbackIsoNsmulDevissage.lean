/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import WeilConjectures.CategoryTheory.Abelian.PrimeFactorDevissage
import WeilConjectures.AlgebraicGeometry.PullbackCohomologyLongExactLadder
import Mathlib.Algebra.FiveLemma

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Prime-torsion dévissage for a sheaf annihilated by one positive integer.
Source: Stacks Project, Tag 0A4B, proof, bounded-torsion reduction, transposed to
cohomology of qcqs schemes (https://stacks.math.columbia.edu/tag/0A4B).
(blueprint: lem-weil-pbc-pullback-iso-nsmul-devissage)

Proof: Let P(G) mean bijectivity of pullback in every nonnegative degree. For a
short exact sequence with P on its outer terms, the pullback cohomology ladder
and the five lemma give P on the middle term in positive degrees. In degree
zero, injectivity follows by exactness and injectivity of the initial arrow;
surjectivity follows by the four lemma on the initial four terms. Thus P is
closed under extensions. Apply the library's prime-factor induction to P: the
kernel-image sequence of multiplication by a prime divisor r of n has outer
terms killed by r and n/r. The induction terminates since 0 < n/r < n. At n = 1,
the identity is zero, so multiplication by 2 is zero and the prime hypothesis
applies. -/
theorem pullback_cohomology_bijective_of_nsmul
    {X Y : Scheme.{u}} (u : Y ⟶ X)
    [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    (hprime : ∀ (r : ℕ), Nat.Prime r →
      ∀ (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}),
        r • 𝟙 G = 0 → ∀ (q : ℕ),
          Function.Bijective (cohomologyMap u G q))
    {n : ℕ} (hn : 0 < n)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hG : n • 𝟙 G = 0) :
    ∀ (q : ℕ), Function.Bijective (cohomologyMap u G q) := by
  let P : ObjectProperty (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    fun G ↦ ∀ q : ℕ, Function.Bijective (cohomologyMap u G q)
  apply ObjectProperty.prop_of_nsmul_id_eq_zero P ?_ hprime n hn G hG
  intro S hS h₁ h₃ q
  obtain ⟨hY, δX, δY, _, _, hf₀, hg₀, hX, hYex, hc₁, hc₂, hcδ⟩ :=
    pullbackCohomology_longExact_ladder u S hS
  let f := fun q ↦ Sheaf.H.map S.f q
  let g := fun q ↦ Sheaf.H.map S.g q
  let fY := fun q ↦ Sheaf.H.map (((u)^*[AddCommGrpCat.{u + 1}]).map S.f) q
  let gY := fun q ↦ Sheaf.H.map (((u)^*[AddCommGrpCat.{u + 1}]).map S.g) q
  have c₁ (q : ℕ) : (fY q).comp (cohomologyMap u S.X₁ q) =
      (cohomologyMap u S.X₂ q).comp (f q) := by
    ext x
    exact (hc₁ q x).symm
  have c₂ (q : ℕ) : (gY q).comp (cohomologyMap u S.X₂ q) =
      (cohomologyMap u S.X₃ q).comp (g q) := by
    ext x
    exact (hc₂ q x).symm
  have cδ (q : ℕ) : (δY q).comp (cohomologyMap u S.X₃ q) =
      (cohomologyMap u S.X₁ (q + 1)).comp (δX q) := by
    ext x
    exact (hcδ q x).symm
  cases q with
  | zero =>
    refine ⟨?_, ?_⟩
    · rw [injective_iff_map_eq_zero]
      intro x hx
      have hgx : g 0 x = 0 := (h₃ 0).1 (by
        change cohomologyMap u S.X₃ 0 (Sheaf.H.map S.g 0 x) = _
        rw [hc₂ 0 x, hx, map_zero, map_zero])
      obtain ⟨a, ha⟩ := ((hX 0).1 x).mp hgx
      have hax : cohomologyMap u S.X₁ 0 a = 0 := hg₀ (by
        rw [← hc₁ 0 a, ha, hx, map_zero])
      have ha₀ : a = 0 := (h₁ 0).1 (by rw [hax, map_zero])
      rw [← ha, ha₀, map_zero]
    · exact AddMonoidHom.surjective_of_surjective_of_surjective_of_injective
        (f 0) (g 0) (δX 0) (fY 0) (gY 0) (δY 0)
        (cohomologyMap u S.X₁ 0) (cohomologyMap u S.X₂ 0)
        (cohomologyMap u S.X₃ 0) (cohomologyMap u S.X₁ 1)
        (c₁ 0) (c₂ 0) (cδ 0) (hX 0).2.1 (hYex 0).1 (hYex 0).2.1
        (h₁ 0).2 (h₃ 0).2 (h₁ 1).1
  | succ q =>
    exact AddMonoidHom.bijective_of_surjective_of_bijective_of_bijective_of_injective
      (δX q) (f (q + 1)) (g (q + 1)) (δX (q + 1))
      (δY q) (fY (q + 1)) (gY (q + 1)) (δY (q + 1))
      (cohomologyMap u S.X₃ q) (cohomologyMap u S.X₁ (q + 1))
      (cohomologyMap u S.X₂ (q + 1)) (cohomologyMap u S.X₃ (q + 1))
      (cohomologyMap u S.X₁ (q + 1 + 1))
      (cδ q) (c₁ (q + 1)) (c₂ (q + 1)) (cδ (q + 1))
      (hX q).2.2 (hX (q + 1)).1 (hX (q + 1)).2.1
      (hYex q).2.2 (hYex (q + 1)).1 (hYex (q + 1)).2.1
      (h₃ q).2 (h₁ (q + 1)) (h₃ (q + 1)) (h₁ (q + 1 + 1)).1

end AlgebraicGeometry.Etale
