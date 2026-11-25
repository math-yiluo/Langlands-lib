/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import WeilConjectures.AlgebraicGeometry.TorsionEtaleSheaf
import WeilConjectures.AlgebraicGeometry.PullbackIsoNsmulDevissage
import WeilConjectures.AlgebraicGeometry.PullbackIsoTorsionColimit

/-!
# Pullback isomorphisms on cohomology: prime-torsion dévissage

Source: literature/stacks-project/etale-cohomology.tex, proof of Lemma 0A4B,
paragraphs 2--3 (blueprint: lem-weil-pbc-pullback-iso-prime-torsion-devissage).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- If pullback is bijective on every prime-torsion étale abelian sheaf, then it is
bijective on every torsion étale abelian sheaf. Source: Stacks Project,
`etale-cohomology.tex`, proof of Lemma 0A4B
(`lemma-proper-base-change-in-terms-of-injectives`), paragraphs 2--3, transposed from
higher direct images to global cohomology using Theorem 09YQ (`theorem-colimit`).
(blueprint: lem-weil-pbc-pullback-iso-prime-torsion-devissage)

Proof:
1. Cohomology is functorial in the sheaf, sends isomorphisms to bijections, and the
pullback maps are natural in the sheaf
(`proposition-cohomology-p-1-over-henselian--1`).
2. By `definition-torsion-sheaves`, a torsion sheaf `F` is the colimit of
`F[n] = ker (n : F ⟶ F)`, indexed by positive integers ordered by divisibility.
The canonical colimit map to `F` is an isomorphism and `n F[n] = 0`.
3. For a sheaf `G` killed by a positive integer `n`, induct on the number of prime
factors of `n`. If `n = 1`, then `G = 0`, so the hypothesis for the prime 2 applies.
For prime `n`, apply the hypothesis directly. Otherwise choose a prime `r ∣ n`.
The short exact sequence `0 → G[r] → G → rG → 0` has its end terms killed by
`r` and `n/r` (`theorem-proper-base-change-classical-pro`). The pullback is exact and
the two long exact cohomology sequences form a commutative ladder
(`lem-weil-pbc-pullback-cohomology-long-exact-ladder`). In degree `q`, the four
outer vertical maps in the five-term segment are bijections by the prime
hypothesis and induction in all degrees. For `q = 0`, replace the preceding
negative-degree term by zero. The five lemma (`lem-weil-pbc-five-lemma`) gives
bijectivity for `G`.
4. Apply step 3 to every `F[n]`. Cohomology commutes with this filtered colimit
on both qcqs schemes (`lemma-finiteness-small-etale-topoi--2`), and inverse
image preserves colimits.
Naturality makes the pullback maps a morphism of directed systems; their inverses
are compatible too, so their colimit map is bijective. The canonical comparison
isomorphisms identify this map with pullback on the colimit. Finally use naturality
for the canonical isomorphism from the colimit to `F` to obtain bijectivity for `F`
in every degree. -/
theorem pullback_cohomology_bijective_of_prime_torsion_devissage
    {X Y : Scheme.{u}} (u : Y ⟶ X)
    [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    (hprime : ∀ (r : ℕ), Nat.Prime r →
      ∀ (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}),
        r • 𝟙 G = 0 → ∀ (q : ℕ),
          Function.Bijective (cohomologyMap u G q))
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : Scheme.IsTorsionAbelianSheaf F) :
    ∀ (q : ℕ), Function.Bijective (cohomologyMap u F q) := by
  apply pullback_cohomology_bijective_of_torsion_colimit u
  · intro n hn G hG q
    exact pullback_cohomology_bijective_of_nsmul u hprime hn G hG q
  · exact hF

end AlgebraicGeometry.Etale
