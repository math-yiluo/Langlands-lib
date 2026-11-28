import Langlands.GroupScheme.IntegralModel.CongruenceLie

/-! # The congruence–Lie map with a second model in the denominator -/

universe u

open AlgebraicGeometry

namespace Langlands.GroupScheme.IntegralModel

variable {R K : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  {G : GroupScheme (Spec (CommRingCat.of K))} [IsAffineHom G.X.hom]
  {N M : IntegralModel R K G}

/-- The level-`n` scaled Lie lattice of `N` modulo its intersection with the level-`n`
scaled Lie lattice of `M`, the intersection being viewed inside the former. -/
abbrev truncatedCongruenceLieQuotient (N M : IntegralModel R K G) (n : ℕ+) :=
  N.lieLatticeAt n ⧸ (M.lieLatticeAt n).comap (N.lieLatticeAt n).subtype

/-- For smooth `N`, levels `n ≤ m ≤ 2n` and `L_{N,m} ⊆ L_{M,n}`, the canonical
congruence–Lie homomorphism of `N` on its level-`n` congruence subgroup followed by the
projection `L_{N,n}/L_{N,m} → L_{N,n}/(L_{N,n} ∩ L_{M,n})`. -/
noncomputable def truncatedCongruenceLieHom (hN : N.IsSmooth) {n m : ℕ+} (hnm : n ≤ m)
    (hm : (m : ℕ) ≤ 2 * (n : ℕ)) (hL : N.lieLatticeAt m ≤ M.lieLatticeAt n) :
    N.congruenceSubgroupAt n →* Multiplicative (N.truncatedCongruenceLieQuotient M n) :=
  ((Submodule.factor (Submodule.comap_mono hL)).toAddMonoidHom.toMultiplicative).comp
    (N.congruenceLieHom hN hnm hm)

/-- The value of the projected comparison is the image, under the quotient projection,
of the value of the canonical comparison for `N`. -/
theorem truncatedCongruenceLieHom_apply (hN : N.IsSmooth) {n m : ℕ+} (hnm : n ≤ m)
    (hm : (m : ℕ) ≤ 2 * (n : ℕ)) (hL : N.lieLatticeAt m ≤ M.lieLatticeAt n)
    (g : N.congruenceSubgroupAt n) :
    Multiplicative.toAdd (truncatedCongruenceLieHom hN hnm hm hL g) =
      Submodule.factor (Submodule.comap_mono hL)
        (Multiplicative.toAdd (N.congruenceLieHom hN hnm hm g)) := rfl

end Langlands.GroupScheme.IntegralModel
