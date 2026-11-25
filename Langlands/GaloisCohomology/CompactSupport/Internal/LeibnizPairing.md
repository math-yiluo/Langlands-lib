# Leibniz pairings of complexes and the cup product of cochains (internal)

`Langlands/GaloisCohomology/CompactSupport/Internal/LeibnizPairing.lean`, namespace
`Langlands.GaloisCohomology`. Internal: no stability promise.

A Leibniz pairing `M ⊗ N → P` of `ℕ`-indexed complexes of `k`-modules is a family of bilinear
maps `Mʳ × Nˢ → Pⁿ` (`r + s = n`) with `d(x·y) = dx·y + (-1)ʳ x·dy`.

```lean
structure LeibnizPairing (M N P : CochainComplex (ModuleCat.{u} k) ℕ) where
  μ : ∀ {r s n : ℕ}, r + s = n → M.X r →ₗ[k] N.X s →ₗ[k] P.X n
  leibniz : ∀ {r s n : ℕ} (h : r + s = n) (x : M.X r) (y : N.X s),
    (P.d n (n + 1)).hom (μ h x y) =
      μ (by omega) ((M.d r (r + 1)).hom x) y + (-1 : k) ^ r • μ (by omega) x ((N.d s (s + 1)).hom y)
noncomputable def LeibnizPairing.homology (μ : LeibnizPairing M N P) {r s n : ℕ} (h : r + s = n) :
    M.homology r →ₗ[k] N.homology s →ₗ[k] P.homology n
theorem LeibnizPairing.homology_δ_add_homology_δ … :
    μ₁.homology h₁ (hSM.δ r (r + 1) rfl x) y + (-1 : k) ^ r • μ₃.homology h₃ x (hSN.δ s (s + 1) rfl y) = 0
noncomputable def cupLeibniz (μ : A ⊗ B ⟶ C) : LeibnizPairing (cochains A) (cochains B) (cochains C)
theorem cupLeibniz_homology (μ : A ⊗ B ⟶ C) {r s n : ℕ} (h : r + s = n) (x : cohomology A r)
    (y : cohomology B s) : (cupLeibniz μ).homology h x y = cupPairing μ h x y
```

## Outline of the proofs

- The product of cycles is a cycle by the Leibniz rule, and the product of a boundary with a cycle
  is a boundary (`cycles_toCycles_left`, `_right`), so the product descends to homology
  (`descHomologyNat`).
- Connecting maps: lift `x₃` to `x₂` and `d x₂` to a cycle `x₁` (`exists_cycles_f_eq_d`), so that
  `δ[x₃] = [x₁]` (`δ_homologyπ_of_lift`); the Leibniz rule for `μ₂` on `x₂·y₂` gives
  `x₁·y₃ + (-1)ʳ x₃·y₁ = d(x₂·y₂)` through the compatibilities of the three pairings.
- `cupLeibniz`: the foundations' cup product of locally constant cochains satisfies the Leibniz rule
  (`d_cupCochain`), and its homology pairing is `cupPairing` by definition of the latter on classes.
- Products: the pairing of product complexes is factorwise; restriction of cochains along `φ_v`
  followed by the local maps commutes with cup products when `μ_v` is compatible with `μ`
  (`localRes_cupPairingCochains`).

## Declarations

`iCycles_hom_injective`, `homologyπ_hom_surjective`, `iCycles_toCycles_hom_apply`,
`homologyπ_toCycles_hom_apply`, `descHomologyNat`, `descHomologyNat_homologyπ`, `LeibnizPairing`;
in namespace `LeibnizPairing`: `d_μ_cycles`, `cyclesProduct`, `iCycles_cyclesProduct`, `cycles`,
`iCycles_cycles`, `cycles_toCycles_left`, `cycles_toCycles_right`, `homologyPairing`,
`homologyPairing_homology_class`, `homology`, `homology_homologyπ`; `δ_homologyπ_of_lift`,
`exists_cycles_f_eq_d`, `LeibnizPairing.homology_δ_add_homology_δ`; `cupPairingCochains`,
`cochainOf_cupPairingCochains`, `d_cupLocallyConstant`, `cupLeibniz`, `cupLeibniz_homology`;
`LeibnizPairing.pi`, `LeibnizPairing.pi_μ_apply`, `LeibnizPairing.piHomologyIso_hom_pi_homology`;
`localRes_cupPairingCochains`.

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis`
(<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, files
`src/GroundTheory/ProfiniteCohomology/CompactSupportCohomology/Pairing.lean` and
`CompactSupportCohomology/CupLeibniz.lean`. The repository has no licence file; its text is used with
attribution (`licenses/RiemannHypothesis/SOURCE.md`). Names are the source's; the foundations' cup
product (`cupCochain`, `cupLocallyConstant`, `cochainOf`, `cupPairing`) replaces the source's.

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008;
  corrected printing 2013), chapter I, §4: Proposition (1.4.1), p. 36 (`∂(a ∪ b) = ∂a ∪ b +
  (−1)^p a ∪ ∂b` for homogeneous cochains), and Proposition (1.4.3), pp. 38–39 (cup products and
  connecting maps, `(−1)^p δ(α ∪ β) = α ∪ δβ`). The cochains here are inhomogeneous and locally
  constant; the sign conventions are those of the foundations' `cupCochain`.
