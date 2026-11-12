# Invariant Laurent algebras under finite groups of characters

Module `Langlands.Representation.CuspidalSupport.RationalInertiaOrbitTorusAlgebra`.
Namespace `Langlands.CuspidalSupport.OrbitTorus`.

Worker 5102 wrote this supporting module for the proof
`Langlands.CuspidalSupport.rationalInertiaOrbitTorus` of Renard V.2.7,
Corollary (module `RationalInertiaOrbitTorusProof`). It imports only Mathlib.
It has no representation theory: it contains the algebra behind the
Corollary's proof, stated for an abstract lattice and its character group.

## Provenance

The source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
V.2.7, Corollary, its proof and the following Notations paragraph, printed
p.109 / PDF p.115. Renard's proof is one sentence: the quotient of a complex
torus by a finite subgroup is again a torus. This module supplies the details
for the coordinate-algebra form of that sentence used by the published
statement `RationalInertiaOrbitTorusStatement`. Every declaration here is an
internal helper for that proof; none is a separately cited result of the
source.

## Setting

- `Λ` is a commutative group (written multiplicatively; `Additive Λ` is its
  `ℤ`-module), and `X` is a commutative group.
- `D : X →* (Λ →* ℂˣ)` sends a point of `X` to a complex character of `Λ`.
  In the application `X` is the group `X(G)` of unramified characters, `Λ` is
  the valuation image `Λ(G)`, and `D` is descent of characters to `Λ(G)`.
- `E : ℂ[Additive Λ] →ₐ[ℂ] (X → ℂ)` evaluates group-algebra elements on `X`,
  with `E (single a c) χ = c · D χ a` (hypothesis `hE`).
- `S` is a subgroup of `X`. In the application it is the stabilizer
  `X(G)(π)`.

## Declarations

- `complexUnits_zpow_surjective`: for `n ≠ 0`, `u ↦ uⁿ` is surjective on
  `ℂˣ`. The proof takes an `|n|`-th root with `IsAlgClosed.exists_pow_nat_eq`,
  and inverts it when `n < 0`.
- `exists_character_extension`: every additive map `L →+ Additive ℂˣ` on a
  `ℤ`-submodule `L` of `Additive Λ` extends to a character `Λ →* ℂˣ`.
  The previous lemma makes `Additive ℂˣ` divisible. Mathlib's
  `Module.Baer.of_divisible` then gives Baer's criterion, and
  `Module.Baer.extension_property_addMonoidHom` gives the extension.
- `annihilatorLattice D S`: the `ℤ`-submodule `Λ′ = {a | D s a = 1 for all
  s ∈ S}` of `Additive Λ`.
- `card_smul_mem_annihilatorLattice`: `|S| • a ∈ Λ′` for every `a`, because
  `s^{|S|} = 1` for `s ∈ S` (`pow_card_eq_one'`).
- `exists_basis_annihilatorLattice`: if `S` is finite and `Additive Λ` has a
  `ℤ`-basis indexed by `Fin d`, then so does `Λ′`. `Submodule.basisOfPid`
  gives a basis of `Λ′` indexed by some `Fin n`. `Submodule.finrank_le` gives
  `n ≤ d`. The vectors `|S| • bᵢ` lie in `Λ′` and are linearly independent,
  since multiplication by `|S| ≠ 0` is injective on a free module
  (`Basis.smul_eq_zero`). This gives `d ≤ n`.
- `mem_of_forall_annihilator` (finite duality): if `S` is finite, `D` is
  injective and `D t` is trivial on `Λ′`, then `t ∈ S`. Let
  `ev : Λ →* (S →* ℂˣ)` be the pairing `ev a s = D s a` (`MonoidHom.flip`).
  - `ev` is surjective. By Mathlib's order-reversing bijection
    `CommGroup.subgroupOrderIsoSubgroupMonoidHom` between subgroups of the
    finite group `S` and subgroups of its dual, the range of `ev`
    corresponds to the subgroup of `S` killed by every `ev a`. That subgroup
    is trivial because `D` is injective. Hence the range is the whole dual.
    `ℂ` has enough roots of unity (`IsSepClosed.hasEnoughRootsOfUnity`),
    since the exponent of the finite group `S` is nonzero.
  - The kernel of `ev` is `Λ′`, on which `D t` is trivial. So `D t` factors
    as `τ ∘ ev` (`MonoidHom.liftOfSurjective`).
  - By double duality (`CommGroup.monoidHomMonoidHomEquiv`) there is
    `s₀ ∈ S` with `τ φ = φ s₀` for all `φ`. Then `D t a = D s₀ a` for all
    `a`, so `t = s₀ ∈ S` by injectivity of `D`.
- `characterTwist D s`: the algebra endomorphism of `ℂ[Additive Λ]` sending
  `single a c` to `single a (c · D s a)` (`AddMonoidAlgebra.lift`).
  - `characterTwist_single` gives its value on monomials.
  - `coeff_characterTwist` gives its coefficients: the coefficient at `a` is
    multiplied by `D s a`.
  - `apply_characterTwist` shows `E (characterTwist D s p) χ = E p (χ · s)`,
    i.e. it is translation by `s` on evaluations.
- `exists_invariant_laurent` (main result): assume `S` is finite,
  `Additive Λ` has a basis indexed by `Fin d`, `D` is bijective, `hE` holds
  and `E` is injective. Write `F^S = {f ∈ range E | f(χ s) = f(χ) for all
  s ∈ S, χ ∈ X}`. Then there is `Φ : ℂ[ℤ^d] →ₐ[ℂ] (X → ℂ)` such that:
  1. `Φ` is injective;
  2. the range of `Φ` is `F^S`;
  3. every `ℂ`-algebra map `φ : ℂ[ℤ^d] → ℂ` is `p ↦ Φ p χ` for some
     `χ ∈ X`;
  4. for all `χ, χ'`: `χ⁻¹ χ' ∈ S` if and only if every element of `F^S`
     takes the same value at `χ` and `χ'`.

## Proof of `exists_invariant_laurent`

Choose a basis `bL` of `Λ′` indexed by `Fin d`
(`exists_basis_annihilatorLattice`). Let `μ : ℤ^d →+ Additive Λ` be its
coordinate map followed by the inclusion. It is injective and its range is
`Λ′`. Put `Φ = E ∘ mapDomain μ`, so `Φ (single m c) χ = c · D χ (μ m)`.

1. **Injective.** `mapDomain μ` is injective because `μ` is
   (`AddMonoidAlgebra.mapDomain_injective`), and `E` is injective.
2. **Range.**
   - `Φ q ∈ F^S`: it lies in the range of `E`. It is `S`-invariant by
     induction on `q`, because `D (χ s) (μ m) = D χ (μ m) · D s (μ m)` and
     `D s (μ m) = 1` since `μ m ∈ Λ′`.
   - Conversely, let `f = E p ∈ F^S` and `s ∈ S`. By `apply_characterTwist`,
     `E (characterTwist D s p) = E p`, so `characterTwist D s p = p` by
     injectivity of `E`. Comparing coefficients (`coeff_characterTwist`)
     gives `D s a = 1` whenever the coefficient of `p` at `a` is nonzero.
     So the support of `p` lies in `Λ′`, the range of `μ`, and
     `p = mapDomain μ (comapDomain μ p)` (`mapDomain_comapDomain`). Hence
     `f = Φ (comapDomain μ p)`.
3. **Points.** An algebra map `φ` gives a character `ψ₀` of `ℤ^d` with values
   in `ℂˣ`: `m ↦ φ (single m 1)` (`MonoidHom.toHomUnits`). Through `bL`,
   `ψ₀` becomes a character of `Λ′`. Extend it to `χ₀ : Λ →* ℂˣ`
   (`exists_character_extension`), and choose `χ` with `D χ = χ₀` (`D` is
   surjective). Then `φ` and `p ↦ Φ p χ` agree on every monomial
   `single m 1`. They are equal by `AddMonoidAlgebra.algHom_ext`; the second
   hypothesis of that lemma holds because there is at most one `ℂ`-algebra
   map `ℂ → ℂ`.
4. **Orbits.**
   - If `χ⁻¹ χ' ∈ S`, invariance at `χ` under `χ⁻¹ χ'` gives
     `f χ' = f χ`.
   - Conversely, for `a ∈ Λ′` the evaluation `E (single a 1)` lies in
     `F^S`. Equal values at `χ` and `χ'` give `D (χ⁻¹ χ') a = 1`. Hence
     `χ⁻¹ χ' ∈ S` by `mem_of_forall_annihilator`.

## Scope

The module adds no axioms and uses no `sorry`. Every result above is proved
for arbitrary universes of `Λ` and `X`. The hypotheses are exactly those
listed; the application discharges them with published results.
