# The tame quotient of inertia

Laumon (1987), (2.1.1), p. 151, works with a henselian trait of equal characteristic `p` whose
residue field `k` is perfect ((0.1), p. 134). The action of the inertia group `I` on the roots
of order prime to `p` of a uniformizer `π` factors through a canonical quotient
`I → Ẑ'(1)(k̄)`, where `Ẑ'(1)(k̄) = lim μ_N(k̄)` over the integers `N` prime to `p`, and
`μ_N(k̄)` acts on the `π^(1/N)` in the evident way. This is the tame quotient; its kernel is
the unique pro-`p` Sylow subgroup `P`, the wild inertia. At finite levels this is the
structure of the first lower ramification group (Serre, *Local Fields*, IV §2, Proposition 7
and Corollaries 1–4, pp. 66–68): for a finite Galois extension `L/K` with separable residue
extension and a uniformizer `π_L` of `L`, the map sending the class of `s ∈ G₀` in `G₀/G₁` to
the reduction of the unit `s(π_L)/π_L` in the residue field of `L` is an injective
homomorphism; its image is cyclic of order prime to `p`, and `G₁` is the `p`-Sylow subgroup of
`G₀`.

## The inverse limit of the roots of unity

- `TameIndex p` is the type of integers `n ≥ 1` with `p ∤ n`.
- `tameRootsSubgroup F p` is the subgroup of the product `∏_{n} Fˣ` of the families `(ζ_n)`
  with `ζ_n ^ n = 1` and `ζ_m ^ (m/n) = ζ_n` whenever `n ∣ m`: the inverse limit of the
  groups `μ_n(F)` for the transition maps `ζ ↦ ζ^(m/n)`.
- `TameRoots F p` is this inverse limit as a type, with its commutative group structure and
  the subspace topology of the product of the discrete groups `Fˣ`. As the components lie in
  the finite groups `μ_n(F)`, this is the profinite inverse limit topology.
- `TameRoots.component ζ n` is the component `ζ_n`, as an element of `F`.

## `LocalTameInertiaQuotientStatement`

For a finite field `k` with `p = ringChar k`, put `X = LaurentSeries k` and
`Ω_X = SeparableClosure X`. Let `Ω = endGenericClosure k`, the separable generic closure of the
end trait, let `t ∈ Ω` be the uniformizer of the end trait, and let `k̄ = endConstants k` be the
algebraic closure of `k` in `Ω`, the residue field of the strict end trait. The Galois groups
act on `Ω` through `completionRestriction k` of `Langlands.Correspondence.Laumon.Completion`.

1. **Galois side.** There is an isomorphism of topological groups `θ` from the quotient of the
   Library's `Langlands.LocalGalois.SepClosed.absoluteInertia X Ω_X` by
   `Langlands.Ramification.Local.localWildInertia X Ω_X` onto `TameRoots k̄ p` with:
   - for every inertia element `σ`, every `n` prime to `p` and every `ϖ ∈ Ω` with `ϖ^n = t`,
     `σ(ϖ) = θ(σ)_n · ϖ`: the tame character is the action on the roots of the uniformizer,
     as in Laumon (2.1.1);
   - for every `g` in the Galois group and inertia elements `σ`, `τ` with `τ = g σ g⁻¹`,
     `θ(τ)_n = g(θ(σ)_n)`: conjugation corresponds to the Galois action on the roots of unity.
     By `HenselianCompletionRamificationStatement`, clause 2, the action of `g` on `k̄` is the
     Library's residue map `absoluteResidueHom`.
2. **Weil side.** The same holds for the inertia subgroup
   `Langlands.Weil.Local.SepClosed.localInertia X Ω_X` of the Library's local Weil group,
   modulo the preimage of wild inertia under `localProjection X Ω_X`. The Weil group acts
   through `localProjection`, and conjugation is by Weil elements.

The statement is read over the strict end trait. The roots `ϖ` are taken in the separable
closure of the henselian end field, and the `n`-th component is a root of unity in the
constants `k̄`. The groups are the Library's groups of the completion, carried there by the
bridge (b2) of `Langlands.Correspondence.Laumon.Completion`. In that module,
`HenselianCompletionRamificationStatement`, clauses 1 and 4, identifies them with the inertia
and the wild inertia of the strict trait. The Kummer formula determines `θ`: an inertia element
fixes the roots of unity of order prime to `p`, as they lie in the maximal unramified
subextension. So `σ(ϖ)/ϖ` does not depend on the chosen root `ϖ`, and the conjugation clause
follows from it. The conjugation identity expresses equivariance for the residue Galois
action on the inverse limit.

## Library declarations

The module imports `Langlands.Correspondence.Laumon.Completion`. It uses the Library's
`Langlands.LocalField.Laurent.valuativeRel` (as a local instance),
`Langlands.LocalGalois.SepClosed.absoluteInertia`,
`Langlands.Ramification.Local.localWildInertia`,
`Langlands.Weil.Local.SepClosed.localWeilGroup`, `localInertia` and `localProjection`, and
`endGenericClosure`, `endConstants` and `endUniformizer` from
`Langlands.Correspondence.Laumon.Traits`, and `completionRestriction` from
`Langlands.Correspondence.Laumon.Completion`. It uses no further declaration of weil-conjectures. Every
declaration of this module depends at most on `propext`, `Classical.choice` and `Quot.sound`.
