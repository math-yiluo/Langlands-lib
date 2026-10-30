# Hom out of permutation modules: functions and freeness

Author: Worker 61. Built on the published
`Langlands.Representation.Induction.PermutationModule` (`permutation`,
`permutation_apply`, `permutation_single`, `permutationFinsuppEquiv`) and
`Langlands.Representation.Induction.PermutationInvariants`
(`asModuleLinearEquiv`). From Mathlib it uses Hom representations
(`Representation.linHom`), trivial and free representations
(`Representation.trivial`, `Representation.free` and its freeness over the
group algebra, `Representation.free_asModule_free`), equivalences of
representations (`Representation.Equiv`), finitely supported functions
(`Finsupp.llift`, `Finsupp.lsum`, `Finsupp.linearEquivFunOnFinite`,
`Finsupp.mapRange.linearEquiv`, `Finsupp.domLCongr`,
`Finsupp.curryLinearEquiv`), orbit spaces (`MulAction.orbitRel.Quotient`),
the bijection `MulAction.selfEquivOrbitsQuotientProd` for free actions, the
freeness of cancellative actions (`IsCancelSMul.stabilizer_eq_bot`), bases
and free modules (`Module.Basis`, `Module.Free.chooseBasis`,
`Module.Free.of_equiv`), and the freeness of `Hom_R(M, W)` for `M` finite
free and `W` free.

All new names are in the namespace `Langlands.Induction`. `R` is a
commutative ring, `G` a group acting on a set `X`, and `M`, `W` are
`R`-modules.

## Conventions

`permutation R G X M` is the published representation of `G` on
`M[X] = X →₀ M` in which `g` moves the value at `x` to `g • x`. For
representations `ρ` on `V` and `σ` on `W`, Mathlib's `ρ.linHom σ` is the
representation on `V →ₗ[R] W` with `g • φ = σ g ∘ φ ∘ ρ g⁻¹`.
`MulAction.orbitRel.Quotient G X`, written `X / G`, is the set of orbits,
and `ω.out` is a chosen point of the orbit `ω`. The action is free when
every stabilizer is trivial, `h : ∀ x, MulAction.stabilizer G x = ⊥`. For a
representation `ρ`, `ρ.asModule` is its module over the group algebra
`MonoidAlgebra R G`, written `R[G]`.

## Functions and group rings

`σ` is a representation of `G` on `W`.

- `functionRepresentation σ X`: the representation of `G` on all functions
  `X → W` with `(g • f) x = σ g (f (g⁻¹ • x))`; `functionRepresentation_apply`
  (simp lemma) states this formula.
- `permutationDualEquiv σ X`: an equivalence of representations from
  `(permutation R G X R).linHom σ`, the representation on
  `Hom_R(R[X], W)`, to `functionRepresentation σ X`. The linear equivalence
  is the inverse of Mathlib's `Finsupp.llift`; it sends `φ` to the function
  `x ↦ φ (single x 1)` (`permutationDualEquiv_apply`). This is Harris's
  "duality between functions and group rings".
- `permutationHomEquiv σ X M`: the version with coefficients `M`: an
  equivalence of representations from `(permutation R G X M).linHom σ` on
  `Hom_R(M[X], W)` to `functionRepresentation τ X` on functions
  `X → Hom_R(M, W)`, where `τ = (Representation.trivial R G M).linHom σ` lets
  `G` act on `Hom_R(M, W)` through `W` only. The linear equivalence is the
  inverse of Mathlib's `Finsupp.lsum`, sending `φ` to `x ↦ φ ∘ single x`.
- `functionPermutationEquiv σ X hσ`: for finite `X` and
  `hσ : ∀ g, σ g = LinearMap.id` (`G` acts trivially on `W`), an equivalence
  of representations from `functionRepresentation σ X` to
  `permutation R G X W`; it keeps the values of a function
  (`functionPermutationEquiv_apply`).
- `permutationHomPermutationEquiv σ X hσ M`: for finite `X` and `G` acting
  trivially on `W`, the composite of the two previous equivalences, from
  `(permutation R G X M).linHom σ` to `permutation R G X (M →ₗ[R] W)`;
  `permutationHomPermutationEquiv_apply` gives its value at `x` and `m` as
  `φ (single x m)`.

## Free actions

- `freeActionEquiv h`: for a free action, the bijection
  `G × X / G ≃ X`, `(g, ω) ↦ g • ω.out` (`freeActionEquiv_apply`, true by
  definition). It is defined as the inverse of Mathlib's
  `MulAction.selfEquivOrbitsQuotientProd h : X ≃ X / G × G` composed with the
  swap of the factors.
- `freeActionEquiv_symm_smul h g x`: the inverse of `freeActionEquiv h` sends
  `g • x` to `(g * a, ω)` when it sends `x` to `(a, ω)`; that is, the
  bijection is equivariant for left multiplication on the factor `G`. Proof:
  `g • (a • ω.out) = (g * a) • ω.out`.

## Freeness over the group algebra

- `permutationCongr R G X e`: a linear equivalence `e : M ≃ W` induces an
  equivalence of representations from `permutation R G X M` to
  `permutation R G X W` (apply `e` to the values).
- `permutationFreeActionEquiv R G h`: for a free action, an equivalence of
  representations from `permutation R G X W` to the permutation
  representation of `G` on `G` (left multiplication) with coefficients
  `X / G →₀ W`. The linear equivalence reindexes `X →₀ W` along the inverse
  of `freeActionEquiv h` and curries `G × X / G →₀ W` to
  `G →₀ X / G →₀ W`; the intertwining condition follows from
  `freeActionEquiv_symm_smul`.
- `permutationFreeEquiv R G h b`: for a free action and a basis `b` of `W`
  indexed by `I`, an equivalence of representations from
  `permutation R G X W` to Mathlib's free representation
  `Representation.free R G (X / G × I)`. It is
  `permutationFreeActionEquiv`, then `permutationCongr` along
  `X / G →₀ W ≃ X / G →₀ I →₀ R ≃ X / G × I →₀ R` (coordinates in `b`,
  then uncurrying), then the published `permutationFinsuppEquiv` for
  `X = G`.
- `permutation_asModule_free h`: for a free action and a free `R`-module
  `W`, `(permutation R G X W).asModule` is a free `R[G]`-module. Proof:
  `permutationFreeEquiv` for the chosen basis of `W`, turned into an
  `R[G]`-linear equivalence by `asModuleLinearEquiv`, and
  `Representation.free_asModule_free`.
- `linHom_permutation_asModule_free h`: if `X` is finite, the action on `X`
  is free, `M` is a finite free `R`-module and `W` a free `R`-module, then
  the representation `(permutation R G X M).linHom (Representation.trivial R G W)`
  on `Hom_R(M[X], W)` (`G` acting trivially on `W`) is a free `R[G]`-module.
  Proof: `permutationHomPermutationEquiv` identifies it with the permutation
  representation on `Hom_R(M, W)[X]`, and `Hom_R(M, W)` is a free
  `R`-module, so `permutation_asModule_free` applies.
- `linHom_permutation_subgroup_asModule_free S`: for a subgroup `S` of a
  finite group `Q`, acting on `Q` by left multiplication (which is free,
  `IsCancelSMul.stabilizer_eq_bot`), `Hom_R(M[Q], W)` is a free
  `R[S]`-module, for `M` finite free and `W` free with trivial actions.

## Provenance and interpretation

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), §4 (Worker 61 read the rendered scanned
pages):

- printed p.311 (one-based PDF page 13), after (4.7): "The right-hand side
  of (4.7) is the sum of `M` copies of the group `D_m(K_{ℓ,m} × C_p/H_p)` of
  `𝒪_m`-valued functions on `K_{ℓ,m} × C_p/H_p`. Via the duality between
  functions and group rings, this is canonically isomorphic to
  `Hom(𝒪_m[K_{ℓ,m} × C_p/H_p]^M, 𝒪_m)`, and thus the decomposition (4.6)
  yields a canonical isomorphism (4.8)
  `𝒜_ℓ(GJ, 𝓛_m, H(m))^K_ℓ ≅ Hom(𝒪_m[C_p/H_p]^M, 𝓛_m)`";
- printed p.312 (one-based PDF page 14), proof of Proposition 4.10: "Since
  `C^j_m(ẽ)^{H_p}` and `Hom(𝒪_m[C_p/H_p]^M, 𝓛_m)` are both free
  `𝒪/ℓ^m𝒪[S(ẽ)/H_p]`-modules, it follows that the maps (4.10.3) are
  surjective for all `m`." On p.311 Harris also notes that, up to
  conjugacy, `S(ẽ) ⊂ C_p` for all `ẽ` that contribute.

In this module `R` plays `𝒪_m = 𝒪/ℓ^m𝒪`, `X` a finite set such as
`C_p/H_p`, and `M` the free module `𝒪_m^M`, so that `M[X] ≅ 𝒪_m[X]^M`.
`permutationDualEquiv` and `permutationHomEquiv` formalize the duality
between functions and group rings, and `linHom_permutation_asModule_free`
the freeness of `Hom(𝒪_m[C_p/H_p]^M, 𝓛_m)`, with `W` in the role of `𝓛_m`.
That `S(ẽ)/H_p` acts trivially on `𝓛_m` (on which the `ℓ`-adic group
`K_ℓ` acts) and freely on `C_p/H_p` is our reading of Harris's setting:
`linHom_permutation_subgroup_asModule_free` covers it with
`Q = C_p/H_p` and `S = S(ẽ)/H_p` when `H_p` is a normal subgroup of `C_p`
contained in `S(ẽ)`; in general the freeness of the action is the
hypothesis `h`. Harris uses freeness for the surjectivity of (4.10.3); the
published `FreeOverPowQuotient` and `PowTorsionProjective` (module
`Langlands.Cohomology.DivisibleSystem.FreeTorsionProjective`) carry that
step for representations over `𝒪` killed by `ℓ^m`.

The module is derived: the duality between functions and group rings and
the freeness of permutation modules for free actions are standard, and the
definitions, the reduction to free representations and the proofs are ours.

## Scope

The identifications (4.7) and (4.8) of spaces of automorphic forms with
these modules, the groups `K_{ℓ,m}`, `C_p`, `H_p` and `S(ẽ)`, and the
`K_ℓ`-invariants in (4.8) are not formalized. The freeness is proved over
the group algebra of an arbitrary commutative ring `R`; this module does not
derive the published `FreeOverPowQuotient ℓ m` for representations over
`𝒪` from it (that needs the comparison of a representation over `𝒪/ℓ^m𝒪`,
restricted to `𝒪`, with its `torsionQuotientRep`). Infinite `X` is treated
only for `W[X]` (`permutation_asModule_free`), not for Hom modules.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Dependencies are the modules named above, pinned to Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
