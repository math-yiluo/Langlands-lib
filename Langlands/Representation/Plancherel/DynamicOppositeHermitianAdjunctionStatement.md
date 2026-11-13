# Hermitian adjunction of the opposite standard integrals (target)

Worker 5. `Langlands.Plancherel.ConditionalDynamicOppositeHermitianAdjunctionStatement`
is a Prop-valued target. It states the Hermitian form of Waldspurger's
adjunction IV.1 (11) for the Library's actual opposite standard integrals
`J_{P̄|P}` and `J_{P|P̄}` in the fixed compact pictures, on their convergence
domains. The module does not prove the target. It also defines the
conjugate-inverse `z† = z̄⁻¹` of a continuous complex character and of an
unramified character, and the compact-picture Hermitian pairing
`(φ, ψ) = ∫_K b(φ(k), ψ(k)) dk`. It proves three elementary facts about `z†`.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d'après Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI
10.1017/S1474748003000082, registered as `waldspurger-2003-plancherel`, PDF
SHA256 `4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.

- IV.1 (11), printed p.283 / PDF p.49: for all `f ∈ I_P^G V` and
  `f̌' ∈ I_{P'}^G V̌`, `⟨J_{P'|P}(π) f, f̌'⟩ = ⟨f, J_{P|P'}(π̌) f̌'⟩`. This is
  the bilinear adjunction for the contragredient, between operators viewed
  as rational functions of `π`.
- Proof of IV.3 (6), printed p.287 / PDF p.53. `V` carries a positive
  definite Hermitian product, and the compact pictures `I_{K∩P}^K V` and
  `I_{K∩P̄}^K V` carry the positive definite Hermitian products
  `(f, f') = ∫_K (f(k), f'(k)) dk`. For `χ ∈ Im X(M)` (unitary),
  `f ∈ I_{K∩P}^K V` and `f' ∈ I_{K∩P̄}^K V` the proof uses the adjunction
  `(J_{P̄|P}(π ⊗ χ) f, f') = (f, J_{P|P̄}(π ⊗ χ) f')`.
- Waldspurger's `K` (fixed in I.1) is a special maximal compact subgroup in
  good position relative to the minimal Levi subgroup, so
  `K ∩ P = (K ∩ M)(K ∩ U)` for every semistandard parabolic `P = MU`.

## Provenance of the target

The target is derived from the Hermitian adjunction in the proof of IV.3 (6).
Waldspurger states it for unitary `χ`, where the operators are the rational
continuations of the integrals. Unitary `χ` need not lie in the convergence
domain. The Library has the integrals on their convergence domains (the
families `conditionalForwardCompactFamily` and
`conditionalReverseCompactFamily`), and it does not yet have their
continuations as operators. The target is therefore stated on the
convergence domains.

There, the Hermitian adjunction pairs the parameter `z` of `J_{P̄|P}` with
the parameter `z† = z̄⁻¹` of `J_{P|P̄}`. The reason is the following. For a
`b`-invariant `A`, the Hermitian pairing of normalized inductions
`(f, f')_P = ∫_{P\G} b(f(g), f'(g)) dg` is `G`-invariant between
`I_P^G(A ⊗ z)` (first, conjugate-linear argument) and `I_P^G(A ⊗ z†)`
(second argument). This uses `conj(z(m)) z†(m) = 1`. At a unitary point
`z† = z` (`unramifiedConjInv_eq_self_of_mem_unitary`), so the target
specializes to Waldspurger's form whenever a unitary point lies in both
domains. The continuation to all unitary points is a separate step and is
not stated here.

The constant in the adjunction depends on the Haar normalizations. In the
Library the compact pictures integrate against the Haar probability measure
`CompactInduction.measure K hK` on `K`. The integrals use the source
measures `forwardQuotientMeasure` and `reverseQuotientMeasure`, which
give `K ∩ Ū` and `K ∩ U` volume `1`. Write `Ψ(g) = b(f(g), f'(g))` for `f`
in the `P`-induction and `f'` in the `P̄`-induction. `Ψ` is left
`M`-invariant, because the half-moduli of `P` and `P̄` are inverse on `M`.
The left side of the adjunction is `∫_K ∫_Ū Ψ(ū k) dū dk` and the right
side is `∫_K ∫_U Ψ(u k) du dk`, because `f'` is left `Ū`-invariant and `f`
is left `U`-invariant. Fix Haar measures with `vol(K) = 1` on `G` and
`vol(K ∩ M) = 1` on `M`, and the quotient measure on `M\G`. Write `m` for
the Levi projection. From `∫_G = ∫_P ∫_K`, with left Haar measure
`dm du / [m(K ∩ P) : K ∩ M]` on `P`, the right side equals
`[m(K ∩ P) : K ∩ M]` times the integral of `Ψ` over `M\G`. In the same
way, the left side equals `[m(K ∩ P̄) : K ∩ M]` times the same integral.
So the left side is `[m(K ∩ P̄) : K ∩ M] / [m(K ∩ P) : K ∩ M]` times the
right side. This ratio is `1` under the hypotheses `_hKsplit` and
`_hOppKsplit`, which say that the Levi projections send `P ∩ K` and
`P̄ ∩ K` into `K`. These hypotheses are the Lean form of Waldspurger's
property `K ∩ P = (K ∩ M)(K ∩ U)` and its analogue for `P̄`. Without them
the constant can differ from `1`, so they are hypotheses of the target.
They are not used to define anything.

Absolute convergence follows from the definition of the full domains (see
the target section below). The double integral over `K × Ū` reduces to
finitely many integrals over `Ū`, because the sections are right invariant
under an open subgroup of `K`, and `v ↦ b(w, v)` is a smooth-dual vector of
the twisted `A` for each `w`.

## The conjugate-inverse

- `unitsConj : ℂˣ →ₜ* ℂˣ` is complex conjugation on units
  (`Units.map` of `starRingEnd ℂ`), with `unitsConj_apply_coe`.
- `characterConjInv z = (unitsConj.comp z)⁻¹` for `z : G →ₜ* ℂˣ`, so
  `characterConjInv z g = conj(z g)⁻¹` (`characterConjInv_apply`,
  `characterConjInv_apply_coe`).
- Proved: `characterConjInv_characterConjInv` (an involution), and
  `characterConjInv_eq_self_of_mem_unitary` (`z† = z` when `‖z g‖ = 1` for
  all `g`, i.e. `z ∈ unitaryCharacters G`).
- `unramifiedConjInv ν z` is the same map on the Library's
  `unramifiedCharacters ν`. It preserves the defining condition (triviality
  on the common kernel), because `conj(1)⁻¹ = 1`. Proved:
  `unramifiedConjInv_val`, `unramifiedConjInv_unramifiedConjInv`, and
  `unramifiedConjInv_eq_self_of_mem_unitary` for
  `z.val ∈ unitaryUnramifiedCharacters ν`.

## The pairing

`compactPictureHermitianPairing h K hK A b φ ψ` is
`∫ k : K, b.inner (eval φ k) (eval ψ k) ∂CompactInduction.measure K hK`.
Here `h : IsSemidirectDecomposition P M U`, `φ ψ` are sections in
`CompactInductionPicture h K A`, and `b : InvariantPositiveForm
A.representation` is an `M`-invariant positive definite Hermitian form,
conjugate-linear in its first argument. The module only defines the
pairing; it proves nothing about it.

## The target

`ConditionalDynamicOppositeHermitianAdjunctionStatement` quantifies over:

- a nonarchimedean local field `F` and an affine group scheme `G` over `F`
  of locally finite type, a cocharacter `χ : 𝔾_m → G`, the structural
  premises `hRefl`, `hCST` and `hG : IsConnectedReductive G` used by the
  Library's integrals, with `P = parabolic χ`, `P̄ = oppositeParabolic χ`
  and `M = levi χ`;
- a compact open subgroup `K` of `G(F)` with `G(F) = P K` (`hPK`) and
  `G(F) = P̄ K` (`hOppK`);
- the split hypotheses `_hKsplit` and `_hOppKsplit`: for `p ∈ P ∩ K`,
  `(decomposition χ).projection p ∈ K`, and the same for `P̄`;
- a smooth complex representation `A` of `M(F)` with an invariant positive
  form `b`;
- `z ∈ forwardFullDomainRegion χ K hK A`, and the hypothesis
  `hz : z† ∈ reverseFullDomainRegion χ K hK A`;
- `φ` in the compact picture for `P`, and `φ'` in the compact picture for
  `P̄`.

The conclusion is

```
(J_{P̄|P}(z) φ, φ')_{P̄} = (φ, J_{P|P̄}(z†) φ')_P,
```

with `J_{P̄|P}(z) = conditionalForwardCompactFamily … A z`,
`J_{P|P̄}(z†) = conditionalReverseCompactFamily … A ⟨z†, hz⟩` and
`( , )_P`, `( , )_{P̄}` the pairing above for `decomposition χ` and
`oppositeDecomposition χ`.

The full domains are where every section has absolutely convergent
smooth-dual scalar integrals (`standardIntertwiningFullDomainRegion`). No
openness or nonemptiness of the domains is asserted. The hypothesis `hz` is
kept. It would follow from a proof that `z ↦ z†` maps the forward domain
onto the reverse domain, which is not available in the Library.

The Borel `MeasurableSpace` and `BorelSpace` instances on `RationalPoint F
G.X` are local instances of this module. They are needed to form
`CompactInduction.measure`.

## Intended use

In the proof of IV.3 (6), the adjunction at unitary points gives
`j(π ⊗ χ)(e, e) = ‖J_{P̄|P}(π ⊗ χ) e‖²`. With the target
`ConditionalDynamicOppositeUnitaryScalarStatement` (module
`DynamicOppositeUnitaryScalarStatement`), this target is meant to be used to
show that `j_P` is real and nonnegative at unitary points. That step also
needs an identity theorem for the rational continuations. It is not part of
this module.

## Not proved here

The target itself. Its continuation from the convergence domains to all
unitary points. The bilinear form IV.1 (11) with the contragredient.

## Axioms

The proved lemmas use only `propext`, `Classical.choice` and `Quot.sound`.
The target is a `def … : Prop` and introduces no axioms.
