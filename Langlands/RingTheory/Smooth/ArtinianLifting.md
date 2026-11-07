# Smoothness from lifting along elementary Artinian surjections

This module proves a ring-theoretic infinitesimal lifting criterion for
smoothness over a noetherian base. Lifting is required only along surjections of
local Artinian algebras. It is the algebraic core of the criterion of The Stacks
Project, Lemma 37.12.1 (Tag 02HX), implication (4) ⇒ (1). The cited source is
the snapshot `stacks-artin-axioms-approximation-2026-11-06`, file `02HX.html`.
Its proof reduces to Algebra, Lemma 10.141.2, which is not in the snapshot. The
proof here is an independent argument through Mathlib's Jacobian criterion.

Namespace: `Langlands.RingTheory.ArtinianLifting`. All rings live in one
universe `u`.

## The lifting condition

Let `C` be a commutative ring and `S` a commutative `C`-algebra.
`HasArtinianLifting C S : Prop` says the following. Let `B'` and `B` be local
Artinian `C`-algebras in `Type u` and `φ : B' →ₐ[C] B` a surjection with
`maximalIdeal B' * ker φ = ⊥`. Let `ψ : S →ₐ[C] B` be a map whose composite with
the residue map `B → ResidueField B` is surjective. Then `φ.comp ψ' = ψ` for some
`ψ' : S →ₐ[C] B'`.

The kernel condition is the convention of the Library's
`ArtinianTest.IsElementarySurjection`. It is weaker than the Stacks "small
extension" condition, which also asks for a length-one kernel, so more
surjections are tested. The surjective residue map replaces the
Stacks condition `κ(x) ≅ κ(m)`. It forces the kernel of `S → ResidueField B` to
be a maximal ideal `q` of `S`, with `S/q ≅ ResidueField B`.

## Main results

Assume `C` is noetherian and `S` is of finite type over `C`.

- `formallySmooth_localization (h : HasArtinianLifting C S) (q) [q.IsMaximal]`:
  `Localization.AtPrime q` is formally smooth over `C`.
- `smooth (h : HasArtinianLifting C S) : Algebra.Smooth C S`. Finite
  presentation comes from `Algebra.FinitePresentation.of_finiteType`.
  Mathlib's `Algebra.isOpen_smoothLocus` makes the smooth locus open. If its
  closed complement were nonempty, it would contain a closed point
  (`IsClosed.exists_closed_singleton`), that is, a maximal ideal. The previous
  result rules this out. So the smooth locus is everything, and
  `Algebra.smoothLocus_eq_univ_iff` gives formal smoothness.

## Proof of `formallySmooth_localization`

Choose a surjection `π : MvPolynomial (Fin n) C →ₐ[C] S`. Let
`Q = π⁻¹(q)`, a maximal ideal, `Pm = Localization.AtPrime Q`, and
`Sq = Localization.AtPrime q`. The map `ρ : Pm → Sq` is
`Localization.localRingHom`, and it is surjective. Put `I = ker ρ` and let
`m` be the maximal ideal of `Pm`.

`Pm` is formally smooth over `C`, as a localization of a polynomial ring. Its
Kähler differentials have the basis `Module.Basis.ofIsLocalizedModule` of
`KaehlerDifferential.mvPolynomialBasis`, so they are finite free. `I` is
finitely generated because `Pm` is noetherian. Mathlib's Jacobian criterion
`Algebra.FormallySmooth.iff_injective_cotangentComplexBaseChange_residueField`
reduces the claim to injectivity of

```
cotangentComplexBaseChange C Sq Pm κ : κ ⊗[Pm] I → κ ⊗[Pm] Ω[Pm/C],
```

where `κ = ResidueField Sq`.

The Artin–Rees lemma (`Ideal.exists_pow_inf_eq_pow_smul`) gives `k` with
`m^(k+1) ⊓ I ≤ m * I`. Put `N = k + 1` and define the ideals

```
testIdeal = m * I ⊔ m^N,   baseIdeal = I ⊔ m^N.
```

Both are proper and contain `m^N`. `quotient_isLocalRing` and
`quotient_isArtinianRing` make `B' = Pm ⧸ testIdeal` and `B = Pm ⧸ baseIdeal`
local Artinian. The factor map `φ : B' → B` is surjective, and its kernel, the
image of `baseIdeal`, is killed by the maximal ideal: `m * (I ⊔ m^N) ≤
m * I ⊔ m^N`. The map `ψ : S → B` is `S → Sq ≅ Pm ⧸ I → B`. Its residue map is
surjective. To see this, write an element of `Pm` as `a / t` with `t ∉ Q`.
Choose `t'` and `i ∈ Q` with `t' * t + i = 1`. Then `a / t` and `a * t'` have
the same residue, and `a * t'` is in the image of `S` through `π`.

The hypothesis gives `ψ' : S →ₐ[C] B'` with `φ.comp ψ' = ψ`. It sends
`q.primeCompl` to units, because `φ` is a local homomorphism. So it extends to
`Sq` (`IsLocalization.liftAlgHom`). Composing with `ρ` gives
`σ : Pm →ₐ[C] B'` with `σ(I) = 0` and `φ ∘ σ = mk baseIdeal`.

The core (sections `Core` and `Derivation`) works for any surjection
`P → T` of local rings with these data:

- `tmul_eq_zero_of_mem_mul`: elements of `m * I` vanish in `κ ⊗[P] I`.
- `testIdeal_inf_le`: `testIdeal ⊓ I ≤ m * I`, by the modular law and the
  Artin–Rees bound.
- `tmul_eq_of_mk_eq`: if `j, j' ∈ I` have the same image in `B'`, then
  `1 ⊗ j = 1 ⊗ j'` in `κ ⊗[P] I`.
- `exists_rep`, `rep`, `mk_rep`: for each `p`, the difference
  `σ p - mk p` lies in `ker φ`, the image of `I`. Here `rep p ∈ I` is a chosen
  representative.
- `delta : Derivation C P (κ ⊗[P] I)` sends `p` to `1 ⊗ rep p`. Additivity,
  `C`-linearity, `δ 1 = 0` and the Leibniz rule follow from `tmul_eq_of_mk_eq`.
  For Leibniz, the cross term `(σ p - mk p)(σ p' - mk p')` is the image of an
  element of `I * I ≤ m * I`, so it vanishes in `B'`.
- `delta_apply_of_mem`: `δ j = -(1 ⊗ j)` for `j ∈ I`, since `σ j = 0`.
- `injective_cotangentComplexBaseChange`: let `G` be the base change to `κ` of
  `delta.liftKaehlerDifferential`. Then `G` composed with the cotangent map is
  `-id` on `κ ⊗[P] I`, checked on pure tensors. Hence the cotangent map is
  injective.

## Provenance

Derived from The Stacks Project, More on Morphisms, Lemma 37.12.1 (Tag 02HX),
implication (4) ⇒ (1), in the affine case that its proof reduces to. The
hypotheses differ in two ways, both recorded above: elementary instead of small
extensions, and a surjective residue map instead of `κ(x) ≅ κ(m)` at an
arbitrary point. The conclusion is stated for the whole finite-type algebra.
The Lean proof is new: it uses Mathlib's Jacobian criterion, the Artin–Rees
lemma and an explicit derivation. It does not follow the source's route.
