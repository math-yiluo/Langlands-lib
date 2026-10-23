# Actual geometric monodromy on prime-adic Tate modules

Author: Worker 142.

This module constructs the geometric action on the existing integral and
rational prime-adic Tate modules of an actual abelian scheme. It proves
integral joint continuity, equivariance of actual homomorphisms, and
compatibility with selected, full, and away prime-coordinate maps, including
their existing semilinear forms.

## Sources and derived provenance

- Edixhoven–van der Geer–Moonen, *Abelian Varieties*, preliminary draft built
  2012-02-08, Chapter X, (10.2)–(10.3), printed p.142 / PDF p.146,
  (10.5), printed p.143 / PDF p.147, and Definitions (10.25)–(10.26),
  printed p.150 / PDF p.154. Registered source:
  `edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256
  `81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
  Pages 142–143 describe the coordinatewise prime-adic scalar action, the
  Galois representation on the prime-power limit and its rationalization,
  and the equivariance of maps induced by homomorphisms. The ordinary
  prime-adic case in that discussion assumes the prime differs from the
  field characteristic. Page 150 defines the finite étale fibre functor
  and its automorphism group over a connected locally noetherian scheme.
- Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura Varieties*
  (2001), Chapter I, printed p.18 / PDF p.26, and Section III.1, printed
  pp.91–92 / PDF pp.99–100. Registered source:
  `harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA256
  `5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
  Page 18 supplies the full and away rationalization conventions. Pages
  91–92 use geometric monodromy in the full and prime-to-prime invariant
  orbit conditions.

These passages were read directly. No source-specific errata file was found
in the available Library. The construction is **derived**: the published
finite-level geometric action is evaluated on each existing prime-power
coordinate, then extended through the existing tensor product. The
comparison laws follow from the definitions of the published coordinate
maps. The arbitrary selected-predicate API is an internal generalization,
not a claim that these declarations appear verbatim in either source.

## Actual objects and explicit assumptions

The action declarations are in `Langlands.AbelianScheme.Tate.PrimeAdic`.
Fix an actual abelian scheme `A : AbelianScheme S`, a field `Ω`, a point
`s : Spec (.of Ω) ⟶ S`, and a prime `p : ℕ` with `[Fact p.Prime]`.
The geometric inputs remain explicit:

```lean
hfin : ∀ Y : FiniteEtale.Cover S, Finite (FiniteEtale.Fiber s Y)
htor : Langlands.AbelianScheme.TorsionFiniteEtaleStatement
hu : ∀ n : ℕ, IsUnit ((p ^ n : ℕ) : Γ(S, ⊤))
```

The theorem `primePower_isUnit` derives the last family from the single
hypothesis `IsUnit (p : Γ(S, ⊤))`, using preservation of units under powers
and the natural-number cast formula. Its proof does not need primality.
The displayed hypotheses ensure that every actual multiplication kernel
used by this construction is finite étale. They are not proved geometric
existence assertions in this unit.

The acting group is the imported `FiniteEtale.FundamentalGroup s hfin`,
the automorphism group of the actual finite-fibre functor, with its existing
evaluation topology. The intended geometric application uses algebraically
closed `Ω` and connected locally noetherian `S`. The conditional construction
here works for a field-valued point once the displayed hypotheses are given;
this broader scope does not assert the Galois-category classification.

The integral carrier is exactly `PrimeAdic.Integral A (Over.mk s) p`,
the coherent submodule of actual `A[p^n]` torsion sections, with its existing
coordinatewise `ℤ_[p]` action and product-subspace topology. Successive
transitions are multiplication by `p`. The rational carrier is exactly
`PrimeAdic.Rational A (Over.mk s) p`, namely
`ℚ_[p] ⊗[ℤ_[p]] PrimeAdic.Integral A (Over.mk s) p`.
No new carrier, supplied family of actions, or chosen basis is introduced.

## Integral action, linearity, and topology

`levelMonodromyLinear` equips the existing finite-level geometric action at
order `p^n` with `ℤ_[p]`-linearity. Its scalar proof applies
`levelMonodromy_zmod_smul` to `PadicInt.toZModPow n a`.
The underlying finite action evaluates the geometric automorphism at the
actual multiplication-kernel cover, through the existing kernel-point
identification.

`monodromyMap` applies the published prime-adic universal lift to these
linear maps composed with the coordinate projections. Finite-level
transition equivariance and coherence of the input sequence prove that
the output is coherent. `evaluation_monodromyMap` is its defining formula:

```text
(ρ_p(g)x)_n = ρ_{p^n}(g)(x_n).
```

`monodromyMap_one` and `monodromyMap_mul` follow from finite-level action
laws by subtype and coordinate extensionality. In particular the order is

```text
ρ_p(g*k)(x) = ρ_p(g)(ρ_p(k)(x)).
```

`monodromy` bundles the map as an `ℤ_[p]`-linear equivalence. Its inverse
is the map for `g⁻¹`; the two inverse identities use the preceding group
laws. `monodromy_apply` identifies the underlying map.
`monodromyRepresentation` is the resulting group homomorphism into
`ℤ_[p]`-linear automorphisms, whose multiplication is composition.
`monodromyAction` supplies the same additive action as a locally installable
`DistribMulAction`; no global instance chooses an action.

`continuous_monodromy_coordinate` proves joint continuity in the group and
Tate variables. It composes finite-level joint continuity with the map
`(g,x) ↦ (g,evaluation n x)`. `continuous_monodromy` then uses the product
and subtype continuity criteria. This uses precisely the existing topology
on the prime-power limit. `monodromyAction_continuousSMul` packages the same
result for the locally installed action. No new compactness or topological
scalar-multiplication theorem is asserted.

For an actual abelian-scheme homomorphism `f : A ⟶ B`, `monodromy_map` proves
that the existing map on integral prime-adic Tate modules intertwines these
actions. Coordinate extensionality reduces it to `levelMonodromy_map`.
Equivariance of `f` is a conclusion, not a supplied hypothesis.

## Rational extension

`rationalMonodromyMap` is `LinearMap.baseChange ℚ_[p]` applied to
`monodromyMap`. Its pure-tensor formula is

```text
ρ_{V_p}(g)(a ⊗ x) = a ⊗ ρ_p(g)(x).
```

`rationalMonodromyMap_one` and `rationalMonodromyMap_mul` use tensor induction
and the integral action laws. `rationalMonodromy` packages the map as an
`ℚ_[p]`-linear equivalence with inverse given by `g⁻¹`.
`rationalMonodromy_apply` identifies its function, and
`rationalMonodromyRepresentation` bundles the same action as a group
homomorphism. `toRational_monodromy` proves equivariance of the existing
map `x ↦ 1 ⊗ x`. It asserts no injectivity. `rationalMonodromy_map` proves
equivariance for the existing rational map induced by `f : A ⟶ B`, by
tensor induction and the integral naturality theorem.

This part is algebraic. It does not define a topology on the rational carrier
or prove continuity there.

## Selected, full, and away comparison laws

The comparison declarations are in
`Langlands.AbelianScheme.Tate.PrimeComparison`. For a predicate
`P : ℕ → Prop`, assume the existing selected invertibility condition

```lean
hu : ∀ n : GroupScheme.Tate.Index P, IsUnit (n.val : Γ(S, ⊤))
hP : ∀ n : ℕ, P (p ^ n)
```

The prime action uses the restriction
`fun n => hu (primePowerIndex P p hP n)` of this same invertibility proof.
`toPrime_monodromy` proves equivariance of the existing additive coordinate
map. Both sides read the identical prime-power coordinate and apply the
same finite action, so the proof is definitional equality.
`toPrimeContinuousSemilinear_monodromy` proves this for the existing
continuous semilinear map over
`Global.ProfiniteIntegerRing.toPadic p`. Its scalar and continuity laws
remain those already constructed in `PrimeScalars`.

`rationalToPrime_monodromy` proves equivariance of the existing rational
coordinate map. Its source and target have different scalar-extension
rings:

```text
Q ⊗_Z T_P  →  Q_p ⊗_{Z_p} T_p,
q ⊗ x      ↦  (q : Q_p) ⊗ toPrime(x).
```

Tensor induction reduces equivariance to this formula and
`toPrime_monodromy`. `rationalToPrimeSemilinear_monodromy` gives the same
law for the published semilinear map over
`Global.ProfiniteIntegerRing.rationalToPadic p`. Thus the scalar-compatible
coordinate map is itself equivariant; no identification with a restricted
product or finite-adelic ring is assumed.

The full specializations are
`fullToPrimeContinuousSemilinear_monodromy`,
`rationalFullToPrime_monodromy`, and
`rationalFullToPrimeSemilinear_monodromy`. They select every positive order.
The away specializations are
`awayToPrimeContinuousSemilinear_monodromy`,
`rationalAwayToPrime_monodromy`, and
`rationalAwayToPrimeSemilinear_monodromy`. They use
`P(k) = Nat.Coprime k m` and require `hp : Nat.Coprime p m`.
The witness `hp.pow_left n` retains every prime power. These are
specializations of the selected law, with no new comparison hypotheses.
For nonzero `m` the retained primes do not divide `m`; `m = 1` retains
all primes, while `m = 0` has no prime satisfying `hp`.

## Remaining scope

This unit does not prove the geometric hypotheses, the Galois-category
classification, prime-product or restricted-product comparison theorems,
rational continuity, pairings, or pointed base change. It does not construct
a prime-adic Hom⁰/End⁰ action or identify the field-valued fibre-functor
automorphism group with an absolute Galois group. The source's usual Galois
representation is motivating provenance for the actual geometric
construction, not an additional identification proved here. Weil pairings,
base-point independence, and invariant-orbit PEL level assembly remain
separate obligations of the parent task.
