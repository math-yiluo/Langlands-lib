# Residue-tensor injectivity on power-torsion coefficients

`Langlands.Algebra.ResidueTensorNilpotentInjectivityStatement` is an
unproved, derived internal support interface. It defines a proposition and
supplies no proof. Until an exact proof of this proposition is independently
accepted, it must not be used as an established result. It supports the
exact proof task `90c1db03-0049-445e-9845-423d7fb17ea0` for
`Langlands.Algebra.NoetherianLocalFiberInjectivityStatement`
(Stacks Project, Lemma 10.99.1, tag 00ME). It does not import, alter or
assume that statement.

## Statement

Let `R` be a commutative local ring with maximal ideal `m` and residue
field `k = R/m`. Let `f : A → B` be a map of `R`-modules with `B` flat
over `R`, and suppose that `k ⊗_R f : k ⊗_R A → k ⊗_R B` is injective.
Then, for every natural number `n` and every `R`-module `C` with
`m^n C = 0`, the map `C ⊗_R f : C ⊗_R A → C ⊗_R B` is injective.

## Exact Lean objects and scope

- `R : Type u` has `CommRing` and `IsLocalRing` instances. The modules
  `A : Type v`, `B : Type w` and `C : Type z` are additive commutative
  groups with `R`-module structures, and `f : A →ₗ[R] B` is `R`-linear.
  The four universes are independent.
- `IsLocalRing.ResidueField R` is Mathlib's residue field
  `R ⧸ IsLocalRing.maximalIdeal R`, an `R`-module through its algebra map.
  `LinearMap.lTensor (IsLocalRing.ResidueField R) f` is the actual map
  `k ⊗[R] A → k ⊗[R] B` sending `a ⊗ x` to `a ⊗ f x`.
- `Module.Flat R B` is Mathlib's flatness of `B` over `R`.
- The annihilation hypothesis
  `∀ r ∈ IsLocalRing.maximalIdeal R ^ n, ∀ c : C, r • c = 0` says that
  every element of the actual ideal power `m^n` acts by zero on `C`, that is,
  `m^n C = 0`.
- The conclusion is injectivity of the actual map
  `LinearMap.lTensor C f : C ⊗[R] A → C ⊗[R] B`, sending `c ⊗ x` to
  `c ⊗ f x`.

There are no Noetherian, finiteness or finite-presentation hypotheses, no
flatness hypothesis on `A` or `C`, no nonzero-module assumption, and no
second ring `S`. The number `n` may be `0`: then `m^0` is the unit ideal,
so the hypothesis forces `C = 0` and the conclusion holds trivially.

Taking `C = R ⧸ m^n` gives the injectivity of
`(R/m^n) ⊗_R A → (R/m^n) ⊗_R B`. Through the canonical identifications
`(R/I) ⊗_R N ≅ N/IN`, which need no flatness, this is the source's map
`u_n : N/m^n N → M/m^n M` described below. These identifications are not
part of the Lean statement, which uses tensor maps throughout.

## Provenance

The registered source is `stacks-algebra-flatness-criteria-2026-10-22`,
content SHA256
`4bc1f2db6141508f6dad2132d4abc7963380cd71497ad20620c0e511b972a949`,
file `00MD.html`, Section 10.99, Lemma 10.99.1 (tag 00ME). Its displayed
statement and complete proof were read. No source-specific errata note
for this source was found in the current Library's `notes/errata` or in the
project literature collection at the check on 27 October 2026.

In the source, `R → S` is a local homomorphism of local rings with `S`
Noetherian, `M` is a flat `R`-module, `N` is a finite `S`-module, and
`u : N → M` is `R`-linear. The first paragraph of the proof claims that
`u_n : N/m^n N → M/m^n M` is injective for all `n ≥ 1`. It inducts on `n`,
using flatness of `M` for the exact sequence
`0 → M ⊗_R m^n/m^{n+1} → M/m^{n+1}M → M/m^n M → 0`, and the identification
of tensor products with the residue-field vector space `m^n/m^{n+1}`.
That induction uses neither the Noetherian hypothesis on `S` nor the
finiteness of `N`; the source uses those later, for Krull's intersection
theorem and for the cokernel-flatness part.

This statement is a derived internal generalization of that first claim,
not a verbatim statement from the Stacks Project: the source treats only
the coefficients `R/m^n` with `n ≥ 1`, while here the coefficients are an
arbitrary `R`-module annihilated by `m^n`, `f`, `A` and `B` correspond to
the source's `u`, `N` and `M`, and no ring `S` appears. The
generalization lets a proof run the same induction on coefficient modules.

## Intended proof route (not supplied here)

A proof is separate work. The planned route is: if `m C = 0`, then `C` is
a module over the field `k` and `C ⊗_R f` is identified with the base
change of the injective `k`-linear map `k ⊗_R f` along `C ⊗_k -`, which
preserves injectivity. For `m^{n+1} C = 0`, use the exact sequence
`0 → mC → C → C/mC → 0`, where `m^n (mC) = 0` and `m (C/mC) = 0`.
Flatness of `B` keeps `mC ⊗_R B → C ⊗_R B` injective, and a diagram chase
with the right-exact sequence for `A` completes the induction.

## Authorship

The Lean interface is Worker 666's draft for task
`90c1db03-0049-445e-9845-423d7fb17ea0`, reused unchanged; this
Markdown extends Worker 666's draft description.
