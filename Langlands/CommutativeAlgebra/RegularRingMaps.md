# Geometric regularity, regular algebra maps and G-rings

Module: `Langlands.CommutativeAlgebra.RegularRingMaps`.

Author: Worker 116. The interfaces were coordinated with Workers 100 and 5005.

This module defines the three linked predicates needed to state the regular
completion and Popescu inputs of finite-type integer etale approximation. It
uses Mathlib's existing `IsRegularRing`, `IsNoetherianRing`, `Module.Flat`,
residue fields, actual tensor-product fibres and adic completions.

## Definitions

`GeometricallyRegular k A` says that `A` is Noetherian and, for every finite
purely inseparable field extension `k'/k`, the actual scalar extension
`k' ⊗[k] A` satisfies `IsRegularRing`. The field `k : Type u` and algebra
`A : Type v` may have different universes. The extension fields are quantified
in `Type u`, the universe of the base field; this includes same-universe
representatives of finite field extensions. The definition does not require
finite type of `A`.

This is the finite purely inseparable criterion in Stacks Project,
Algebra, Section 10.166 (045K), Lemma 10.166.1(2) and Definition 10.166.2
(0382). We use that criterion directly. The module does not prove the
equivalence with testing all finitely generated field extensions.

`RegularAlgebra R S` is a property of the specified algebra map
`algebraMap R S`. It says that `S` is flat as an `R`-module and that, for
every prime ideal `p` of `R`, Mathlib's actual fibre
`p.Fiber S = p.ResidueField ⊗[R] S` is geometrically regular over
`p.ResidueField`. In particular, each fibre must be Noetherian.
Neither `R` nor `S` is assumed Noetherian. This is More on Algebra,
Definition 15.42.1 (07BZ), in Section 15.42 (07BY). The source writes the
tensor factors in the reverse order; the canonical tensor commutativity
equivalence identifies the same fibre ring and residue-field algebra.

`IsGRing R` says that `R` is Noetherian and that, for every prime ideal `p`,
the canonical algebra map from `P = Localization.AtPrime p` to
`AdicCompletion (IsLocalRing.maximalIdeal P) P` satisfies `RegularAlgebra`.
This is More on Algebra, Definition 15.51.1 in Section 15.51 (07GG).
Every prime is tested, including nonmaximal primes. All rings and all prime
localizations in this definition retain the arbitrary universe of `R`.

The predicates are proposition-valued definitions. They add no regularity
instances or assumed theorems. They impose no domain or reducedness
hypothesis on the base rings.

## Implemented helper proofs

`GeometricallyRegular.isRegularRing` specializes the extension test to the
identity extension `k/k` and transports regularity along the standard
equivalence `k ⊗[k] A ≃ A`.

`GeometricallyRegular.of_algEquiv` transports Noetherianity through the
specified algebra equivalence. At each finite purely inseparable extension,
the tensor-product equivalence induced by that algebra equivalence transports
Mathlib regularity.

`geometricallyRegular_self` proves the predicate for the field `k` as its own
algebra. The scalar extension is equivalent to the extension field `k'`;
Mathlib proves that a field is a regular ring.

The other helpers expose flatness, geometric regularity of actual fibres,
Noetherianity of a G-ring and the regular completion map at any prime directly
from their definitions. These are elementary consequences of the predicates,
not further external mathematical inputs.

## Sources and remaining obligations

The original source pages are retained as
`stacks-regular-maps-g-rings-2026-11-11`, HTML snapshots retrieved
11 November 2026: `045K.html`, `07BY.html`, and `07GG.html` at the locators above.
Their finite extension and Noetherianity conventions are kept explicitly.

This module does not show that a finite-type integer algebra is a G-ring,
that its localization-to-completion map is regular, that regular maps factor
through smooth algebras, or that etale approximation holds. Those substantive
assertions require separate statements and proofs. In particular, the exact
unrestricted `FiniteTypeIntEtaleCompletionApproximationStatement` remains
unchanged and unproved by this contribution.
