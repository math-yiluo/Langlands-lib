# Decomposition, inertia and ramification groups under base change

Module `Nyll.ValuedFieldTheory.Ramification.HilbertRamification.BaseChange`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The file considers a commutative square of field embeddings `τ_K : K → K'` and `τ_L : L → L'` over extensions `L / K` and `L' / K'`, with `L / K` normal. It restricts `K'`-automorphisms of `L'` to `K`-automorphisms of `L`, and shows that this restriction sends decomposition, inertia and ramification groups upstairs into the corresponding groups for the pulled-back absolute value or valuation ring.

## Main declarations

- `galoisPullbackElement σ` and the homomorphism `galoisPullback_galoisPullback : Gal(L'/K') →* Gal(L/K)`: for `σ ∈ Gal(L'/K')`, the automorphism `σ*` of `L` with `τ_L(σ* x) = σ(τ_L x)` (`galoisPullback_galoisPullback_commutes`). It exists because `σ ∘ τ_L` is a `K`-embedding of the normal extension `L`.
- `galoisPullback_absoluteValueDecompositionGroupMap w'`: for any real absolute value `w'` on `L'`, archimedean or not, the restriction maps the decomposition group of `w'` into that of `w' ∘ τ_L`. Here membership of `σ` means `w(σx) < 1 ↔ w(x) < 1` for all `x`.
- For a valuation subring `A'` of `L'` and its pullback `pulledValuationSubring τ_L A'` to `L`:
  - `mem_nonunits_pulled_iff`: `x` lies in the maximal ideal of the pullback exactly when `τ_L x` lies in that of `A'`;
  - `mem_inertiaGroup_iff_sub_mem_nonunits`: for any extension `E / F` and valuation subring `A` of `E`, an element of the decomposition group lies in the inertia group exactly when `σx − x` lies in the maximal ideal for every `x ∈ A`;
  - `galoisPullback_decompositionGroupMap`, `galoisPullback_inertiaGroupMap`, `galoisPullback_ramificationGroupMap`: the restriction maps the decomposition, inertia and ramification groups of `A'` into those of the pullback, as group homomorphisms.

## Proofs

Each map is checked through the defining identity `τ_L(σ* x) = σ(τ_L x)`. The ramification-group step uses that a unit of `L` is a principal unit for the pullback exactly when its image under `τ_L` is a principal unit for `A'`.

## Watch for

- Only normality of `L / K` is assumed: no finiteness, separability or completeness, and nothing about `L' / K'` beyond being an extension.
- The maps are only shown to be group homomorphisms; nothing is said about their injectivity or surjectivity.
- The decomposition, inertia and ramification groups are the library's own definitions from other files. In particular the ramification group is defined by a principal-unit condition on the library's `automorphismUnitQuotient`, not by the classical valuation condition on `σx − x`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Ramification/HilbertRamification/BaseChange.lean`: the Lean file is the source byte for byte (SHA-256 `078cfed4ceb260558533636622ca107428d6dd596b58f4b285632ad85dee684d`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
