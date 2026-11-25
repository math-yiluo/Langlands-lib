# Comparison with an affine fpqc quotient

For a supplied affinization `hq : IsAffinization q` of an actual field group `G`, an affine actual field group `H`, and an actual flat, surjective, quasi-compact homomorphism `q₀ : G ⟶ H`, `hq.fpqcComparisonIso q₀ hk` constructs an actual group isomorphism `H ≅ Q` when `hk : kernelι q₀ ≫ q = 0`. The accompanying `fpqcComparisonIso_fac` proves the exact equation `q₀ ≫ (hq.fpqcComparisonIso q₀ hk).hom = q`. The kernel in the hypothesis is the unchanged actual scheme-theoretic kernel, including its full scheme structure.

There is no smoothness, connectedness, reducedness, finite-type, quasi-compact-source, perfect-field, or algebraically-closed-field premise. Affineness of `Q` and the isomorphism on its actual global functions are the fields of `IsAffinization q`; affineness of `H` is an explicit input. Quasi-compactness, flatness and surjectivity apply to the supplied map `q₀` itself.

This is an internal derived comparison from the published `FpqcHomDescent` construction, the published injectivity of global-function pullback along an epimorphism of schemes, and Mathlib's reflection of affine scheme isomorphisms from global functions. This final comparison serves the affinization geometry argument. The Lean implementation proceeds as follows.

1. `FpqcHomDescent.hom q₀ q hk` gives the actual descended homomorphism `t : H ⟶ Q`, and its factorization theorem gives `q₀ ≫ t = q`.
2. Applying actual global functions yields `t.appTop ≫ q₀.appTop = q.appTop`. The right side is an isomorphism by `hq`. The pullback `q₀.appTop` is injective because the actual fpqc scheme map is an epimorphism, using `UnitCocycleDescent.appTop_injective_of_epi`. Its surjectivity follows directly from surjectivity of the composite: for a function on `G`, choose its preimage under `q.appTop` and then apply `t.appTop`. Thus `q₀.appTop` is an isomorphism.
3. Cancel that isomorphism from the actual composite to show `t.appTop` is an isomorphism. Since both `H` and `Q` are affine, the affine isomorphism criterion makes `t` an isomorphism of actual schemes. The forgetful functors from group objects through monoid objects and relative schemes reflect isomorphisms, producing the actual group isomorphism.
4. Its homomorphism is definitionally the descended `t`, so the retained factorization equation is exactly `FpqcHomDescent.fac`.

The construction uses the arbitrary universe `u` of the field, schemes and maps. It changes neither the affinization interface nor any source or quotient. The descended homomorphism is unique by the imported fpqc descent uniqueness theorem; the retained equation identifies it with the prescribed affinization projection.
