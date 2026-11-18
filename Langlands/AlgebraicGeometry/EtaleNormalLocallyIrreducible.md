# Étale schemes over normal schemes: normality, local irreducibility, generic determination

This module collects the topological and commutative-algebra facts about étale
schemes over a normal base. The proof of Conrad's Corollary B.3.6 uses them
(Brian Conrad, *Reductive group schemes*, 2014, `conrad-2014-reductive-group-schemes`,
pp.294–295). They are proved here for an arbitrary base: no noetherian, quasi-compactness
or finiteness hypothesis is assumed. Normality is the hypothesis of the published target
`MultiplicativeTypeNormalIsotrivialStatement`: every stalk is an integrally closed domain,
`∀ s, IsDomain (S.presheaf.stalk s) ∧ IsIntegrallyClosed (S.presheaf.stalk s)`.
All declarations live in the namespace
`Langlands.AlgebraicGeometry.EtaleNormalLocallyIrreducible`.

## Statements

### Commutative algebra

- `exists_isIdempotentElem_isDomain_isIntegrallyClosed R Q`. Let `R` be an integrally
  closed domain, `C` an étale `R`-algebra (`Algebra.Etale R C`) and `Q` a prime ideal of
  `C`. Then there is an idempotent `e ∈ C` with `e ∉ Q` such that `Localization.Away e`
  is an integrally closed domain. Geometrically, `Spec C` is covered by open and closed
  pieces `D(e) = Spec C[1/e]`, each the spectrum of an integrally closed domain.
- `isDomain_isIntegrallyClosed_localization_atPrime_of_etale hR Q`. Suppose every
  localization of `R` at a prime ideal is an integrally closed domain, and `C` is an étale
  `R`-algebra. Then every localization of `C` at a prime ideal is an integrally closed
  domain. This is the ring-level form of "étale over normal is normal".

### General topology

The module defines one predicate.

- `IsLocallyPreirreducible X` (a `Prop`-valued definition on a topological space `X`):
  every point has a preirreducible open neighbourhood,
  `∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ IsPreirreducible U`. This is a derived
  auxiliary notion that names the hypothesis of the three statements below. It is not a
  definition from Conrad's text. Every point has an *irreducible* open neighbourhood
  (namely a preirreducible one, which contains the point and so is nonempty), so this is
  the usual notion of a locally irreducible space.

Each statement below has the hypothesis `hX : IsLocallyPreirreducible X`.

- `isClopen_closure_of_isOpen hX hW`: the closure of every open set is clopen.
- `isIrreducible_connectedComponent_and_isOpen hX x`: the connected component of `x` is
  irreducible and open.
- `irreducibleSpace_of_connectedSpace hX`: a connected space with this property is an
  irreducible space.

Two statements about generalizing maps (`GeneralizingMap f`) follow.

- `eq_of_isLocallyConstant_of_generalizingMap hf hη h₁ h₂ h`. Let `f : X → S` be
  generalizing and let `η` specialize to every point of `S`. Two locally constant
  functions `g₁ g₂ : X → T` that agree on `f⁻¹{η}` are equal.
- `apply_eq_of_generalizingMap hf hξ hη`: if `X` is `T₀`, `f` is generalizing, `ξ`
  specializes to every point of `X` and `η` to every point of `S`, then `f ξ = η`.

### Schemes

Here `X S : Scheme.{u}`.

- `isDomain_isIntegrallyClosed_of_ringEquiv`: the property "integrally closed domain" is
  invariant under ring isomorphisms (a bookkeeping lemma).
- `localization_atPrime_of_stalk hS hV P`. Suppose every stalk of `S` is an integrally
  closed domain, `V` is an affine open of `S` and `P` is a prime of `Γ(S, V)`. Then
  `Localization.AtPrime P` is an integrally closed domain.
- `stalk_isDomain_isIntegrallyClosed_of_etale f hS x` (**étale over normal is normal**).
  If every stalk of `S` is an integrally closed domain and `f : X ⟶ S` is étale, then
  every stalk of `X` is an integrally closed domain.
- `isDomain_isIntegrallyClosed_sections hS hV`. Suppose `S` is an irreducible space whose
  stalks are integrally closed domains, and `V` is a nonempty affine open. Then
  `Γ(S, V)` is an integrally closed domain.
- `exists_isIrreducible_of_etale f hS x`. Suppose `S` is irreducible with integrally
  closed domain stalks and `f : X ⟶ S` is étale. Then every `x : X` lies in an open
  `U : X.Opens` with `IsIrreducible (U : Set X)`.
- `isLocallyPreirreducible_of_etale f hS`: under the same hypotheses,
  `IsLocallyPreirreducible X` holds (a restatement of the previous item with the
  predicate).
- `irreducibleSpace_of_etale f hS`: under the same hypotheses, if `X` is moreover a
  connected space then it is an irreducible space.
- `isIrreducible_connectedComponent_of_etale f hS x`: under the same hypotheses (without
  connectedness of `X`), every connected component of `X` is irreducible and open.
- `eq_of_isLocallyConstant_of_flat f h₁ h₂ h` (**generic determination**). Let `S` be
  irreducible and `f : X ⟶ S` flat. Two locally constant functions on `X` (with any
  target type) that agree at every point of the fibre over `genericPoint S` are equal.
- `apply_genericPoint_of_flat f`: a flat morphism between irreducible schemes sends
  `genericPoint X` to `genericPoint S`.
- `surjective_of_isFinite_of_etale f`: a finite étale morphism from a nonempty scheme to
  a connected scheme is surjective.

## Correspondence with the source

Conrad's proof of Corollary B.3.6 uses these facts at the following points.

- p.294, first paragraph: "Every connected finite étale `S`-scheme `S'` is also
  irreducible … These components are pairwise disjoint (since `S'` is normal)". This is
  `irreducibleSpace_of_etale`. Conrad's argument uses finiteness of the cover to get
  finitely many generic points. The Lean statement needs no finiteness: it applies to
  every connected scheme étale over an irreducible normal scheme. Its normality input is
  `stalk_isDomain_isIntegrallyClosed_of_etale`.
- p.294, "a finite étale map has open and closed image": `surjective_of_isFinite_of_etale`
  records the consequence that is used, surjectivity onto a connected base.
- p.295, local case: "The finitely many irreducible components of `S'` are pairwise
  disjoint, so each is open. Hence … connected components … are irreducible". This is
  `isIrreducible_connectedComponent_of_etale`, again with no finiteness hypothesis.
- p.295: "each of which meets `S''_K`, so `ϕ` is the identity", and in the global step
  "the overlaps `Uᵢ ∩ Uⱼ` are irreducible with generic point `η`, so `fᵢ` and `fⱼ`
  coincide". These are instances of generic determination, `eq_of_isLocallyConstant_of_flat`:
  locally constant data on a flat `S`-scheme is determined by its generic fibre.

Conrad uses that étale over normal is normal without proof; this module proves it.
Everything here is derived from Mathlib and the Library. No statement of the module
mentions group schemes. Each item is either a step of Conrad's argument or a
generalization of one (finiteness removed). The module does not prove Proposition B.3.4
or Corollary B.3.6.

## Proofs

**Idempotent splitting.** Let `K = Frac R`. By `Algebra.Etale.iff_exists_algEquiv_prod`,
the étale `K`-algebra `K ⊗[R] C` is a finite product `Π i, L i` of fields. The proof
writes `e₀ : C ⊗[R] K ≃+* Π i, L i` for this isomorphism, composed with the swap of
tensor factors. The map `φ : C → C ⊗[R] K` is injective because `C` is `R`-flat. Each
`εᵢ = e₀⁻¹(Pi.single i 1)` is idempotent, so it is integral over `C`. The Library lemma
`exists_algebraMap_eq_of_isIntegral_genericFibre` (from the FLT port: elements of the
generic fibre integral over `C` come from `C`, for `R` integrally closed and `C` étale,
via Mathlib's `TensorProduct.toIntegralClosure_bijective_of_smooth`) gives `cᵢ ∈ C`
with `φ cᵢ = εᵢ`.

Since `Σ cᵢ = 1`, some `e = cᵢ` is not in `Q`, and `e` is idempotent by injectivity of
`φ`. Let `ψ : C → L i` be the `i`-th projection. Then `ψ e = 1`, and `ψ x = 0` implies
`x e = 0`. Because `e` is idempotent, `C → C[1/e]` is surjective, and `ψ` induces an
injective map `ψ' : C[1/e] → L i`. Hence `C[1/e]` is a domain.

For integral closedness, let `x ∈ Frac C[1/e]` be integral. Lift its monic equation to
a monic `q` over `C` and let `y` be the image of `x` in `L i`. Set
`Y = e₀⁻¹(Pi.single i y)`. Then `Y` is a root of `X · q`, so `Y` is integral over `C`.
The same Library lemma gives `c' ∈ C` with `φ c' = Y`, and `x` is the image of `c'` by
injectivity of the lift of `ψ'` to the fraction field.

**Ring-level normality.** Let `p = Q ∩ R`. The algebra `Rₚ ⊗[R] C` is étale over the
integrally closed local domain `Rₚ`, and it is the localization of `C` at the image of
`R ∖ p`. The Library theorem
`Algebra.Etale.isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime` (FLT port,
integrally closed domain base) shows that its localization at the extended prime `Q'` is
an integrally closed domain. That localization is also a localization of `C` at
`Q.primeCompl`, by `IsLocalization.isLocalization_isLocalization_atPrime_isLocalization`
and transport along the equality of submonoids. So it is isomorphic to `C_Q`.

**Topology.** Let `y ∈ closure W` with `W` open. Take a preirreducible open `U ∋ y`.
Then `U ∩ W` is nonempty, and `U ⊆ closure (U ∩ W)` by Mathlib's
`subset_closure_inter_of_isPreirreducible_of_isOpen`. So `closure W` is open. For a
point `x` with preirreducible open neighbourhood `U`, the set `closure U` is clopen,
irreducible and contains `x`. Hence it equals the connected component of `x`. If the
space is connected, that component is the whole space.

**Generic determination** uses only that `f` is generalizing. For `x : X`, the point
`η` specializes to `f x`, so there is `x' ⤳ x` with `f x' = η`. Locally constant
functions have open fibres, so `gⱼ x' = gⱼ x` for `j = 1, 2`. Flat morphisms of schemes
are generalizing (`Flat.generalizingMap`), and the generic point of an irreducible
scheme specializes to every point (`genericPoint_specializes`). For
`apply_eq_of_generalizingMap`, lift the specialization `η ⤳ f ξ` to `x' ⤳ ξ`. Since
`ξ ⤳ x'` as well, `T₀` gives `x' = ξ`.

**Schemes.** For the stalk statements, choose affine opens `V ∋ f x` and
`U ∋ x` with `U ≤ f⁻¹ V`. The ring map `Γ(S, V) → Γ(X, U)` is étale
(`HasRingHomProperty.appLE`). Stalks are localizations of sections at primes
(`IsAffineOpen.isLocalization_stalk`). Apply the ring-level result.

For `isDomain_isIntegrallyClosed_sections`, `S` is reduced (its stalks are domains) and
irreducible, hence integral, so `Γ(S, V)` is a domain. Integral closedness is checked
at maximal ideals (`IsIntegrallyClosed.of_localization_maximal`).

For local irreducibility, apply idempotent splitting to the étale `Γ(S, V)`-algebra
`Γ(X, U)`. The base is an integrally closed domain by the previous item, and the prime
is the one of `x`. This gives `e` with `x ∈ X.basicOpen e`. The set `X.basicOpen e` is
the image under `IsAffineOpen.fromSpec` of `PrimeSpectrum.basicOpen e`. That basic open
is the range of `Spec Γ(X, U)[1/e]`, which is irreducible because `Γ(X, U)[1/e]` is a
domain. This gives `isLocallyPreirreducible_of_etale`, and the irreducibility and
connected-component statements then follow from the topology section.

`surjective_of_isFinite_of_etale`: the range of `f` is closed (finite morphisms are
closed maps) and open (étale morphisms are open maps). It is nonempty, so it is
everything because `S` is connected.
