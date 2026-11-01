# Finite free models along ring maps

Author: Worker 1119.

Module `Langlands.Cohomology.ModuleComplex.FibreH0RestrictionSpread.Model`, namespace
`Langlands.Cohomology.ModuleComplex.FibreH0Spread`. It is a helper for the proof of
`Langlands.Cohomology.ModuleComplex.FibreH0RestrictionSpreadStatement` (see `Main.md`). It
imports the published proofs `Langlands.Cohomology.PrimeMinimalPerfectProof`
(`primeMinimalPerfect`) and `Langlands.Cohomology.PrimeFreeHomotopyDescentProof`
(`primeFreeHomotopyDescent`), and the helper `Core`. No `sorry` and no new axioms. No
unproved Library proposition is assumed.

Notation: `baseChange β` is the Library's termwise scalar extension of cochain complexes;
`baseChangeCompIso α β : baseChange (β.comp α) ≅ baseChange α ⋙ baseChange β` and
`baseChangeHomotopyEquiv β` (scalar extension of a homotopy equivalence) are Library
declarations from `PerfectModuleComplexBaseChange` and `PerfectModuleComplexHomotopy`.

## The model predicate

`HasModel α K n`, for `α : R →+* A`, a complex `K` over `R` and `n : ℤ → ℕ`: there is a finite
free complex `P` over `A` (`IsFiniteFree P`), some `HomotopyEquiv P ((baseChange α).obj K)`,
and for every `i` some `P.X i ≃ₗ[A] (Fin (n i) → A)`.

This is an internal definition: a finite free complex over `A` homotopy equivalent to the
scalar extension of `K`, with prescribed term ranks. It packages exactly the output of
`primeFreeHomotopyDescent`.

## Lemmas

- `isFiniteFree_baseChange β hP`: scalar extension preserves `IsFiniteFree`
  (`bounded_baseChange`, `finite_extendScalars`, `free_extendScalars`).
- `HasModel.comp h β`: a model along `α` gives a model along `β.comp α`, with the same ranks.
  The model is `(baseChange β).obj P`, and the homotopy equivalence is
  `baseChangeHomotopyEquiv β e` followed by the isomorphism `baseChangeCompIso α β` at `K`.
- `HasModel.of_dvd h hrs`: if `r ∣ s`, a model along `R → R[1/r]` gives one along
  `R → R[1/s]`. Here `r` is a unit in `R[1/s]`. Apply `HasModel.comp` with
  `IsLocalization.Away.lift r` and rewrite with `IsLocalization.Away.lift_comp`.
- `exists_hasModel hK p`: for strictly perfect `K` and a prime `p`, there is `r ∉ p` with
  `HasModel (algebraMap R (Localization.Away r)) K n`, where `n i` is the dimension over the
  residue field `κ(p) = p.ResidueField` of the degree-`i` homology of
  `(baseChange (algebraMap R κ(p))).obj K`. Proof: `primeMinimalPerfect` gives a finite free
  complex over `R_p` homotopy equivalent to `K ⊗ R_p` with exactly these ranks.
  `primeFreeHomotopyDescent` descends it to `R[1/r]` for some `r ∉ p`, preserving the homotopy
  equivalence and ranks.
- `transportIso e β i`: for `e : HomotopyEquiv P ((baseChange α).obj K)` and `β : A →+* T`,
  the isomorphism `H^i(P ⊗ T) ≅ H^i(K ⊗_{β ∘ α} T)`. It is the homology isomorphism of
  `baseChangeHomotopyEquiv β e`, followed by the homology of the inverse of
  `baseChangeCompIso α β` at `K`.
- `transportIso_comm e e₁ ψ β i`: for models `e`, `e₁` of `K`, `K₁` and a chain map
  `ψ : K ⟶ K₁`, let `χ = e.hom ≫ (baseChange α).map ψ ≫ e₁.inv : P ⟶ P₁`. Then the transport
  isomorphisms intertwine `H^i(χ ⊗ T)` and `H^i(ψ ⊗_{β ∘ α} T)`. Proof: `e₁.inv ≫ e₁.hom` is
  homotopic to the identity (`homotopyInvHomId`), and scalar extension preserves homotopies
  (`mapHomotopy`), so on homology `χ ⊗ T` followed by `e₁.hom ⊗ T` equals
  `(e.hom ≫ (baseChange α).map ψ) ⊗ T`. Then use naturality of `(baseChangeCompIso α β).inv`
  at `ψ`.
- `bijective_iff_of_comm`, `jointly_injective_of_comm`: bijectivity, and joint injectivity of a
  pair, transfer along isomorphisms of `T`-modules intertwining the maps.
- `bijective_homologyMap_iff_of_model e e₁ ψ β γ hγ i`: if `β.comp α = γ`, then
  `H^i(χ ⊗_β T)` is bijective iff `H^i(ψ ⊗_γ T)` is bijective.
- `jointly_injective_homologyMap_of_model e e₁ e₂ ψ₁ ψ₂ β γ hγ i h`: if `β.comp α = γ` and
  `H^i(ψ₁ ⊗_γ T)`, `H^i(ψ₂ ⊗_γ T)` are jointly injective, then so are `H^i(χ₁ ⊗_β T)` and
  `H^i(χ₂ ⊗_β T)`, where `χⱼ = e.hom ≫ (baseChange α).map ψⱼ ≫ eⱼ.inv`.
- `nonempty_homology_equiv_of_model e β γ hγ i`: if `β.comp α = γ`, then `H^i(P ⊗_β T)` is
  linearly equivalent to `H^i(K ⊗_γ T)`.

## Provenance

Internal helper. Stacks tag 0BF2 (`more-morphisms.tex`, lines 9543–9619, registered source
`stacks-picard-diagonal-seesaw-0bdp-0bf0-a04446e5`, commit
`a04446e57ec1fbc252a871afcec7752fb2807b14`) replaces the complexes near the point by minimal
finite free complexes and the restriction maps by maps between them. Here that step is
`exists_hasModel` (from the Library's minimal-model and descent theorems). The maps between
models are the transported maps `e.hom ≫ (baseChange α).map ψ ≫ e₁.inv`, compared with the
original maps on homology after every scalar extension.
