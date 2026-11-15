# Equivariant uniformizer families for permutation index sets

This internal helper module builds the family of units used in the proof of KP
Corollary 11.1.9 (`inducedTorusKottwitzRationalSurjectivity`). It adds no
assertion from the literature. It makes precise the standard fact behind the
source's "obvious" case `T = 𝔾_m` over a finite extension `ℓ/F`: a uniformizer
of `ℓ` has Kottwitz value `1`, because `ℓ·K/ℓ` is unramified.

## Setting

All declarations are in `Langlands.Geometry.Building.Kottwitz.UniformizerFamily`.
`F` is a nonarchimedean local field, `Ω = SeparableClosure F`,
`K = UnramifiedClosure F`, and `E` is a finite Galois intermediate field of
`Ω/F`. `J` is a finite index type. `act : (E ≃ₐ[F] E) →* Equiv.Perm J` is an
action of `Gal(E/F)`. `Gal(Ω/F)` acts on `J` by a `MulAction` instance that
factors through `Gal(E/F)` by the hypothesis
`hact : σ • j = act (σ.restrictNormal E) j`. The inertia subgroup is
`H = relativeInertia F K Ω`. For the final results, `L : IntermediateField K Ω`
is finite over `K` and contains `E` (`hEL`). `ord_L` denotes the integer order
for `normalizedIntermediateValuation F L`.

## Fixed fields and primitive elements

* `stab p` is the stabilizer of `p` in `Gal(E/F)`. `fixedOmega p` is its fixed
  field, mapped into `Ω`; it lies in `E` (`fixedOmega_le`).
* `forall_fixedOmega_iff`: `σ ∈ Gal(Ω/F)` fixes `fixedOmega p` pointwise iff
  `σ • p = p`. Proof: restriction to `E` (`AlgEquiv.restrictNormal_commutes`) and
  finite Galois correspondence (`IntermediateField.fixingSubgroup_fixedField`).
* `forall_eq_iff`: `σ` and `σ'` agree on `fixedOmega p` iff `σ • p = σ' • p`.
  Apply the previous lemma to `σ'⁻¹ σ`.
* `exists_adjoin_eq`, `prim`, `adjoin_prim`, `prim_mem`: a primitive element
  `prim p` with `F(prim p) = fixedOmega p` (`Field.exists_primitive_element`).

## Counting inertia orbits

* `restrictScalars_mem_inertia`: every `K`-automorphism of `Ω` lies in `H`.
  Conversely `inertiaToK` regards an element of `H` as a `K`-automorphism, and
  `inertiaToK_restrictScalars` shows the two are inverse.
* `card_orbit_eq_finrank` and `orbitFunSum_one_eq_finrank`: the `H`-orbit of `p`
  has `[K(prim p) : K]` elements. Proof: `[K(α) : K]` is the number of roots of
  `minpoly K α` in `Ω` (`IntermediateField.adjoin.finrank`,
  `Polynomial.card_rootSet_eq_natDegree`). Each root is `τ α` for some
  `τ ∈ Gal(Ω/K)`. The map `τ α ↦ τ • p` is well defined and injective, because
  `τ α = τ' α` iff `τ` and `τ'` agree on `F(α) = fixedOmega p`
  (`IntermediateField.algHom_ext_of_eq_adjoin`), iff `τ • p = τ' • p`. Its image
  is the `H`-orbit of `p`, by the conversions between `H` and `Gal(Ω/K)`.

## Uniformizers

* `compositum p = K(prim p)`, finite over `K`. Its restriction of scalars is
  `K ⊔ fixedOmega p` (`compositum_restrictScalars`), so it contains
  `fixedOmega p` and lies in `K ⊔ fixedOmega p`.
* `exists_unif`, `unif`, `unif_mem`, `unif_val`, `unif_ne_zero`: by
  `CompositumUniformizer.exists_uniformizer_of_le_sup`, `fixedOmega p` contains a
  uniformizer `unif p` of `compositum p`.
* `normalizedIntermediateValuation_of_le`: if `M ≤ L` are finite over `K` and
  `w ∈ M` has `M`-value `exp n`, then its `L`-value is `exp ([L : M] • n)`. Proof:
  `normalizedIntermediateValuation_norm` and `Algebra.norm_algebraMap`.
* `orderUnits_eq_of_val`: units of `L` with the same spectral value have the same
  integer order.

## The family

* `rep j` is a representative of the `Gal(Ω/F)`-orbit of `j` (`Quotient.out`),
  with `rep_smul` and `rep_rep`. `mover j` is an automorphism with
  `mover j • rep j = j`.
* `fam j = mover j (unif (rep j))`, and `famUnits j` is the same element as a unit
  of `E`. `fam_smul`: `fam (σ • j) = σ (fam j)`. The automorphisms
  `mover (σ • j)` and `σ * mover j` both send `rep j` to `σ • j`, so they agree on
  `fixedOmega (rep j)` by `forall_eq_iff`. `famUnits_act` is the resulting
  `Gal(E/F)`-equivariance, using surjectivity of restriction
  (`AlgEquiv.restrictNormalHom_surjective`).
* `famOrder j = ord_L(famUnits j)`. It is `Gal(Ω/F)`-invariant
  (`famOrder_smul`), because the spectral valuation is
  (`CompositumUniformizer.sepClosureValuation_map`).
* `orbitFunSum_famOrder`: every `H`-orbit sum of `famOrder` equals `[L : K]`.
  Proof: `famOrder` is constant on `H`-orbits, so the orbit sum at `j` is
  `famOrder j` times the orbit size (`orbitFunSum_mul_const`). This orbit sum is
  `Gal(Ω/F)`-invariant (`orbitFunSum_comp_smul`), so it suffices to take
  `p = rep j`. There `mover p` fixes `p`, hence fixes `unif p`, so
  `fam p = unif p`. Its `L`-order is `[L : compositum p]`. The orbit has
  `[compositum p : K]` elements, and the tower law
  (`Module.finrank_mul_finrank`) gives `[L : K]`.
* `exists_family` packages the result: there is a `Gal(E/F)`-equivariant family
  `u : J → Eˣ` whose `L`-orders have every inertia-orbit sum equal to `[L : K]`.
