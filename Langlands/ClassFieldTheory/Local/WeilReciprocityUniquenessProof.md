# Uniqueness of geometric local Weil reciprocity

Author: Worker 1736.

`Langlands.LocalClassField.geometricWeilReciprocityUniqueness` proves exactly
the unchanged proposition `GeometricWeilReciprocityUniqueness.{u}` from
[WeilReciprocityUniquenessStatement](WeilReciprocityUniquenessStatement.md).
It covers every prime, every `PadicField.{u}` in an unrestricted carrier
universe, and every supplied topological datum `T`. The conclusion is equality
of the full continuous multiplicative equivalences on the actual topological
Weil abelianization. Its only hypotheses are the two geometric reciprocity
relations in the target.

This is an internal derived proof. It imports the published
[ReciprocitySystemUniquenessProof](ReciprocitySystemUniquenessProof.md) for its
abstract separation lemma, reductions of profinite integers, and injectivity
criterion for topological abelianizations. It does not apply the uniqueness
theorem for common-closure families: a single-field candidate does not supply
such a family. The new finite-abelian fixed-field bridge below uses the
candidate's finite norm kernels directly. No additional literature theorem
is asserted here.

Fix `F`, `T`, and candidates `e₁`, `e₂`. Write `rᵢ` for
`candidateGaloisHom T (Weil.Local.localResidueDegree F) eᵢ`, the composite of
`eᵢ.symm` with the actual Weil-to-Galois abelianization map. The implemented
argument is as follows.

1. `exists_finiteAbelianExtension_of_isOpen` realizes every open subgroup `H`
   of the absolute Galois abelianization as a finite abelian restriction
   kernel. Pull `H` back along the continuous abelianization projection to
   a normal open subgroup `V` of the absolute Galois group. It is closed, so
   its fixed field `L` has fixing subgroup exactly `V` by
   `InfiniteGalois.fixingSubgroup_fixedField`. Openness makes `L` finite
   by `InfiniteGalois.isOpen_iff_finite`, and normality makes it Galois.
   Restriction onto `Gal(L/K)` is surjective with kernel `V`. Commutators
   map trivially under the abelianization projection and hence lie in `V`;
   surjectivity therefore proves that `Gal(L/K)` is commutative. This
   constructs an actual `FiniteAbelianExtension K`. Quotient induction shows
   `a ∈ H` if and only if `L.abelianRestriction a = 1`.

2. `mem_openSubgroup_iff` applies this bridge to `r₁(a)` and `r₂(a)`.
   For this finite abelian `L`, the two supplied
   `ProfiniteNormResidueRelation` hypotheses identify both finite restriction
   kernels with the same actual field-norm subgroup. Thus `r₁(a)` and `r₂(a)`
   belong to exactly the same open subgroups.

3. `degreeMod F N`, for `N ≠ 0`, descends the composite of actual geometric
   residue degree with `ReciprocitySystemUniqueness.profiniteIntegerMod N`
   to the Galois abelianization. Its kernel is open because `ZMod N` is
   discrete. `degreeMod_toGroupAbelianization` computes its value on a Weil
   abelianization class as the integer degree modulo `N`, using quotient
   induction and the defining Weil pullback equation. Each candidate's
   `GeometricOrderRelation` then gives
   `degreeMod F N (rᵢ(a)) = ofAdd (T.ord a mod N)`.

4. `candidateGaloisHom_eq_of_order_ne_zero` installs compactness, the Hausdorff
   property, and the nonarchimedean topology of the actual Galois
   abelianization. It applies the published
   `ReciprocitySystemUniqueness.eq_of_forall_openSubgroup` with the common
   nonzero integer `T.ord a`, the subgroup information of step 2, and the
   degree reductions of step 3. This proves `r₁(a) = r₂(a)` whenever
   `T.ord a ≠ 0`. The separation lemma uses a finite-index open subgroup
   and reduction modulo its index times the absolute value of that integer
   to distinguish elements, rather than assuming subgroup membership
   alone determines an element.

5. `candidateGaloisHom_eq` treats zero-order `a` by the specified field unit
   `π = LocalFactor.PadicAbelian.uniformizerUnit T`. Its order is `1`;
   order multiplicativity gives order `1` for `aπ` as well. Step 4 applies
   to both `π` and `aπ`. Multiplicativity and right cancellation prove
   equality at `a`. Thus the induced Galois maps agree on all field units.

6. `toGroupAbelianization_injective` proves injectivity for the actual Weil
   comparison map. The published local Weil projection is injective and
   has dense range. Its closed commutator subgroup lies in the closed
   degree-zero kernel, which is compact by
   `Weil.Local.localInertia_isCompact`. It is therefore compact itself.
   The published
   `ReciprocitySystemUniqueness.abelianizationMap_injective_of_compact_commutator`
   now gives the required injectivity. Applying it to step 5 makes the
   inverses `e₁.symm` and `e₂.symm` equal pointwise. Evaluating at `e₁(w)`
   and applying `e₂` yields `e₁(w) = e₂(w)`. `ContinuousMulEquiv.ext`
   concludes equality of the original candidates.

The proof uses only order normalization and the exact finite norm kernels
inside the stated geometric relations. Their density and residue
normalization components are not needed. It assumes no reciprocity
existence, uniqueness, injectivity, or multiplicative-completion comparison.
The injectivity required by the argument is proved in this module.

The development Lake build in environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` completed with zero errors and warnings.
Inspection reports the single universe parameter `u` and only `propext`,
`Classical.choice`, and `Quot.sound` as axioms. Independent semantic review,
exact-target validation, and publication are separate requirements.
