# Actual intersection characters for the standard intertwiner

Author: Worker 200.

## Provenance and purpose

This is a derived comparison for the standard integral of Waldspurger,
*La formule de Plancherel pour les groupes p-adiques (d'après Harish-Chandra)*,
J. Inst. Math. Jussieu 2 (2003), I.3, printed p.243 (PDF p.9), and IV.1,
printed pp.277–278 (PDF pp.43–44), DOI 10.1017/S1474748003000082.
The registered original is `waldspurger-2003-plancherel`, content SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.

I.3 uses the positive Levi half-modulus in induced functions. IV.1 defines
the standard integral on the left quotient `(U ∩ U') \ U'` through absolute
convergence against every smooth contragredient functional and a representing
vector in the original carrier. The imported
`StandardIntertwiningTarget` construction packages that actual integral in
the target induction on its existing domain under the explicit predicate
`SquaredModulusCompatibility`. This module compares that predicate with
the actual ambient-intersection formula used by the imported corrected-orbit
target. The subgroup equivalences and character comparisons below are internal
deductions, rather than additional assertions attributed to those source pages.

## Objects and hypotheses

Let `G` be a group with a topology. For any subgroups `U,U'`, put
`I = U.subgroupOf U'` and `Z = U ⊓ U'`. The first is the actual
intersection regarded as a subgroup of `U'`; the second is a subgroup of `G`.
`intersectionContinuousEquiv U U' : I ≃ₜ* Z` sends an element to the
same ambient element and reconstructs the nested subtype in its inverse.
Its two evaluation lemmas are definitional equalities. Neither containment
between `U` and `U'` nor normality of the intersection is assumed.

For the character comparisons, `G` is locally compact and nonarchimedean.
The source and target have actual semidirect decompositions
`h : IsSemidirectDecomposition P M U` and
`h' : IsSemidirectDecomposition P' M U'` with the same Levi `M`.
Both radicals are closed. A measurable structure with `BorelSpace` is
supplied on `I`; no particular measurable-space instance is imposed.
Closedness supplies local compactness of `U'`, `I`, and `Z` when needed.
No Hausdorff assumption, quotient measure, representation, convergence
condition, or closedness of `M` is required by this module.

Write `δ_U`, `δ_U'`, and `δ_Z` for the actual
`HaarModulus.closedRestrictCharacter` on `M`, viewed in `ℝ≥0`.
These are fixed Haar characters of actual conjugations. They are not chosen
normalization parameters. Let `φ_m` be conjugation by `m ∈ M` on `U'`,
restricted to `I` using `QuotientIntegration.subgroupAutomorphism`.

## Declarations and implemented proofs

`intersectionContinuousEquiv` is constructed explicitly from the two
membership proofs. Multiplication and inverse identities reduce
definitionally; continuity in both directions follows from continuity of
subtype projections and subtype inclusions.

`levi_le_normalizer_intersection` proves that `M` normalizes `Z`.
Each semidirect decomposition supplies normalization of its radical.
The inclusion from the intersection of their normalizers into the
normalizer of their intersection completes the proof. This lemma is purely
algebraic.

`intersection_haarChar` proves

```text
mulEquivHaarChar(φ_m) = δ_Z(m).
```

The explicit equivalence from `I` to `Z` carries `φ_m` to conjugation
by the same ambient `m`; that compatibility is definitional on elements.
The imported `CorrectedFiltration.mulEquivHaarChar_eq_closedNormalizerCharacter`
transports the Haar character through this equivalence and identifies it
with the closed normalizer character of `Z`. Restriction along `M`
is the displayed restricted character. The transport theorem handles
the supplied Borel structure on `I` and the canonical Borel structure
used internally by the closed-subgroup character.

`squaredModulusCompatibility_iff` applies this pointwise equality in
both directions to prove the exact equivalence

```text
SquaredModulusCompatibility h hU h' hU'
  ↔ ∀ m : M, δ_U(m) * δ_U'(m) = δ_Z(m)^2.
```

Thus the actual nested-intersection identity from the analytic construction
is equivalent to the ambient closed-subgroup identity, without a new
character-comparison premise.

For the conjugation adapter, take an additional semidirect decomposition
`hK : IsSemidirectDecomposition PK MK UK`, with `UK` closed, and `n : G`.
The explicit comparison hypotheses are the whole-subgroup equivalences

```text
x ∈ M  ↔ n⁻¹ * x * n ∈ MK,
x ∈ U' ↔ n⁻¹ * x * n ∈ UK.
```

`intersection_eq_orbitUnipotentIntersection` proves
`U ⊓ U' = CorrectedFiltration.orbitUnipotentIntersection U UK n`
by subgroup extensionality and the second equivalence. Its proof is
algebraic and does not assume the squared-modulus identity.

`squaredModulusCompatibility_of_orbit` takes the exact pointwise premise

```text
δ_U(m) * δ_UK(conjugationEquiv n hMM' m)
  = δ_orbitUnipotentIntersection(m)^2
```

for every `m : M`. The imported `closedRestrictCharacter_conj` proves
the target-radical character comparison. The proved subgroup equality
identifies the intersection character; substitution includes its closedness
and normalizer proofs. The preceding equivalence then gives the actual
analytic `SquaredModulusCompatibility`.

`squaredModulusCompatibility_of_orbitTarget` specializes the imported
`CorrectedFiltration.OrbitSquaredModulusTarget` for a family `P₀,M₀,U₀`.
It retains that target as an explicit premise and all its Weyl/Coxeter
data: the finite Weyl group, the valid index `j` in the length-ordered list,
and an actual normalizer lift `n` of the inverse list entry.
For a reference index `K` it retains the whole-Levi comparison with `M₀ I`,
and supplies the actual target radical `U'` through the displayed radical
comparison. Applying the premise at `I,j,n,K` supplies exactly the
pointwise premise of the preceding lemma. The group and root-index
universes remain independent.

## Scope

The result can be passed directly to the existing conditional target
intertwiner when that construction's separate measure and representation
hypotheses hold. This module proves the nested-subgroup and conjugation
comparisons. It neither proves the shared squared-modulus target nor
constructs the conjugate subgroup data for arbitrary reductive rational
points. Those are retained proof and realization obligations, not additional
permitted external structural assumptions.

Full-source convergence, the convergence cone, rational continuation,
composition scalars, and the Plancherel theorem are not established here.
