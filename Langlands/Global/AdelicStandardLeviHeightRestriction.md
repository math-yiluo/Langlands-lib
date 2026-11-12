# Canonical standard Levi restriction of height minima

Author: Worker 83.

This derived prerequisite implements the algebraic restriction step of
Godement section 9.3, printed p.215 (PDF page 16), for the Library's canonical
standard subgroup schemes and actual number-field adelic points. It supplies
unipotence, normalization, line preservation and rational comparison-subgroup
containment for the transfer theorem in `AdelicHeightMinimumLeviRestriction`.
It retains a supplied factorization and separate norm-one membership of the
Levi factor. The full chamber-reduction theorem remains open.

Fix an arbitrary universe `u`, a field `F : Type u`, an affine group scheme
`G` over `Spec F`, a commutative group scheme `T`, a morphism `i : T.toGrp ⟶ G`
and a cocharacter `ν`. Write `P_J`, `L_J` and `U_J` for the choice-free standard
subgroup functors and use their canonical `Standard` representatives and
inclusions throughout. The purely algebraic lemmas do not require a number
field. Actual adelic images and the final transfer require `[NumberField F]`.

## Canonical structural inputs

`isUnipotent_standardUnipotentScheme` assumes connected reductivity of `G`,
maximal splitness of `i`, genericity of `ν` and `J ⊆ simpleRelativeRoots i ν`.
The published `standardCocharacter` supplies a standard cocharacter `ζ` and
the equality `U_J = Dynamic.unipotent (ζ ≫ i)`. Rewriting the canonical
representability theorem by this equality and applying
`Dynamic.isUnipotent_unipotentRepresentative` proves unipotence of the actual
`Standard.unipotentScheme i ν J`. Smoothness comes from connected reductivity.

`standardLevi_adelic_range_le_normalizer` holds for every index set `J`,
without reductivity, maximality, genericity or a simple-root-subset premise.
The represented-functor equalities identify the two actual adelic ranges with
the `L_J` and `U_J` carriers on the adele-algebra test scheme.
`StandardLeviIntersection.conj_mem_standardUnipotent`, together with
`L_J ≤ P_J`, gives closure of `U_J(A)` under conjugation by `L_J(A)`.
Applying it to the inverse gives the reverse implication in the normalizer
criterion. Thus the conclusion concerns the actual adelic images of the
canonical morphisms.

`standardUnipotent_le_other_standardParabolic` uses the same reductive,
maximal-split and generic hypotheses as the unipotence lemma and valid
subsets `J,K` of the fixed simple roots. The published standard-parabolic
order gives

`U_J ≤ U_empty ≤ P_empty ≤ P_K`.

`preservesCoordinateLine_standardUnipotent_of_standardParabolic` uses this
inclusion on every scheme test. A point in the canonical `U_J` image lies
in `P_K`, so canonical representability factors it through the `P_K`
representative. The point-matrix restriction identity then transports the
supplied unit-scalar action on the coordinate line. This is all-test
preservation, not merely preservation on rational or adelic points.

## The exact tail comparison subgroups

Let `K : ℕ → Set (characterLattice T)` be an arbitrary family and let
`f : L_(K 0) ⟶ G` be the canonical inclusion. Write `f_F` for its actual
rational-point homomorphism. The definition
`standardLeviTailPrefixRationalSubgroup F G T i ν K l` is

`R_l = intersection over a < l of f_F⁻¹(P_(K (a+1))(F))`.

There is no root-subset or nesting hypothesis in this definition or its
elementary properties. `mem_standardLeviTailPrefixRationalSubgroup` gives
exactly the displayed membership condition.
`standardLeviTailPrefixRationalSubgroup_zero` makes `R_0` the full rational
Levi group, and `standardLeviTailPrefixRationalSubgroup_antitone` proves
automatic descent by containment of prefix index sets.

Let `Q_l` be `closedPrefixRationalSubgroup` for the ambient canonical
parabolic family `P_(K a)`. Then
`standardLeviTailPrefixRationalSubgroup_eq_comap` proves

`R_l = f_F⁻¹(Q_(l+1))`.

Indeed, canonical representability identifies each ambient rational range
with the corresponding parabolic carrier. The first condition in `Q_(l+1)`
is automatic because `L_(K 0) ≤ P_(K 0)`. Splitting an index into zero or
a successor identifies the remaining conditions with exactly `a < l`.
This equality does not identify a tail intersection with an individual
standard parabolic.

## Transfer of the remaining minima

`mem_chainHeightMinimalSet_standardLevi_tail` assumes the reductive,
maximal-split and generic hypotheses above and that every `K a` is a
subset of the fixed simple roots. It takes actual representations `ρ_a`,
coordinate indices `j_a`, and all-test preservation of the `j_a` line by
the canonical `P_(K a)` representative. The adapted-family construction
in `AdelicIntersectionHeightChain` supplies such preservation data when
its hypotheses are available.

For any `s : ℕ` and `c : ℝ`, suppose an ambient norm-one point `p` satisfies
the first `s+1` minimum inequalities for `ρ_a,e_(j_a),Q_a` with constant `c`.
Suppose also that

`p = image(m) image(x)`,

where `m ∈ L_(K 0)(A)^1` is supplied separately and `x ∈ U_(K 0)(A)`.
The conclusion puts `m` in the first `s` minimum inequalities for

`ρ_(a+1)|_L, e_(j_(a+1)), R_a`,

with the same constant `c`.
The proof applies
`mem_chainHeightMinimalSet_restrict_of_unipotent_factor` with the index
map `a ↦ a+1`. The four helpers above discharge actual unipotence,
normalization, coordinate-line preservation and rational comparison
containment. Restriction and naturality in that theorem remove the
unipotent factor both before and after right rational translation.

There is no sign restriction on `c`. The case `s=0` is included. Coordinate
indices enforce positive dimension, but no faithfulness or exact stabilizer
condition on the representations is needed. No nesting of `K` is assumed.
Ambient norm-one membership does not infer Levi norm-one membership:
the latter is an explicit input with all Levi character conditions.

## Source and remaining obligations

R. Godement, *Domaines fondamentaux des groupes arithmétiques*, Séminaire
Bourbaki, Exposé 257 (1963; collected 1964), section 9.3, printed p.215
(PDF page 16), first paragraph. Registered source
`godement-1963-bourbaki-257-domaines-fondamentaux`, SHA-256
`b0a531469f376c1a56a7816f0fa579cd301c4162fb1c1aa8909c886e303c722d`.
The original rendered page was read directly. Godement writes `p=zu`,
uses normalization and fixedness by `U(1)`, and obtains the second
representation's inequality over `Z(1)(k)`, the third over
`Z(1)(k) ∩ P(2)(k)`, and so on.

The Lean derives this restriction step for arbitrary finite prefixes of
canonical standard parabolics over any number field and universe. Its
structural inputs are the published standard-cocharacter, standard-order,
dynamic-unipotence and all-test normalization proofs, rather than extra
unproved premises. The two imported height-interface modules supply the
actual orbit-height transfer and preceding-intersection definitions.

This module does not construct the factorization or prove the norm-one
condition on its Levi factor. It does not identify the restricted
representations' exact stabilizers with standard parabolics of that Levi,
prove connected reductivity of the chosen Levi, compare its root system,
prove a rank-one height-to-root bound, or carry out rank induction.
Those comparisons, positive-torus coordinates and the final chamber
coverage remain obligations for `AdelicSiegelChamberReductionStatement`.
