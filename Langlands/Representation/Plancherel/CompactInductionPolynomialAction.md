# Polynomial actual normalized-induction actions on the compact picture

This derived construction bundles the existing `compactTranslate` operators
as a representation of the whole ambient group on the fixed compact carrier.
It identifies that representation with the actual normalized unramified
induction and proves polynomiality of each fixed group element in the
parameter. All declarations lie in `Langlands.Plancherel`.

## Hypotheses and conventions

The ambient group `G` has a topology, is locally compact and
nonarchimedean. The subgroups `P`, `M`, `U` come with the existing
`IsSemidirectDecomposition P M U`. The hypotheses display closedness of
`U` and `P`, `IsUnimodularModulus U hU`, and continuity of the Levi
projection. The compact open subgroup `K` comes with the factorization
`G = P K`. These are the same hypotheses as the imported normalized
compact-picture equivalence.

The inducing object `A` is the canonical complex `Langlands.SmoothRep` of
`M`, with its carrier universe independent of the ambient group universe.
The index type of norm characters has another independent universe.
The functions `ν i : M →* ℝ≥0ˣ` are continuous. Parameters are the
existing `unramifiedCharacters ν`, namely continuous complex characters
trivial on the common kernel of these norms. The regular scalar algebra
is the existing evaluation-generated `unramifiedRegularFunctions ν`.
There is no admissibility, finite-length, irreducibility or
finite-dimensionality hypothesis on `A` or its fixed-vector spaces.

This generic group construction has no splitness or field-characteristic
restriction. Specializing it to rational parabolics of a reductive group
still requires the displayed subgroup, topology, decomposition, modulus
and continuity inputs; the file does not realize those inputs for every
reductive group.

## The actual full action

Write `Eχ` for the published restriction/extension equivalence
`unramifiedLeviInductionCompactEquiv`, and `ρχ` for the representation of
the canonical `UnramifiedLeviInduction` at `χ`. The imported operator is

`compactTranslate χ g = Eχ ∘ ρχ(g) ∘ Eχ⁻¹`.

`unramifiedCompactRepresentation` bundles this operator as a genuine
representation of `G` on `CompactInductionPicture h K A`. The identity
law follows from inverse cancellation in `Eχ`; the multiplication law
reuses `compactTranslate_mul`.

`unramifiedCompactRepresentationEquiv` retains `Eχ` as its underlying
linear equivalence and proves the intertwining equation for every
`g : G`. It is therefore an equivalence for the full ambient actions.
`unramifiedCompactRepresentation_comp` identifies its restriction to
`K` with the original parameter-independent `compactPictureAction`.
`unramifiedCompactRepresentation_isSmooth` transports an open
stabilizer of `Eχ⁻¹ f` through this full equivalence.

## Polynomiality proof

`exists_compactPicture_stabilizer` starts with the smooth `K` action
on any compact section `f`. Mapping a stabilizing open subgroup of `K`
into `G` gives an ambient open subgroup `H ≤ K` fixing `f`.
This lemma does not use ambient local compactness.

`compactTranslate_mem_compactFixed` proves a useful uniform statement:
if `f` is `H`-fixed and every `x ∈ L` satisfies `g⁻¹ x g ∈ H`, then
`compactTranslate χ g f` is `L`-fixed in the compact picture for every
`χ`. The proof uses the original `K` action, the multiplication law,
and the equality `x g = g (g⁻¹ x g)`.

For a fixed `g` and `f`, choose `H` as above and put
`L = K ∩ g H g⁻¹`, implemented by the comap under conjugation by
`g⁻¹`. Thus all parameter translates of `f` belong to the same
`CompactFixedVectors h K A L`. For each `k ∈ K`, their values at `k`
are the normalized extensions of `f` evaluated at `k g`, by
`eval_compactTranslate`. The published
`unramifiedCompactExtension_eval_isPolynomialOn` proves polynomiality
of each such evaluation.

The published `isPolynomialOn_compactFixed_of_eval` then reconstructs
a polynomial family of fixed sections from those evaluations. Its
finite set of right-coset representatives comes from compactness of
`K` and openness of `L`; it does not require finite-dimensional
fixed-vector spaces. Applying the fixed-space inclusion yields
`isPolynomialOperatorOn_compactTranslate` for any parameter subset
`Ω`. The final theorem
`unramifiedCompactRepresentation_polynomial` states precisely that
each fixed `g` in the newly bundled actual representation satisfies
the existing `IsPolynomialOperatorOn` predicate on `Ω`. This predicate
is a finite regular expansion for each fixed input vector.

## Source correspondence and retained obligations

The motivating passage is Waldspurger, *La formule de Plancherel pour
les groupes p-adiques (d'après Harish-Chandra)* (2003), IV.1,
printed pp.276–277 / PDF pp.42–43, registered as
`waldspurger-2003-plancherel`, content SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
It identifies the compact carrier for unramified twists and defines
polynomial operators by finite expansions per input vector.

This file provides an internal proof that the actual normalized
induction actions have that polynomial dependence, using the existing
compact-picture constructions. This proof route and its stronger
absence of an admissibility premise are derived content. It does not
assert the full source equivalence with algebraic families over the
regular-function algebra.

Transporting continued compact intertwiners back to the actual
induction spaces remains a separate construction. Standard-integral
convergence and rationality, invariance under equivalences of
representation representatives, orbit descent, generic irreducibility,
the global composition scalar `j`, the density `mu`, and all main
Plancherel assertions remain obligations of the overall program.
