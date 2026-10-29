# Projectivity of permutation modules of pro-`p` subgroups

Author: Worker 61. Built on
`Langlands.Cohomology.DivisibleSystem.PowTorsionProjective`
(`powTorsionProjective_obj_of_adjunction`,
`powTorsionProjective_compactInduction`,
`powTorsionProjective_cokernel_powSMul`), on
`Langlands.Cohomology.DivisibleSystem.HomSurjective`
(`PowTorsionProjective`, `powTorsionProjective_of_projective`), on
`Langlands.Cohomology.DivisibleSystem` (`powSMul`), on
`Langlands.Cohomology.DivisibleSystem.ProPInvariants` (`IsProPSubgroup`), on
`Langlands.Cohomology.ProPInvariants.Statement`
(`ProPInvariantsExactStatement`), on
`Langlands.Representation.Induction.OpenAdjunction`
(`Induction.smoothCompactInduction`,
`Induction.projective_smoothCompactInduction`), on
`Langlands.Cohomology.SupercuspidalExt.Statement`
(`SupercuspidalExt.compactInduction`), and on the Library's smooth
representations (`IsSmooth`, `SmoothRep`, `smoothRepProperty`,
`SmoothRep.toRep`, and the abelian structure and instances of
`Langlands.Representation.Category.Abelian`). From Mathlib it uses the
trivial-representation and invariants functors and their adjunction
(`Rep.trivialFunctor`, `Rep.invariantsFunctor`, `Rep.invariantsAdjunction`),
full subcategories (`ObjectProperty.lift`, `ObjectProperty.liftCompιIso`,
`ObjectProperty.fullyFaithfulι`), restriction of adjunctions
(`Adjunction.restrictFullyFaithful`), `Adjunction.map_projective`, and short
exact sequences (`ShortComplex.exact_of_f_is_kernel`, `ShortExact.map`,
`ShortExact.epi_g`, `Functor.preservesHomology_of_preservesEpis_and_kernels`).

`PowTorsionProjective ℓ m P` (published in HomSurjective) means: for every
epimorphism `p : X ⟶ Y` such that multiplication by `ℓ ^ m` on `X`
(`powSMul ℓ m X`) is zero, every morphism `P ⟶ Y` lifts along `p`. It is read
as "`P` is projective relative to objects killed by `ℓ ^ m`".

`ProPInvariantsExactStatement` (Worker 3) says: for a prime `p`, a compact,
totally disconnected topological group `K` whose quotient by every open normal
subgroup is a `p`-group, and a commutative ring `R` in which `p` is a unit,
the `K`-invariants of a short exact sequence of smooth representations of `K`
over `R` form a short exact sequence of `R`-modules. It is not proved in this
module or, as of this module, in the Library. Every result after the first
section takes it as a hypothesis `hP`.

All new names are in the namespace `Langlands.Cohomology`.

## Trivial representations and invariants

`R` is a commutative ring and `K` a group with a topology.

- `isSmooth_trivial R K M`: the trivial representation of `K` on an
  `R`-module `M` is smooth; every vector is fixed by the open subgroup `⊤`.
- `smoothTrivialFunctor R K : ModuleCat R ⥤ SmoothRep R K`: Mathlib's
  `Rep.trivialFunctor R K` (the trivial representation on an `R`-module),
  lifted to the full subcategory of smooth representations by
  `isSmooth_trivial`.
- `smoothInvariantsFunctor R K : SmoothRep R K ⥤ ModuleCat R`: the
  `K`-invariants of the underlying representation, `SmoothRep.toRep` followed
  by Mathlib's `Rep.invariantsFunctor R K`.
- `smoothTrivialAdjunction R K`: `smoothTrivialFunctor R K` is left adjoint to
  `smoothInvariantsFunctor R K`. A morphism of smooth representations from
  the trivial representation on `M` to `A` is the same as an `R`-linear map
  from `M` to the `K`-invariants of `A`. It is Mathlib's
  `Rep.invariantsAdjunction R K` restricted along the identity of
  `ModuleCat R` and the fully faithful inclusion `SmoothRep.toRep`
  (`Adjunction.restrictFullyFaithful`), with the comparison isomorphisms
  `smoothTrivialFunctor ⋙ SmoothRep.toRep ≅ Rep.trivialFunctor` (from
  `ObjectProperty.liftCompιIso`) and the unitors.

## Projectivity under the pro-`p` hypothesis

From here on `K` is a topological group. In the next three results `K` is
also compact and totally disconnected, `p` is a prime, every quotient of `K`
by an open normal subgroup is a `p`-group (`hK`) and `p` is a unit in `R`
(`hR`): the hypotheses of `ProPInvariantsExactStatement` on `K` and `R`.

- `smoothInvariantsFunctor_preservesEpimorphisms R K hP hp hK hR`: the
  `K`-invariants functor preserves epimorphisms. For an epimorphism `f` of
  smooth representations, the short complex `kernel f ⟶ A ⟶ B` is short exact
  in the abelian category of smooth representations (Mathlib's
  `ShortComplex.exact_of_f_is_kernel`); `SmoothRep.toRep` preserves
  epimorphisms and finite limits (Library instances), hence homology
  (`Functor.preservesHomology_of_preservesEpis_and_kernels`), so the image of
  the short complex in `Rep R K` is short exact, and its terms are smooth;
  `hP` makes the invariants of this short complex short exact, and its last
  map, the invariants of `f`, is an epimorphism.
- `projective_smoothTrivialFunctor_obj R K hP hp hK hR M`: for a projective
  `R`-module `M`, the trivial smooth representation of `K` on `M` is a
  projective object of `SmoothRep R K`. A left adjoint whose right adjoint
  preserves epimorphisms sends projective objects to projective objects
  (`Adjunction.map_projective` for `smoothTrivialAdjunction`).
- `powTorsionProjective_smoothTrivialFunctor_obj R K hP hp hK hR hM`: if an
  `R`-module `M` satisfies `PowTorsionProjective ℓ m` in `ModuleCat R`, its
  trivial smooth representation satisfies `PowTorsionProjective ℓ m` in
  `SmoothRep R K`; this is the published
  `powTorsionProjective_obj_of_adjunction` for `smoothTrivialAdjunction`,
  whose right adjoint `smoothInvariantsFunctor` is additive (a composite of
  additive functors; Mathlib's instance for `Rep.invariantsFunctor`) and, by
  the first result, preserves epimorphisms.

## Pro-`p` subgroups and compact induction

`G` is a topological group and `H` a subgroup with
`hH : IsProPSubgroup p H` (published in ProPInvariants: with the subspace
topology, `H` is compact and totally disconnected, `p` is prime, and every
quotient of `H` by an open normal subgroup is a `p`-group), and `p` is a unit
in `R`.

- `projective_smoothTrivialFunctor_obj_of_isProPSubgroup hP hH hR M`: the
  trivial smooth representation of `H` on a projective `R`-module `M` is
  projective; the fields of `hH` are the hypotheses on `K = H` above.
- `projective_smoothCompactInduction_smoothTrivialFunctor_obj hP hH hHo hR M`:
  for `H` open (`hHo`), the compact induction
  `Induction.smoothCompactInduction R H` of the trivial representation of `H`
  on a projective `R`-module `M` is a projective smooth representation of
  `G`, by the published `Induction.projective_smoothCompactInduction`
  (compact induction from an open subgroup is left adjoint to restriction).
  Here `M : ModuleCat.{max uG uV} R`, the universe of the published
  `smoothCompactInduction`, and `hP` is used in the universes
  `uG, uR, max uG uV`.

In the remaining two results `R` and `G` are in one universe `u`, the setting
of the published `SupercuspidalExt.compactInduction R G H` and
`powTorsionProjective_compactInduction`, and `H` is open (`hHo`).

- `powTorsionProjective_compactInduction_smoothTrivialFunctor_obj hP hH hHo hR hM`:
  if an `R`-module `M` satisfies `PowTorsionProjective ℓ m`, so does
  `c-Ind_H^G` of the trivial representation of `H` on `M`, by the published
  `powTorsionProjective_compactInduction` applied to
  `powTorsionProjective_smoothTrivialFunctor_obj`.
- `powTorsionProjective_cokernel_compactInduction_smoothTrivialFunctor_obj hP hH hHo hR m M`:
  for a projective `R`-module `M`, the cokernel of `powSMul ℓ m` on
  `c-Ind_H^G` of the trivial representation on `M` satisfies
  `PowTorsionProjective ℓ m`. A projective `M` satisfies
  `PowTorsionProjective ℓ m` (`powTorsionProjective_of_projective`), the
  previous result applies, and the published
  `powTorsionProjective_cokernel_powSMul` passes to the cokernel. That this
  cokernel is killed by `ℓ ^ m` is the published `powSMul_cokernel_powSMul`;
  it is not restated here.

## Provenance and interpretation

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999).

Section 2, printed p.305 (Worker 61 read the page in the scanned original):
Harris takes "an open normal pro-`p` subgroup `H ⊂ S(ẽ)`" and writes "Since
`p` is prime to `ℓ`, the functor `H⁰(H, •)` is exact on `ℓ`-primary torsion
modules".

Proof of Proposition 4.10, printed p.312 (one-based PDF page 14, read in the
rendered scanned page): "Since `C^j_m(ẽ)^{H_p}` and
`Hom(𝒪_m[C_p/H_p]^M, 𝓛_m)` are both free `𝒪/ℓ^m𝒪[S(ẽ)/H_p]`-modules, it
follows that the maps (4.10.3) are surjective for all m."

The published PowTorsionProjective module shows that the hypothesis
`PowTorsionProjective ℓ m` passes from the inducing representations to direct
sums of compact inductions, and its Scope notes that for
`𝒪/ℓ^m𝒪[S(ẽ)/H_p] = c-Ind_{H_p}^{S(ẽ)} 𝒪/ℓ^m` this would require the
trivial representation of `H_p` to have the property. This module supplies
that step under the hypothesis `hP`: the trivial representation of a pro-`p`
subgroup on a projective module, and its compact induction from an open
pro-`p` subgroup, are projective, and the quotient of the latter by `ℓ ^ m`
has `PowTorsionProjective ℓ m`.

The hypothesis `hP` replaces Harris's exactness of `H⁰(H, •)` on `ℓ`-primary
torsion modules for `p` prime to `ℓ` by exactness of invariants on smooth
representations over a ring in which `p` is a unit (for example `ℤ/ℓ^mℤ` or
`𝒪/ℓ^m𝒪` with `p ≠ ℓ`), as in the published ProPInvariants module. Only the
surjectivity part of that exactness is used. Harris's `H_p` is normal in
`S(ẽ)`; the results here do not need normality.

For a free `R`-module `M = R^(I)` and `H` open, `c-Ind_H^G M` is the direct
sum of `I` copies of the permutation representation of `G` on finitely
supported functions on the right cosets `H\G` (the published compact
induction consists of smooth `H`-covariant functions with compact support
modulo `H`, acted on by right translation). For `H` normal this is the free
`R[G/H]`-module of rank `I`, and its quotient by `ℓ ^ m` is the free
`R/ℓ^m R[G/H]`-module of rank `I`, the kind of module Harris names. These
identifications are not formalized.

All definitions, results and proofs are ours; the cited passages contain only
the exactness of pro-`p` invariants and the freeness statement used for the
surjectivity of (4.10.3). That a left adjoint whose right adjoint preserves
epimorphisms preserves projective objects, and that invariants are right
adjoint to the trivial representation, are standard (and in Mathlib).

## Scope

The module does not prove `ProPInvariantsExactStatement`. It does not
identify `c-Ind_H^G` of a trivial representation with a permutation module or
a free `R[G/H]`-module, and it does not prove that Harris's modules
`C^j_m(ẽ)^{H_p}` or `Hom(𝒪_m[C_p/H_p]^M, 𝓛_m)` are free, or that they
satisfy `PowTorsionProjective`. It does not treat the passage from
`C^j_m(ẽ)` to its `H_p`-invariants, the Hom complexes of (4.10.2) or their
Mittag-Leffler condition beyond the published lemmas it feeds.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Dependencies are the modules named above, pinned to Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
