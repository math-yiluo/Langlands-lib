# Irreducible admissible scalar quotients detected by central dual eigenfunctionals

This module states one proposition,
`Langlands.CentralDualEigenQuotientStatement.{uG,uC,uV}`. It is a statement
only; this module contains no proof of it.

## Quantifiers and hypotheses

The proposition is closed: it has no parameters and quantifies over

- a group `G : Type uG` with a topology and `IsTopologicalGroup G`
  (`[Group G] [TopologicalSpace G] [IsTopologicalGroup G]`);
- the cofinality hypothesis
  `∀ H : OpenSubgroup G, ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ K ≤ H`:
  every open subgroup contains a compact open subgroup;
- a group `C : Type uC` (`[Group C]`, with no topology and not assumed
  commutative), a homomorphism `z : C →* G`, and the centrality hypothesis
  `∀ (c : C) (g : G), z c * g = g * z c`;
- a character `χ : C →* ℂˣ`, with no continuity or other condition;
- a complex vector space `V : Type uV` (`[AddCommGroup V] [Module ℂ V]`), with
  no finiteness or topology on `V`, and an actual representation
  `ρ : Representation ℂ G V`.

The universes `uG` (group), `uC` (central parameter group) and `uV`
(representation carrier) are independent. The three hypotheses on `ρ` are
exactly:

1. `Module.Finite (MonoidAlgebra ℂ G) ρ.asModule`: `ρ` is finitely generated as
   a module over the complex group algebra, using Mathlib's
   `Representation.asModule`.
2. `IsAdmissible ρ`: the project's admissibility predicate from
   `Langlands.Representation.Smooth.Definitions`, i.e. `ρ` is smooth and its
   space of `K`-fixed vectors is finite dimensional for every open subgroup `K`.
3. There is `φ : Module.Dual ℂ V` with `φ ≠ 0` and
   `∀ (c : C) (v : V), φ (ρ (z c) v) = (χ c : ℂ) * φ v`. The functional lies in
   the full algebraic dual of `V`; it need not be smooth. The eigen-equation
   precomposes `φ` with `ρ (z c)` itself, with no inverse `z c⁻¹`, no complex
   conjugation and no modulus factor.

## Conclusion

There exist an actual bundled representation `S : Rep.{uV} ℂ G`, whose carrier
lies in the same universe `uV` as `V`, and an actual intertwiner, such that

- `Representation.IsIrreducible S.ρ` (Mathlib's irreducibility: the lattice of
  subrepresentations of `S.ρ` is a simple order, so in particular `S` is
  nonzero);
- `IsAdmissible S.ρ`;
- `Classification.HasScalarCharacter S.ρ z χ`, the published predicate of
  `Langlands.Representation.Classification.ConstituentRelations`, which unfolds
  to `∀ (c : C) (w : S), S.ρ (z c) w = (χ c : ℂ) • w`: every `z c` acts on `S`
  by the scalar `χ c`;
- `∃ q : ρ.IntertwiningMap S.ρ, Function.Surjective q`: `S` is an actual
  quotient of the whole representation `ρ`, not of a subrepresentation or a
  subquotient.

Nothing else is assumed. There is no finite-length or semisimplicity
hypothesis, no smoothness of `φ`, no topology or smoothness of `C` or `χ`, no
generalized-eigenspace finiteness, and no supplied scalar quotient, irreducible
constituent, maximal subrepresentation or choice function.

## Intended proof route (not part of this statement)

The existing `Langlands.MaximalConeQuotient.exists_irreducible_quotient` in
`Langlands.Representation.Classification.MaximalConeQuotient` already proves
the generic extraction result with the functional and its two properties as
separate arguments. This closed statement packages their existence as one
antecedent. Its proof successor can reuse that theorem after unpacking the
existential hypothesis; this module remains statement-only.

Let `D ⊆ V` be the complex span of the defects `ρ (z c) v - (χ c : ℂ) • v` for
`c : C` and `v : V`. Centrality gives
`ρ g (ρ (z c) v - χ c • v) = ρ (z c) (ρ g v) - χ c • ρ g v`, so `D` is
`G`-invariant. The eigen-equation says that `φ` vanishes on every defect, hence
on `D`; since `φ ≠ 0`, the quotient `V ⧸ D` is nonzero. Every `z c` acts on
`V ⧸ D` by the scalar `χ c`, and `V ⧸ D` is finitely generated over the group
algebra as a quotient of `ρ.asModule`. A nonzero finitely generated module has a
maximal proper submodule (the submodule lattice is coatomic), and
`Subrepresentation.subrepresentationSubmoduleOrderIso` transports it
to a coatom among subrepresentations. The quotient `S` by this coatom is
irreducible, still has the scalar action `χ`, and lies in universe `uV`. The
composite `V → V ⧸ D → S` is a surjective intertwiner. Admissibility of `S`
follows from `Langlands.Unramified.SphericalExistence.isAdmissible_of_surjective`
(in `Langlands.Representation.Unramified.SphericalConstituentExistenceProof`),
which takes exactly the cofinality hypothesis above, a surjective intertwiner
and admissibility of the source. Alternatively one may quotient by the common
kernel of all ordinary `χ`-eigenfunctionals in place of `D`.

## Provenance

The statement is project-internal and derived. It is a generic algebraic and
admissibility prerequisite for the prescribed dual-exponent support argument,
namely TaskHub task `06fcd45a-6509-4a2f-a84b-a119382a9953` (publisher Worker
532), whose exact target is `Langlands.GLUnitaryDualJacquetTemperedSupportStatement`.
It is not an analytic theorem from the literature and not a verbatim
translation of any literature statement.

Its model is the extraction step in the proof of Theorem 2.4.1 of A. J.
Silberger, *Introduction to harmonic analysis on reductive p-adic groups*
(1979), registered as `silberger-1979-harmonic-analysis`, printed pp. 91–92
(PDF pp. 97–98). There Silberger passes from a dual exponent `χ` of an
irreducible admissible representation to the quotient module `V̄_χ` of the
Jacquet module dual to the generalized dual eigenspace `V'_χ`, notes that it is
finitely generated, and takes an irreducible quotient of it by his Lemma 1.5.3.
The statement here differs from the source in three ways. It is generic: it
concerns an arbitrary finitely generated admissible representation and an
arbitrary central homomorphism `z`, not a Jacquet module of `GL_n` or a split
component `A`. It uses one ordinary eigenfunctional and the quotient on which
`z` acts by exactly `χ`, rather than generalized dual eigenspaces and their
multiplicity `d(χ)`. And it builds in no normalization: any modulus factor such
as Silberger's `δ_P̄^{1/2}` must already be part of `ρ` or `χ`. The
GL-specific inputs of the application (finite generation and admissibility of
the actual normalized opposite Jacquet module, centrality of block scalars and
the existence of a full-dual eigenfunctional) are not assumed here and are
supplied separately. In the published adapters of
`Langlands.Representation.Exponents.UnitaryDualJacquetSupportAdapters`,
`levi_compactOpen_cofinal`, `jacquet_admissible` and
`exists_dualEigenfunctional` have exactly the shapes of the cofinality,
admissibility and eigenfunctional hypotheses above, and
`GeneralLinear.BlockShape.blockScalarLevi_mem_center` gives the centrality
hypothesis through `Subgroup.mem_center_iff`; finite generation over the group
algebra remains an input of the application.

The proposition body is the one prescribed by TaskHub task
`eb5551f7-36fd-4e8c-88d9-2dd9f398fa0c` (Worker 261).
