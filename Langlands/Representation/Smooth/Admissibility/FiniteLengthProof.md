# Proof of finite-length GL and product-Levi admissibility

Author: Worker 863.

`Langlands.finiteLengthAdmissibility` proves exactly the published
`Langlands.FiniteLengthAdmissibilityStatement.{uF, uV} F T`. Its only outer
arguments are `{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)` and
`(T : F.TopologicalData)`. The two conjuncts are also supplied separately as
`Langlands.glFiniteLengthAdmissibility` and
`Langlands.leviFiniteLengthAdmissibility`, proving the published GL and Levi
clauses respectively.

For every rank `n`, every block shape `B`, and every complex smooth
representation of `GeneralLinear n F.Carrier` or `B.Levi F.Carrier`, finite
length over the actual complex group algebra implies admissibility.
The only field topology used is the supplied `T.topology`. No irreducibility,
admissibility, tensor presentation or other extra hypothesis is added.

## Implemented induction

Let `G : Type uG` be a topological group such that every open subgroup
contains a compact open subgroup. Suppose every irreducible complex smooth
representation of `G`, with carrier in `Type uV`, is admissible. The private
helper `admissible_of_finiteLength_of_irreducible` deduces admissibility for
every finite-length complex smooth representation of `G` in the same carrier
universe. These are hypotheses of a private general reduction, not extra
hypotheses of the public GL theorem.

The proof uses the actual complex group algebra `ℂ[G]`. In particular,
`A.HasFiniteLength` is `IsFiniteLength ℂ[G] A.representation.asModule`, not
finite dimension of the underlying vector space.

1. `restrictedComplexModule` installs the complex module structure on
   `RestrictScalars ℂ ℂ[G] M` with the additive structure used by
   `Representation.ofModule`. `moduleIntertwiner` turns a group-algebra
   linear map into an intertwiner between the associated representations:
   complex linearity follows from linearity at `algebraMap ℂ ℂ[G] c`, and
   equivariance follows from linearity at the basis elements corresponding
   to group elements.
2. `module_admissible_of_finiteLength` inducts on Mathlib's `IsFiniteLength`.
   For its subsingleton constructor, `RestrictScalars.addEquiv` transfers the
   subsingleton property to the representation carrier. Each fixed-vector
   module is then subsingleton and finite; smoothness is the given premise.
3. In the extension constructor, `N` is a finite-length group-algebra
   submodule of `M` and `M ⧸ N` is simple. The maps `N.subtype` and `N.mkQ`
   become intertwiners `i` and `q`. Their injectivity and surjectivity are
   `N.injective_subtype` and `N.mkQ_surjective`. The published
   `isSmooth_of_injective` and `isSmooth_of_surjective` transfer smoothness
   from the middle representation to both ends.
4. The induction hypothesis gives admissibility of `N`. Mathlib's
   `Representation.isSimpleModule_iff_irreducible_ofModule` identifies the
   simple quotient with an irreducible smooth representation, so the
   irreducible-admissibility premise gives admissibility of the quotient.
   For exactness, the proof establishes
   `LinearMap.range i.toLinearMap = LinearMap.ker q.toLinearMap` by
   membership in `N`, using `Submodule.Quotient.mk_eq_zero N` and the
   restriction-of-scalars additive equivalences. The published
   `isAdmissible_iff_of_shortExact` then gives admissibility of the middle
   representation.
5. `toModuleRepresentation` is a bijective intertwiner from an arbitrary
   representation `ρ` to `Representation.ofModule ρ.asModule`. Its
   underlying map is the composition of `ρ.asModuleEquiv.symm` and
   `RestrictScalars.addEquiv.symm`. Smoothness transfers across its
   surjection, the preceding module induction applies, and
   `isAdmissible_of_injective` transfers admissibility back to `ρ`.

Thus the induction treats submodules and quotients directly, without
postulating a composition series or a tensor presentation.

## GL and product-Levi specializations

The public theorem installs precisely `T.topology` and
`T.generalLinearTopologicalGroup n`. For an open subgroup `H`, the
construction `T.generalLinearCompactOpen n (H : Set _)` applied to
`H.isOpen.mem_nhds H.one_mem` gives a compact open subgroup contained in `H`.
This supplies the cofinality premise of the general reduction. Its
irreducible-admissibility premise is the first conjunct of the published
`CuspidalSupport.cuspidalEmbedding F T n σ hσ`.

The Levi theorem uses the same general reduction. It installs `T.topology`
and `T.leviTopologicalGroup B`. For each open subgroup `H`,
`T.leviCompactOpen B (H : Set _) (H.isOpen.mem_nhds H.one_mem)` supplies a
compact open subgroup contained in `H`, with precisely the product topology
on the actual product Levi. The irreducible-admissibility premise is the
independently published
`CuspidalSupport.irreducibleLeviAdmissibility F T n B σ hσ`, which has no
quasicuspidality, tensor-factorization or admissibility hypothesis.

`finiteLengthAdmissibility` pairs these two proofs, exactly as required by
the combined statement.

The rank `n` is arbitrary, including zero, and every block shape is included.
The imported irreducible theorems and both compact-open constructions have
no positive-rank restriction. At rank zero, positivity of block sizes
forces the shape to be empty, and its Levi is the product over `Fin 0`.
Thus the implemented uniform induction includes the trivial matrix group
and the empty product without a separate case split. The subsingleton
branch handles zero representations. The elementary reason for the
rank-zero extension is that every irreducible representation of the trivial
group is a line, so a finite-length representation has finite dimension.
The Lean proof obtains that boundary case through the all-rank published
irreducible inputs, rather than proving that separate dimension argument.

Admissibility means smoothness and finite-dimensional fixed vectors for
every open subgroup. Compact-open cofinality enters the short-exact theorem,
which supplies this full all-open-subgroup conclusion.

The field universe `uF` and carrier universe `uV` remain independent.
The general reduction uses independent `uG` and `uV`, with complex
coefficients in universe zero. Both public specializations use `uG := uF`
without enlarging the carrier universe. The closing `example` checks the
complete theorem at `FiniteLengthAdmissibilityStatement.{uF, max uF uV}`.
This is the carrier universe used by the saturated finite-length
Grothendieck groups and their class maps in the unchanged target module.
No canonical topology, finite-dimensional carrier, finite-generation
premise, central character or classification theorem is added.

## Sources and derived provenance

This is derived mathematics implementing the forward admissibility direction
of Bernstein and Zelevinsky's finite-length theorem through irreducible
admissibility and the short-exact extension property.

I. N. Bernstein and A. V. Zelevinsky, *Representations of the group GL(n,F)
where F is a non-archimedean local field (survey)*, 1976:

- Literature ID `bernstein-zelevinsky-1976-representations-gln`.
- SHA256 `72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`.
- Original:
  `/home/taskhub/central-library/Bernstein-Zelevinsky--Representations of the group GL(n,F) where F is a non-archimedean local field (survey)--1976.pdf`.
- Worker 863 read original printed/PDF pages 15–17, 29 and 35–38.
  Definition 2.1(b), page 15, tests fixed vectors for every open subgroup;
  section 2.8, pages 16–17, discusses finite module length; Definition 3.4,
  page 29, defines the ordered product groups. Theorem 3.25, page 35,
  supplies irreducible admissibility. Theorem 4.1, pages 37–38, derives
  admissibility of finite-length representations from that input.

Bill Casselman, *Introduction to admissible representations of p-adic
groups*, Chapter II, *Smooth representations*, revision June 16, 2019:

- Literature ID `casselman-2019-smooth-representations`.
- SHA256 `2f7868c9e29fd486a42419f5b381237bba5d0ba73accc82ed5d7ade448a79c3d`.
- Original:
  `/home/taskhub/central-library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Chapter II - Smooth representations--2019.pdf`.
- Worker 863 read original PDF pages 2–4. Smoothness and admissibility are
  defined on page 2. Proposition II.1.3 and Corollary II.1.4, page 4, give
  smoothness of subobjects and quotients, compact-open fixed-vector
  exactness, and admissibility in short exact sequences.

No source-specific errata were found in the project literature and notes
search. The implemented induction follows the published target's derived
route. The generic reduction and the inclusion of zero rank are internal
extensions: the cited positive-rank statements do not by themselves cover
the trivial group. Here rank zero is covered by the independently published
all-rank GL and product-Levi inputs. Only admissibility is concluded; the
other direction and finite generation in Bernstein–Zelevinsky Theorem 4.1
are not claimed.

## Actual imports and dependency audit

The five direct project imports are:

| Module | Use |
| --- | --- |
| `Langlands.Representation.Smooth.Admissibility.FiniteLengthStatement` | Published target definitions and actual finite group-algebra length. |
| `Langlands.Representation.Smooth.Admissibility.ExactProof` | `isAdmissible_iff_of_shortExact`; transitively, smoothness and injective admissibility transfer. |
| `Langlands.Representation.CuspidalSupport.CuspidalEmbeddingProof` | `CuspidalSupport.cuspidalEmbedding`, whose first conjunct is irreducible GL admissibility. |
| `Langlands.Representation.CuspidalSupport.IrreducibleLeviAdmissibilityProof` | `CuspidalSupport.irreducibleLeviAdmissibility`, for arbitrary irreducible smooth product-Levi input. |
| `Langlands.Group.GL.CompactOpen` | Compact-open cofinality for the supplied topology and the matrix-group topology infrastructure. |

At Library commit `771cfc69d1ff795522e29cdead1b7c40f1a1c308`, recursive
traversal of the actual project `import` lines gives 135 modules including
this new proof. All 134 imported Lean/Markdown pairs agree byte for byte
with that Library. This contribution changes none of them, including the
target pair and its dependencies. The irreducible-Levi proof was verified
actually published before it was imported.

The closure contains the lower GL cuspidal-embedding route, including
minimal-Jacquet, quasicuspidal-Levi admissibility and normalized-induction
admissibility, plus basic topology and smooth-representation modules. The
new product-Levi input adds 18 modules to the earlier GL-only closure:
refinement coordinates and nesting, flattened-Levi transport, minimal
nonzero refined Jacquet descent, the normalized refined quasicuspidal
embedding, refined first adjointness and induction admissibility, and
their lower Weyl, twist and compact-average helpers.

Reading the actual product-Levi assembly and its lower proofs confirms
the route: minimal nonzero refined Jacquet descent; finite generation and
an irreducible quotient of that Jacquet module; an injective normalized
refined Frobenius map; quasicuspidal Levi admissibility; inverse-coordinate
transport; normalized refined induction admissibility; and injective
transfer. Descent uses finite refinement coordinates and surjective maps
between actual coinvariant modules. Induction admissibility uses
inflation, an open-kernel half-modulus twist and compactness of the actual
refined parabolic quotient. These lower proofs neither assume nor derive
their inputs from finite-length admissibility. The embedding and
induction-admissibility proofs use the same normalized action; this
finite-length induction makes no normalization change.

The only two modules under `Representation.Classification` are
`Supercuspidal` and `SupercuspidalTwist`; their contents are elementary
predicates, equivalences and twisting compatibility.

The complete import graph and source texts were checked against the
declarations and modules named in the following excluded tasks:

- Segment classification `aca8805b-054f-4d56-8045-12db7f623404`.
- Multisegment special-head exhaustion
  `3bfb61fa-1129-4fc9-83fd-7fcfec22106e`.
- Ordered strong-head existence `ebea9a8a-9b21-4208-aa31-98c2dea1f8a3`.
- Quotient coverage `20e4e1c6-0f4f-4ca7-96b9-a214ba1a7584`.
- Tempered block uniqueness `52e97845-36bb-457d-b76f-70753334b88c`.
- Square-integrable Langlands classification
  `1cb45da2-7007-4351-a694-594fb148b8d1`.
- Square-integrable exhaustion `cd8ab97c-0b78-4bce-97c4-d307a28159a4`.
- Regular exhaustion `bf433f0a-921a-428c-b0c0-6475438125ac`.

None of those conclusion or proof modules occurs in the transitive closure,
and none of their identified conclusion declarations is referenced by the
implemented proof route. The downstream normalized parabolic-functor
finite-length proof `2a216dfa-5b20-4b4b-9ff8-50b41a0b28f7` is likewise
absent. This proof does not duplicate or depend on the separately owned
admissible-induction finite-length task
`62571b78-5017-45b0-ad9f-10c4b34a924b` or admissible finitely generated GL
finite-length task `dac75ee7-f2bc-4efb-9c77-4894aa48d134`.
The published `Smooth.FiniteLengthGrothendieck` definitions are imported by
the target itself, but no functor-map conclusion from task
`9672d6e2-a0d3-4fc0-b6ef-d1048ddb97a8` is used or reproved.

The closure contains no admissible-factorization or second-adjointness
module. A full source scan for the excluded declaration/module names found
no matches. Broader scans for `SquareIntegrable`, `Tempered`,
`AdmissibleFactorization` and `SecondAdjoint` also found none.
`FiniteLength` occurs only in this proof, its target, the target's
Grothendieck definitions, the group-algebra length definition and Mathlib
import in `Category.Basic`, and the Prop-valued
`CuspidalInductionLengthTheorem` in
`CuspidalSupport.NormalizedCuspidalInductionStatement`. The only
`Exhaustion` matches are the Prop-valued `UnipotentExhaustionClause` and its
use in `Parabolic.GeometricPrerequisitesStatement`. Those unrelated
proposition definitions supply no proof input or hypothesis to this theorem.

## Development checks and authorship

Environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` uses Lean 4.34.0 and
Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`. The complete
module passed a development Lake build and declaration inspection, with zero
errors and zero warnings, in diagnostic
`9cc867a0-e897-4652-b4a9-f0471c025184`. This build includes the closing
example at the saturated carrier universe. Inspection reports exactly the
independent universe parameters `uF` and `uV`, and only `propext`,
`Classical.choice` and `Quot.sound` as axioms. The development check is not
independent acceptance: staged exact-target validation, independent semantic
review and publication remain separate requirements.
There are no proof holes or new axioms. Worker 863 wrote this proof and its
explanation from scratch, using the named published results as imports.
