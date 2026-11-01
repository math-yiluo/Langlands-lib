# Finite length and exactness of the actual product-Levi refinement functors

Author: Worker 717, for task f1ed5bbb (objective by Worker 320). This module
declares five proposition definitions and nine compilation-checked `example`s.
It declares no theorem and proves none of the propositions. Their proof is a
separate later task.

## The declarations

Throughout, `p` is a prime, `F : PadicField.{uF} p` is an arbitrary finite
extension of `ℚ_p`, and `T : F.TopologicalData` is an arbitrary supplied
local-field realization. The only topology installed is `letI := T.topology`
on `F.Carrier`. It is not specialized to `canonicalTopologicalData`. All five
declarations live in namespace `Langlands.Parabolic`. They take exactly the
outer arguments `{p} [Fact p.Prime] F T` and the two independent universe
levels `uF` (the field) and `uV` (the input carrier).

Each of the first four declarations installs `letI := T.topology` and then
quantifies, inside the proposition, every `n : ℕ`, every
`B : GeneralLinear.BlockShape n` and every `S : Geometric.BlockRefinement B`.

1. `NormalizedRefinedInductionFiniteLengthStatement.{uF, uV} F T` concludes
   `SmoothRep.PreservesFiniteLength (T.normalizedRefinedInductionFunctor.{uF, uV} B S)`.
   Unfolded: every `A : SmoothRep.{0, uF, uV} ℂ (Geometric.refinedLevi F.Carrier B S)`
   with `A.HasFiniteLength` has `((T.normalizedRefinedInductionFunctor B S).obj A).HasFiniteLength`.
2. `NormalizedRefinedJacquetFiniteLengthStatement.{uF, uV} F T` concludes
   `SmoothRep.PreservesFiniteLength (T.normalizedRefinedJacquetFunctor.{uF, uV} B S)`.
   Unfolded: every `A : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier)` of finite
   length has a refined Jacquet module of finite length.
3. `NormalizedRefinedInductionShortExactStatement.{uF, uV} F T` concludes
   `SmoothRep.PreservesFiniteLengthShortExact (T.normalizedRefinedInductionFunctor.{uF, uV} B S)`.
4. `NormalizedRefinedJacquetShortExactStatement.{uF, uV} F T` concludes
   `SmoothRep.PreservesFiniteLengthShortExact (T.normalizedRefinedJacquetFunctor.{uF, uV} B S)`.
5. `NormalizedRefinedFiniteLengthExactnessStatement.{uF, uV} F T` is
   `1 ∧ (2 ∧ (3 ∧ 4))`, the right-associated conjunction of the four
   declarations above, in that order, at the same `F`, `T`, `uF` and `uV`.
   Rank, outer shape and refinement are quantified inside each conjunct, so only
   `F` and `T` stay outside. It is the intended exact target of the later proof.
   Inspection reports its level parameters as `[uF, uV]`, its kind as a
   definition and its type as `Prop`.

The names are those prescribed by the task. They were unused in the Library.

## The objects and the predicates

All of these are existing Library definitions, reused by name.

- `SmoothRep.{0, uF, uV} ℂ G` is the actual category of complex
  representations of `G` on modules in `Type uV` in which every vector has an
  open stabilizer. No topology, finite dimension, admissibility or central
  character is imposed on the module. `SmoothRep.hom f` is the underlying
  intertwiner of a morphism `f`.
- `SmoothRep.HasFiniteLength A` (`Category/Basic`) is Mathlib's
  `IsFiniteLength ℂ[G]` for `A.representation.asModule`: finite composition
  length over the actual complex group algebra, not finite complex dimension.
  The zero representation has finite length.
- `SmoothRep.IsShortExact f g` (`Smooth/FiniteLengthGrothendieck`), for
  intertwiners `f : A → D` and `g : D → E`, says that `f` is injective, `g` is
  surjective and the range of `f` equals the kernel of `g`.
- `SmoothRep.PreservesFiniteLength Φ` (`Smooth/FiniteLengthGrothendieckFunctor`)
  says that `Φ.obj A` has finite length whenever `A` has.
  `SmoothRep.PreservesFiniteLengthShortExact Φ` says: for all objects `A`, `D`,
  `E` and morphisms `f : A ⟶ D`, `g : D ⟶ E`, if `A`, `D` and `E` all have
  finite length and `IsShortExact (hom f) (hom g)`, then
  `IsShortExact (hom (Φ.map f)) (hom (Φ.map g))`. Both predicates allow
  independent source and target universes. Declarations 3 and 4 use them
  verbatim, so all three input terms have finite length, as in the published
  predicate. Nothing is asserted about the finite length of the output terms
  in clauses 3 and 4; that is the content of clauses 1 and 2.

**The groups.** `B.Levi F.Carrier` is the product over the outer blocks of
`GeneralLinear (B.size i) F.Carrier`, with the product of the topologies
induced by `T.topology`. A refinement `S : Geometric.BlockRefinement B` is a
block shape `S i : BlockShape (B.size i)` for each outer block `i`
(`Geometric/WeylDefinitions`). Inside `B.Levi F.Carrier` there are three actual
subgroups, each `Subgroup.pi` over the outer blocks:

- `Geometric.refinedParabolic F.Carrier B S`, the product of the standard upper
  block parabolics `(S i).parabolic F.Carrier`;
- `Geometric.refinedLevi F.Carrier B S`, the product of the block-diagonal
  subgroups `(S i).leviSubgroup F.Carrier`;
- `Geometric.refinedUnipotent F.Carrier B S`, the product of the block-upper
  unipotent radicals `(S i).unipotentSubgroup F.Carrier`.

They carry the subspace topology. The surjection
`Geometric.refinedLeviProjection F.Carrier B S` from the refined parabolic onto
the refined Levi is the Levi part. So the source category of induction and the
target category of Jacquet are representations of this actual subgroup of the
product Levi, not of an abstract product or of a flattened standard Levi of
`GL_n`. `letI := T.topology` alone makes all clauses typecheck.

## The two functors

Both are published in `Geometric/RefinementFunctors` (Worker 14) and reused
unchanged. Write `P_S`, `M_S` and `N_S` for the three subgroups above and
`pr` for `refinedLeviProjection`.

**The modulus.** `T.refinedLeviModulus B S` (`Geometric/RefinementDefinitions`)
is the positive character of `M_S` given by
`m ↦ ∏_i T.leviModulus (S i) (m_i)`, where `m_i` is the `i`-th inner Levi
coordinate (`refinedLeviBlock`) and `T.leviModulus (S i)` is the explicit
standard upper-block modulus of `GL_{B.size i}`,
`∏_{j<k} |det m_j|^(n_k) / |det m_k|^(n_j)` (`Group/GL/BlockModulus`).
`T.refinedLeviHalfModulus B S` is its positive square root, as a character to
`ℂˣ`, and `T.refinedLeviInverseHalfModulus B S` is the inverse of that square
root.

**Induction.** `T.normalizedRefinedInductionFunctor.{uF, uV} B S` goes from
`SmoothRep.{0, uF, uV} ℂ (Geometric.refinedLevi F.Carrier B S)` to
`SmoothRep.{0, uF, max uF uV} ℂ (B.Levi F.Carrier)`. It sends `σ` on `V` to the
smooth induction from `P_S` of `refinedInducingRepresentation`, that is of
`σ ∘ pr` twisted by the positive half-modulus `χ = T.refinedLeviHalfModulus B S`
inflated through `pr`. Its space consists of the functions
`f : B.Levi F.Carrier → V` with an open right stabilizer and

`f(q g) = χ(pr q) • σ(pr q) (f g)` for all `q ∈ P_S`,

(`normalizedRefinedInducedOf_covariant`), on which the product Levi acts by
**right translation**, `(g · f)(x) = f(x g)` (`normalizedRefinedInducedOf_apply`).
It is smooth induction, not the compactly supported variant. Morphisms act by
postcomposition (`normalizedRefinedInducedMap`).

**Jacquet.** `T.normalizedRefinedJacquetFunctor.{uF, uV} B S` goes from
`SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier)` to
`SmoothRep.{0, uF, uV} ℂ (Geometric.refinedLevi F.Carrier B S)`. It sends `ρ`
on `V` to the actual coinvariants `Jacquet.Coinvariants ρ N_S`
(`RefinedJacquetModule`), on which `M_S` acts by

`m · [v] = δ(m)^(-1/2) • [ρ(m) v]`, with `δ = T.refinedLeviModulus B S`

(`normalizedRefinedJacquet_mk`, using `refinedLeviInverseHalfModulus`). Here
`ρ(m)` is the action of `m` as an element of the product Levi. Morphisms act by
the induced map on quotient classes (`normalizedRefinedJacquetMap`).

All clauses apply `Functor.obj` and `Functor.map` of these exact functors. No
external tensor product of block factors, chosen image, formal label or
admissible full subcategory replaces them.

## Scope

- Every rank is included, including `n = 0`. Every outer shape is included,
  including the empty shape, which is the only shape of rank `0` because block
  sizes are positive. Every refinement is included, from the coarsest one (one
  inner block per outer block) to the finest one.
- Every smooth representation of finite length is included, in particular zero
  representations and arbitrary smooth representations of the whole product
  Levi or refined Levi, not only external tensor products of block factors.
- No admissibility, finite generation, irreducibility, cuspidality, finite
  complex dimension, central character, tensor decomposition or positive rank is
  assumed. Smoothness is part of each object. No proof-valued parameter or
  theorem-valued preservation premise stands in for the assertions.
- Only finite length of images and short exactness of image sequences are
  concluded. No length bound, no Grothendieck-group map, no alternating operator
  and no statement about irreducible constituents is asserted.

## Universe accounting and the examples

The field universe `uF` and the input carrier universe `uV` are independent.
The coefficient field `ℂ` lies in universe `0`, and all groups here lie in
`Type uF`. Induction sends carriers in `Type uV` to carriers in
`Type (max uF uV)`, because its space consists of functions on the product Levi.
Jacquet keeps the carrier universe `uV`.

Substituting `uV := max uF uV` makes the induction output universe
`max uF (max uF uV)`, which Lean's universe normalization reduces to
`max uF uV`. Then both functors act between the saturated carrier categories
`SmoothRep.{0, uF, max uF uV} ℂ` of the refined Levi and of the product Levi.
No resizing or finite-dimensional replacement is used. The module checks this
with nine `example`s, all for arbitrary `n`, `B` and `S` and under
`letI := T.topology`:

1. `T.normalizedRefinedInductionFunctor.{uF, max uF uV} B S` has type
   `SmoothRep.{0, uF, max uF uV} ℂ (Geometric.refinedLevi F.Carrier B S) ⥤ SmoothRep.{0, uF, max uF uV} ℂ (B.Levi F.Carrier)`.
2. `T.normalizedRefinedJacquetFunctor.{uF, max uF uV} B S` has type
   `SmoothRep.{0, uF, max uF uV} ℂ (B.Levi F.Carrier) ⥤ SmoothRep.{0, uF, max uF uV} ℂ (Geometric.refinedLevi F.Carrier B S)`.
3. From `h : NormalizedRefinedInductionFiniteLengthStatement.{uF, max uF uV} F T`,
   `h n B S` is the published `SmoothRep.PreservesFiniteLength` for the
   saturated induction functor.
4. Likewise for declaration 2 and `SmoothRep.PreservesFiniteLength` of the
   saturated Jacquet functor.
5. Likewise for declaration 3 and `SmoothRep.PreservesFiniteLengthShortExact`
   of the saturated induction functor.
6. Likewise for declaration 4 and `SmoothRep.PreservesFiniteLengthShortExact`
   of the saturated Jacquet functor.
7. From `h : NormalizedRefinedFiniteLengthExactnessStatement.{uF, max uF uV} F T`,
   `⟨h.1 n B S, h.2.1 n B S, h.2.2.1 n B S, h.2.2.2 n B S⟩` gives all four
   saturated predicates, in the stated order.
8. At a general `uV`, declaration 1 applies to each individual actual object
   `A` of the refined-Levi category: `A.HasFiniteLength` implies finite length
   of its induced object.
9. At a general `uV`, declaration 4 applies to each individual pair of actual
   morphisms `f : A ⟶ D`, `g : D ⟶ E` of the product-Levi category with finite
   length terms and `IsShortExact (hom f) (hom g)`, and gives short exactness
   of the two refined Jacquet maps.

Each of these is closed by the hypothesis itself, by definitional unfolding.
Examples 1 and 2 produce data, so they are marked `noncomputable`. No example
constructs a Grothendieck-group map.

## Sources and provenance

The statement has **derived** provenance. It is a GL/product-Levi formulation
of published results on exactness, admissibility and finite length; it is not
the verbatim statement of any source theorem. For a nonempty outer shape it
specializes those results through the extra admissibility input explained
below. The empty-shape (rank-zero) case is an elementary extension not covered
by the cited passages.

**Bernstein and Zelevinsky**, *Induced representations of reductive p-adic
groups I*, Ann. Sci. ENS 10 (1977). Literature ID
`bernstein-zelevinsky-1977-induced-i`, SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`. Printed
pages (PDF page = printed page minus 439); these pages were read:

- §1.7, pp.443–444: the modulus character used for normalization.
- §1.8, pp.444–445: for `P = MU`, the induction `I_{U,θ}(ρ)` consists of
  smooth `f` with `f(umg) = θ(u) mod_U^(1/2)(m) ρ(m) f(g)`, with `G` acting by
  right translation; the localisation `r_{U,θ}(π)` is the quotient
  `E/E(U,θ)` with `M` acting by `mod_U^(-1/2)(m) π(m)`.
- §1.9, Proposition, p.445: (a) the functors `I_{U,θ}` and `i_{U,θ}` are exact,
  and `r_{U,θ}` is exact if `U` is a limit of compact subgroups; (e) if `G` is
  compact modulo `P` then `I = i` and both carry admissible representations to
  admissible ones.
- §2.1–2.3, p.446: standard subgroups of a connected reductive group, and of
  each standard subgroup in turn; for `GL(n, F)` the standard subgroups are the
  cellular-diagonal `G_α` of ordered partitions `α`, with `G_β < G_α` iff `β` is
  a subpartition of `α` (§2.2); Proposition 2.3 (a) the functors `i_{G,M}` and
  `r_{M,G}` are exact, (c) transitivity, (e) both preserve admissibility.
- §2.8, pp.447–448: finite length of induction from irreducible cuspidal data.
  This special case is not a substitute for the general scope here.

**Casselman**, *Introduction to the theory of admissible representations of
p-adic reductive groups*, draft of 1 May 1995. Literature ID
`casselman-1995-admissible-representations`, SHA256
`78b921fc6331ad2b75389f37d15bd5ac3399e6cfc2d7555e1a4d666e0d42612a`. Printed
page numbers agree with the PDF pages; these pages were read:

- §2.4, p.26: `Ind_H^G σ` consists of smooth `f` with `f(hg) = σ(h) f(g)`, and
  `G` acts by the right regular representation.
- Proposition 2.4.4, p.28: smooth induction is exact.
- §3.1, p.32: normalized induction `i_P^G σ := Ind_P^G(σ δ_P^(1/2))`, with
  `δ_P(mn) = |det Ad_n(m)|`.
- Proposition 3.2.3, p.34: `V ↦ V_N` is exact.
- Theorem 3.3.1, p.35: if a smooth `(π, V)` is finitely generated (resp.
  admissible), then the unnormalized Jacquet module `V_N` is a smooth, finitely
  generated (resp. admissible) representation of `M`.
- The unnumbered "Corollary of the Corollary 6.3.8", p.60: for any parabolic
  `P`, if `σ` is an admissible representation of `M` of finite length, then
  `i_P^G σ` has finite length.
- Theorem 6.3.10, p.60: any finitely generated admissible representation of
  `G` has finite length.

Casselman's `G` is a connected reductive group over a locally compact
non-archimedean field, as is Bernstein–Zelevinsky's from §2 on. Worker 320 and
the author found no source-specific `notes/errata/<source-id>.md` for either
source in the workspace, the project or the supplied Library. This bounded check
does not exclude errata elsewhere.

## Correspondence with the sources

- **Groups.** The ambient group is `G = B.Levi F.Carrier = ∏_i GL_{n_i}(F)`.
  For a nonempty outer shape it is a connected reductive group, and it is
  itself a standard Levi `G_α` of `GL_n` in the sense of BZ §2.2. The refinement
  `S` gives the subpartition `β` obtained by concatenating the inner shapes,
  and `M_S`, `P_S`, `N_S` correspond to `G_β`, its standard upper parabolic
  inside `G_α`, and that parabolic's unipotent radical (BZ §2.1: standard
  subgroups of a standard subgroup). In the Library they are actual subgroups
  of the abstract product, built factorwise.
- **Normalization.** The induction covariance `f(qg) = δ(pr q)^(1/2) σ(pr q) f(g)`
  with right translation is Casselman's `i_P^G σ = Ind_P^G(σ δ_P^(1/2))` of §2.4
  and §3.1, and BZ's `I_{U,1}` of §1.8. The Jacquet action
  `m[v] = δ(m)^(-1/2)[ρ(m)v]` on the actual `N_S`-coinvariants is BZ's
  normalized `r_{U,1}` and Casselman's `V_N` twisted by `δ^(-1/2)`. The Lean
  modulus is the explicit product of the standard block formulas of the inner
  shapes, fixed by the existing definitions. Its equality with the Haar modulus
  of `P_S` is a separate obligation, neither asserted nor needed here: twisting
  by any smooth positive character is the identity on underlying linear maps,
  so it changes neither invariant subspaces, finite length, admissibility nor
  short exactness.
- **Finite length.** The sources' finite length is finite length as
  `G`-modules, i.e. over `ℂ[G]`. This is `HasFiniteLength`.
- **Short exactness.** The sources' exactness of a functor on the abelian
  category of smooth representations specializes to `IsShortExact` on the
  underlying intertwiners. The published predicate asks this only for sequences
  whose terms have finite length, a weaker requirement than full exactness.

## All-smooth finite length versus Casselman's admissible statement

Casselman's corollary on p.60 assumes that `σ` is **admissible** and of finite
length. Clause 1 assumes only that `σ` is smooth and of finite length. The
difference is supplied by the published theorem
`Langlands.finiteLengthAdmissibility` (`Smooth/Admissibility/FiniteLengthProof`),
which proves `Langlands.FiniteLengthAdmissibilityStatement` for every `F`, `T`
and carrier universe. Its Levi clause `leviFiniteLengthAdmissibility` says that
every finite-length smooth representation of `B'.Levi F.Carrier` is admissible,
for every rank and shape `B'`. The refined Levi `M_S` is topologically
isomorphic, through `Geometric.refinedLeviEquivContinuous`, to
`∀ i, (S i).Levi F.Carrier`, a product of general linear groups that can be
reindexed as the product Levi of the concatenated shape. Transporting the Levi
clause along these isomorphisms makes every finite-length smooth `σ` of `M_S`
admissible. Casselman's admissible statement then applies. So the all-smooth
clause 1 is Casselman's corollary composed with the finite-length admissibility
theorem, not a verbatim instance of it. The transport is part of the later
proof, not of this unit.

For clause 2 the same Levi clause, applied directly to `B`, makes every
finite-length smooth representation of `B.Levi F.Carrier` admissible.

## Derivation, for explanation only

The following explains why the statements are expected to hold. It is not a
proof, and the later proof may follow another route, for instance the
all-rank reduction sketched in the task context.

- *Clause 1, nonempty shape.* As above, finite-length `σ` is admissible; the
  half-modulus twist keeps it admissible and of finite length; Casselman's
  corollary on p.60 for `G = B.Levi F.Carrier` and `P = P_S` gives finite
  length of the induced representation.
- *Clause 2, nonempty shape.* A finite-length `ρ` of the product Levi is
  admissible by the Levi clause, and finitely generated because a module of
  finite length is Noetherian. Theorem 3.3.1 makes `V_{N_S}` admissible and
  finitely generated over `M_S`. Theorem 6.3.10 for `M_S`, a connected reductive
  group, gives finite length, and the inverse half-modulus twist preserves it.
- *Clauses 3 and 4.* Smooth induction is exact (Casselman 2.4.4; BZ 1.9 (a)),
  and inflation through `pr` and twisting are exact. Coinvariants of a unipotent
  radical, a limit of compact subgroups, are exact (Casselman 3.2.3; BZ 1.9 (a)
  and the proof of 2.3). These source results give exactness on all smooth
  sequences, so the finite-length hypotheses of the published predicate are not
  needed for them.
- *Empty shape.* For `n = 0` the outer shape is empty, so the product Levi is
  the empty product, a trivial group, and the only refinement is the empty one.
  The refined parabolic, Levi and radical are then trivial and the modulus is
  `1`. Induction gives a representation of the trivial group whose space is
  canonically isomorphic to that of `σ`, and the Jacquet module is the space of
  `ρ` with no relations. All four clauses then reduce to elementary statements
  about the same spaces. This case is not covered by the positive-rank source
  results and must be proved separately.

## Relation to existing results

- `Langlands.Parabolic.normalizedParabolicFiniteLength`
  (`Parabolic/FiniteLengthFunctorProof`, published) proves finite-length
  preservation for standard induction from `B.Levi` to `GL_n` and standard
  Jacquet from `GL_n` to `B.Levi`. The new clauses concern induction and
  Jacquet **inside** the product Levi, between `B.Levi` and the actual subgroup
  `M_S`. Neither is a literal instance of the other. The published theorem is a
  likely input of the later proof, not a proof of this statement.
- `Langlands.finiteLengthAdmissibility` (`Smooth/Admissibility/FiniteLengthProof`,
  published) supplies the admissibility input described above.
- `Langlands.Parabolic.normalizedRefinedInductionAdmissibility`
  (`Parabolic/RefinedInductionAdmissibility`) and
  `Langlands.Parabolic.upperRefinedJacquetAdmissibility`
  (`Parabolic/UpperRefinedJacquetAdmissibilityProof`) prove that the refined
  functors preserve admissibility. They say nothing about finite length.
- `Langlands.CuspidalSupport.refinedCuspidalInductionFiniteLength`
  (`CuspidalSupport/RefinedCuspidalInductionLengthProof`) gives finite length of
  refined induction only for irreducible Levi-cuspidal data transported from the
  flattened Levi. Clause 1 covers every finite-length smooth input.
- `Langlands.CuspidalSupport.RefinedJacquetLengthProof.map_exact`
  (`CuspidalSupport/RefinedJacquetLengthProof`) proves, assuming only that the
  middle representation is smooth, that the refined Jacquet maps of an
  injective `i` and a surjective `q` with range equal to kernel are again
  injective, surjective and exact in the middle. It is a natural input for
  clause 4 but is stated on raw intertwiners rather than as the published
  functor predicate. It is not restated or strengthened here.
- `Langlands.CuspidalSupport.refinedJacquetFiniteLengthDetection` is a
  finite-length detection criterion through proper refined Jacquet modules; it
  does not assert preservation.

None of these existing pairs is changed.

## Dependencies and what is not claimed

The imports are `Langlands.Representation.Geometric.RefinementFunctors` (the two
functors) and `Langlands.Representation.Smooth.FiniteLengthGrothendieckFunctor`
(the two preservation predicates). No existing Library file is changed.

This pair proves none of the five propositions. It does not prove the
admissibility transport, Casselman's corollary, Theorem 3.3.1 or Theorem 6.3.10
in Lean, any exactness, or the rank-zero case. It introduces no Grothendieck
group map (K0 map) and no alternating operator, asserts no length bound and
says nothing about classification.
