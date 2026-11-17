# Truncation quotients and restriction of Weil representations

The module
`Langlands.LocalFactor.Ramification.Herbrand.TruncationQuotientStatement`,
in namespace `Langlands.Ramification.Kummer`, supplies five supporting
definitions and exactly eight proposition definitions. It proves none of
the eight assertions. Each statement quantifies over every prime `p`,
with `[Fact p.Prime]`, and every `F : PadicField.{u} p`; the restriction
statement also has an independent representation-carrier universe `v`.

## Existing objects and conventions

Write `G_F = Field.absoluteGaloisGroup F.Carrier` and
`G_F^x = Langlands.Ramification.Padic.absoluteUpperRamificationGroup F x`.
For `E : Langlands.LocalClassField.FiniteIntermediateExtension F.Carrier`,
put `EP = E.asPadicField (p := p)` and `G_E = Field.absoluteGaloisGroup E.field`.
The inclusion `ι_G : G_E →ₜ* G_F` is the existing
`Langlands.Weil.Local.intermediateGaloisMap F E`; its image is
`E.field.fixingSubgroup`. Thus the transitivity hypothesis is

`E.field.fixingSubgroup ⊔ G_F^μ = ⊤`.

Because `G_F^μ` is normal, this says that its product with the fixing
subgroup is `G_F`, or equivalently that `G_F^μ` acts transitively on the
`F`-embeddings of `E`. This is the same hypothesis used by Task 7450.

Write `W_F = Langlands.Weil.Local.localWeilGroup F` and
`R_F(x) = Langlands.VirtualRepresentation.LocalWeil.Ramification.upperGroup F x`,
and similarly for `EP`. These are the actual Weil groups and the preimages
of the absolute upper groups under `localProjection`. The inclusion
`ι_W : W_E →ₜ* W_F` is the existing `intermediateWeilMap F E`.
The module reuses `HerbrandBridge.weilRestrict E A`,
`FiniteRepresentation.restrictClass ι_W.toMonoidHom`, `upperFixedSpace`,
`IsTrivialAt` and `localDegree`.

All quotient groups carry their quotient topologies. Absolute upper
groups have a published normality instance. For Weil upper groups the
published `LocalFactor.NonabelianSystem.DeligneHenniart.upperGroup_normal`
is a theorem rather than an instance. This module supplies a local
instance by `Subgroup.Normal.comap inferInstance _`, pulling the existing
absolute-group normality instance back along `localProjection`. It
introduces no new upper group or normality assumption.

Task 7450's imported `KummerTowerStatement` supplies `kummerBreak F`,
`IsKummerRootSystem F ϖ πs` and `kummerStage F πs n`. In particular
`b = kummerBreak F = p e_F / (p - 1)` with real arithmetic, and
`K_n = (kummerStage F πs n).field = F(πs n)`.
Neither a Galois hypothesis on `E/F` nor a roots-of-unity hypothesis on
`F` is imposed.

## Supporting definitions

These internal predicates encode the isomorphisms and representation
classes in the route note's Lemma `lem:trunc`, lines 876–887.

- `GaloisQuotientIsoAlong K F ι x` means that there exists a continuous
  multiplicative equivalence
  `φ : G_K/G_K^x ≃ₜ* G_F/G_F^x` such that `φ(mk τ) = mk(ι τ)` for every
  `τ`. For every real `y` with `-1 ≤ y ≤ x`, the image under `φ` of the
  image of `G_K^y` in the source quotient equals the image of `G_F^y` in
  the target quotient. Thus it specifies the map and the full induced
  filtration, as well as the topology.
- `WeilQuotientIsoAlong K F ι x` has the same meaning for
  `φ : W_K/R_K(x) ≃ₜ* W_F/R_F(x)` and the images of `R_K(y)` and `R_F(y)`.
- `GaloisTruncationIsoAt F E x` specializes the first predicate to
  `K = EP` and `ι = intermediateGaloisMap F E`.
- `WeilTruncationIsoAt F E x` specializes the second predicate to
  `K = EP` and `ι = intermediateWeilMap F E`.
- `truncatedWeilClasses.{u, v} F μ` is the subset of
  `FiniteRepresentation.IsomorphismClasses.{0, u, v} ℂ W_F` consisting of
  classes with a representative `A` satisfying
  `A.IsContinuous ∧ IsTrivialAt F A μ`. Here `IsTrivialAt` means that
  every element of `R_F(μ)` acts as the identity. The existential
  representative formulation uses the Library's actual `classOf`
  quotient and requires no new quotient construction.

The general predicates with a variable field `K` are used before
specializing to `EP`: direct quotient expressions at `E.asPadicField`
do not elaborate with the existing normality and quotient-group
instances. This factorization changes no mathematical content.

## The eight statements

For statements 1–6, let `E/F` be any finite intermediate extension and let
`μ : ℝ` satisfy the transitivity hypothesis above.

1. **`TruncationGaloisComapStatement.{u}`.** For every real `x` with
   `-1 ≤ x ≤ μ`, the preimage of `G_F^x` under `ι_G` is `G_E^x`.
   This is the absolute-Galois form of the injectivity clause of the
   route note's Lemma `lem:trunc`, lines 878 and 887.

2. **`TruncationGaloisQuotientStatement.{u}`.** For every real `x` with
   `-1 ≤ x ≤ μ`, `GaloisTruncationIsoAt F E x` holds. Thus the map
   induced by `ι_G` identifies the quotients as filtered topological
   groups. This is the absolute-Galois counterpart of the filtered
   quotient assertion in `lem:trunc`, lines 878–880.

3. **`TruncationWeilComapStatement.{u}`.** For every real `x` with
   `-1 ≤ x ≤ μ`, the preimage of `R_F(x)` under `ι_W` is `R_E(x)`.
   This is precisely the subgroup-intersection or injectivity clause
   `W_E ∩ R_F(x) = R_E(x)` of `lem:trunc`, lines 878 and 887.

4. **`TruncationWeilQuotientStatement.{u}`.** For every real `x` with
   `-1 ≤ x ≤ μ`, `WeilTruncationIsoAt F E x` holds. This states the
   filtered quotient isomorphism of `lem:trunc`, lines 878–880.

5. **`TruncationWeilDegreeStatement.{u}`.** If also `0 ≤ μ`, then for
   every `w : W_E`,
   `localDegree F (ι_W w) = localDegree EP w`. This records the degree
   compatibility underlying the unramified-twist clause of `lem:trunc`,
   line 882. An unramified character is
   `Weil.Local.unramifiedCharacter (localDegree F) z`, so this equality
   identifies its restriction with the character with the same `z`
   over `EP`.

6. **`TruncationWeilRestrictionStatement.{u, v}`.** If also `-1 ≤ μ`,
   restriction on isomorphism classes is a `Set.BijOn` from
   `truncatedWeilClasses F μ` onto `truncatedWeilClasses EP μ`.
   In addition, for every finite-dimensional complex representation
   `A` of `W_F` with `IsTrivialAt F A μ`,
   `weilRestrict E A` is irreducible if and only if `A` is, and for
   every real `r ≥ -1` the fixed spaces
   `upperFixedSpace EP (weilRestrict E A) r` and `upperFixedSpace F A r`
   have the same `Module.finrank ℂ`. This second clause does not add
   a continuity hypothesis. The class bijection concerns continuous
   representatives, as specified by the supporting set definition.
   This is the “consequently” sentence of `lem:trunc`, line 882.
   Restriction keeps the original vector space, hence its dimension.
   The fixed-space ranks record the ramification data from which the
   triviality thresholds, slope and Swan exponent are read.

7. **`KummerStageGaloisQuotientStatement.{u}`.** For every `ϖ` and `πs`
   satisfying `IsKummerRootSystem F ϖ πs`, every natural `n`, and
   every real `x` with `-1 ≤ x ≤ b`,
   `GaloisTruncationIsoAt F (kummerStage F πs n) x` holds.
   This is the absolute-Galois counterpart of the first sentence of
   the route note's Corollary `cor:kummer`, line 891.

8. **`KummerStageWeilQuotientStatement.{u}`.** With the same root-system
   hypothesis, every natural `n` and every real `x` with `-1 ≤ x ≤ b`
   satisfy `WeilTruncationIsoAt F (kummerStage F πs n) x`.
   This is the Weil quotient assertion of `cor:kummer`, line 891.
   Both Kummer statements include stage zero.

## Scope and route for later proofs

The route note uses `μ > 0`, `0 ≤ x ≤ μ` for subgroup comparison and
`0 < x ≤ μ` for quotient isomorphisms. These statements use Serre's
range `[-1, μ]`. At `x = -1` the upper groups are the whole groups,
so the quotients are trivial. For `-1 < x ≤ 0` the upper groups are
inertia; transitivity at such an index forces total ramification and
gives the inertia quotient comparison. For `μ < -1` statements 1–4
have an empty conclusion interval. Statement 5 requires `μ ≥ 0`
and statement 6 requires `μ ≥ -1`, exactly as stated.

For `μ > 0` the route note's slope condition `< μ` is expressed by
triviality on `R_F(μ)`, using its line 183 slope convention and the
left continuity of the upper filtration (Serre IV §3, Remark 1).
The Lean statements use the actual triviality predicate. They do
not identify the Library's separately defined finite-inertia Swan
conductor with an expression in these fixed-space ranks. For an
irreducible continuous representation, the ranks determine the
triviality threshold and hence the slope; the source's relation
`sw = dim · slope` then gives the Swan exponent. That comparison is
an obligation for later proofs, not a theorem supplied here.

The following dependency route explains the formulation; it is not
implemented as a proof in this module.

- Statements 1 and 3 come from Task 7450's
  `HerbrandPsiTruncationStatement` together with the existing Herbrand
  comparisons
  `HerbrandBridge.intermediateGaloisMap_mem_absoluteUpperRamificationGroup_iff`
  and `HerbrandBridge.intermediateWeilMap_mem_upperGroup_iff`.
  Those compare upper groups at `x` and `relativeHerbrandPsi E x`.
- Statements 2 and 4 use statements 1 and 3 for the kernel and the
  transitivity product for surjectivity. The induced maps also identify
  the images of all upper groups of indices `-1 ≤ y ≤ x`.
  The Galois topological comparison uses compactness and closedness
  of absolute upper groups. The Weil comparison needs continuity
  of the inverse as well, obtainable through compact inertia and
  the degree map.
- Statement 5 uses total ramification when `μ ≥ 0`, so the residue
  degree is one. The existing `localDegree_intermediateWeilMap`
  gives the degree in the base as the degree over `EP` raised to
  the residue degree.
- Statement 6 uses statements 3 and 4 at `x = μ`: representations
  trivial at `μ` descend to the topological quotients, and the
  quotient isomorphism gives the bijection with continuity in both
  directions. Their action images agree, giving irreducibility.
  For `-1 ≤ r ≤ μ`, the filtered comparison identifies the actions
  determining the fixed spaces; for `r ≥ μ`, both groups act trivially.
- Statements 7 and 8 specialize statements 2 and 4 using Task 7450's
  `KummerTowerUpperSupStatement` at `μ = kummerBreak F`. That bound
  is positive for a p-adic field.

There is no statement about the infinite union of the tower, its Weil
group, the field of norms, characteristic `p`, Deligne's close-fields
theorem, or twist-orbit counts in this module.

## Sources and reading locations

- Operator, *Numerical local Langlands for GL_n, counts on the two sides
  and the recommended route* (16 November 2026), registered
  `operator-numerical-llc-route-2026-11-16`; source
  `/home/taskhub/pilot/literature/Operator note - Numerical local Langlands for GL_n, counts on the two sides and the recommended route (16 November 2026)/numerical-LLC-route.tex`.
  Read lines 168 and 183 for upper groups and slope, Lemma `lem:trunc`
  at lines 876–887, and the first sentence and proof of Corollary
  `cor:kummer` at lines 890–897. The extension to the Galois group,
  the nonpositive index range and the supporting predicates are
  internal formulations explained above.
- Jean-Pierre Wintenberger, *Le corps des normes de certaines extensions
  infinies de corps locaux; applications* (1983), registered
  `wintenberger-1983-field-of-norms`; original
  `/home/taskhub/central-library/Wintenberger--Le corps des normes de certaines extensions infinies de corps locaux ; applications--1983.pdf`.
  Read 1.1.1–1.1.2, printed p. 61 (PDF p. 4), for the relative-function
  convention, the identity on `[-1, 0]` and the subgroup comparison;
  1.2.1, printed p. 62 (PDF p. 5), for the integral formula; and
  1.3.1, printed p. 64 (PDF p. 7), for the elementary-extension
  transitivity criterion behind the Kummer application.
- Jean-Pierre Serre, *Local Fields*, GTM 67, Springer (1979), registered
  `serre-1979-local-fields`; original
  `/home/taskhub/central-library/Serre--Local Fields--1979.pdf`.
  Read IV §3, Remarks 1–2, printed p. 75 (PDF p. 82), for left
  continuity of the absolute upper filtration and the relative
  Herbrand function for a possibly non-Galois subextension.
