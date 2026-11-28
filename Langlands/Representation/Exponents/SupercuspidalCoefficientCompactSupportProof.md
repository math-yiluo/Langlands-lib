# Supercuspidal coefficient norms on the full central quotient: proof

Module
`Langlands.Representation.Exponents.SupercuspidalCoefficientCompactSupportProof`,
namespace `Langlands.Aubert.General.RepresentedParabolic`.

## Result

`supercuspidalUnitaryCoefficientCompactSupport` has type exactly
`SupercuspidalUnitaryCoefficientCompactSupportStatement.{u, v}`, the
proposition of the module
`Langlands.Representation.Exponents.SupercuspidalCoefficientCompactSupportStatement`
([statement](SupercuspidalCoefficientCompactSupportStatement.md)), with the two
universe parameters `u` (the field) and `v` (the representation carrier) left
independent. The theorem has no hypotheses.

So, for every nonarchimedean local field `k : Type u` with Hausdorff topology,
every group scheme `H` over `Spec k` with `IsConnectedReductive H`, the canonical
point topology on `rationalPoints H` with the assumed local compactness and
nonarchimedean group structure, every irreducible
`ρ : SmoothRep.{0, u, v} ℂ (rationalPoints H)` whose normalized Jacquet module
`(jacquetFunctor p' l' r' hp' hr' hl' hmul').obj ρ` is a subsingleton for every
proper actual rational parabolic `p'` with rational Levi `l'` and geometric
unipotent radical `r'`, every `c : UnitaryCentralCharacter ρ.representation`,
every `ℓ : SmoothDual ρ.representation` and every vector `v : ρ`, the function
`c.coefficientNorm ℓ.1 v` on
`rationalPoints H ⧸ Subgroup.center (rationalPoints H)` has compact support.
No characteristic, residue-characteristic, splitness, quasi-splitness or
admissibility condition is added. Irreducibility of `ρ` is a binder of the
statement; the proof does not use it.

Lean reports only the standard axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Implemented proof

The proof is one application:

```
supercuspidalUnitaryCoefficientCompactSupportStructuralReduction
  GroupScheme.standardCocharacter GroupScheme.relativeRootSystem
  BruhatTits.SpecialCompact.jointSpecialCompactBasisExistence
```

- `supercuspidalUnitaryCoefficientCompactSupportStructuralReduction`
  (module `Langlands.Representation.Exponents.SupercuspidalCoefficientCompactSupportReduction`)
  proves that `StandardCocharacterStatement.{u}`, `RelativeRootSystemStatement.{u}`
  and `JointSpecialCompactBasisExistenceStatement.{u}` together imply
  `SupercuspidalUnitaryCoefficientCompactSupportStatement.{u, v}`.
  [Reduction](SupercuspidalCoefficientCompactSupportReduction.md)
- `Langlands.GroupScheme.standardCocharacter`
  (module `Langlands.GroupScheme.Rational.StandardCocharacterProof`) proves
  `StandardCocharacterStatement.{u}` with no hypotheses: for a maximal split
  torus of a connected reductive group over any field and a generic
  cocharacter, every set of simple relative roots has a standard cocharacter,
  and the choice-free standard parabolic, Levi and unipotent subgroup functors
  equal its dynamic subgroup functors.
  [Proof](../../GroupScheme/Rational/StandardCocharacterProof.md)
- `Langlands.GroupScheme.relativeRootSystem`
  (module `Langlands.GroupScheme.Rational.RelativeRootSystemProof`) proves
  `RelativeRootSystemStatement.{u}` with no hypotheses: the relative roots of a
  maximal split torus of a connected reductive group over any field form a
  finite crystallographic root system whose Weyl group is the image of
  `N(k)/Z(k)`. [Proof](../../GroupScheme/Rational/RelativeRootSystemProof.md)
- `Langlands.BruhatTits.SpecialCompact.jointSpecialCompactBasisExistence`
  (module `Langlands.BruhatTits.SpecialCompact.JointBasisProof`) proves
  `JointSpecialCompactBasisExistenceStatement.{u}` with no hypotheses: for every
  nonarchimedean local field, connected reductive group, maximal split torus
  and generic cocharacter, one apartment datum, one special vertex and one
  represented torus centralizer carry the special compact properties, the
  Cartan comparison (Renard V.5.1) and the simultaneous standard basis of
  compact open subgroups with Iwahori decompositions (Renard V.5.2).
  [Proof](../../BruhatTits/SpecialCompact/JointBasisProof.md)

The three premises of the reduction are quantified over the field universe
`u` only, and the reduction is universe-polymorphic in `u` and `v`, so the
application leaves both universes free.

## What the reduction does with these inputs

For the given `k`, `H` and `ρ`, the reduction's proof (described in its
Markdown) runs as follows.

1. `exists_maximalSplitTorus_genericCocharacter` gives a maximal split torus
   `i` with a generic cocharacter `ν`; the relative root system gives a
   realization for `i`, and with it a finite enumeration of the simple
   relative roots (`simpleRelativeRootFintype`).
2. The joint basis theorem, applied to `i` and `ν`, gives an apartment datum
   `D`, a special vertex `x`, a represented centralizer with its character
   comparison, the special compact properties of
   `K₀ = D.specialCompactSubgroup x` (in particular compactness), the Cartan
   comparison and `SimultaneousStandardBasisAt i ν K₀`, all for the same
   torus and cocharacter. `rationalPositiveCartanCover` turns the Cartan
   comparison into a `FiniteCartanCovering` for `K₀`.
3. `isCuspidal_of_all_represented_parabolics_of_standardCocharacter` uses the
   standard cocharacters to recognize each actual standard parabolic, with its
   Levi and unipotent radical, as a represented rational parabolic in the sense
   of the hypothesis, and proves it proper for every proper standard face. The
   vanishing hypothesis on every proper actual rational parabolic therefore
   makes `ρ` cuspidal for the actual standard point-subgroup family.
   The standard unipotent subgroups are closed by
   `isClosed_unipotent_of_isNonarchimedeanLocalField`.
4. `compactUnitaryCoefficients_centerQuotient_of_isCuspidal` combines this
   cuspidality, the simultaneous standard basis and the finite Cartan cover:
   for each finite set of centralizer representatives in the cover, cuspidality
   bounds all simple-root coordinates on the nonzero locus of the coefficient
   after compact translates, and these bounds with dominance in the Cartan
   cover give compact support of `c.coefficientNorm ℓ.1 v` modulo the full
   abstract center.

The proof establishes compactness of the descended norm directly on the
quotient by `Subgroup.center (rationalPoints H)`; it does not pass through
Renard's compactness modulo `Z(G)` and the comparison described in the
statement's Markdown.

## Prerequisites actually used

The four theorems applied are proved in the Library. The three structural
theorems have no hypotheses, and the only premises of the reduction are
exactly the three statements they prove. No unproved proposition enters as a
premise. In particular the theorem takes no structural statement, no chosen
special compact subgroup, Cartan covering or simultaneous basis, and no
standard-parabolic family as a hypothesis: these are all produced inside the
proof from the three theorems above.

## Provenance

The statement is a consequence of Renard, *Représentations des groupes
réductifs p-adiques* (French version dated 9 July 2026), VI.2.1, theorem,
(a) ⇒ (b); the theorem is on printed pp.137–139 / PDF pp.143–145 and the
proof of (a) ⇒ (b) on printed pp.138–139 / PDF pp.144–145. The source is
registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. Renard's
proof is by contraposition: a coefficient without compact support modulo the
center gives, through the Cartan decomposition (V.5.1), a sequence `t_n` in the
positive cone and a simple root `α` with `|α(t_n)|_F → 0` (VI.2.1.1), and
averaging over a compact open
subgroup with an Iwahori decomposition (V.5.2) along the corresponding maximal
standard parabolic produces a nonzero Jacquet module. The Library route
follows this argument in the positive form of step 4: cuspidality gives an
upper bound on the simple-root coordinates of the support, and the Cartan
covering turns the bound into compactness. This theorem itself is an internal
composition of the published Library results named above.
