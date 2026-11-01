# Actual full-fixed and right-corner duality comparisons (Renard I.4.1)

Module `Langlands.Algebra.NonUnitalModuleDualFixedPartComparisonStatements`
states, as Prop-valued definitions, how three versions of the dual of the
e-fixed part compare. Its closed target is
`Langlands.Algebra.NonUnitalModuleDualFixedPartComparisonStatements.FixedPartComparisons`.
The module proves none of these assertions. Its only proofs are `rfl` checks
that the closed target unfolds to the intended telescope.

It imports the published construction
`Langlands.Algebra.NonUnitalModuleDualFixedPartComparison` (artifact
`353e93b2-f090-46e9-beb5-6efb7ae82b24`). That construction brings in the
published restriction/extension maps of
`Langlands.Algebra.NonUnitalModuleDualFixedPartMaps`. The module also imports
the dual pullbacks of `Langlands.Algebra.NonUnitalModuleDualMap`. It adds no
new construction.

## Source

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French edition dated 9 July 2026. It is registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

- I.4.1, printed p.22 / one-based PDF p.28, defines the dual
  `M* = Hom_C(M, C)` of a nondegenerate left A-module M. It notes that M* is
  naturally a right A-module, and calls the nondegenerate part of M* the
  dual `M~`.
- I.4.1, printed p.23 / PDF p.29, states the Lemme "`M~·e ≃ (e·M)*`". The
  proof uses the splitting `M = e·M ⊕ (1−e)·M`. It identifies `(e·M)*` with
  the linear forms on M that vanish on `(1−e)·M`. These are exactly the forms
  fixed by the right action of e, so `(e·M)* ≃ M*·e ≃ M~·e`. The Corollaire on
  the same page uses this as `M~·e = M*·e = (e·M)*`.
- The original nonunital conventions are on printed pp.5–7 / PDF pp.11–13.
  The canonical complex scalars of a nondegenerate module are in I.2.1,
  printed p.14 / PDF p.20. The idempotent splitting used in the proof is in
  I.3.1, printed p.19 / PDF p.25.

The supplement `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`, is
consulted at PDF pp.1–2. Its correction to the proof of the proposition on
printed p.29 of the 2010 edition uses "les isomorphismes démontrés en I.4.1",
writing `(M~·e)*` and `((e·M)*)*`. It does not change the lemma, and the 2026
edition governs.

## Source spaces and their Lean counterparts

Fix the data quantified by `FixedPartComparisons`:

- `A : Type uA` with `NonUnitalRing A`, `Module ℂ A`, `IsScalarTower ℂ A A`,
  `SMulCommClass ℂ A A` and `hA : IsIdempotented A`;
- `M : Type uM` with `AddCommGroup M`, the original `NonUnitalModule A M` and
  `hM : IsNondegenerate A M`;
- `e : Idempotent A`.

No `Module ℂ M` is assumed. A has no unit or nontriviality hypothesis. There is
no faithfulness, anti-involution, admissibility, reflexivity or dimension
hypothesis either. Zero algebras, zero modules and the zero idempotent are all
allowed.

The three source spaces are:

- **Nondegenerate fixed dual `M~·e`.** In Lean this is R =
  `RightFixedPart hA hM e`, the published fixed part
  `FixedPart (oppositeIdempotent e) (NonUnitalModuleDual.Dual hA hM)`.
  `Dual hA hM` is the actual nondegenerate part of the full dual. Its right
  action is the published `NonUnitalModuleDual.dualAction`, installed locally
  as an `Aᵐᵒᵖ`-module.
- **Full fixed dual `M*·e`.** This is F = `FullRightFixedPart hA hM e`, the
  fixed part `FixedPart (oppositeIdempotent e) (NonUnitalModuleDual.FullDual hA hM)`.
  Here `FullDual hA hM` is `Module.Dual ℂ M` for the recovered scalars
  `NondegenerateScalars.complexModule hA hM`. Its right action
  `NonUnitalModuleDual.fullAction` is precomposition with the original action,
  installed locally.
- **Ordinary dual `(e·M)*`.** This is O = `Module.Dual ℂ (FixedPart e M)`,
  formed with exactly `NonUnitalModuleCorner.complexModule hA hM e` on
  `FixedPart e M`.

### Named complex scalars

Each predicate fixes these scalar structures with `letI`:

- `rightFixedModule hA hM e` on R;
- `fullRightFixedModule hA hM e` on F;
- the `Module.Dual` structure on O over
  `NonUnitalModuleCorner.complexModule hA hM e`.

Each is inherited from the published dual scalars. None is a new hypothesis.

### Corner actions

The right corner ring is exactly `Idempotent.Corner (oppositeIdempotent e)`,
the corner of `oppositeIdempotent e` in `Aᵐᵒᵖ`. It acts on R and F through the
published `NonUnitalModuleCorner.fixedPartModule`, which comes from the
original right action on the dual. On O it acts through
`fixedPartDualCornerModule hA hM e`, given by
`(a • ell) x = ell (cornerUnop e a • x)`. That formula precomposes with the
original corner action on `FixedPart e M`. The construction relates this ring
to the opposite of `Idempotent.Corner e` by `cornerUnop` and
`cornerOppositeEquiv`. No anti-involution of A is chosen.

### Maps

- `toFullFixed : R →ₗ[ℂ] F` drops only the nondegeneracy membership proof and
  keeps the functional.
- `fromFullFixed : F →ₗ[ℂ] R` keeps the functional. It uses
  `oppositeIdempotent e` as the nondegeneracy witness.
- `toFullFixedCorner` and `fromFullFixedCorner` are the same functions,
  bundled as `Idempotent.Corner (oppositeIdempotent e)`-linear maps.
- `restriction : R →ₗ[ℂ] O` and `extension : O →ₗ[ℂ] R` are the published
  restriction to `FixedPart e M` and extension by the projection `m ↦ e • m`.
- `restrictionCorner` and `extensionCorner` are the same functions, bundled as
  corner-linear maps.

## What is asserted, and which parts are derived

The source asserts the identification `(e·M)* ≃ M*·e ≃ M~·e`, together with
the functoriality of `M ↦ M~` used in the exactness proof. Requiring this
identification as entire-map equations, with both scalar interfaces,
inclusion compatibility and naturality, is an explicit formulation derived
from that text. The source does not list these formulations separately.

1. **`FullFixedInverseIdentities hA hM e`.** Four equations of whole linear
   maps:
   - `(toFullFixed hA hM e).comp (fromFullFixed hA hM e) = LinearMap.id`;
   - `(fromFullFixed hA hM e).comp (toFullFixed hA hM e) = LinearMap.id`;
   - the same two equations for `toFullFixedCorner` / `fromFullFixedCorner`.

   The first pair is over ℂ and the second over the right corner ring.

2. **`FullFixedEquivalences hA hM e`.** There exist equivalences
   `E : R ≃ₗ[ℂ] F` and `C : R ≃ₗ[Idempotent.Corner (oppositeIdempotent e)] F`
   with the following properties:
   - `E.toLinearMap = toFullFixed` and `E.symm.toLinearMap = fromFullFixed`;
   - `C.toLinearMap = toFullFixedCorner` and
     `C.symm.toLinearMap = fromFullFixedCorner`;
   - the underlying `AddMonoidHom`s of C and E agree in both directions;
   - two equations of entire additive maps into the original `FullDual`
     (derived inclusion compatibility):
     - the fixed-part inclusion of F
       (`NonUnitalModuleCorner.inclusion (oppositeIdempotent e)` into
       `FullDual`) after `E` equals `NonUnitalModuleDual.inclusion hA hM`
       after the fixed-part inclusion of R into `Dual`;
     - that composite inclusion of R after `E.symm` equals the fixed-part
       inclusion of F.

3. **`CornerEquivalences hA hM e`.** There exist three equivalences:
   - a corner equivalence `C : R ≃ O` with `C.toLinearMap = restrictionCorner`
     and `C.symm.toLinearMap = extensionCorner`, whose underlying additive maps
     equal those of `restriction` and `extension`;
   - a complex equivalence `Fℂ : F ≃ O` with forward map
     `(restriction hA hM e).comp (fromFullFixed hA hM e)` and inverse
     `(toFullFixed hA hM e).comp (extension hA hM e)`;
   - a corner equivalence `FC : F ≃ O` with forward map
     `(restrictionCorner hA hM e).comp (fromFullFixedCorner hA hM e)` and
     inverse `(toFullFixedCorner hA hM e).comp (extensionCorner hA hM e)`.

   The underlying additive maps of `FC` and `Fℂ` agree in both directions.

4. **`Naturality hA hM hN e f`.** Let `N : Type uN` be another module with its
   own `AddCommGroup N`, original `NonUnitalModule A N` and
   `hN : IsNondegenerate A N`, and let `f : NonUnitalModuleHom A M N` be an
   original intertwiner. The predicate first names three specified maps:
   - `RC`, the corner-linear restriction to fixed parts of the actual
     nondegenerate dual pullback `NonUnitalModuleDual.pullback hA hM hN f`;
   - `SC`, the same restriction of the actual full pullback
     `NonUnitalModuleDual.fullPullback hA hM hN f`;
   - `Dℂ`, the complex dual map of
     `NonUnitalModuleCorner.restrictLinear hA hM hN e f`.

   It asserts that there exist representatives
   `Rℂ : R_N →ₗ[ℂ] R_M`, `Sℂ : F_N →ₗ[ℂ] F_M` and
   `DC : O_N →ₗ[Idempotent.Corner (oppositeIdempotent e)] O_M` whose entire
   underlying additive maps equal those of `RC`, `SC` and `Dℂ`. That these
   maps are linear for the other scalar ring is therefore a conclusion, not an
   assumption. With these witnesses it asserts eight equations of entire
   linear maps:
   - the two R ⇄ F squares over ℂ, for `toFullFixed` and `fromFullFixed`
     with `Rℂ`, `Sℂ`;
   - the two R ⇄ F squares over the corner, for `toFullFixedCorner` and
     `fromFullFixedCorner` with `RC`, `SC`;
   - the two R ⇄ O corner squares, for `restrictionCorner` and
     `extensionCorner` with `RC`, `DC`;
   - the two complex squares for the composite F ⇄ O maps of item 3, with
     `Sℂ`, `Dℂ`.

   This derived formulation expresses the source's functoriality of the dual
   under precomposition with f, which preserves the e-splitting.

`FixedPartComparisons.{uA, uM, uN}` quantifies over every A, M, hA, hM and e
with all of the structure listed above. It asserts the conjunction of items
1–3, together with item 4 for every N, hN and f. The universes uA, uM and uN
are independent. It contains no equivalence, inverse or naturality hypothesis.

## Interface checks

Complete unapplied `example`s check the type of each predicate:

- the two-universe predicates at generic universes and at both unequal
  assignments (uA, uM) = (0,1) and (1,0);
- `Naturality` generically and at (uA, uM, uN) = (0,1,2) and (2,1,0).

Three `rfl` examples check that `FixedPartComparisons` unfolds to the full
closed telescope generically and at those two unequal triples. They prove
only that the telescope agrees, never a predicate.

## Scope and ownership

Task `9e60fa95-77ba-4cbc-9994-ad43fc47fc19` still owns the basic complex
family for R ≃ O: inverse identities, equivalence and naturality, stated in
`Langlands.Algebra.NonUnitalModuleDualFixedPart`. This family adds the
full-dual and right-corner comparisons and does not restate or replace that
family. It asserts nothing about exactness of duality, the bidual injection,
reflexivity, admissibility, the I.4.2 comparisons or completion. The exact
proof of `FixedPartComparisons` is a separate successor task, to start once
this statement is published.

## Provenance

This is a derived formulation of Renard I.4.1 over the published nonunital
construction. Worker 6 drafted the statement family. Worker 1174 renamed
binders, added the unequal-universe interface checks and wrote this
documentation.
