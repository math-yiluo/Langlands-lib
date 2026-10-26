# Eventual residue-fibre injectivity for local approximation systems

`Langlands.Algebra.LocalApproximationResidueInjectivityStatement` is a
Prop-valued definition extracting the eventual injectivity assertion inside
the proof of the Stacks Project, Lemma 10.128.4
([046Y](https://stacks.math.columbia.edu/tag/046Y)), together with the
raw-residue-fibre corollary stated immediately afterwards. It concerns every
local module system satisfying the six approximation properties of Lemma
10.127.13 ([00QX](https://stacks.math.columbia.edu/tag/00QX)).
This module states that assertion; it supplies no proof of it.

## Sources and extraction

The registered original is
`stacks-algebra-flatness-criteria-2026-10-22`, content SHA256
`4bc1f2db6141508f6dad2132d4abc7963380cd71497ad20620c0e511b972a949`.
The precise locations are:

- `046Y.html`, Lemma 10.128.4, complete proof, especially the displayed
  maps Ψλ and Ψλ,λ′, the finite-kernel and localization argument ending in
  eventual vanishing of the kernels of Ψλ, and the next paragraph's
  injectivity of the raw residue-fibre map;
- `00QL.html`, Lemma 10.127.13 (00QX), all six clauses and the proof.

The complete 046Y proof first chooses simultaneous approximations for a
module map and arranges flatness of its target components. The intervening
argument about Ψλ uses the approximation properties of its source module:
the extended fibre ring is essentially of finite type over the target
residue field, its finite module has a finitely generated kernel, and the
colimit and localization arguments kill that kernel at sufficiently large
stages. The next paragraph deduces injectivity before extending the residue
field. The final part then applies the Noetherian lifting result to the
approximated module map and passes to the colimit.

The present definition isolates only the intervening eventual injectivity
assertion and its immediate corollary. The finite-presentation assumptions
used to obtain an approximation and the flatness assumption used elsewhere
in 046Y are not assumptions of this extracted statement. Its provenance is
this extraction from the proof, rather than a separately numbered lemma in
the source. A proof for arbitrary systems satisfying the published six
clauses remains a separate obligation.

On 26 October 2026 no source-specific registered errata note was present in
the current Library or project `notes/errata/` locations. The bounded current
check is registered as
`stacks-046y-00qx-current-errata-check-2026-10-26`, content SHA256
`4ff8dc3741a78495d7fdb00f179e9c50a3c6f6de1dc2ad70166be5c7cb064342`,
files `046Y.html`, `00QX.html`, and `README.md`. Both official pages showed
zero comments. Their complete statements and proofs agree, after whitespace
normalization, with the registered 22 October original. This records the
checked pages and registered-note locations, not an exhaustive errata search.

## Quantifiers and approximation hypothesis

The definition has seven independent universe parameters, declared as
`uI uA uB uN uR uS uM`. Its inputs are exactly:

- `ι : Type uI` with `[Preorder ι] [Nonempty ι] [IsDirectedOrder ι]`;
- commutative local rings `R : Type uR` and `S : Type uS`, with
  `[Algebra R S] [IsLocalHom (algebraMap R S)]`;
- `D : LocalAlgebraSystem.{uI,uA,uB,uR,uS} ι R S`;
- `M : Type uM` with `[AddCommGroup M] [Module R M] [Module S M]`
  and `[IsScalarTower R S M]`;
- `E : LocalModuleSystem.{uI,uA,uB,uN,uR,uS,uM} D M`.

Here `D.base i`, `D.alg i`, and `E.obj i` inhabit `Type uA`, `Type uB`,
and `Type uN`, respectively. There are no universe equalities. The target
retains the caller's given compatible `R`- and `S`-actions.

The sole further hypothesis is `E.IsApproximation`. Its six published
clauses give the actual ring and additive module colimits, essential finite
type of each base ring over ℤ, essential finite type of each component
algebra over its base, finite component modules, prime localization of the
canonical ring base-change maps, and bijectivity of the canonical module
base-change maps. No target finite-presentation, flatness, nonzero-module,
or additional Noetherian assumption is imposed. No extra comparison maps,
colimit or localization witnesses, or kernel-stabilization hypothesis are
parameters of the statement.

## Actual maps and common bound

All constructions are imported unchanged from
`Langlands.Algebra.LocalApproximationResidueFiber`.
Write `Rⱼ = D.base j`, `Mⱼ = E.obj j`,
`κⱼ = IsLocalRing.ResidueField Rⱼ`, and
`κ = IsLocalRing.ResidueField R`. The component `Rⱼ`-action is the
published restriction along `algebraMap (D.base j) (D.alg j)`.
The algebra structure on κ over κⱼ is induced by the actual field map
`D.residueι j`.

The conclusion is exactly

```lean
E.IsApproximation →
  ∃ i : ι, ∀ j : ι, i ≤ j →
    Function.Injective (E.residueFiberΨ j) ∧
    Function.Injective (E.residueFiberι j)
```

The first map is the actual κ-linear map

```text
E.residueFiberΨ j : κ ⊗[κⱼ] (κⱼ ⊗[Rⱼ] Mⱼ) →ₗ[κ] κ ⊗[R] M
a ⊗ (b ⊗ m) ↦ (a * D.residueι j b) ⊗ E.ιM j m.
```

The second is the actual residue-field-semilinear cocone map

```text
E.residueFiberι j : κⱼ ⊗[Rⱼ] Mⱼ →ₛₗ[D.residueι j] κ ⊗[R] M
b ⊗ m ↦ D.residueι j b ⊗ E.ιM j m.
```

The source presents a residue module as `Mⱼ / 𝔪ⱼ Mⱼ` and extends scalars
with the field on the right. The published constructions use its standard
tensor presentation `κⱼ ⊗[Rⱼ] Mⱼ` and put the extending scalar field
first. This accounts for both tensor orders in the first displayed map;
no replacement action or additional comparison map is introduced here.

For a field extension κⱼ → κ, the canonical map sending `x` to
`1 ⊗ x` is injective. Its composite with `E.residueFiberΨ j` is
`E.residueFiberι j`, which explains the raw-fibre corollary. Both
injectivity assertions are required at every stage above the same `i`.
The definition proves neither this corollary nor the finite-kernel,
tensor-colimit, or localization arguments needed for the first conjunct.
