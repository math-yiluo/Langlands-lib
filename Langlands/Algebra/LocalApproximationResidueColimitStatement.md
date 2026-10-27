# Preservation of the actual residue-fibre colimits

`Langlands.Algebra.LocalApproximationResidueColimitStatement` is a
Prop-valued definition. It states that residue fields, fibre rings, and
residue modules of a directed local algebra or module system pass to the
colimit along the actual published maps. This module states that assertion
only and supplies no proof of it.

It is an internal general colimit-preservation statement. The Stacks Project
contains no separate lemma of this form. It generalizes the particular
quotient-colimit observations made inside two proofs, described under
provenance below.

## Quantifiers and universes

The definition has seven independent universe parameters,
`uI uA uB uN uR uS uM`, and no universe equalities. Its common inputs are:

- `ι : Type uI` with `[Preorder ι] [Nonempty ι] [IsDirectedOrder ι]`;
- commutative local rings `R : Type uR` and `S : Type uS`, with
  `[Algebra R S] [IsLocalHom (algebraMap R S)]`;
- `D : LocalAlgebraSystem.{uI,uA,uB,uR,uS} ι R S`, whose base rings
  `D.base i : Type uA` and algebras `D.alg i : Type uB` are local.

The third conjunct also quantifies over `M : Type uM` with
`[AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]`,
and over `E : LocalModuleSystem.{uI,uA,uB,uN,uR,uS,uM} D M`, whose
components `E.obj i` inhabit `Type uN`. The target keeps the caller's given
compatible `R`-action. The direct-limit and tensor carriers live in the
appropriate maxima of these universes.

Write `Rᵢ = D.base i`, `Sᵢ = D.alg i`, `Mᵢ = E.obj i`,
`κᵢ = IsLocalRing.ResidueField Rᵢ`, and `κ = IsLocalRing.ResidueField R`.
The component `Rᵢ`-action on `Mᵢ` is the published restriction along
`algebraMap Rᵢ Sᵢ`, opened by `open scoped Langlands.Algebra.LocalModuleSystem`.
No other scoped instance is opened.

## The three conjuncts

The proposition is the conjunction of three implications. Each conclusion is
bijectivity of an actual lift out of a direct limit. Each lift is let-bound
inside the proposition with its full type.

1. **Residue fields.** Assume `Function.Bijective D.baseColimitMap`. The
   diagram is `fun i ↦ κᵢ` with transitions `D.residueMap h : κᵢ →+* κⱼ`.
   The cocone is `D.residueι i : κᵢ →+* κ`. Both maps are induced by
   `IsLocalRing.ResidueField.map` from the given base transitions and
   cocone. The lift is
   `Ring.DirectLimit.lift (fun i ↦ κᵢ) (fun _ _ h ↦ D.residueMap h) κ
   (fun i ↦ D.residueι i) (fun _ _ h a ↦ D.residueι_compat h a)`.
   The conclusion is that this ring map is bijective.
2. **Fibre rings.** Assume `D.IsColimit`. This is bijectivity of both
   `D.baseColimitMap` and `D.algebraColimitMap`. The diagram is
   `D.FiberRing i = Sᵢ ⊗[Rᵢ] κᵢ` with transitions `D.fiberRingMap h`,
   which send `s ⊗ a ↦ D.algMap i j h s ⊗ D.residueMap h a`. The target is
   `LocalAlgebraSystem.TargetFiberRing R S = S ⊗[R] κ`. The cocone is
   `D.fiberRingι i`, sending `s ⊗ a ↦ D.algι i s ⊗ D.residueι i a`. The lift is
   `Ring.DirectLimit.lift D.FiberRing (fun _ _ h ↦ D.fiberRingMap h)
   (S ⊗[R] κ) (fun i ↦ D.fiberRingι i) (fun _ _ h x ↦ D.fiberRingι_compat h x)`.
   The conclusion is that this ring map is bijective.
3. **Residue modules.** For every `M` and `E` as above, assume
   `E.IsColimit`. This is `D.IsColimit` together with bijectivity of
   `E.moduleColimitMap`. The diagram is `E.ResidueFiber i = κᵢ ⊗[Rᵢ] Mᵢ`,
   with additive transitions `(E.residueFiberMap h).toAddMonoidHom`. These
   send `a ⊗ m ↦ D.residueMap h a ⊗ E.map i j h m`. The target is
   `LocalModuleSystem.TargetResidueFiber R M = κ ⊗[R] M`. The cocone is
   `(E.residueFiberι i).toAddMonoidHom`, sending
   `a ⊗ m ↦ D.residueι i a ⊗ E.ιM i m`. After `letI := Classical.decEq ι`,
   the lift is
   `AddCommGroup.DirectLimit.lift E.ResidueFiber
   (fun _ _ h ↦ (E.residueFiberMap h).toAddMonoidHom) (κ ⊗[R] M)
   (fun i ↦ (E.residueFiberι i).toAddMonoidHom)
   (fun _ _ h x ↦ E.residueFiberι_compat h x)`.
   The conclusion is that this additive map is bijective. The additive
   direct limit and the explicit `Classical.decEq ι` match
   `LocalModuleSystem.moduleColimitMap`.

All transitions, cocones, and compatibility laws are imported unchanged from
`Langlands.Algebra.LocalApproximationResidueFiber` and
`Langlands.Algebra.LocalTowerResidueFiberRings`. The definition introduces
no comparison map, witness field, or isomorphism in place of these lifts.

The hypotheses are exactly those listed. The first conjunct uses only the
base colimit. The second uses only the two given ring colimits. The third
uses only the given ring and additive module colimits. The statement adds
none of the following hypotheses:

- finite generation, finite type, or essential finite type;
- finite or essential finite presentation;
- approximation, flatness, or transition injectivity;
- prime localization, canonical base-change bijectivity, or Noetherianity.

No colimit or bijectivity property of any residue diagram is assumed.

## Provenance in Stacks 00R7 and 046Y

The registered original is `stacks-algebra-flatness-criteria-2026-10-22`,
content SHA256
`4bc1f2db6141508f6dad2132d4abc7963380cd71497ad20620c0e511b972a949`.
The relevant passages are:

- `00R7.html`, Lemma 10.128.8 (00R7), proof. With `𝔪` and `𝔭_λ` the
  maximal ideals of `R` and `R_λ`, the proof notes that
  `𝔪 = colim 𝔭_λ`. It also notes that `S/𝔪S = colim S_λ/𝔭_λS_λ` and
  `S'/𝔪S' = colim S'_λ/𝔭_λS'_λ`. Finally it notes that
  `M/𝔪M = colim M_λ/𝔭_λM_λ`. It then uses these quotient diagrams as
  approximation systems over the residue rings.
- `046Y.html`, Lemma 10.128.4 (046Y), proof. Here `M/𝔪M` is the colimit
  of `M_λ/𝔪_λM_λ`, and `κ` is the colimit of the fields `κ_λ`.
- `00QL.html`, Lemma 10.127.13 (00QX), supplies the ring and module
  colimits of the approximation systems the source constructs. The
  observations above are drawn from those colimits.

In the source, these are observations about specific systems produced by the
approximation lemmas. The present definition is broader. It applies to any
directed local system whose stated actual colimit comparisons are bijective.
Its provenance is that generalization together with general facts on directed
colimits. It is not a displayed lemma of the source.

The source uses quotients, and the Lean definitions use tensor presentations.
The source writes fibres as `S_λ/𝔭_λS_λ` and `M_λ/𝔭_λM_λ`. The published
definitions use `Sᵢ ⊗[Rᵢ] κᵢ`, with the algebra first, for the fibre ring.
They use `κᵢ ⊗[Rᵢ] Mᵢ`, with the field first, for the residue module. These
are the standard tensor presentations of the same quotients, since
`A ⊗[R] R/𝔪 ≅ A/𝔪A`. The source's observation `𝔪 = colim 𝔭_λ` enters here
only through its residue-field consequence `κ = colim κᵢ`, the form used in
046Y. The quotient presentation and the identification of these isomorphisms
with the actual lifts belong to a proof, not to this statement.

A proof might combine several facts. Directed colimits commute with
quotients and tensor products. Locality of the cocone maps identifies the
component maximal ideal with the inverse image of the target maximal ideal.
Surjectivity of the base colimit lets target maximal-ideal elements be
represented at a component. Directedness places the finitely many terms and
relations of an expression in one component. These remarks describe expected
proof obligations only. They are neither hypotheses of the definition nor
accepted results.

The 046Y and 00QX pages were rechecked on 26 October 2026. That check is
registered as `stacks-046y-00qx-current-errata-check-2026-10-26`, content
SHA256 `4ff8dc3741a78495d7fdb00f179e9c50a3c6f6de1dc2ad70166be5c7cb064342`,
and both official pages showed zero comments. On 26 October 2026 the
official 00R7 page also showed zero comments. Its proof paragraph from "Moreover, note that"
to the end agrees with the registered 22 October original. That page is
registered as `stacks-00r7-current-check-2026-10-26`, content SHA256
`0ebd31dcec075d89683e27a816dc0a77b0ec462984d789d441a843296e5fb9e9`,
files `00R7.html` and `README.md`. No
source-specific errata note was found in the current Library or project
`notes/errata/` locations. This was a bounded check, not an exhaustive errata
search.
