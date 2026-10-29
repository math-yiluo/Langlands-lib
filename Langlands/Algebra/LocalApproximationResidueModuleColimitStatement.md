# Preservation of the actual residue-module colimit

`Langlands.Algebra.LocalApproximationResidueModuleColimitStatement` is a
Prop-valued definition. Suppose a module system over a directed local algebra
system has the given ring and module colimits. The definition states that the
residue modules of the system then also pass to the colimit, along the actual
published maps. This module states that assertion only and supplies no proof
of it.

It is an internal projection of the published
`Langlands.Algebra.LocalApproximationResidueColimitStatement`. It is exactly
that statement's third conjunct, the residue-module conjunct, universally
quantified over the common inputs that the published statement binds before
its three conjuncts. Its Lean body copies that conjunct's hypothesis,
`letI := Classical.decEq ι`, let-bound lift and conclusion unchanged. It omits
the residue-field and fibre-ring conjuncts. This split gives the
residue-module conjunct its own proof target. The broader statement, its pair
and its imports are unchanged.

## Quantifiers and universes

The definition has seven independent universe parameters,
`uI uA uB uN uR uS uM`, and no universe equalities. It quantifies over:

- `ι : Type uI` with `[Preorder ι] [Nonempty ι] [IsDirectedOrder ι]`;
- commutative local rings `R : Type uR` and `S : Type uS`, with
  `[Algebra R S] [IsLocalHom (algebraMap R S)]`;
- `D : LocalAlgebraSystem.{uI,uA,uB,uR,uS} ι R S`, whose base rings
  `D.base i : Type uA` and algebras `D.alg i : Type uB` are local;
- `M : Type uM` with
  `[AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]`;
- `E : LocalModuleSystem.{uI,uA,uB,uN,uR,uS,uM} D M`, whose components
  `E.obj i` inhabit `Type uN`.

The first three items are the common inputs of the broader statement. The
last two are the inputs its third conjunct quantifies over. The target keeps
the caller's given compatible `R`-action on `M`. The direct-limit and tensor
carriers live in the appropriate maxima of these universes.

Write `Rᵢ = D.base i`, `Mᵢ = E.obj i`,
`κᵢ = IsLocalRing.ResidueField Rᵢ`, and `κ = IsLocalRing.ResidueField R`.
The component `Rᵢ`-action on `Mᵢ` is the published restriction along
`algebraMap Rᵢ (D.alg i)`, opened by
`open scoped Langlands.Algebra.LocalModuleSystem`. No other scoped instance
is opened.

## The statement

The only hypothesis is `E.IsColimit`. It is `D.IsColimit`, which is
bijectivity of both `D.baseColimitMap` and `D.algebraColimitMap`, together
with bijectivity of `E.moduleColimitMap`.

The diagram is `E.ResidueFiber i = κᵢ ⊗[Rᵢ] Mᵢ`. Its additive transitions are
`(E.residueFiberMap h).toAddMonoidHom`, which send
`a ⊗ m ↦ D.residueMap h a ⊗ E.map i j h m`. The target is
`LocalModuleSystem.TargetResidueFiber R M = κ ⊗[R] M`. The cocone is
`(E.residueFiberι i).toAddMonoidHom`, which sends
`a ⊗ m ↦ D.residueι i a ⊗ E.ιM i m`. Its compatibility law is
`E.residueFiberι_compat`.

After `letI := Classical.decEq ι`, the lift is let-bound inside the
proposition with its full type:

```
AddCommGroup.DirectLimit.lift E.ResidueFiber
  (fun _ _ h ↦ (E.residueFiberMap h).toAddMonoidHom)
  (LocalModuleSystem.TargetResidueFiber R M)
  (fun i ↦ (E.residueFiberι i).toAddMonoidHom)
  (fun _ _ h x ↦ E.residueFiberι_compat h x)
```

The conclusion is that this additive map is bijective. The additive direct
limit and the explicit `Classical.decEq ι` match
`LocalModuleSystem.moduleColimitMap` and the broader statement.

All transitions, cocones and compatibility laws are imported unchanged from
`Langlands.Algebra.LocalApproximationResidueFiber`. The definition introduces
no comparison map, witness field or isomorphism in place of this lift.

The statement adds none of the following hypotheses:

- finite generation, finite type, or essential finite type;
- finite or essential finite presentation;
- approximation, flatness, or transition injectivity;
- prime localization, canonical base-change bijectivity, or Noetherianity.

No colimit or bijectivity property of any residue diagram is assumed. In
particular, the residue-field colimit is not a hypothesis.

## Provenance

The source scope is that of the broader statement, restricted to modules. The
registered original is `stacks-algebra-flatness-criteria-2026-10-22`, content
SHA256
`4bc1f2db6141508f6dad2132d4abc7963380cd71497ad20620c0e511b972a949`.
The relevant passages are:

- `00R7.html`, Lemma 10.128.8 (00R7), proof. With `𝔪` and `𝔭_λ` the
  maximal ideals of `R` and `R_λ`, the proof notes, among other colimits,
  that `M/𝔪M = colim M_λ/𝔭_λM_λ`.
- `046Y.html`, Lemma 10.128.4 (046Y), proof. Here `M/𝔪M` is the colimit of
  `M_λ/𝔪_λM_λ`.
- `00QL.html`, Lemma 10.127.13 (00QX), supplies the ring and module colimits
  of the approximation systems the source constructs. The observations above
  are drawn from those colimits.

In the source, these are observations about specific systems produced by the
approximation lemmas. The present definition is broader. It applies to any
directed local module system whose given ring and module colimit comparisons
are bijective. Its provenance is that generalization together with general
facts on directed colimits. It is not a displayed lemma of the source.

The source uses quotients, and the Lean definitions use tensor presentations.
The source writes the residue module of a component as `M_λ/𝔭_λM_λ`. The
published definitions use `κᵢ ⊗[Rᵢ] Mᵢ`, with the field first. This is the
standard tensor presentation of the same quotient, since
`R/𝔪 ⊗[R] N ≅ N/𝔪N`. The quotient presentation and the identification of
these isomorphisms with the actual lift belong to a proof, not to this
statement.

The broader statement's Markdown records the errata checks. The 046Y and 00QX
pages were rechecked on 26 October 2026, registered as
`stacks-046y-00qx-current-errata-check-2026-10-26`, content SHA256
`4ff8dc3741a78495d7fdb00f179e9c50a3c6f6de1dc2ad70166be5c7cb064342`. The 00R7
page was rechecked the same day, registered as
`stacks-00r7-current-check-2026-10-26`, content SHA256
`0ebd31dcec075d89683e27a816dc0a77b0ec462984d789d441a843296e5fb9e9`. Those
checks found no comments on the official pages. This was a bounded check, not
an exhaustive errata search.
