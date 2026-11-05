# Renard C.II: the final proposition under each candidate finiteness reading

Worker 709 prepared this statement-only unit. It states the final
proposition of Appendix C.II three times, once for each of the three
candidate meanings of Renard's finiteness phrases for a possibly nonunital
algebra that the project's source audit lists. It proves nothing, and it
does not declare any of the three readings to be the author's.

## Source

The governing original is David Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 709 reread the proposition on printed p.279 / one-based PDF285, the
conventions on printed p.6 / PDF12, and the A.I.3 definitions of
Noetherian objects and objects of finite type on printed pp.248–249 /
PDF254–255:

> Proposition. Soit B une ℂ-algèbre commutative noethérienne, et L un
> B-module de type fini. Soit a ∈ End_B(L) et supposons que le localisé
> (L_a, ã) de L en a (voir A.III.1, exemple 5) soit un B-module de type
> fini. Alors a est finalement stable. Soit n ∈ ℕ* tel que a^n soit
> stable, et soient K = ker a^n, I = Im a^n. Alors L = K ⊕ I et le localisé
> (L_a, ã) est isomorphe à (I, a|_I).

PDF12 says that rings are not assumed unital and that modules over a
unital ring are not assumed unital. Neither that page nor C.II says which
subobjects or generation operations "noethérienne" and "de type fini"
refer to for such an algebra. The published audit
`notes/renard/nonunital-finiteness-sources.md` records this gap. It names
three candidate models: all stable additive subgroups, compatible
complex-linear stable subspaces, or an explicitly compared unitization
model. This unit states the proposition for each of them.

## Common data and conclusion

The namespace is `Langlands.Renard.SourceFiniteLocalization`. The three
reading statements quantify over the same data, at independent universes
`uB` and `uV`:

- `B : Type uB` with `NonUnitalCommRing B`, `Module ℂ B`,
  `IsScalarTower ℂ B B` and `SMulCommClass ℂ B B`: a commutative,
  associative, possibly nonunital complex algebra;
- `V : Type uV` with `AddCommGroup V` and `Module ℂ V`, and an actual
  compatible action `ρ : B →ₙₐ[ℂ] Module.End ℂ V`;
- `f : LinearIntertwiner ρ ρ`, a complex-linear map commuting with every
  `ρ b`, with underlying endomorphism `a = f.toLinearMap`.

`L`, `B` and `a` are Renard's `L`, `B` and `a`. The proposition refers to
the localization of A.III.1, example 5, which is built from a complex
vector space and an endomorphism. Accordingly, `L` carries its complex
structure, the action is complex-linear, and `a` is complex-linear and
`B`-linear. The actual localization is the published
`Localized f.toLinearMap`, with the published localized action
`localizedAction f.toLinearMap ρ (fun b v => f.map_action' b v)`.
No unit, unit-action law, nondegeneracy, countability or finite complex
dimension is assumed.

`SourceConclusion ρ f` is the source's conclusion, exactly:

1. `EventuallyStable f.toLinearMap`: some positive power of `a` is
   stable, that is, has the same kernel and range as its square;
2. for every `n > 0` with `Stable (f.toLinearMap ^ n)`, the published
   `CompatibleStablePowerImageAt ρ f n`: the compatible kernel `K` and
   image `I` of the `n`-th power are complementary, and there is a unique
   complex-linear equivalence from the localization to `I` that
   intertwines the `B`-actions and the operators `ã` and `a|_I`, and whose
   inverse is the restriction of the canonical map `L → L_a`.

The second clause applies to every positive stable exponent, as in the
source. It uses the published predicates unchanged.

## The three readings

`IsNoetherianObject` and `IsFiniteTypeObject` are the published
`Langlands.Renard` formalizations of A.I.3. An object is Noetherian when
every nonempty set of its categorical subobjects has a maximal element. It
is of finite type when its subobjects have all unions and no nonempty chain
of proper subobjects has union equal to the whole object. Each of the first
two readings applies them to actual objects of an actual category of
`B`-modules. In those categories, the regular object is `B` acting on
itself by left multiplication. Since `B` is commutative, its subobjects are
the ideals of that category's kind.

1. `AdditiveReadingStatement`. The modules are those of the published
   `NonUnitalModuleCat B`: abelian groups with a possibly nonunital action
   and additive intertwiners. The published
   `NonUnitalModuleCat.subobjectOrderIso` identifies its subobjects with
   stable additive subgroups. The objects are `NonUnitalModuleCat.of` applied to `B`, `V`
   and the localization, each with the ambient action
   `NonUnitalModule.ofLinearEndHom` of `NonUnitalAlgHom.lmul ℂ B`, `ρ` or
   the localized action. The hypotheses are: the regular object is
   Noetherian, and the other two objects are of finite type.
2. `CompatibleReadingStatement`. The modules are those of the published
   `ActionModuleCat ℂ B`: complex vector spaces with a compatible action,
   and complex-linear intertwiners. The hypotheses use its actual
   categorical subobjects. The objects are `ActionModuleCat.of` applied to the
   same three actions, with the same three hypotheses.
3. `UnitizationReadingStatement`. `B` is Noetherian when the actual ring
   `Unitization ℂ B` is Noetherian (`IsNoetherianRing`). A module is of
   finite type when it is finitely generated (`Module.Finite`) over that
   ring, acting by `(c, b) • v = c • v + ρ b v` through the published
   `CompatibleUnitization.module`. The same condition is imposed on the
   localization with its localized action.

Each reading statement asserts `SourceConclusion ρ f` from its three
hypotheses. `SourceFiniteLocalizationStatements.{uB,uV}` is the conjunction
of the additive, compatible and unitization readings, in that order.

## Provenance and boundary

All three statements are derived formulations. They make Renard's
categorical definitions and his module conventions explicit in actual
Lean categories, and they replace the single unstated convention by a
separate statement for each candidate model. Proving all three would make
the proposition hold whichever of these models the author intended; it
would not identify the intended model.

The models are related by published results. The
`Langlands.Algebra.AdditiveScalarStableGeneration` comparisons show that
finite stable additive generation implies finite stable complex-linear
generation. `CompatibleUnitization.submoduleOrderIso` identifies the
stable complex subspaces with the submodules over the unitization. These
relations motivate the formulation; they are not part of these statements.

The published internal theorems
`Langlands.Renard.AlgebraActionLocalization.stableIdealFiniteLocalization`
and `additiveIdealFiniteLocalization` state the same conclusions from
explicit stable-generation hypotheses. The published
`Langlands.Algebra.NonUnitalModuleFiniteness` comparisons identify
Renard's categorical predicates with stable additive generation in
`NonUnitalModuleCat`. No corresponding categorical comparison for
`ActionModuleCat` is published; a proof of the compatible reading must
supply one. Renard's own route through the finiteness of `End_B(L_a)` and
an integral equation for `ã⁻¹` is not prescribed.

This file supplies proposition definitions only, including the Prop-valued
helper `SourceConclusion`. After independent acceptance and publication, a
separate exact-proof task can target `SourceFiniteLocalizationStatements`
in environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`.
