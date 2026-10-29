# Compatible algebra actions on actual endomorphism localization

Authors: Worker 709 and Worker 926, for task
`9c7386f8-303b-46a6-8f0b-06ae387874bf`, revision 1. Worker 709 read the
passages below and implemented the construction, its fraction and
canonical-map laws, the intertwiners, the adapters, the zero laws and the field
constructor. Worker 926 independently reread the same source passages and
errata pages and checked both PDF hashes. Worker 926 added the uniqueness laws
`extendEnd_unique` and `localizedAction_unique`, the conditional unit law
`localizedAction_one`, and `fieldLocalizedAction_eq` and
`fieldLocalizedAction_iota`. Worker 926 also ran the declaration inspections.

The module `Langlands/Algebra/RenardAlgebraActionLocalization.lean` constructs
an actual compatible nonunital algebra action on the existing carrier
`Langlands.Renard.EndomorphismLocalization.Localized a`. Its declarations are in
`Langlands.Renard.AlgebraActionLocalization`. The construction extends each
commuting action endomorphism using the published scalar-linear localization
factor. It proves the homomorphism laws, formulas on fractions, compatibility
of the actual canonical map, localized operator and inverse, and uniqueness of
the extension.

## Original source and derived content

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated **9 July 2026**, Appendix A.III.1, example 5,
printed p. 252 / PDF p. 258. Registered source:
`renard-2026-representations-groupes-reductifs-padiques`; file:
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`;
SHA256:
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Printed body page = PDF page minus 6.

Workers 709 and 926 read example 5, including its final sentence, and the global
conventions on printed pp. 5–6 / PDF pp. 11–12. The final sentence reads: « Si B
est une k-algèbre, on peut faire la même construction en remplaçant les
k-espaces vectoriels par des B-modules, et les endomorphismes d'espaces
vectoriels par des endomorphismes de B-modules. » It extends the
localization construction from vector spaces with endomorphisms to modules over
a k-algebra B with B-module endomorphisms. It adds no commutativity or unit
hypothesis on B. The global conventions allow nonunital rings and actions; even
for a unital ring, its module need not have the unit acting as identity.

The registered supplementary source `renard-2010-corrections-complements`,
SHA256 `fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
was checked on PDF pp. 17–19. Those pages contain no correction to this
localization example. Its PDF p. 15 entry for 2010-edition "p. 225, l. -1"
only makes a reference elsewhere in the body point to A.III.1 example 5; it does
not change the example. This is a limited check of the older edition's errata;
the 2026 original governs. The public passage audits
`notes/renard/appendix-a-corrections.md` and `notes/renard/stable-quotients.md`
were also read. In particular, the scalar-linear localization imported here
uses invertibility of endomorphisms rather than the stronger scalar-inverse
parenthesis in example 4.

The actual homomorphism interface, extension to coefficient rings, fraction
formulas, bundled linear intertwiners and named ambient-action adapters are
**derived implementation content** realizing the construction part of the final
sentence. These encodings and proofs are not quoted from the book. The book's
extension also includes a B-linear universal property; that remains a separate
statement and proof obligation.

## Inputs, universes and algebra hypotheses

The general construction has independent universes:

```text
k : Type u, B : Type v, V : Type w
[CommRing k] [NonUnitalRing B] [Module k B]
[AddCommGroup V] [Module k V]
a : Module.End k V
ρ : B →ₙₐ[k] Module.End k V
ha : ∀ b z, a (ρ b z) = ρ b (a z)
```

Thus each action map is k-linear and commutes with a. The actual carrier
`Localized a` is the imported localized polynomial evaluation module, in
`Type (max u w)`. It is reused without a new carrier, quotient or assumed action.
The homomorphism ρ is an input on V; its extension on `Localized a` is constructed.

These are weaker hypotheses than the complete k-algebra interface: Mathlib can
form `NonUnitalAlgHom` without requiring multiplication on B to be k-bilinear.
The general helpers do not use that bilinearity and do not derive it from ρ.
The explicit source specialization `fieldLocalizedAction` retains

```text
[Field k] [NonUnitalRing B] [Module k B]
[IsScalarTower k B B] [SMulCommClass k B B]
[AddCommGroup V] [Module k V]
```

Here the two compatibility classes on B express bilinearity of its
multiplication. `fieldLocalizedAction` is the general constructor specialized to
this full interface; `fieldLocalizedAction_frac` and
`fieldLocalizedAction_iota` give its fraction and canonical-map formulas.
`fieldLocalizedAction_eq` states, by `rfl`, that it equals
`localizedAction a ρ ha`. Rewriting with it transfers the commutation,
uniqueness, intertwiner, adapter and zero laws to the field constructor.
These declarations retain all these assumptions and the independent u, v and w.
The generalization from fields to commutative rings is internal content.

No declaration assumes commutativity on B, nondegeneracy for ρ, nontriviality
of V, finite dimension, finite generation or noetherianity. Only the conditional
unit law `localizedAction_one` assumes a unit on B and a unit law for ρ. The original a may be noninjective, zero or nilpotent.

## Extending a commuting linear endomorphism

For `f : Module.End k V` and `hf : ∀ z, f (a z) = a (f z)`,
`extendEnd a f hf : Module.End k (Localized a)` is the published
`EndomorphismLocalization.factor` with target operator `localizedEnd a`,
its proved unit certificate `isUnit_localizedEnd a`, and input map
`(iota a).comp f`. The required intertwining follows from hf and
`iota_intertwines`.

The helper laws are:

- `extendEnd_localizedEnd`: the extension commutes with `localizedEnd a`,
  directly from `factor_intertwines`.
- `extendEnd_comp_iota`: its composite with `iota a` is `(iota a).comp f`,
  by `factor_comp_iota`.
- `extendEnd_iota`: the evaluated equation
  `extendEnd a f hf (iota a z) = iota a (f z)`.
- `extendEnd_frac`: the numerator formula
  `extendEnd a f hf (frac a z n) = frac a (f z) n`.
  The proof applies the injective power `(localizedEnd a ^ n)` to both sides.
  The imported `pow_apply_frac`, the canonical-map equation and
  `localizedEnd_pow_frac` identify their images. Injectivity follows from the
  imported actual automorphism `localizedEquiv a`.
- `extendEnd_localizedInv`: the extension also commutes with `localizedInv a`.
  The proof applies injectivity of `localizedEnd a`, commutes it past the
  extension, and uses `localizedEnd_localizedInv`.
- `extendEnd_unique`: any `g : Module.End k (Localized a)` that commutes with
  `localizedEnd a` and satisfies `g.comp (iota a) = (iota a).comp f` equals
  `extendEnd a f hf`. This is the imported `factor_unique` with target operator
  `localizedEnd a`.

The private helper `frac_zero_numerator` proves `frac a 0 n = 0` using
`frac_eq_localizedInv_pow` and the zero laws for linear maps.

## The localized action and its intrinsic laws

`localizedAction a ρ ha : B →ₙₐ[k] Module.End k (Localized a)` sends b to
`extendEnd a (ρ b) (fun z => (ha b z).symm)`. Its zero, addition,
multiplication and k-scalar laws are proved by extensionality: write each
localized element as a fraction using the imported `frac_surjective`, apply
`extendEnd_frac`, and use the corresponding law of ρ. The addition and scalar
cases also use `frac_add` and `frac_smul`. This constructs the actual
homomorphism; no localized-action law is a hypothesis.

| Declaration | Equation |
| --- | --- |
| `localizedAction_frac` | `localizedAction a ρ ha b (frac a z n) = frac a (ρ b z) n` |
| `localizedAction_iota` | `localizedAction a ρ ha b (iota a z) = iota a (ρ b z)` |
| `localizedAction_localizedEnd` | The action of b commutes with `localizedEnd a`. |
| `localizedAction_localizedInv` | The action of b commutes with `localizedInv a`. |

Each follows from the corresponding `extendEnd` law. In source notation the
fraction formula is `b · (z / Xⁿ) = (b · z) / Xⁿ`.

`localizedAction_unique` characterizes the construction. Let
`σ : B →ₙₐ[k] Module.End k (Localized a)` be any homomorphism such that each
`σ b` commutes with `localizedEnd a` and `σ b (iota a z) = iota a (ρ b z)`.
Then `σ = localizedAction a ρ ha`. The proof applies `extendEnd_unique` to each
`σ b`, using `NonUnitalAlgHom.ext`. This is a uniqueness statement for the
scalar-linear extension of each action map. It is not the B-linear universal
property for arbitrary targets.

The following are actual objects of the imported
`Langlands.Algebra.LinearIntertwiner` type:

- `iotaIntertwiner a ρ ha` goes from ρ to `localizedAction a ρ ha`;
  its underlying k-linear map is `iota a`.
- `localizedEndIntertwiner a ρ ha` is an endomorphism of the localized action,
  with underlying map `localizedEnd a`.
- `localizedInvIntertwiner a ρ ha` is an endomorphism of the same action,
  with underlying map `localizedInv a`.

Their action equations use the three laws above, with the orientation required
by `LinearIntertwiner`. The three simp lemmas
`iotaIntertwiner_toLinearMap`, `localizedEndIntertwiner_toLinearMap` and
`localizedInvIntertwiner_toLinearMap` identify the underlying maps by `rfl`.
The inverse identities for the last two maps remain the imported
`localizedEnd_localizedInv` and `localizedInv_localizedEnd`.

## Named ambient-action adapters and instance selection

`localizedModule a ρ ha : NonUnitalModule B (Localized a)` is a named
abbreviation for
`NonUnitalModule.ofLinearEndHom (localizedAction a ρ ha)`.
It is not a global instance. Under `letI := localizedModule a ρ ha`,
`localizedModule_smul` identifies `b • z` with `localizedAction a ρ ha b z`
by `rfl`. The named proofs `localizedModule_isScalarTower` and
`localizedModule_smulCommClass` supply respectively
`IsScalarTower k B (Localized a)` and `SMulCommClass k B (Localized a)` for
that chosen action. They specialize the corresponding imported
`ofLinearEndHom` adapters.

Downstream code must select this ambient action locally when using it.
The imported `NonUnitalModule.actionSMul` instance has priority 1200, so a
chosen local B-action controls `b • z` even if another scalar action on those
carrier types exists. In particular, when k and B are instantiated as the same
type, newly written `c • z` under that local action can select the B-action
rather than the k-module scalar action. New statements in that setting should
specify the intended k-scalar action explicitly. The generic statements here
were elaborated with distinct variables k and B, so specializing them preserves
their already selected scalar actions.

Likewise, avoid installing two different actions on definitionally equal
carrier types simultaneously. Keep the homomorphisms and bundled
`LinearIntertwiner` objects explicit, or scope each ambient action separately.
Specializing a statement elaborated with independent carrier variables does
not rerun instance search. No competing global B-action, scalar-tower or
commuting-action instance is introduced by this module.

## Zero actions, reuse and remaining obligations

`localizedAction_zero` states that localization of the zero compatible
homomorphism is the zero homomorphism. Its commutation hypothesis is proved
from zero laws; the proof evaluates on fractions and applies
`frac_zero_numerator`. `localizedModule_zero` then identifies the ambient
action with the published `NonUnitalModule.zero`, using
`NonUnitalModule.ofLinearEndHom_zero`. These results retain arbitrary source
spaces and operators, including zero actions on nonzero spaces.

`localizedAction_one` is a conditional unit law and an intrinsic
specialization. It assumes `[Ring B]` and `h1 : ρ 1 = 1`, and concludes
`localizedAction a ρ ha 1 = 1`. The proof evaluates on fractions with
`localizedAction_frac` and h1. It keeps `[CommRing k]` and the independent
universes. Neither the main constructor nor any other declaration has the unit
or unit-law hypothesis.

The module imports the current published
`Langlands.Algebra.CompatibleNonUnitalAction` and
`Langlands.Algebra.RenardEndomorphismLocalization`, implemented by Worker 751
with the attribution recorded in their paired Markdown. It reuses their
declarations by Lean name and copies no implementation bodies. In particular
it relies on the existing actual `Localized`, `frac`, `iota`, `localizedEnd`,
`localizedInv`, `localizedEquiv` and scalar-linear `factor` APIs, and on
`NonUnitalModule.ofLinearEndHom` and `LinearIntertwiner`. No new axioms are
introduced. In environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` the module
compiled with no errors or warnings. Declaration inspections of
`localizedAction`, `localizedAction_unique`, `iotaIntertwiner`,
`localizedModule_isScalarTower`, `localizedAction_zero`, `localizedAction_one`,
`fieldLocalizedAction` and `fieldLocalizedAction_frac` reported only `propext`,
`Classical.choice` and `Quot.sound`.

The B-linear universal property remains to be stated and proved over this
actual action, with an independent target universe and actual compatible
target actions and linear intertwiners. In particular this module does not
assume or prove B-linearity of the scalar-linear universal factor for arbitrary
targets. Kernel and quotient descriptions, the inverse-iterate converse,
the surjective-canonical-map corollary, categorical packaging, localization
exactness and the finite-localization proposition of C.II remain separate
obligations. This construction does not close the whole final sentence of
example 5 or any whole-book coverage claim.
