# Compatible rigidifications along two axes

This internal construction equips two ordinary axis trivializations of the
same actual module sheaf with compatibility at their common base. It supplies
the compatibility step needed before the correspondence comparison in
Raynaud's argument. It does not construct a correspondence space or extend
a bundle over a valuation ring.

## Data and source convention

For schemes `S`, `X`, `Y`, `Z`, maps `e : S → X`, `t : S → Y`,
`i : X → Z`, `j : Y → Z`, and an equality `h : e ≫ i = t ≫ j`,
`TwoAxisRigidification e t i j h M` contains actual isomorphisms
`α : O_X ≅ i* M` and `β : O_Y ≅ j* M`. Their restrictions agree as
isomorphisms from `O_S` to `(t ≫ j)* M`.

The helper `axisRestrictionIso` makes each restriction explicit: first use
the inverse of `pullbackUnitIso` to identify `O_S` with the pullback of
the axis structure sheaf, then pull back the axis trivialization, then use
`Scheme.Modules.pullbackComp`. On the first axis the compatibility equation
also uses `Scheme.Modules.pullbackCongr h` to identify the two composite maps.
Thus the condition concerns actual module sheaves and actual isomorphisms.

For a product `Z = X ×_S Y` with sections, these are precisely the
compatible rigidifications of Raynaud, *Faisceaux amples sur les schémas en
groupes et les espaces homogènes*, LNM 119, second corrected printing
(1986), Definition III 2.2(2), printed pp.39–40, PDF pp.43–44.
Registered source:
`provided-5d5546c6572c2556d06cb8181d9d78944bca00a4138a3ab39df0a5810f0fd485`,
SHA256 `29bce9a9be67396fd1bd8f0396e57d5ff08325eed53819e240eb14155711f38d`.
Both rendered pages were read. No Raynaud-specific errata note was found
in the checked workspace, project notes and Library notes; this is a bounded
check, not a claim that no errata exist.

The more general commuting diagram is an internal generalization of that
source definition. The construction below is derived from the published
categorical `RigidificationAdjustment` interface.

## Construction and implemented compatibility proof

`TwoAxisRigidification.ofTrivializations` takes any chosen `α` and `β`,
along with a map `g : Y → S` satisfying `t ≫ g = id_S`.
It retains `α` exactly and replaces `β` by a compatible isomorphism.
No structure map or section law on `X` is required.

The proof sets `F = t*` and `G = g*`. The section equation and the
published pullback composition, congruence and identity comparisons give
`G ⋙ F ≅ id`. The given second trivialization identifies `j* M` with
`G(O_S)`. Pulling the first trivialization to the common base and
transporting along `h` prescribes an isomorphism
`δ : O_S ≅ t*(j* M)`.

`RigidificationAdjustment.adjustIso` then corrects `β` so that its
pullback, preceded by the inverse structure-sheaf comparison, equals `δ`.
The constructor's compatibility field follows from
`adjustIso_compatible`, composed with the pullback composition comparison
for `t ≫ j`; inverse comparisons cancel. The lemma
`ofTrivializations_first` records that the chosen first trivialization is
unchanged.

The construction works for any module sheaf for which these two
trivializations are given. It requires no field, valuation, smoothness,
properness, connectedness, scalar-automorphism classification, tensor
inverse, Picard quotient or representability theorem.

## Exact abelian-scheme axes

For `A : AbelianScheme S`, `twoAxisSecond A` abbreviates precisely

```text
pullback.lift (A.X.hom ≫ unitSection A) (id A.X.left) ...
```

The first axis is the published `mumfordSection A`.
`twoAxis_unit_comp` proves their restrictions along `unitSection A`
agree, by the two projections of the actual pullback and the unit section
law.

`twoAxisRigidificationOfTrivializations` accepts an actual line bundle
`D` on `(mumfordProduct A).left` and trivializations in the orientation
of `ValuationRingTwoAxisExtensionStatement`. It inverts them and applies
the general construction with retraction `A.X.hom`.
`nonempty_twoAxisRigidification` eliminates the two `Nonempty`
hypotheses and returns compatible rigidification data on the same `D.obj`.
It therefore applies to the actual generic base change in that target,
over any chosen fraction field, without changing its bundle or its axes.

This establishes only compatible rigidification data. Raynaud III 2.3(2),
correspondence representability and XI 1.5, including arbitrary valuation
bases and the eventual actual restriction isomorphism along the target's
canonical product map, remain separate obligations.
