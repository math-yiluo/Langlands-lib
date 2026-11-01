# The annihilator of `eA` and the quotient functor `M ↦ M_e`

Worker 1111. This module constructs the annihilator `F(eA,M)` and the quotient
`M_e = M/F(eA,M)` of Renard I.3.2. It builds the quotient as an additive
endofunctor of the published category of original modules, with the quotient
projections as a natural transformation from the identity, and restricts both
to the published full subcategory of nondegenerate modules. The constructions
reuse the published stable-subgroup quotient and descent machinery. No
statement of I.3.2 beyond the definition is proved or assumed here.

## Source

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Section I.3.2, printed page 20 / PDF page 26, states:

> Définition. Soient `M` un `A`-module non dégénéré et `e ∈ Idem(A)`. On
> définit le `A`-module non dégénéré :
> `M_e := M/F(eA,M)`, où `F(eA,M) = {m ∈ M | eA·m = 0}`.

Here `A` is a complex idempotented algebra and `M` is a nondegenerate
`A`-module. The condition `eA·m = 0` says that every element `e * a` of the
right ideal `eA` kills `m`. This is not the generally unstable kernel of `e`
alone. The lemma `(M_e)_e = M_e` that follows on the same page was read but is
not part of this construction (see Scope).

## Generalization from the source

The ambient construction works over an arbitrary associative ring
`A : Type uA` with `[NonUnitalRing A]`. It may be noncommutative and need not
have a unit. It takes an actual `e : Idempotent A` and any additive group
`M : Type uM` with a specified original `NonUnitalModule A M` action. No ambient
unit law (`one_smul`), nondegeneracy, idempotented-ring hypothesis,
complex-linearity, finite-dimensionality or commutativity is used. None of the
definitions needs these hypotheses: the annihilator's closure laws use only
`smul_zero`, `smul_add`, `smul_neg`, `mul_smul` and associativity. The quotient
and its maps come from the published integer-compatible quotient
infrastructure.

Renard's construction is the restriction to nondegenerate modules.
`annihilatorQuotient_isNondegenerate` shows that the quotient of a
nondegenerate module is nondegenerate, and
`NonUnitalModuleCat.nondegenerateAnnihilatorQuotientFunctor` is the resulting
endofunctor of `NondegenerateModuleCat A`. On each object it is literally the
ambient quotient. Renard's `A`-modules carry in particular an additive group
and an `A`-action, which is the structure the published original actions
record. The definitions of `F(eA,M)` and of `M_e` in the source use only this
structure. Complex-linearity of the quotient is not stated here, and no
separate coefficient-linearity bridge is claimed.

## The annihilator `F(eA,M)`

In the namespace `NonUnitalSubmodule`:

- `idempotentAnnihilator e M : NonUnitalSubmodule A M` has carrier
  `{m | ∀ a : A, ((e : A) * a) • m = 0}`. `mem_idempotentAnnihilator` states
  this membership condition (by `Iff.rfl`).
- `zero_mem_idempotentAnnihilator`, `add_mem_idempotentAnnihilator` and
  `neg_mem_idempotentAnnihilator` give additive closure.
  `smul_mem_idempotentAnnihilator` gives stability under the original action:
  for `b : A`, `(e * a) • (b • m) = (e * (a * b)) • m` by `mul_smul` and
  associativity.
- `idempotent_smul_eq_zero_of_mem`: a vector of `F(eA,M)` is killed by `e`,
  taking `a = e` and using `e * e = e`.
- `le_idempotentAnnihilator_iff S`: for every original stable subgroup
  `S : NonUnitalSubmodule A M`, `S ≤ F(eA,M)` if and only if `e` kills every
  vector of `S`. The reverse direction applies the hypothesis to `a • m ∈ S`
  and uses `mul_smul`. So `F(eA,M)` is the largest stable subgroup killed by
  `e`.
- `coe_idempotentAnnihilator_eq_univ_iff`: `F(eA,M)` is all of `M` exactly
  when `e` acts by zero on `M`.

## The quotient `M_e`

`annihilatorQuotientCarrier e M : Type uM` is a `def` equal to
`M ⧸ (idempotentAnnihilator e M).toIntCompatible.toSubmodule`. This is the
published quotient by the canonical integer-compatible form
(`NonUnitalSubmodule.toIntCompatible`) of `F(eA,M)`. Two named instances give
its structures:

- `annihilatorQuotientAddCommGroup` is Mathlib's quotient additive group
  `Submodule.Quotient.addCommGroup` (`annihilatorQuotientAddCommGroup_eq`).
- `annihilatorQuotientModule` is the published
  `CompatibleSubmodule.quotientNonUnitalModule` of the integer-compatible
  submodule (`annihilatorQuotientModule_eq`). It is the quotient action of the
  given original action.

The carrier is a separate `def`, not a reducible alias of the quotient type.
Instance search therefore does not unfold it to Mathlib's quotient type and
does not find Mathlib's quotient instances on it. Its additive group and its
`A`-action come from the two named instances. The final checks in the Lean
file test this for the competing actions that remain. The `NonUnitalModule` instance
found on the carrier is exactly `quotientNonUnitalModule`, by `rfl`. For
`A = ℤ`, the `SMul ℤ` instance found on the carrier is the selected quotient
action, not the canonical integer action of the additive group, by `rfl`.
Also for `A = ℤ` with the zero original action selected by `letI`, the
projection of `(2 : ℤ) • m` is `0` by `rfl`. So the scalar is the selected
zero action and not the canonical `2 • m = m + m`, whose projection would be
zero only by a quotient argument.

`annihilatorQuotientProjection e M : NonUnitalModuleHom A M (annihilatorQuotientCarrier e M)`
is the published `mkQNonUnitalModuleHom`. Its laws:

- `annihilatorQuotientProjection_apply`: the projection of `m` is
  `Submodule.Quotient.mk m`.
- `annihilatorQuotientProjection_toAddMonoidHom`: its underlying additive map
  is the underlying additive map of Mathlib's `mkQ`.
- `annihilatorQuotient_smul_projection` and `smul_annihilatorQuotientProjection`:
  `a` acting on the projection of `m` is the projection of `a • m`. The first
  is stated with the named structure `annihilatorQuotientModule` explicitly.
- `annihilatorQuotientProjection_surjective`.
- `annihilatorQuotientProjection_eq_zero_iff`: the projection of `m` is zero
  if and only if `m ∈ idempotentAnnihilator e M` (Mathlib's
  `Submodule.Quotient.mk_eq_zero`).
- `kernelSubmodule_annihilatorQuotientProjection`: the published
  `kernelSubmodule` of the projection equals `F(eA,M)`.
- `annihilatorQuotient_hom_ext`: two original intertwiners out of `M_e` that
  agree after composing with the projection are equal, by surjectivity.
- `annihilatorQuotient_subsingleton_iff`: `M_e` is trivial if and only if `e`
  acts by zero on `M`.
- `annihilatorQuotient_isNondegenerate`: if `M` is nondegenerate, so is `M_e`.
  Lift a quotient vector to a representative `m`, take `f : Idempotent A` with
  `f • m = m`, and project. No idempotented-ring assumption is needed.

## Induced maps

In the namespace `NonUnitalModuleHom`, with
`f : NonUnitalModuleHom A M N` for `M : Type uM` and `N : Type uN` in
independent universes:

- `map_mem_idempotentAnnihilator`: `f` maps `F(eA,M)` into `F(eA,N)`, since
  `(e * a) • f m = f ((e * a) • m) = 0`.
- `idempotentAnnihilator_le_comap`: the same inclusion of integer-compatible
  submodules, in the form required by the published `LinearIntertwiner.mapQ`.
- `annihilatorQuotientMap e f` is the published `LinearIntertwiner.mapQ` of
  `f.toIntLinearIntertwiner`, converted back by `toNonUnitalModuleHom`. The
  conversion forgets only integer linearity and keeps the original actions on
  source and target.
- `annihilatorQuotientMap_apply_projection`: the induced map sends the
  projection of `m` to the projection of `f m`.
  `annihilatorQuotientMap_toAddMonoidHom`: the underlying additive map is
  Mathlib's `Submodule.mapQ` of `f.toAddMonoidHom.toIntLinearMap`.
- `annihilatorQuotientMap_comp_projection`: naturality of the whole
  projections, `(annihilatorQuotientMap e f).comp (annihilatorQuotientProjection e M) = (annihilatorQuotientProjection e N).comp f`.
- `annihilatorQuotientMap_id`, `annihilatorQuotientMap_comp`,
  `annihilatorQuotientMap_zero`, `annihilatorQuotientMap_add` and
  `annihilatorQuotientMap_neg` give functoriality and additivity, each by
  `annihilatorQuotient_hom_ext`.

## Descent (universal property)

For `g : NonUnitalModuleHom A M P` with `P : Type uP` and
`h : idempotentAnnihilator e M ≤ g.kernelSubmodule`:

- `annihilatorQuotientDesc e g h : NonUnitalModuleHom A (annihilatorQuotientCarrier e M) P`
  is the published `LinearIntertwiner.liftQ` of `g.toIntLinearIntertwiner`,
  converted back by `toNonUnitalModuleHom`.
- `annihilatorQuotientDesc_apply_projection`: it sends the projection of `m`
  to `g m`. `annihilatorQuotientDesc_toAddMonoidHom`: its underlying additive
  map is Mathlib's `Submodule.liftQ`.
- `annihilatorQuotientDesc_comp_projection`: the factorization
  `(annihilatorQuotientDesc e g h).comp (annihilatorQuotientProjection e M) = g`.
- `annihilatorQuotientDesc_unique`: any `l` with
  `l.comp (annihilatorQuotientProjection e M) = g` equals the descent.
- `idempotentAnnihilator_le_kernelSubmodule_comp`: conversely, every map
  `l` out of `M_e` composed with the projection kills `F(eA,M)`, so the
  hypothesis `h` is necessary.

## The functors

In the namespace `NonUnitalModuleCat`:

- `annihilatorQuotientFunctor e : NonUnitalModuleCat.{uA, uM} A ⥤ NonUnitalModuleCat.{uA, uM} A`
  has objects `of A (annihilatorQuotientCarrier e M)` and maps
  `annihilatorQuotientMap e f`
  (`annihilatorQuotientFunctor_obj`, `annihilatorQuotientFunctor_obj_carrier`,
  `annihilatorQuotientFunctor_map`). The instance
  `annihilatorQuotientFunctor_additive` gives additivity for the published
  pointwise Hom groups, from `annihilatorQuotientMap_add`.
- `annihilatorQuotientπ e : 𝟭 _ ⟶ annihilatorQuotientFunctor e` has
  components `annihilatorQuotientProjection e M` (`annihilatorQuotientπ_app`).
  Its naturality is `annihilatorQuotientMap_comp_projection`.
- `nondegenerateAnnihilatorQuotientFunctor e : NondegenerateModuleCat.{uA, uM} A ⥤ NondegenerateModuleCat.{uA, uM} A`
  is Mathlib's `ObjectProperty.lift` of
  `nondegenerateInclusion A ⋙ annihilatorQuotientFunctor e`, using
  `annihilatorQuotient_isNondegenerate`. Its relation to the ambient functor:
  `nondegenerateAnnihilatorQuotientFunctor_comp_inclusion` proves the equality
  of functors
  `nondegenerateAnnihilatorQuotientFunctor e ⋙ nondegenerateInclusion A = nondegenerateInclusion A ⋙ annihilatorQuotientFunctor e`
  by `rfl`, and `nondegenerateAnnihilatorQuotientFunctorCompInclusionIso` is
  Mathlib's canonical isomorphism `liftCompιIso`. The object and map formulas
  are `nondegenerateAnnihilatorQuotientFunctor_obj_obj` and
  `nondegenerateAnnihilatorQuotientFunctor_map_hom`.
- The instance `nondegenerateAnnihilatorQuotientFunctor_additive` is Mathlib's
  additivity instance for lifts of additive functors through full
  subcategories (`Functor.instAdditiveFullSubcategoryLift`). It is applied
  explicitly because instance search does not unify its `ObjectProperty.lift`
  pattern with the unfolded definition. The full subcategory carries its
  inherited preadditive structure.
- `nondegenerateAnnihilatorQuotientπ e` is the natural quotient projection on
  nondegenerate modules. Its components are `ObjectProperty.homMk` of the
  ambient projections (`nondegenerateAnnihilatorQuotientπ_app_hom`).

## Zero cases

The zero idempotent appears as a hypothesis `(e : A) = 0`, because
`Idempotent A` has no `Zero` instance.

- Zero idempotent: `coe_idempotentAnnihilator_eq_univ_of_val_eq_zero` (the
  annihilator is all of `M`) and
  `annihilatorQuotient_subsingleton_of_val_eq_zero` (the quotient is trivial).
  Both use `NonUnitalModule.zero_smul`.
- Zero original action `NonUnitalModule.zero`:
  `coe_idempotentAnnihilator_zero_action` and
  `annihilatorQuotient_subsingleton_zero_action`.
- Zero carrier: `coe_idempotentAnnihilator_eq_univ_of_subsingleton` and the
  instance `annihilatorQuotient_subsingleton` for `[Subsingleton M]`.

## Universe and action checks

The final `example`s state the complete unapplied types of
`idempotentAnnihilator`, `annihilatorQuotientModule`,
`annihilatorQuotientProjection`, `annihilatorQuotientMap` (with distinct
source and target universes `uM`, `uN`), `annihilatorQuotientDesc` (with
`uM`, `uP`), both functors and both additivity instances, all with the ring
universe `uA` independent. They also check concrete universe
instantiations: `annihilatorQuotientMap.{0, 1, 2}`,
`annihilatorQuotientDesc.{1, 0, 2}`,
`annihilatorQuotientFunctor_additive.{0, 1}` and
`nondegenerateAnnihilatorQuotientFunctor.{1, 0}`. The action checks are
described under "The quotient `M_e`" above.

## Reuse

- `Langlands.Algebra.NonUnitalModule` (accepted base candidate
  `e1b5cfdd-e161-4f49-9807-6db2d68e2a05` for the original additive module
  constructions): `NonUnitalModule`,
  `NonUnitalModuleHom`, `NonUnitalSubmodule`, `NonUnitalModule.zero`,
  `IsNondegenerate`, `NonUnitalModuleCat`, `nondegenerateProperty`,
  `NondegenerateModuleCat`, `nondegenerateInclusion`.
- `Langlands.Algebra.IdempotentedRing`: `Idempotent`.
- `Langlands.Algebra.IntegerNonUnitalSubmodule` (accepted candidate
  `be182b75-5913-4e3c-b1b8-047b7d50d65d`): `NonUnitalSubmodule.toIntCompatible`.
- `Langlands.Algebra.IntegerCompatibleNonUnitalAction`:
  `NonUnitalModuleHom.toIntLinearIntertwiner`.
- `Langlands.Algebra.CompatibleSubmodule`:
  `CompatibleSubmodule.quotientNonUnitalModule`, `mkQNonUnitalModuleHom`,
  `CompatibleSubmodule.comap`, `LinearIntertwiner.mapQ`,
  `LinearIntertwiner.liftQ`.
- `Langlands.Algebra.CompatibleNonUnitalAction`:
  `LinearIntertwiner.toNonUnitalModuleHom`.
- `Langlands.Algebra.NonUnitalModuleKernels`:
  `NonUnitalModuleHom.kernelSubmodule`.
- `Langlands.Algebra.NonUnitalModuleAdditive` and
  `Langlands.Algebra.NondegenerateModuleAdditive`: the pointwise Hom groups,
  the preadditive structure and the additivity of `nondegenerateInclusion`.
- Mathlib: `Submodule.Quotient.mk`, `mk_surjective`, `mk_eq_zero`, `mapQ`,
  `liftQ`, `ObjectProperty.lift`, `liftCompιIso`, `homMk`, `hom_ext`,
  `Preadditive.fullSubcategory` and
  `Functor.instAdditiveFullSubcategoryLift`.

The published `NondegenerateModuleClosureProof` is not used. The concrete
nondegeneracy proof lifts a representative directly and needs no
idempotented-ring assumption.

## Scope

This is a construction unit. The following parts of Renard I.3.2 and its
sequel on printed pages 20–22 are not stated or proved here, and none of them
is an assumption of this definition family. They remain separate statement
and proof successors over these constructions:

- the lemma `(M_e)_e = M_e`;
- the isomorphism induced by the quotient on `e`-fixed parts;
- tensor induction `Z ↦ A ⊗_{eAe} Z` and the isomorphism (I.3.2.1);
- generated subcategories `M(A,e)`;
- the bijection of simple classes;
- the equivalence criterion.

The `e`-fixed corner module of I.3.1 is a separate task and is not
constructed here. No completion of I.3.2 or of the book is claimed.

Integration placement: this reviewed implementation is preserved in the NamedCarrier submodule; the parent `Langlands.Algebra.IdempotentAnnihilatorQuotient` imports both reviewed interfaces.
