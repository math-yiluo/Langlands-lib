# Bilinear covariance spaces over two ambient monoids

This module is an internal algebraic construction. It generalizes the existing
single-group covariance space `Langlands.InvariantBilinear.forms` to two
representations with different ambient monoids. The existing module is
imported and left unchanged.

## Data and conventions

Fix a field `k`, monoids `G` and `H`, and a type `I` of tests. A test acts through
the maps `a : I → G` and `b : I → H` and has weight `χ : I → k`. The
representations are `ρ : Representation k G V` and `σ : Representation k H W`.
The maps `a`, `b` and `χ` are arbitrary functions, not homomorphisms. `I` has no
algebraic structure and may be empty. The universes of the field, both monoids,
the tests and all carriers are independent level parameters.

All declarations take their arguments in the order `a b χ ρ σ`, with the test
data first. This differs from `InvariantBilinear.forms ρ σ χ`, which has only one
monoid and tests every element of it.

## The covariance space

`IsCovariant a b χ ρ σ B` is the Prop-valued predicate on a bilinear form
`B : V →ₗ[k] W →ₗ[k] k`:

```text
∀ i v w, B (ρ (a i) v) (σ (b i) w) = χ i * B v w.
```

`IsCovariant.zero`, `IsCovariant.add` and `IsCovariant.smul` prove closure under
zero, addition and scalar multiplication. `forms a b χ ρ σ` is the resulting
actual submodule of `V →ₗ[k] W →ₗ[k] k`. Membership is exactly the displayed law,
by `mem_forms`, and exactly `IsCovariant`, by `mem_forms_iff_isCovariant`. Both
hold by `Iff.rfl`. `length a b χ ρ σ : ℕ∞` is `Module.length k` of this
submodule. No finite-dimensionality or finite-length assumption is made.

Some elementary facts about the test family follow.

- `forms_eq_top_of_isEmpty`: for an empty test type every bilinear form is covariant.
- `forms_le_comp`: precomposing all three test maps with any `t : J → I`
  enlarges the space.
- `forms_sumElim`: the tests `Sum.elim a a'`, `Sum.elim b b'` and `Sum.elim χ χ'`
  give exactly the intersection of the two separate form spaces. Concatenating
  two test families therefore keeps both covariance laws.
- `forms_id` and `length_id`: when `H = G`, `I = G` and `a = b = id`, the space and
  its length are definitionally `InvariantBilinear.forms ρ σ χ` and
  `InvariantBilinear.length ρ σ χ`.

## Elementary transport

- `comapLeft b χ σ f` pulls a form back in the first argument along an actual
  `G`-intertwiner `f : ρ.IntertwiningMap τ`. `comapRight a χ ρ f` pulls back in
  the second argument along an actual `H`-intertwiner `f : σ.IntertwiningMap υ`.
  The tests are unchanged. `comapLeft_apply` and `comapRight_apply` give the
  values, and `comapLeft_injective` and `comapRight_injective` prove injectivity
  for a surjective underlying intertwiner.
- `equivLeft b χ σ e` and `equivRight a χ ρ e` are linear equivalences of form
  spaces induced by an actual representation equivalence `e`. The inverse pulls
  back along `e`, and the forward map pulls back along `e.symm`.
  `length_congr_left` and `length_congr_right` give the length equalities.
- `flipEquiv a b χ ρ σ : forms a b χ ρ σ ≃ₗ[k] forms b a χ σ ρ` exchanges the two
  arguments of every form and the roles of `a` and `b`. The test type and the
  weight `χ` stay the same. `length_flip` is the resulting length equality.

## Subrepresentations and quotients

`inclusion S` is the inclusion of an actual `Subrepresentation` as an
intertwiner. `topEquiv π` is the representation equivalence from the top
subrepresentation to the whole representation. They give `topEquivLeft` and
`topEquivRight`, and the total-space equalities `length_top_left` and
`length_top_right`. Every form on the bottom subrepresentation vanishes, since
that carrier contains only zero. The instances `subsingleton_bot_left` and
`subsingleton_bot_right` record this, and `length_bot_left` and
`length_bot_right` give length zero.

For `S : Subrepresentation ρ`, `restrictLeft a b χ σ S` is pullback along
`inclusion S`. `descendLeft a b χ σ S` maps its kernel linearly to the form space
of the actual quotient

```text
ρ.quotient S.toSubmodule (fun g _ hv => S.apply_mem_toSubmodule g hv)
```

against `σ`, with the same tests `a b χ`. A form in the kernel vanishes on `S` in
its first argument and descends through `Submodule.liftQ`. Covariance on quotient
classes is checked on representatives. `descendLeft_apply_mkQ` evaluates the
descended form on a class, and `descendLeft_injective` proves injectivity.

The second-argument version is constructed directly. For `S : Subrepresentation σ`,
`restrictRight a b χ ρ S` restricts the second argument. `descendRight a b χ ρ S`
flips a kernel form, descends it through `Submodule.liftQ`, and flips back. The
target is the form space of `ρ` against the actual quotient
`σ.quotient S.toSubmodule (fun h _ hw => S.apply_mem_toSubmodule h hw)`.
`descendRight_apply_mkQ` and `descendRight_injective` are its value and
injectivity theorems.

`length_le_restrict_add_quotient_left` and `length_le_restrict_add_quotient_right`
are the two-term length bounds of the single-group module. The same argument
applies in either argument. Mathlib's exact-sequence length formula splits the
length into the restriction's kernel and range. The range injects into the form
space on `S`, and descent injects the kernel into the form space on the quotient.

## Provenance and scope

This is internal linear algebra over Mathlib's actual representations,
intertwiners, subrepresentations and representation quotients. The proofs follow
the same pattern as `Langlands.Representation.Filtration.InvariantBilinear`. No
original source is transcribed, so no source citation applies. The construction
is motivated by Rankin–Selberg uniqueness for unequal ranks. There, two
representations are filtered over their own ambient groups, so both covariance
laws must be kept: one through the first ambient group and one through the
second. Passing to one common covariance subgroup is not assumed.

The module proves no source theorem. In particular, it contains no dimension
inequality beyond the two-term bounds above, no finite-filtration bound, no
Whittaker exactness, no irreducible-pair rigidity and no uniqueness result. The
specialization to the actual mirabolic and general-linear groups and their
determinant and unipotent tests belongs to downstream work.
