# Factorization of finite-dimensional simple modules over a tensor algebra

Module `Langlands.Algebra.AlgebraTensorSimpleFactorizationProof` proves
`Langlands.algebraTensorSimpleFactorization`, whose type is the published
`Langlands.AlgebraTensorSimpleFactorizationStatement.{u₁, u₂, v}`.
The two algebra universes and the module universe are independent. The factors
constructed in the conclusion both live in the given module's universe `v`.

This is the existence assertion of Renard III.1.14, Scholium, printed pp.66–67 /
PDF pp.72–73 of *Représentations des groupes réductifs p-adiques*, French edition
dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The published statement Markdown explains the tensor-algebra interpretation of
the source's product notation. The proof below is an algebra-module adaptation
of the evaluation construction in the published
`Langlands.Representation.Smooth.Factorization.TwoFactorExistenceProof`; it uses
finite-dimensional Burnside in place of its group-algebra density argument.
The helpers in `Langlands.AlgebraTensor` are internal derived lemmas for this
proof. This unit proves existence only.

## Commuting actions and multiplicity

For the helpers, let `W` carry compatible complex, `A₁`, and `A₂` module
structures, with the `A₁` and `A₂` actions commuting. If `U` is an
`A₁`-submodule of `W`, put `Mult U = U →ₗ[A₁] W`. The action of `A₂` on
this space is pointwise on the values in `W`. Commutativity ensures that the
resulting maps remain `A₁`-linear; no `A₂`-action on `U` is required.

The map `evalAt U u` evaluates an intertwiner at `u`, and
`eval U : U ⊗[ℂ] Mult U →ₗ[ℂ] W` sends `u ⊗ f` to `f u`.
For simple `U` and nonzero `u`, evaluation at `u` is injective: an
`A₁`-linear map from a simple module is either injective or zero.

If `U` is also finite-dimensional, `eval U` is injective. Expand an element
of its kernel in a basis of `U`, with finitely supported multiplicity
coefficients. For a basis index `j` and arbitrary `u`, the published Burnside
lemma `Langlands.RankOneGraded.exists_forall_eq_smul_of_isSimpleModule`
realizes the rank-one operator `v ↦ (b.coord j v) • u` as the action of some
`a : A₁`. Apply `a` to the vanishing evaluation. Intertwining and
complex linearity isolate the value of the `j`th coefficient at `u`, so
every coefficient is zero. This proves `eval_injective`.

## Surjectivity and simplicity of the second factor

Now suppose `W` is simple over `A₁ ⊗[ℂ] A₂` and the action of a pure tensor
satisfies `(a ⊗ b) • w = a • b • w`. For any nonzero
`A₂`-submodule `N` of `Mult U`, restrict evaluation to `U ⊗[ℂ] N`.
Its image is an `A₁ ⊗[ℂ] A₂`-submodule: on a pure tensor, use the
preimage `(a • u) ⊗ (b • n)`, and extend by addition in both tensor
arguments. The image is nonzero because a nonzero multiplicity map cannot
vanish at a nonzero vector of simple `U`. Simplicity of `W` makes this
image the whole space. This is `eval_restricted_surjective`.

To prove `mult_simple`, first observe that the inclusion `U → W` is a
nonzero element of `Mult U`. If `N` is a nonzero submodule, the preceding
surjectivity supplies a tensor `t ∈ U ⊗ N` evaluating to `f u` for any
`f ∈ Mult U` and fixed nonzero `u`. Injectivity of full evaluation gives
`T t = u ⊗ f`, where `T` includes `U ⊗ N` in `U ⊗ Mult U`.
Choose a complex-linear functional `φ` with `φ u = 1`. Contraction
`v ⊗ g ↦ (φ v) • g` sends the image of `T` into `N` and sends
`u ⊗ f` to `f`. Thus every `f` is in `N`.

The helper `eval_comm` checks that evaluation intertwines the exact external
action `AlgebraTensor.action` from the published first-conjunct proof with
the given tensor-algebra action on `W`. It uses the displayed pure-tensor
identity and induction on the acting tensor and the vector tensor.

## Construction of the factorization

The final theorem restricts the given tensor-algebra module along the algebra
homomorphisms `a ↦ a ⊗ 1` and `b ↦ 1 ⊗ b`. Their scalar towers agree
with the given complex structure, and tensor multiplication verifies both
commutativity and the pure-tensor action identity.

Finite-dimensionality makes `W` Artinian as a complex module, hence as an
`A₁`-module by restriction of scalars. An atom of its submodule lattice
therefore supplies a simple `A₁`-submodule `U`. It is finite-dimensional
by its inclusion in `W`. The second factor is `Mult U`, simple by the
lemma above and finite-dimensional because evaluation at a nonzero vector of
`U` injects it into `W`. Both types are in universe `v`.

Use `eval_restricted_surjective` with `N = ⊤` to obtain surjectivity of
full evaluation. Together with `eval_injective`, this defines the
complex-linear equivalence in the conclusion; `eval_comm` supplies its
required intertwining law. The theorem proves precisely the published
existence statement, with the given finite-dimensionality and simplicity
hypotheses and no additional assumptions.
