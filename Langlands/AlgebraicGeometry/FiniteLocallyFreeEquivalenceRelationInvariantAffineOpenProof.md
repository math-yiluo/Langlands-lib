# Proof of the invariant affine open statement (finite-set Stacks 03JE)

`finiteLocallyFreeEquivalenceRelationInvariantAffineOpen` proves
`FiniteLocallyFreeEquivalenceRelationInvariantAffineOpenStatement.{u}` from the Library module
`FiniteLocallyFreeEquivalenceRelationStatements`, for every universe `u`: for `t, s : R ⟶ U`
with `prod.lift t s` a monomorphism, reflexive, symmetric and transitive on `T`-valued points,
and `t`, `s` finite, flat and locally of finite presentation, a finite set `E` of points of
`U` with `t r ∈ W` whenever `s r ∈ E`, for an affine open `W`, lies in an affine open `V` with
`s⁻¹ V = t⁻¹ V`.

The proof applies the ported Anthropic FLT theorem
`AlgebraicGeometry.Scheme.exists_invariant_isAffineOpen_of_finite_of_finiteLocallyFree_equivalenceRelation`
(module `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_exists_invariant_isAffineOpen_of_finite_of_finiteLocallyFree_equivalenceRelation`;
see its Markdown for source, licence and proof) with its `s, t` instantiated as the
statement's `s, t`:

1. The finiteness, flatness and finite presentation hypotheses are introduced as instances.
2. The FLT hypothesis `hequiv` says that for each scheme `T` the relation "`x = φ ≫ s` and
   `y = φ ≫ t` for some `φ : T ⟶ R`" is an `Equivalence` on `T ⟶ U`. Reflexivity is the
   statement's reflexivity. Symmetry applies the statement's symmetry to `φ`. Transitivity
   applies the statement's transitivity to `ψ, φ` where `x = φ ≫ s`, `y = φ ≫ t = ψ ≫ s` and
   `z = ψ ≫ t`; the resulting `r` has `r ≫ s = x` and `r ≫ t = z`.
3. The FLT hypothesis `∀ x ∈ S, ∀ r, s r = x → t r ∈ U` is the statement's
   `∀ r, s r ∈ E → t r ∈ W`.
4. The FLT conclusion gives an affine open `V ⊆ W` with `E ⊆ V` and `s⁻¹ V = t⁻¹ V`; the
   inclusion `V ⊆ W` is dropped.

The monomorphism hypothesis is not used.
