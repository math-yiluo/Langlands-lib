# Minimal finite free homotopy models at a prime: proof

This module proves the published proposition
`Langlands.Cohomology.ModuleComplex.PrimeMinimalPerfectStatement.{u}` as the
theorem `Langlands.Cohomology.ModuleComplex.primeMinimalPerfect`, for an
arbitrary universe `u`. It imports the statement module unchanged, the
Library's `PerfectModuleComplexBaseChange` and `PerfectModuleComplexHomotopy`,
and Mathlib. The final theorem has no hypotheses beyond those of the statement.

The route is the one suggested by the Stacks Project, More on Algebra, tags
0BCC and 0BCD (`more-algebra.tex` at commit `a04446e5`): over the local ring
`Rₚ`, repeatedly split off contractible two-term pieces `Rₚ → Rₚ` until every
differential vanishes modulo the maximal ideal, and then read off the ranks
after extending to the residue field. The Lean proof below implements this
directly with chain maps and homotopies; it does not use the derived category.

## Helper lemmas (namespace `ModuleComplex.PrimeMinimal`)

All helpers are internal to this proof. Unless stated, `A : Type u` is a
commutative ring and `L` is an integer-indexed cochain complex of `A`-modules.

**Functionals.** `exists_functional_eq_one`: over a local ring, if `w` is a
vector of a finite free module and `w ∉ 𝔪 • ⊤`, there is a linear functional
`f` with `f w = 1`. Some coordinate of `w` in a basis is a unit, otherwise `w`
would lie in `𝔪 • ⊤`; scale that coordinate functional by the inverse unit.

**Kernel subcomplex of an idempotent.** For an endomorphism `e : L ⟶ L`,
`kerComplex e` has terms `ker (e.f k)` and the restricted differentials (they
preserve the kernels since `e` is a chain map); `kerComplexι e` is the
inclusion. If `e` is degreewise idempotent, `kerComplexRetr` is the chain map
`1 - e` with codomain restricted to the kernel, and
`kerComplexι_retr` and `kerComplexRetr_ι` say that `ι ≫ r = 𝟙` and
`r ≫ ι = 𝟙 - e`. Given a homotopy `H : Homotopy e 0`,
`kerComplexHomotopyEquiv` is a homotopy equivalence `kerComplex e ≃ L`: the
first composite is the identity on the nose, and the second is `𝟙 - e`, which
is homotopic to `𝟙` through `H`.

**Terms of the kernel subcomplex.** `kerComplex_finite_projective`: the kernel
of an idempotent on a finite projective term is a retract of it, hence finite
and projective. `finite_projective_of_isCompl` gives the same for both members
of a pair of complementary submodules (through `Submodule.prodEquivOfIsCompl`),
and `finrank_add_of_isCompl` shows that, over a local ring, their ranks add up
to the rank of the ambient module. Over a local ring, finite projective
modules are free (`Module.free_of_flat_of_isLocalRing`).
`finrank_kerComplex`: over a local ring the kernel term has rank at most the
original rank, and strictly smaller rank whenever `e.f k ≠ 0`, because the
complementary summand (the kernel of `1 - e`, which contains the nonzero image
of `e`) is then a nonzero free module.

**The elementary null-homotopic idempotent.** Fix a degree `i`, a functional
`f` on `L.X (i + 1)` and a vector `y` in `L.X i`. `funFamily` is the family of
functionals equal to `f` in degree `i + 1` and zero elsewhere; `vecFamily` is
the family of vectors equal to `y` in degree `i` and zero elsewhere.
`elemHomotopy` is the degree-lowering map `z ↦ φ(z) • v`, and
`elemEndo := Homotopy.nullHomotopicMap' elemHomotopy` is the chain map
`d h + h d`, which is null-homotopic by `Homotopy.nullHomotopy'`. By
`elemEndo_apply`, in degree `k` it is
`z ↦ φ_{k+1}(d z) • v_k + φ_k(z) • d(v_{k-1})`; so it is `z ↦ f(d z) • y` in
degree `i`, `z ↦ f(z) • d y` in degree `i + 1`, and zero elsewhere. Under the
hypothesis `f (d y) = 1`, `elemEndo_idem` proves that it is idempotent in
every degree (the auxiliary lemmas `funFamily_vecFamily`,
`funFamily_d_vecFamily_smul` and `mul_funFamily_d_vecFamily` record the needed
evaluations, and `d ∘ d = 0` kills the cross terms), and `elemEndo_self`
proves that it fixes `y`. These helper lemmas assume nothing about `A` beyond
commutativity; in particular they do not assert that the endomorphism is
nonzero (over the zero ring it is zero). Nonzeroness is proved only in the
local cancellation step below.

**One cancellation step.** `exists_cancel`: let `A` be local and `L` have
finite projective terms. If `d z ∉ 𝔪 • ⊤` for some `z` in degree `i`, choose
`f` with `f (d z) = 1` and take `e := elemEndo L i f z`. Then
`kerComplex e` has finite projective terms, is homotopy equivalent to `L`, has
no larger rank in any degree, strictly smaller rank in degree `i`, and is zero
wherever `L` is zero. The strict rank decrease uses `e.f i ≠ 0`, which is
derived from `hz`: if `e` vanished in degree `i`, then `z = e z = 0` by
`elemEndo_self`, so `d z = 0 ∈ 𝔪 • ⊤`, contradicting `hz`.

**Repeated cancellation.** `exists_minimal_aux` proves, by induction on a
natural-number bound `n` for the total rank `∑ k ∈ Finset.Icc a b,
finrank A (L.X k)`, that every complex over a local ring with finite
projective terms which is strictly `≥ a` and strictly `≤ b` is homotopy
equivalent to a complex with the same bounds and finite projective terms whose
differentials all take values in `𝔪 • ⊤`. If some differential `d_{k,l}` has a
value outside `𝔪 • ⊤`, then `l = k + 1` (other differentials vanish by the
shape of the complex) and `k ∈ [a, b]` (outside the bounds the term is zero,
so it has rank zero and could not lose rank); one cancellation step lowers the
total rank, and the induction hypothesis applies to the result. The homotopy
equivalences compose.

**Residue-field ranks.** Let `ψ : A →+* F` be a ring map from a local ring to
a field that kills the maximal ideal. `baseChange_d_eq_zero`: if every
differential of `M` takes values in `𝔪 • ⊤`, every differential of
`(baseChange ψ).obj M` is zero, since `1 ⊗ (r • n) = ψ(r) ⊗ n = 0` for
`r ∈ 𝔪` (checked on the generators `1 ⊗ m` by
`ModuleCat.ExtendScalars.hom_ext`). `finrank_homology_baseChange`: if
moreover all terms of `M` are finite free, then the `F`-dimension of the
degree-`i` homology of `(baseChange ψ).obj M` equals `finrank A (M.X i)`.
With zero differentials the homology is isomorphic to the term
(`isoHomologyπ` and `iCyclesIso`), and `Module.finrank_baseChange` computes
the dimension of `F ⊗_A M.X i`.

## The main theorem

`primeMinimalPerfect` takes `R`, a strictly perfect `K` and a prime `p`. Write
`Rₚ := Localization.AtPrime p` and `κ := p.ResidueField`, the residue field of
the local ring `Rₚ`.

1. Finite dimensionality of each `κ`-homology group is the published lemma
   `finite_homology_baseChange` applied to `algebraMap R κ`.
2. The localized complex `Kₚ := (baseChange (algebraMap R Rₚ)).obj K` is
   strictly perfect (`isStrictlyPerfect_baseChange`), so it has bounds `a`,
   `b` and finite projective terms. `exists_minimal_aux` (with `n` one more
   than its total rank) gives `M` with the same bounds, finite
   projective (hence free, as `Rₚ` is local) terms, a homotopy equivalence
   `M ≃ Kₚ`, and all differentials in `𝔪 • ⊤`. This `M` is the complex `L`
   of the statement; it is `IsFiniteFree`.
3. For the ranks, let `ρ := IsLocalRing.residue Rₚ`, which kills the maximal
   ideal. `IsScalarTower.algebraMap_eq` gives
   `ρ.comp (algebraMap R Rₚ) = algebraMap R κ`. The published
   `baseChangeCompIso` identifies `(baseChange (ρ ∘ algebraMap R Rₚ)).obj K`
   with `(baseChange ρ).obj Kₚ`, so their homology groups are isomorphic
   (`HomologicalComplex.homologyMapIso`). The published
   `baseChangeHomotopyEquiv` turns `M ≃ Kₚ` into a homotopy equivalence
   `(baseChange ρ).obj M ≃ (baseChange ρ).obj Kₚ`, whose homology isomorphism
   is `HomotopyEquiv.toHomologyIso`. Hence the `κ`-dimension `d i` of the
   degree-`i` homology of `(baseChange (algebraMap R κ)).obj K` equals that of
   `(baseChange ρ).obj M`, which is `finrank Rₚ (M.X i)` by
   `finrank_homology_baseChange`.
4. A basis of the finite free module `M.X i` indexed by `Fin (d i)`
   (`Module.finBasisOfFinrankEq`) yields the linear equivalence
   `M.X i ≃ₗ[Rₚ] (Fin (d i) → Rₚ)` via `Basis.equivFun`.

The same `M` gives the homotopy equivalence and every rank equivalence, as the
statement requires. The proof uses only the standard Mathlib axioms.
