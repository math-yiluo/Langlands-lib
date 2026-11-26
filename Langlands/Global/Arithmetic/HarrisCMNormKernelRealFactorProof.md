# Real-norm factorization of a CM cyclic norm-kernel character

`Langlands.Global.Harris.cmNormKernelRealFactor` proves
`Langlands.Global.Harris.CMNormKernelRealFactorStatement.{uE, uD}`, stated in
[`HarrisCyclicDescentCorrectionStatement`](HarrisCyclicDescentCorrectionStatement.md),
with the universes of `E` and `D` independent. It adds no hypothesis.

Let `D / E` be a cyclic Galois extension of CM number fields and let `η` be a Hecke
character of `E` trivial on the idele-class norms from `D`. The theorem gives a
finite-order Hecke character `η₀` of `E⁺ = maximalRealSubfield E`, trivial on the
whole archimedean factor `(InfiniteAdeles E⁺)ˣ`, with
`η = η₀ ∘ N_{E/E⁺}` for the actual idele-class norm `ideleClassNorm`.

## Source

M. Harris, *The local Langlands conjecture for GL(n) over a p-adic field, n < p*,
Invent. Math. 134 (1998), proof of Lemma 1.6, printed p. 189 (registered source
`harris-1998-local-langlands`, companion file `math_9611226v1.tex`, lines 763–767):
"The abelian extension `E^u/E` is a lift of a totally real abelian extension of `E_0`;
thus `η = η_0 ∘ N_{E/E_0}`, for some finite Hecke character `η_0` of the ideles of
`E_0`, trivial at the archimedean places of `E_0`." The source gives no further detail for this step. The Lean proof below derives it from
the Library's global class field theory.

## The same-universe theorem

`CMNormKernelRealFactor.exists_realFactor_sameUniverse` proves the conclusion for a
cyclic Galois extension `L / E` of CM fields with `E` and `L` in one universe, the
setting of the Library's relative Weil groups. Write `E⁺` and `L⁺` for the maximal real
subfields, `c_E` and `c_L` for the CM complex conjugations (`IsCMField.complexConj`) and
`c` for `c_L` viewed as an automorphism of `L` over `E⁺`. The proof makes `L⁺` an
`E⁺`-algebra through `E⁺ → E → L`: the image of a real element of `E` is real under
every complex embedding of `L`.

1. **Complex conjugation.** Two private lemmas compare `c_L` with complex embeddings
   through `IsCMField.complexEmbedding_complexConj`. For every embedding `φ : L → ℂ`
   and every ring automorphism `g` of `L`, `φ ∘ g` is again an embedding, so
   `g ∘ c_L = c_L ∘ g`. The embedding `φ ∘ (E → L)` of `E` gives
   `c_L (x) = c_E (x)` for `x ∈ E`. Hence `c` is central in `Gal(L/E⁺)`, `c² = 1`,
   and `c` does not fix `E`, because `c_E ≠ 1` (`IsCMField.complexConj_ne_one`).
2. **The group `Gal(L/E⁺)`.** The group `Aut(E/E⁺)` has two elements, so it is
   `{1, c_E}` (`Nat.card_eq_two_iff'`). For `g ∈ Aut(L/E⁺)`, its restriction
   `g.restrictNormal E` is `1` or `c_E`. Thus `g` or `g c` fixes `E` and comes from
   `Gal(L/E)` by restriction of scalars. Since `Gal(L/E)` is cyclic and `c` is central,
   `Aut(L/E⁺)` is commutative. The extension `L / E⁺` is Galois by
   `IsGalois.of_fixedField_eq_bot`: an
   element fixed by every automorphism is fixed by `Gal(L/E)`, so it lies in `E`
   (`IsGalois.mem_range_algebraMap_iff_fixed`). It is also fixed by `c`, so it lies in
   `E⁺` (`IsCMField.complexConj_eq_self_iff`).
3. **Reciprocity.** `localRelativeClassFormation` and `fundamentalClass_exists` give an
   arithmetic family of global fundamental classes, which satisfies `Restriction`.
   `RelativeWeilGroup.relativeWeilTransferReciprocity` shows that the transfers
   `W_{L/K} → C_K` are surjective with commutator kernel for `K = E⁺, E, L⁺`.
   `Gal(L/E⁺)` is commutative, so the projection `W_{L/E⁺} → Gal(L/E⁺)` kills the
   commutator subgroup (`Abelianization.commutator_subset_ker`). It descends along the
   transfer to a homomorphism `r : C_{E⁺} → Gal(L/E⁺)` with `r ∘ transfer = projection`.
4. **The character of `Gal(L/E)`.** By `RelativeWeilGroup.exact` the kernel of the
   projection `W_{L/E} → Gal(L/E)` is the image of `C_L`. By
   `RelativeWeilGroup.transfer_inclusion` the transfer is the norm `N_{L/E}` there.
   Hence `η ∘ transfer` kills that kernel and descends along the surjective projection to
   a character `ψ` of `Gal(L/E)` with `ψ ∘ projection = η ∘ transfer`.
5. **Galois restriction.** Let `N = ⟨c⟩`, a normal subgroup because `c` is central.
   Restriction of scalars followed by the quotient map gives a bijection
   `Gal(L/E) → Gal(L/E⁺)/N`. It is injective since `c^k` is `1` or `c` and `c` does not
   fix `E`. It is surjective by step 2. This realizes `Gal(L/E) ≅ Gal(L⁺/E⁺)` as a
   quotient of `Gal(L/E⁺)`. The composite `φ` of the quotient map, the inverse
   bijection and `ψ` is a character of `Gal(L/E⁺)` with `φ (σ|_{E⁺}) = ψ σ` for
   `σ ∈ Gal(L/E)` and `φ c = 1`.
6. **The character `η₀ = φ ∘ r`.** For `a ∈ C_L`, `r (N_{L/E⁺} a)` is the projection of
   the image of `a` in `W_{L/E⁺}`, hence `1`. The image of `N_{L/E⁺}` is open
   (`isOpenMap_ideleClassNorm`), so `η₀` is constant near `1` and continuous by
   `continuous_of_continuousAt_one`. Its values are values of a character of the finite
   group `Gal(L/E⁺)`, so `η₀ ^ |Gal(L/E⁺)| = 1` by `pow_card_eq_one'`.
7. **Factorization.** Every `x ∈ C_E` is `transfer t` for some `t ∈ W_{L/E}`.
   `RelativeWeilGroup.transferNormCompatibility` for the tower `E⁺ ⊆ E ⊆ L` gives
   `N_{E/E⁺} (transfer t) = transfer (ι t)`, with `ι : W_{L/E} → W_{L/E⁺}` the
   intermediate-field inclusion.
   `RelativeWeilGroup.projection_restrictionInclusion` gives
   `projection (ι t) = (projection t)|_{E⁺}`. Therefore
   `η₀ (N_{E/E⁺} x) = φ ((projection t)|_{E⁺}) = ψ (projection t) = η x`.
8. **The archimedean factor.** The same two lemmas for the tower `E⁺ ⊆ L⁺ ⊆ L` show
   that `r (N_{L⁺/E⁺} z)` is the restriction to `E⁺` of an element of `Gal(L/L⁺)` for
   every `z ∈ C_{L⁺}`. That group is generated by `c_L`
   (`IsCMField.zpowers_complexConj_eq_top`), and `φ c = 1`, so `η₀` is trivial on
   `N_{L⁺/E⁺} C_{L⁺}`. Let `v` be an infinite place of `E⁺`. It has a place `w` of `L⁺`
   above it (`exists_infinitePlace_above`). The field `L⁺` is totally real, so `w` is
   real and unramified over `v` (`NonabelianBrauer.isUnramified_of_isReal`). The local
   norm at `w` is then onto `E⁺_vˣ` (`NonabelianBrauer.exists_localUnitNorm_eq`).
   `ideleClassNorm_ofCompletion` identifies the class of a local unit at `v` with the
   norm of the class of its preimage at `w`. Hence `η₀.infiniteComponent v = 1`. Every
   archimedean idele is the product over `v` of its components placed by
   `HarrisDatum.single` (`Finset.univ_prod_mulSingle`), and
   `HarrisDatum.infiniteComponent_eq_atInfinity` gives `η₀.atInfinity = 1`.

## Independent universes

For `E : Type uE` and `D : Type uD`, let `ι : D →ₐ[E] AlgebraicClosure E` be
`IsAlgClosed.lift` and `D'` its field range, an intermediate field in the universe of `E`.
The isomorphism `f = ι.equivFieldRange : D ≃ₐ[E] D'` transports the hypotheses:

- `D'` is finite over `E` (`Module.Finite.equiv`) and a number field
  (`NumberField.of_module_finite`);
- it is Galois over `E` (`IsGalois.of_algEquiv`), and its automorphism group is cyclic,
  the image of the cyclic group `Gal(D/E)` under `AlgEquiv.autCongr`;
- it is totally complex as an extension of the totally complex field `E`
  (`isTotallyComplex_of_algebra`);
- it is CM by `IsCMField.ofCMExtension`, with the totally real base
  `maximalRealSubfield D` acting through `f`. The degree `[D' : D⁺] = 2` comes from
  `Algebra.finrank_eq_of_equiv_equiv`.

Norm triviality transfers by `ideleClassNorm_equiv` for the identity of `E` and `f`,
together with `ideleClassEquiv_refl`. Every idele class of `D'` is the transport of one
of `D`, and its norm to `E` is the norm of that class. The same-universe theorem for
`E` and `D'` then gives the conclusion, which mentions only `E` and `η`.
