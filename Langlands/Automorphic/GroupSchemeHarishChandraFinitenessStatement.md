# Harish-Chandra's finiteness theorem on `V(𝔸)M'(F) \ G(𝔸)`

Module `Langlands.Automorphic.GroupSchemeHarishChandraFinitenessStatement` contains one
`Prop`-valued definition, `Langlands.Automorphic.GroupSchemeFunctions.ParabolicHarishChandraFinitenessStatement`,
and no theorem. It states Harish-Chandra's finiteness theorem for automorphic forms on the
parabolic quotient `V(𝔸)M'(F) \ G(𝔸)` of a connected reductive group over a number field. The
module does not prove it. The Library's `Langlands.Automorphic.HarishChandraFinitenessStatement`
(module `Langlands.Automorphic.AutomorphicAdmissibilityStatement`) is the corresponding statement
for `GL_n` on `GL_n(F) \ GL_n(𝔸)`, in a different framework.

## Statement

The data are:

- a number field `F` and a connected reductive group `G` over `F` (`IsConnectedReductive G`),
  with the instance assumptions `[IsAffineHom G.X.hom] [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom] [IsAffine Q.X.left]`;
- a parabolic subgroup `q : Q → G`, a closed immersion (`IsParabolicSubgroup q`), with geometric
  unipotent radical `iV : V → Q` (`LeviSubgroup.IsGeometricUnipotentRadical iV`) and a rational
  Levi subgroup `l' : M' → Q` (`IsRationalLeviSubgroup l'`) such that multiplication
  `M' × V → Q` is an isomorphism (`IsIso (subgroupMultiplication l' iV)`). The subgroup
  `parabolicQuotientSubgroup F q iV l'` of `G(𝔸)` is `V(𝔸)M'(F)`;
- a maximal compact subgroup `K` of `G(𝔸)` (`IsMaximalCompactSubgroup F G K`) with
  `Q(𝔸)K = G(𝔸)` (`IsIwasawaCompact q K`). Write `K_∞` for
  `K.comap (ofInfinite F G).toMonoidHom`, the points `a` of `G(F_∞)` with `(a, 1) ∈ K`;
- a matrix representation `rho : G → GL_N` that is a closed embedding (`IsClosedSubgroup rho`),
  and the data `hsmooth : SmoothOfRelativeDimension d G.X.hom` and
  `hcalc : AdelicDifferentialCommutator F G hsmooth` that define the center
  `𝔷 = AdelicEnvelopingCenter F G hsmooth` of the complex enveloping algebra of the Lie algebra
  of `G(F_∞)` and its action `plotSmoothCenterAction F G hsmooth hcalc` on plot-smooth functions
  on `G(F_∞)`;
- an ideal `J` of `𝔷` with `𝔷 / J` finite-dimensional over `ℂ`;
- an open subgroup `L` of `G(𝔸_f)`;
- a finite-dimensional complex subspace `E` of the functions `K_∞ → ℂ`.

Let `X` be the set of functions `f : G(𝔸) → ℂ` such that

1. `f` is automorphic on `V(𝔸)M'(F) \ G(𝔸)`:
   `IsAutomorphicFunctionOn F G hsmooth hcalc (parabolicQuotientSubgroup F q iV l') K_∞ rho f`
   (left invariance, smoothness, `K_∞`-finiteness, `𝔷`-finiteness and moderate growth for the
   adelic norm of `rho`; module `Langlands.Automorphic.GroupSchemeInvariantForms`);
2. `f(g b) = f(g)` for every `b ∈ L` and every `g ∈ G(𝔸)`, where `b` acts through `ofFinite`;
3. every `z ∈ J` annihilates every infinite slice `a ↦ f(a, b)` of `f`, for every proof that the
   slice is plot-smooth (the same form as in `IsCenterFiniteFunction`, with `J` fixed);
4. for every `g ∈ G(𝔸)`, the function `k ↦ f(g k)` on `K_∞` belongs to `E`.

The conclusion is that the complex span of `X` in the space of all functions `G(𝔸) → ℂ` is
finite-dimensional.

## Sources

- Harish-Chandra, *Automorphic Forms on Semisimple Lie Groups*, notes by J. G. M. Mars, Lecture
  Notes in Mathematics 62, Springer, 1968, registered as
  `provided-d0ff4732ff6b5d8ecf8562752577df639622e8aad2899ef307bc320213b534af`
  (file `Harish-Chandra–Mars (1968), Automorphic Forms on Semisimple Lie Groups.pdf`).
  Chapter I, §2, printed pp. 6–8 (PDF pp. 16–18). For a finite-dimensional representation
  `(σ, V)` of `K` and a representation `χ` of the center `𝔷` on `V` commuting with `σ`,
  `𝒜(G/Γ, σ, χ)` is the space of smooth `σ`-functions `f : G → V`, right invariant under the
  arithmetic group `Γ`, of moderate growth, with `z f = f χ(z)` for `z ∈ 𝔷` (definitions on
  p. 7). Theorem 1 (p. 8): `dim 𝒜(G/Γ, σ, χ) < ∞`.
- A. Borel and H. Jacquet, *Automorphic forms and automorphic representations*, Proc. Sympos.
  Pure Math. 33, part 1 (1979), 189–202, registered as `borel-jacquet-1979-automorphic` (file
  `Part I.pdf` of the Corvallis volume). §4.1, printed p. 194 (PDF p. 189): a simple element of
  the Hecke algebra is `ξ = ξ_∞ ⊗ ξ_f` with `ξ_∞` idempotent; §3.2: for a compact open subgroup
  `L` of `G(𝔸_f)`, `e_L` is the characteristic function of `L` divided by its volume, and
  `f * e_L = f` if and only if `f` is right invariant under `L`. §4.2, p. 195 (PDF p. 190): `f`
  has type `(ξ, J, K_∞)` if `f * ξ = f` and an ideal `J` of finite codimension of `Z(𝔤_∞)`
  annihilates `f`; one may take `ξ_f = e_L` for a compact open `L`. §4.3 (i), p. 195: the space `𝒜(ξ, J, K_∞)` of automorphic forms of type
  `(ξ, J, K_∞)` on `G(F) \ G(𝔸)` is finite-dimensional, deduced from Harish-Chandra's theorem
  (§1.7, p. 191, PDF p. 186) through the decomposition 4.3 (2).
- C. Mœglin and J.-L. Waldspurger, *Spectral Decomposition and Eisenstein Series*, Cambridge
  University Press, 1995, registered as `moeglin-waldspurger-1995-spectral-decomposition`.
  - I.2.17, printed pp. 37–38 (chapter file
    `05.2_pp_18_40_Automorphic_forms_growth_constant_terms.pdf`, PDF pp. 20–21): automorphic
    forms on `U(𝔸)M(k) \ G`; "A certain number of classical theorems concerning automorphic
    forms on `M(k) \ M` can be immediately generalised to automorphic forms on
    `U(𝔸)M(k) \ G`. For example the finiteness theorem (see [HC] Theorem 1)".
  - I.4.5, printed p. 60 (chapter file
    `05.4_pp_49_77_Upper_bounds_as_functions_of_the_constant_term.pdf`, PDF p. 12): the
    `K`-type condition in the form "the space generated by `{δ(k)φ; k ∈ K}` decomposes into a
    sum of irreducible representations of `K` whose class belongs to" a fixed finite set.
- J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer.
  Math. Soc. 37 (2024), 187–234, registered as
  `bernstein-lapid-2024-meromorphic-continuation-eisenstein` (PDF
  `Bernstein-Lapid--On the meromorphic continuation of Eisenstein series--2024.pdf`). §8.2,
  Lemma and proof, p. 222: the theorem is applied on `V(𝔸)M'(F) \ G(𝔸)` to the functions
  `M(w, λ)φ`, which share a `K`-type idempotent and an annihilating ideal of `𝔷`.

## Correspondence with the sources

- **Quotient.** `Γ = V(𝔸)M'(F)` is MW's `U(𝔸)M(k)` for the parabolic `Q = M'V`; for `Q = G`
  it is `G(F)`, the case of Borel–Jacquet §4.3 (i). The parabolic is not required to be
  standard, and `K` is assumed to be a maximal compact subgroup of `G(𝔸)` with
  `Q(𝔸)K = G(𝔸)`. Its infinite part `K_∞` is then a maximal compact subgroup of `G(F_∞)`, the
  group whose types are fixed in the sources.
- **Level.** Borel–Jacquet §3.2 defines the idempotent `e_L` for a compact open subgroup `L` of
  `G(𝔸_f)`, and `f * e_L = f` if and only if `f` is right invariant under `L`. The Lean statement
  allows any open subgroup `L`, which need not be compact (for `G = G_m` over `ℚ` the whole
  finite idele group is open). Every open subgroup contains a compact open one: `L` is also closed,
  so `L_c = L ∩ C` is compact and open for any compact open subgroup `C` of `G(𝔸_f)` (for
  instance the Library's `FiniteAdelicGroupPoints.compactOpenSubgroup`, module
  `Langlands.Global.FiniteAdelicGroupCompactOpen`). A function satisfying condition 2 is right
  invariant under `L_c`, so `f * e_{L_c} = f`, the finite part of a simple element
  `ξ = ξ_∞ ⊗ e_{L_c}`. When `L` is itself compact, condition 2 is exactly `f * e_L = f`.
- **Center.** Condition 3 is the annihilation of `f` by the ideal `J` of finite codimension of
  `𝔷 = Z(𝔤_∞)`, evaluated on the infinite slices, as the Library's `IsCenterFiniteFunction`
  does. In Harish-Chandra's formulation `χ` is a finite-dimensional representation of `𝔷`;
  its kernel is an ideal of finite codimension, and conversely `J` gives `χ` on `𝔷 / J`.
- **Types under `K_∞`.** Condition 4 replaces "`f * ξ_∞ = f` for an idempotent `ξ_∞`"
  (Borel–Jacquet) and "the `K`-translates of `f` decompose into irreducible representations
  with classes in a finite set" (MW I.4.5 (1)). In both sources the finite set of types is common
  to all the functions of the space, as `E` is common to all the functions of `X`. The two
  formulations bound the same spaces:
  - if the right `K_∞`-translates of `f` decompose into irreducible representations with classes
    in a finite set `δ`, every function `k ↦ f(gk)` lies in the sum `E_δ` of the spaces of matrix
    coefficients of the representations in `δ` (one such function may involve several classes of
    `δ`). `E_δ` is finite-dimensional, so condition 4 holds for `E = E_δ`, for all such `f` at once;
  - conversely, fix `E` and let `E'` be the span of the functions `k ↦ f(gk)` over all `f ∈ X` and
    all `g ∈ G(𝔸)`. Then `E' ⊆ E` is finite-dimensional. It consists of continuous functions,
    since every `f ∈ X` is continuous, and it is stable under left translation by `K_∞`: the left
    translate by `k₀` of the function at `g` is the function `k ↦ f(g k₀⁻¹ k)` at `g k₀⁻¹`. By the
    Peter–Weyl theorem `E'` lies in the sum of the matrix-coefficient spaces of one finite set of
    irreducible representations of `K_∞`. That sum is also stable under right translation, so the
    functions `k ↦ f(g k k₁)` attached to the right translates of `f` lie in it as well, and the
    right `K_∞`-translates of every `f ∈ X` decompose into irreducible representations from one
    finite set `δ`, the same for the whole of `X`. With the character idempotent `ξ_δ` of `δ`
    this is `f * ξ_δ = f` for every `f ∈ X`.

  So, for each `E` and each compact open `L_c ⊆ L` as above, the set `X` lies in a space
  `𝒜(ξ_δ ⊗ e_{L_c}, J, K_∞)` of the sources (on `V(𝔸)M'(F) \ G(𝔸)`). Conversely, for a compact
  open `L` and a finite set `δ`, the forms of that space are elements of `X` for `E = E_δ`.
  Mœglin–Waldspurger impose finiteness under the whole compact group `K = K_∞ K_f`; under a fixed
  compact open level `L_c`, the right translates by the finite part `K_f` factor through the finite
  quotient of `K_f` by the normal core of `K_f ∩ L_c`, so the types of `K_f` are bounded as well.
  Condition 4 involves `f` alone, so the statement can be applied to a family of functions without
  first showing that their `K_∞`-translates satisfy conditions 1–3.
- **Growth.** Moderate growth is measured with the adelic norm of the closed embedding `rho`, as
  in Borel–Jacquet §4.3 (4).
- **Finite dimension.** In the sources the functions of a given type form a linear space. The
  Lean conclusion is that the span of `X` is finite-dimensional, which is equivalent and does not
  require proving first that `X` is closed under addition.

## Provenance

The statement is derived from the sources above: it is Harish-Chandra's Theorem 1 in the adelic
form of Borel–Jacquet §4.3 (i), on the parabolic quotient as indicated by Mœglin–Waldspurger
I.2.17. The formulation of the `K_∞`-types by a finite-dimensional space of functions on `K_∞`
is internal to this module; its equivalence with the sources' formulations is explained above.
