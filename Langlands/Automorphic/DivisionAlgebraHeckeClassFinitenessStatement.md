# Finiteness of the Hecke class of a cuspidal representation of `GL_n` on a division algebra

Module `Langlands.Automorphic.DivisionAlgebraHeckeClassFinitenessStatement`, namespace
`Langlands.Automorphic.DivisionHeckeClass`. It makes six definitions and states one
proposition, `DivisionAlgebraHeckeClassFinitenessStatement`. It contains no proof.

In words: let `π` be a cuspidal automorphic representation of `GL_n` over a number field `E`,
`n = r + 1`, and let `A` be a central division algebra of dimension `n²` over `E`, split at the
infinite places, with unit group `G' = Aˣ`. Fix a finite set `Ω` of finite places and
identifications `E_v ⊗ A ≅ M_n(E_v)` at the finite places `v ∉ Ω` and at infinity. Only
finitely many irreducible summands of `L²([G'])` have, at every finite place outside `Ω`, the
unramified component of `π` and, at infinity, the archimedean component of `π`. This is the
Corollary of Deligne–Kazhdan–Vignéras (DKV), B.1.e, in the form needed for the members of a
Hilbert sum decomposition of `L²([G'])`. As in DKV, the hypothesis is that every local algebra
`E_v ⊗ A` with `v ∈ Ω` is a division algebra or a matrix algebra.

## Library notation

Throughout, `E : Type` is a number field, `r : ℕ`, and `n = r + 1`.

* `GLG = GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of E)` is the group
  scheme `GL_n` over `E`. As in the modules it imports, the module declares local instances
  `IsAffine` and `LocallyOfFiniteType` for `GLG`, and the `AddCommGroup` structures on the
  Library's spaces of functions on `GL_n(𝔸_E)` and on the spaces of operator realizations.
* `A : Type` carries `[Ring A] [Algebra E A] [FiniteDimensional E A]`, and
  `G' = FiniteAlgebraUnits.groupScheme (Module.finBasis E A)` is the affine group scheme of
  units of `A` (`Langlands/GroupScheme/FiniteAlgebraUnits.lean`). For a commutative
  `E`-algebra `R`, `FiniteAlgebraUnits.affinePointsEquiv (Module.finBasis E A) R` identifies
  the `R`-points of `G'` with `(R ⊗[E] A)ˣ`. `hG' : IsConnectedReductive G'` is a hypothesis.
  The right action on the canonical `L²` below requires it (through
  `canonicalMeasure_rightInvariant`); the space `L²([G'])` itself, formed from
  `canonicalMeasure`, does not.
* For a group scheme `G` (here `GLG` or `G'`), `[G] = RestrictionSplitCentre.CanonicalQuotient E G`
  is the Library's canonical quotient `A_G G(E) \ G(𝔸_E)`. Here `A_G` is the group of positive
  real points of the chosen split component of `Res_{E/ℚ} G`
  (`Langlands/Global/AdelicRestrictionSplitCentreCanonical.lean`). `L²([G])` is
  `Lp ℂ 2 (RestrictionSplitCentre.canonicalMeasure E G)`, and
  `RestrictionSplitCentre.canonicalL2RightAction E G centralSplitTorusCharacter hG` is the right
  regular representation of `G(𝔸_E) = AdelicGroupPoints E G` on it. Here
  `centralSplitTorusCharacter` is the published proof of `CentralSplitTorusCharacterStatement`.
  For `G'` the group `A_{G'}` is the group of positive real scalars, embedded diagonally at the
  infinite places.
* `FiniteCompletion E p` is the completion `E_p` at a finite place
  `p : Langlands.Global.FinitePlace E`, and `FiniteLocalGL E (r + 1) p` is `GL_n(E_p)` in the
  matrix model. `PlaceGroupPoints E G (.inr p)` is the group of `E_p`-points of `G`, and
  `AdelicGroupPoints.ofPlace E G (.inr p)` is its inclusion into `G(𝔸_E)`.
* `InfiniteAdeleRing E` is `E_∞ = ∏_{v | ∞} E_v ≅ E ⊗ ℝ`, and `InfiniteAdelicGL E (r + 1)` is
  `GL_n(E_∞)` in the matrix model. `InfiniteAdelicGroupPoints E G` is the group of
  `E_∞`-points of `G`, and `AdelicGroupPoints.ofInfinite E G` is its inclusion into `G(𝔸_E)`
  (finite component `1`).
* `S : CuspidalOperatorRealization E r` is a cuspidal realization of `GL_n`. We write `π` for
  the cuspidal automorphic representation it realizes. `S.realization.localRepresentation p`
  is the action of `GL_n(E_p)` on its space by right translation at `p`.
  `CuspidalPairPoles.IsTrivialOnSplitCentre S` says that its forms are invariant under `A_GLG`.
* From the module `Langlands.Automorphic.GeneralLinearDiscreteCuspidalHeckeIsolationStatement`
  (namespace `Langlands.Automorphic.DiscreteHeckeIsolation`):
  `Unramified.SphericalHeckeAlgebra (CompletionPadic.padicField p) r` is the spherical Hecke
  algebra of `GL_n(E_p)` for `K_p = GL_n(𝒪_p)`.
  `HasSphericalHeckeCharacterOn σ W χ` says that, for a representation `σ` of `GL_n(E_p)`,
  the subspace `W` contains a nonzero smooth `K_p`-fixed vector and the Hecke algebra acts on
  every smooth `K_p`-fixed vector of `W` by the character `χ`.
  `cuspidalRealizationClosure E r S` is the subspace `V_S` of `L²([GLG])`: the closure of the
  span of the `L²` classes of the forms of `S`. It needs `[CompactSpace (AdeleQuotient E)]`,
  which the statement assumes.
* `Langlands.Analysis.IsIrreducibleSubrepresentation ρ V` says that `V` is a nonzero closed
  `ρ`-invariant subspace whose only closed `ρ`-invariant subspaces are `0` and `V`.
* `IsHilbertSum ℂ (fun i => P i) (fun i => (P i).subtypeₗᵢ)` (Mathlib) says that the closed
  subspaces `P i` are pairwise orthogonal and that the closure of their sum is the whole space.

## The definitions

### `localChart p s`

For a finite place `p` and an `E_p`-algebra isomorphism
`s : E_p ⊗[E] A ≃ₐ[E_p] M_n(E_p)`, `localChart p s` is the group isomorphism from the
`E_p`-points of `G'` to `GL_n(E_p)`. It sends a point to its unit of `E_p ⊗[E] A`
(`FiniteAlgebraUnits.affinePointsEquiv` at `placeCompletion E (.inr p)`), then applies `s`
(`Units.mapEquiv`). The Library's `Langlands.Shimura.HarrisClozel.IsSplitLocalTransfer` uses the
same chart.

### `infiniteChart s`

For an `E_∞`-algebra isomorphism `s : E_∞ ⊗[E] A ≃ₐ[E_∞] M_n(E_∞)`, `infiniteChart s` is the
group isomorphism from `InfiniteAdelicGroupPoints E G'` to `GL_n(E_∞)` built in the same way.
The Library's `Langlands.Shimura.HarrisClozel.IsInfiniteTransfer` uses the same chart.

### `divisionL2LocalAction hG' p s` and `divisionL2InfiniteAction hG' s`

These are the representations of `GL_n(E_p)` and of `GL_n(E_∞)` on `L²([G'])`. Each is the
right regular representation composed with the inverse chart and the inclusion `ofPlace`
(respectively `ofInfinite`):

```
divisionL2LocalAction hG' p s g    = R'(ofPlace (.inr p) ((localChart p s)⁻¹ g)),
divisionL2InfiniteAction hG' s g  = R'(ofInfinite ((infiniteChart s)⁻¹ g)),
```

where `R' = canonicalL2RightAction E G' centralSplitTorusCharacter hG'`.

### `canonicalL2InfiniteAction E r`

This is the representation of `GL_n(E_∞)` on `L²([GLG])` in the matrix model. A matrix is
sent to the point of `GLG` with that matrix (`GroupScheme.GeneralLinear.affinePointsEquiv` over
`InfiniteAdeleRing E`), then included by `AdelicGroupPoints.ofInfinite`, then acted on by the
right regular representation. It is the archimedean analogue of the Library's
`canonicalL2LocalAction`.

### `IsInHeckeClass hG' S Ω s sInf T`

The data are a finite set `Ω` of finite places and charts `s p hp` at the finite places
`p ∉ Ω`. There is also an archimedean chart `sInf`. For a closed subspace `T` of `L²([G'])`,
the predicate says that `T` is in the Hecke class of `S` off `Ω`:

1. **Finite places.** For every finite place `p ∉ Ω` there is an algebra character
   `χ : SphericalHeckeAlgebra (padicField p) r →ₐ[ℂ] ℂ` with
   `HasSphericalHeckeCharacterOn (divisionL2LocalAction hG' p (s p hp)) T χ` and
   `HasSphericalHeckeCharacterOn (S.realization.localRepresentation p) ⊤ χ`. Both `T` and the
   space of `S` have nonzero vectors fixed by `K_p`, which on the `G'` side means fixed by
   `s_p⁻¹(GL_n(𝒪_p))`. The spherical Hecke algebra acts on all such vectors by the same
   character `χ`.
2. **Archimedean place.** There is a subspace `W ≤ V_S = cuspidalRealizationClosure E r S`
   with `IsIrreducibleSubrepresentation (canonicalL2InfiniteAction E r) W`, and there is a
   linear isometry `f : W →ₗᵢ[ℂ] L²([G'])` with values in `T` that intertwines the two
   archimedean actions. That is, `f y = divisionL2InfiniteAction hG' sInf g (f x)` whenever
   `y = canonicalL2InfiniteAction E r g x`. Equivalently, some irreducible unitary
   representation of `GL_n(E_∞)` has isometric equivariant embeddings into `V_S` and into
   `T`: the image of the first embedding is such a `W`.

## The statement

`DivisionAlgebraHeckeClassFinitenessStatement` is the following proposition. Let

* `E` be a number field with `[CompactSpace (AdeleQuotient E)]`, `r : ℕ`;
* `S : CuspidalOperatorRealization E r` with `CuspidalPairPoles.IsTrivialOnSplitCentre S`;
* `A` an `E`-algebra (`[Ring A] [Algebra E A] [FiniteDimensional E A]`) that is central
  (`Algebra.IsCentral E A`), of dimension `Module.finrank E A = (r + 1) ^ 2`, and a division
  algebra (`∀ a : A, a ≠ 0 → IsUnit a`);
* `hG' : IsConnectedReductive G'`;
* `Ω : Finset (Langlands.Global.FinitePlace E)` such that at every `v ∈ Ω` the algebra
  `E_v ⊗[E] A` is a division algebra (`∀ a, a ≠ 0 → IsUnit a`) or is isomorphic to
  `M_n(E_v)` as an `E_v`-algebra;
* `s` a family of `E_p`-algebra isomorphisms `E_p ⊗[E] A ≃ M_n(E_p)`, one for each finite
  place `p ∉ Ω`, and `sInf` an `E_∞`-algebra isomorphism `E_∞ ⊗[E] A ≃ M_n(E_∞)`;
* `I : Type` and `P : I → Submodule ℂ L²([G'])` with
  `IsIrreducibleSubrepresentation R' (P i)` for every `i` and
  `IsHilbertSum ℂ (fun i => P i) (fun i => (P i).subtypeₗᵢ)`.

Then the set `{i | IsInHeckeClass hG' S Ω s sInf (P i)}` is finite.

The charts force conditions on `A`: since an isomorphism `sInf` exists, `A` is split at every
infinite place. The places where `A` is ramified lie in `Ω`. Because of the condition at the
finite places, the Hecke class is empty unless `Ω` contains every finite place where `π` is
ramified.

## The hypothesis at the places of `Ω`

The statement follows the scope of the Corollary of DKV B.1.e. Each local group at a place
of `Ω` is `GL_n(E_v)` or the multiplicative group of a division algebra. These are the
two cases of the local level bounds used below. If `A` is division at two finite
places and split everywhere else, the local hypothesis holds for every `Ω`.

## Why the statement is true

The argument uses the functional equation and fixed-level multiplicity count of DKV B.1.d–e
and Appendix 2. At split places in `Ω` it uses a principal congruence bound derived from
Godement–Jacquet's local theory, the newform theorem for supercuspidal representations and
Casselman's lifting of fixed vectors. Fix a nontrivial additive character `ψ = ⊗_v ψ_v` of
`𝔸_E / E`. Let `T = P i` be a member in the Hecke class, and write
`σ_∞ = π_∞ ∘ infiniteChart sInf` for the archimedean component of `π` transported to `G'(E_∞)`.

1. **Factorization.** `T` is an irreducible unitary representation of `G'(𝔸_E)`. Since `A` is a
   division algebra, `[G']` is compact, so `T` is admissible and factors as a restricted tensor
   product `⊗'_v T_v` of irreducible unitary representations.
2. **Components outside `Ω`.** At infinity, `V_S ≅ π_∞ ⊗̂ π_f` is `π_∞`-isotypic for
   `GL_n(E_∞)`, and `T` is `T_∞`-isotypic for `G'(E_∞)`. An irreducible `W ≤ V_S` that embeds
   into `T` therefore gives `T_∞ ≅ σ_∞`. Take a finite place `p ∉ Ω`. Through the chart `s_p`,
   `T_p` has nonzero vectors fixed by `GL_n(𝒪_p)`, and the spherical Hecke algebra acts on them
   by the character `χ_p` of the unramified component `π_p`. An irreducible unramified
   representation is determined by its Hecke character (Getz–Hahn, Proposition 7.1.2), so
   `T_p ≅ π_p ∘ localChart p s_p`. Hence all members of the Hecke class have isomorphic
   components at every place outside `Ω`, infinite places included.
3. **The case `n = 1`.** Then `A ≅ E`, `G' ≅ GL_1`, and every member is a line spanned by a
   unitary character `ω` of `𝔸_E^× / E^× A_{G'}`. For two members `ω`, `ω'` of the Hecke class,
   the ratio `ω' ω⁻¹` is trivial on the subgroup of ideles away from `Ω` by step 2 and
   density of finite-support tuples. The ratio is also trivial on the diagonal `E^×`,
   whose projection to `∏_{v ∈ Ω} E_v^×` is dense by weak approximation. Thus `ω = ω'`.
   Each character spans a single line of `L²([G'])`, so at most one member is in the
   Hecke class. From now on `n ≥ 2`.
4. **Members are cuspidal in the sense of Godement–Jacquet.** For a division algebra
   (matrix size `m = 1`), Godement–Jacquet define the cuspidal space `𝒜_0(G, ω)` as the
   automorphic forms orthogonal to the reduced-norm characters `g ↦ ω_1(ν(g))` with
   `ω_1^n = ω` (printed pp. 144 and 146). For `ω = ω_T`, the central character of `T`,
   each character line lies in `L²([G'])` because `A_{G'}` is connected and `ω_T` is
   trivial there. If the orthogonal projection from `T` onto such a line is nonzero,
   it is injective because its kernel is closed and invariant. This would give
   `dim T = 1`. But the cuspidal `π` is generic (Shalika, as cited in DKV B.1.c, printed
   p. 79). Its archimedean component has a Whittaker functional transforming by a
   nontrivial character of the upper unipotent subgroup. That subgroup lies in the
   commutator subgroup for `n ≥ 2`, so `σ_∞ ≅ T_∞` has dimension greater than one.
   Consequently all the automorphic forms in `T` lie in `𝒜_0(G', ω_T)`.
5. **Comparison by the functional equation.** Godement–Jacquet Corollary 13.8
   (printed p. 179) gives the global functional equation for both `T` and `π`. Write
   `γ(s, τ, ψ_v) = ε(s, τ, ψ_v) L(1 − s, τ̃) / L(s, τ)` for the ratio from the local
   functional equation (Theorem 3.3, printed pp. 30–34). The matching components from
   step 2 give the same factors off `Ω`, including the factors of the contragredients.
   Comparing the global equations as in the proof of DKV B.1.e gives
   `∏_{v ∈ Ω} γ(s, T_v, ψ_v) = ∏_{v ∈ Ω} γ(s, π_v, ψ_v)`.

   Write `X_v = q_v^{−s}` and `ε(s, T_v, ψ_v) = c_v X_v^{m_v(T)}`. If
   `L(s, T̃_v) = 1 / P_{T̃_v}(X_v)` with `P_{T̃_v}(0) = 1`, put `d_v(T) = deg P_{T̃_v}`.
   The order of the local `γ`-factor at `X_v = 0` is `m_v(T) + d_v(T)`. The numerator
   polynomial `1 / L(s, T_v)` has constant term one and the denominator
   `P_{T̃_v}(q_v⁻¹ X_v⁻¹)` has order `−d_v(T)`. For the rational prime `ℓ` below `v`,
   write `q_v = ℓ^{f_v}`. The functions `s ↦ ℓ^{−s}` are algebraically independent
   for distinct primes, since distinct prime monomials give exponentials with
   distinct exponents. In the product equality, take the order at `ℓ^{−s} = 0` for
   each prime. This gives
   `∑_{v ∈ Ω, v | ℓ} f_v (m_v(T) + d_v(T)) = ∑_{v ∈ Ω, v | ℓ} f_v (m_v(π) + d_v(π))`.
6. **Local conductor and level bounds.** For an irreducible local representation `τ`
   at `v`, let `a(τ)` be the exponent of `q_v^{−s}` in `ε(s, τ, ψ_v⁰)` for an additive
   character `ψ_v⁰` of conductor zero, trivial on `𝒪_v` and nontrivial on
   `𝔭_v⁻¹`. If `ψ_v(x) = ψ_v⁰(b_v x)`, the change-of-character formula in DKV B.1.e
   (printed p. 80) gives `m_v(T) = a(T_v) + n ord_v(b_v)`.

   At a division place the lemma of DKV B.1.d gives `a(τ) ≥ n − 1`. The groups
   `K_{n−1} = 𝒪_D^×` and `K_m = 1 + 𝔓_D^{m − n + 1}` for `m ≥ n` have the
   property that `τ` has a nonzero `K_m`-fixed vector when `m ≥ a(τ)`.

   At a split place, write `F = E_v` and `X = q_v^{−s}`. An arbitrary irreducible
   admissible `τ` embeds in the normalized parabolic induction `J` of a tensor
   product of supercuspidal `ρ_j` of `GL_{n_j}(F)` from a standard block parabolic
   (Casselman, Theorem 5.1.2). Godement–Jacquet Theorem 3.4 gives multiplicativity
   of the `ε`-factor for `J`. By the subquotient calculation in §3, printed p. 34,
   `γ(s, τ, ψ_v⁰) = γ(s, J, ψ_v⁰)`, and the ratios `L(s, τ)/L(s, J)` and
   `L(s, τ̃)/L(s, J̃)` are polynomials in `X` with constant term one. If `Q(X)` is
   the latter polynomial, comparing orders at `X = 0` gives
   `a(τ) = ∑_j a(ρ_j) + deg Q`.

   Each `ρ_j` is generic (Bernstein–Zelevinsky, §§3.5 and 4.4). The newform theorem
   of Jacquet–Piatetski-Shapiro–Shalika (§5.1, with Jacquet's 2012 correction) gives
   `a(ρ_j) ≥ 0` and a nonzero fixed vector under the newform subgroup at that
   exponent. For `n_j = 1` this is the character conductor criterion in §1.1.
   In particular `a(τ) ≥ 0`. Let `K_d(M)` be the kernel of reduction modulo
   `𝔭_v^M` on `GL_d(𝒪_v)`. For `M ≥ max(1, a(τ))`, each `K_{n_j}(M)` lies in
   the corresponding newform subgroup of `ρ_j`. The subgroup `K_n(M)` has an
   Iwahori factorization for the parabolic by block elimination and meets its
   block diagonal Levi in `∏_j K_{n_j}(M)`. Casselman Proposition 3.3.6 now gives
   a nonzero `K_n(M)`-fixed vector in the subrepresentation `τ` of `J`. This bound
   holds for every irreducible admissible `τ` of `GL_n(F)`.
7. **A common level.** Step 6 bounds every `m_v(T)` below, and each `d_v(T)` is
   nonnegative. Since `f_v > 0`, the weighted sums in step 5 bound each `m_v(T)`
   above. The same holds for `a(T_v)` by the fixed change-of-character shift.
   Thus the subgroups of step 6 give a single compact open subgroup `K_Ω` of
   `∏_{v ∈ Ω} G'(E_v)` under which every member has a nonzero fixed vector.

   At all places outside a finite set `Ω'` containing `Ω`, use reference
   isomorphisms `r_p : E_p ⊗[E] A ≃ M_n(E_p)` for which the defining compact
   subgroups of the restricted product are `K'_p = r_p⁻¹(GL_n(𝒪_p))`. By
   Skolem–Noether, `s_p = Ad(g_p) ∘ r_p` for some `g_p ∈ GL_n(E_p)`, so
   `T_p ∘ r_p⁻¹ ≅ T_p ∘ s_p⁻¹ ≅ π_p` is unramified and `T_p` has nonzero
   `K'_p`-fixed vectors. At the finitely many `p ∈ Ω' ∖ Ω`, `T_p` has nonzero
   vectors fixed by `s_p⁻¹(GL_n(𝒪_p))`. The restricted tensor product gives
   a nonzero fixed vector in every member for the compact open subgroup
   `K = K_Ω × ∏_{p ∈ Ω' ∖ Ω} s_p⁻¹(GL_n(𝒪_p)) × ∏_{p ∉ Ω'} K'_p` of
   `G'(𝔸_{E,f})`.
8. **Finiteness (DKV Appendix 2).** For finite adeles `c`, let `Γ_c` be the projection to
   `G'(E_∞)` of `G'(E) ∩ (G'(E_∞) × c K c⁻¹)`. The group `G'(𝔸_E)` is the union of finitely
   many double cosets `G'(E) (G'(E_∞) × c K)`, so `f ↦ (f(· c))_c` identifies `L²([G'])^K` with a
   finite sum of spaces `L²(A_{G'} Γ_c \ G'(E_∞))` with compact quotients. In each of them
   `σ_∞` has finite multiplicity, so `Hom_{G'(E_∞)}(σ_∞, L²([G'])^K)` is finite-dimensional;
   this is the count of intertwiners in DKV Appendix 2 (printed pp. 108–109). Each member `T`
   of the Hecke class gives a nonzero intertwining map from `σ_∞` into
   `T^K ≅ T_∞ ⊗ (T_f)^K`. The members are pairwise orthogonal, so maps with values in distinct
   members are linearly independent. Hence the Hecke class has at most
   `dim Hom_{G'(E_∞)}(σ_∞, L²([G'])^K)` members.

## Derived content and comparison with the sources

* **The Hecke class.** DKV fix a representation `π^S` of `G^S` and consider the automorphic
  `π_S ⊗ π^S`, that is, isomorphism of all components outside `S`. Here the components outside
  `Ω` are prescribed by `π`, transported by the charts. At the finite places they are prescribed
  by spherical Hecke characters, which is equivalent for irreducible representations (step 2).
  At infinity they are prescribed by a common irreducible constituent of `V_S` and of `T`, as in
  `IsInfiniteTransfer`. DKV's `S` is the set of places where `D` ramifies, supposed finite
  (B.1.a). Here it is replaced by any finite set `Ω` of finite places with the hypothesis of the
  Corollary, and the archimedean chart expresses that `A` is split at the infinite places.
* **Hilbert sum members.** DKV state that "le nombre de `π_S` est fini", counting isomorphism
  classes, and Appendix 2 bounds the multiplicities. The statement counts the members of an
  arbitrary Hilbert sum decomposition of `L²([G'])` into irreducible closed invariant subspaces.
  For the positive rational quotient of a group scheme, when that quotient is compact, the
  Library's `GroupSchemeCompactQuotientL2DecompositionStatement` states that such a
  decomposition exists, with finite multiplicities. Counting members combines the finiteness of
  the classes with the finiteness of the multiplicities.
* **Conductor bound.** The functional-equation comparison of DKV B.1.e gives the product
  of local ratios in step 5. Taking orders of that product gives the conductor bound
  with the nonnegative dual Euler-factor degrees included. At a split place, the
  bound in step 6 uses principal congruence subgroups for arbitrary irreducibles.
  The newform criterion cited in DKV B.1.d applies to generic representations.
* **The quotient.** DKV work in `L²(G(F) \ G(𝔸), ω)` with a unitary central character `ω`. The
  statement uses the Library's canonical `L²([G']) = L²(A_{G'} G'(E) \ G'(𝔸_E))`. Since
  `Z(𝔸) / A_{G'} Z(E)` is compact, `L²([G'])` is the Hilbert sum of the spaces with fixed central
  character `ω`, `ω` trivial on `A_{G'}`.
* **Other hypotheses.** `hG'` and `centralSplitTorusCharacter` are needed to form the right
  action on the canonical `L²`; the space `L²([G'])` is formed from `canonicalMeasure` alone.
  `[CompactSpace (AdeleQuotient E)]` and `IsTrivialOnSplitCentre S` are those of
  `GeneralLinearDiscreteCuspidalHeckeIsolationStatement`, whose `V_S` is used here.
* The charts and actions `localChart`, `infiniteChart`, `divisionL2LocalAction`,
  `divisionL2InfiniteAction` and `canonicalL2InfiniteAction` are internal packaging of Library
  constructions (`FiniteAlgebraUnits.affinePointsEquiv`, `GeneralLinear.affinePointsEquiv`,
  `AdelicGroupPoints.ofPlace`, `AdelicGroupPoints.ofInfinite`, `canonicalL2RightAction`).

## Sources

* P. Deligne, D. Kazhdan, M.-F. Vignéras, *Représentations des algèbres centrales simples
  p-adiques*, in Bernstein–Deligne–Kazhdan–Vignéras, *Représentations des groupes réductifs sur
  un corps local*, Hermann, 1984 (registered `bdkv-1984-representations-local-field`, printed
  page = PDF page − 4). B.1.a, printed p. 78, gives the split and inner form setting with
  finite ramification set. B.1.c, printed p. 79, cites Shalika for genericity in the
  cuspidal spectrum of `GL_n`. The lemma in B.1.d, printed pp. 79–80, gives the conductor
  criterion for the subgroups `K_m` of `D^×` and invokes the newform subgroups for `GL_n`.
  B.1.e, printed pp. 80–81, compares the global functional equations, gives the
  change-of-character formula and states the finiteness corollary. Appendix 2, printed
  pp. 108–109, gives the fixed-level double cosets and the intertwiner count.
* R. Godement, H. Jacquet, *Zeta Functions of Simple Algebras*, Lecture Notes in Mathematics
  260, Springer, 1972 (registered `godement-jacquet-1972-zeta-simple-algebras`, printed page =
  PDF page − 10). Theorem 3.3, printed pp. 30–31, gives the nonarchimedean factors.
  Printed p. 34 gives the polynomial ratios and the equality of `γ`-factors for an
  irreducible subquotient. Theorem 3.4, printed p. 36, gives multiplicativity for parabolic
  induction. Printed pp. 144 and 146 define `𝒜_0(G, ω)` and identify it for division
  algebras. Theorem 13.8 and Corollary 13.8, printed p. 179, give the global functional
  equation for irreducible representations in that space.
* I. N. Bernstein, A. V. Zelevinsky, *Induced representations of reductive p-adic groups I*,
  Ann. Sci. Éc. Norm. Supér. 10 (1977), 441–472 (registered
  `bernstein-zelevinsky-1977-induced-i`). Sections 3.5 and 4.4, printed pp. 452 and 454,
  identify the top derivative with the Whittaker quotient and give its nonvanishing
  for irreducible supercuspidals.
* H. Jacquet, I. I. Piatetski-Shapiro, J. Shalika, *Conducteur des représentations du groupe
  linéaire*, Math. Ann. 256 (1981), 199–214 (registered `jpss-1981-conductor`).
  Section 1.1, printed p. 199, specifies the conductor-zero additive character and
  the rank-one case. Section 5.1, printed p. 211, gives the newform criterion for
  generic irreducibles. H. Jacquet, *A correction to Conducteur des représentations du
  groupe linéaire*, Pacific J. Math. 260 (2012), 515–525 (registered
  `jacquet-2012-conductor-correction`), gives the corrected proof of essential-vector
  existence in Theorem 1, printed p. 517.
* W. Casselman, *Introduction to the theory of admissible representations of p-adic
  reductive groups*, draft of 1 May 1995 (registered `casselman-1995-admissible-representations`).
  Theorem 5.1.2, printed p. 46, gives the embedding into a supercuspidally induced
  representation. Proposition 3.3.6, printed p. 36, lifts the existence of fixed
  vectors from the inducing representation to a nonzero subrepresentation of its
  parabolic induction.
* J. R. Getz, H. Hahn, *An Introduction to Automorphic Representations* (2024) (registered
  `getz-hahn-2024-automorphic-representations`): Definition 7.1.1 and Proposition 7.1.2,
  printed p. 184 (an unramified representation is determined by its Hecke character).
