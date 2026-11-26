# The normalized Harish-Chandra transfer of the center to a Levi subgroup

Module `Langlands.Global.AdelicLeviCenterTransferStatement` contains one `Prop`-valued
definition, `Langlands.Global.LeviRestrictionCenterTransferStatement`, and no theorems. It
states, for two Weyl-conjugate parabolics, that one element of the enveloping algebra of the
common Levi subgroup at infinity realizes the action of a central element on normalized Levi
restrictions for both parabolics. This file does not prove the statement.

## Data and hypotheses

The statement quantifies over:

- a number field `F` and group schemes `G, P, M, U, Q, M', V` over `F`, with `G`, `P`, `Q`, `M'`
  affine and `P`, `Q` locally of finite type;
- `p : P → G` with `IsParabolicSubgroup p`, a geometric unipotent radical `iU : U → P`
  (`LeviSubgroup.IsGeometricUnipotentRadical iU`) and a rational Levi subgroup `l : M → P`
  (`IsRationalLeviSubgroup l`);
- the same data `q : Q → G`, `iV : V → Q`, `l' : M' → Q` for a second parabolic;
- a Weyl conjugation `(w, c)`, `IsWeylConjugation p l q l' w c`: `w` is a rational point of `G`
  and the isomorphism `c : M' → M` satisfies `l(c(m')) = w⁻¹ l'(m') w` in `G`;
- `IsConnectedReductive G`;
- smooth structures `hsmooth` on `G` and `hsmooth'` on `M'` (`SmoothOfRelativeDimension`) and the
  commutator data `hcalc`, `hcalc'` of the Library's enveloping actions;
- an element `z` of `AdelicEnvelopingCenter F G hsmooth`, the center `𝔷` of the enveloping algebra
  of the complexified Lie algebra of `G(F_∞)`.

Write `G_∞ = InfiniteAdelicGroupPoints F G`, `M'_∞ = InfiniteAdelicGroupPoints F M'`, and
`ι_Q, ι_P : M'_∞ → G_∞` for the point maps of `l' ≫ q` and `c ≫ l ≫ p`, so that
`ι_P(m) = w⁻¹ ι_Q(m) w`. The normalizing factors are

- `δ_Q(m)^{-1/2} = parameterPower F Q (-halfModulusParameter F Q) (l'(m))`,
- `δ_P(c(m))^{-1/2} = parameterPower F P (-halfModulusParameter F P) (l(c(m)))`,

where `m` is viewed as an adelic point with trivial finite components and
`halfModulusParameter F P = ½ ⊗ det(Ad | Lie P)` is `ρ_P`. On points of a Levi subgroup,
`|det(Ad | Lie P)|` is the modulus of the conjugation action on the unipotent radical.

## Conclusion

There is `y : AdelicEnvelopingAlgebra F M' hsmooth'` such that, for every `g ∈ G_∞`:

1. for every plot-smooth `f : G_∞ → ℂ` with `f(v x) = f(x)` for all `v` in the image of `V(F_∞)`,
   and every proof `h` that `m ↦ δ_Q(m)^{-1/2} f(ι_Q(m) g)` is plot-smooth on `M'_∞`,
   `plotSmoothEnvelopingAction F M' hsmooth' hcalc' y` sends this function to
   `m ↦ δ_Q(m)^{-1/2} (z f)(ι_Q(m) g)`, where `z f` is `plotSmoothCenterAction F G hsmooth hcalc z`
   applied to `f`;
2. for every plot-smooth `f : G_∞ → ℂ` with `f(u x) = f(x)` for all `u` in the image of `U(F_∞)`,
   and every proof that `m ↦ δ_P(c(m))^{-1/2} f(ι_P(m) g)` is plot-smooth on `M'_∞`, the same `y`
   sends this function to `m ↦ δ_P(c(m))^{-1/2} (z f)(ι_P(m) g)`.

The element `y` depends on `z` but not on `g` or `f`. The restricted functions are always
plot-smooth: they are compositions of plot-smooth functions with point maps of morphisms of group
schemes, right translations and characters. The statement quantifies over the proofs, so that it
needs no separate smoothness lemma.

## Mathematical content

Let `𝔤`, `𝔪'` be the complexified Lie algebras of `G_∞`, `M'_∞`, and `𝔳` that of `V(F_∞)`. Two
differentiated actions are involved. The Library's enveloping action is the right action
`R(X) f(x) = d/dt f(x exp(tX))` at `t = 0`. The left action is
`L(X) f(x) = d/dt f(exp(−tX) x)` at `t = 0`. Both extend to the enveloping algebras. For a
central `z`, `R(z) = L(S z)`, where `S` is the antipode of `U(𝔤)`. This uses that `Ad(G_∞)` fixes
`𝔷`, which holds because `G` is connected.

Let `𝔳̄` be the opposite nilradical. By Poincaré–Birkhoff–Witt,
`U(𝔤) = U(𝔪') ⊕ (𝔳̄ U(𝔤) + U(𝔤) 𝔳)`. The second component of a central element lies in
`U(𝔤) 𝔳`, and its `U(𝔪')` component `μ_𝔳(S z)` lies in the center of `U(𝔪')` (Knapp–Vogan,
Lemma 4.123). On a function left invariant under `V(F_∞)` the term in
`U(𝔤) 𝔳` acts by `0` under `L`. So `L(S z)` acts on the restrictions `m ↦ f(m g)` through
`μ_𝔳(S z)` and the left action of `M'_∞`. On the Levi, differentiating `δ_Q^{-1/2}` under `L` adds
`ρ_𝔳(X)`. The normalized left operator is therefore `τ_𝔳 μ_𝔳(S z)`, with
`τ_𝔳(X) = X − ρ_𝔳(X)`, the shift (4.124) of Knapp–Vogan. Converting back to the right action of
`M'_∞` gives clause 1 with `y = S_{𝔪'}(τ_𝔳 μ_𝔳(S z))`, where `S_{𝔪'}` is the antipode of `U(𝔪')`.

The normalized map `τ_𝔳 ∘ μ_𝔳` restricted to `𝔷` is `γ_{𝔪'}⁻¹ ∘ γ_𝔤`, where `γ` denotes the
Harish-Chandra isomorphisms onto Weyl group invariants (Knapp–Vogan, Proposition 4.129 (c)). It
therefore does not depend on the parabolic containing `M'` as a Levi subgroup. Apply this to the
parabolic `w P w⁻¹`, whose Levi subgroup is `M'`. Transport along `Ad(w)`, which fixes `𝔷`, then
gives clause 2 with the same element `y`.

Bernstein–Lapid, in the proof of the Lemma in §8.2, use the normalized restriction formula (6.5)
and carry a whole ideal `I` of `𝔷^M` to `w I ⊆ 𝔷^{M_Q}`. A single operator `y` serving both
parabolics for a prescribed `z` is a further consequence of Knapp–Vogan 4.129 (c) and conjugation
by `w`. It is what this statement asserts.

## Sources

- C. Mœglin and J.-L. Waldspurger, *Spectral decomposition and Eisenstein series*, Cambridge
  University Press, 1995 (`moeglin-waldspurger-1995-spectral-decomposition`), I.2.17, printed
  pp. 37–38 (chapter PDF `05.2_pp_18_40_Automorphic_forms_growth_constant_terms.pdf`,
  pp. 20–21). It gives a homomorphism `i : 𝔷 → 𝔷_M` relating the right action of `𝔷` on
  functions on `U(𝔸) \ G` to the left action of `𝔷_M` on their restrictions
  `φ' = m_P^{-ρ_P} φ`. The printed display `z·φ = i(z)·φ'` omits the normalization on the left.
  With it restored, the compatibility reads `(z·φ)' = i(z)·φ'`. For `N_P f(m) = δ_P(m)^{-1/2} f(m g)`
  this is `N_P(R(z) f) = i(z)·N_P f`, with `𝔷_M` acting by left translation. The left and right
  actions of `𝔷_M` differ by an automorphism of `𝔷_M` (p. 38).
- A. W. Knapp and D. A. Vogan, *Cohomological Induction and Unitary Representations*, Princeton
  University Press, 1995 (`knapp-vogan-1995-cohomological-induction`). Lemma 4.123, printed p. 301,
  gives the decomposition and the central component. The definitions (4.124)–(4.128), printed
  pp. 302–303, give the shift `τ_𝔲` and `γ̃_{𝔤/𝔩} = τ_𝔲 ∘ μ_{𝔤/𝔩}`. Proposition 4.129, printed
  p. 303, proves `γ̃_{𝔤/𝔩} = γ_𝔩⁻¹ ∘ γ` "independent of `𝔲`". The full-book PDF pages are the
  printed pages plus 22.
- J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer.
  Math. Soc. 37 (2024) (`bernstein-lapid-2024-meromorphic-continuation-eisenstein`): (6.5),
  p. 201 (TeX lines 1242–1257), and the proof of the Lemma in §8.2, p. 222 (TeX lines 3274–3290).

## Provenance

The statement is derived from these sources. The formulation with plot-smooth functions on
`G(F_∞)`, the Library's right enveloping actions and the parameters `ρ_P`, `ρ_Q` is internal to the
Library. Clause 1 is the normalized Levi transfer of Mœglin–Waldspurger I.2.17, with the
normalization on both sides. Clause 2 with the same element `y` follows from the independence of
the parabolic in Knapp–Vogan 4.129 (c) and conjugation by `w`. Bernstein–Lapid §8.2 use (6.5) and
the transport of a Levi ideal. The single shared operator for each `z` is a derived refinement of
that argument, which the reduction of the uniform center ideal uses.
