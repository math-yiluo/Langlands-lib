# Standardization of intertwining operators: proof

Module `Langlands.Global.AdelicIntertwiningStandardizationProof`. Its main theorem,
`Langlands.Global.intertwiningStandardization`, proves
`Langlands.Global.IntertwiningStandardizationStatement.{u}` (module
`Langlands.Global.AdelicIntertwiningElementaryChainStatement`) without change. The module
also proves auxiliary lemmas, described first. The proof uses only the Library's published
results, and its axioms are `propext`, `Classical.choice` and `Quot.sound`.

Conventions. For a rational point `s` of `G`, `(G.innerIso s).hom` is the inner automorphism
`x ↦ s x s⁻¹`. So `q ≫ (G.innerIso s).hom` is the parabolic `sQs⁻¹`, presented by the same
group `Q`. `innerAdelicPoint F G s` is the image of `s` in `G(𝔸)`. For a parabolic `p` and a
compact `K` with `hK : IsIwasawaCompact p K`, `hK.height` is the height `H_P` and
`hK.heightPower λ g = exp ⟨λ, H_P(g)⟩` is `m_P(g)^λ`. The operator
`hK.intertwiningOperator hQ … w φ λ g` is `m_Q(g)^{-wλ}` times the intertwining integral, where
`wλ = weylParameter l c π' λ`. Composites are written in diagrammatic order, as in Lean:
`e.hom ≫ p` is `p ∘ e`.

## Auxiliary lemmas

### Height powers and transport of operators (namespace `AdelicGroupPoints`)

- `IsIwasawaCompact.heightPower_restrict_of_comp_eq`. Let `f : P₁ → P` be a map with
  `f ≫ p = p₁`. Then the height power of `p₁` at the restriction `parameterRestrict f λ` equals
  the height power of `p` at `λ`. This is the published `IsIwasawaCompact.heightPower_restrict`
  after substituting `p₁ = f ≫ p`.
- `IsIwasawaCompact.heightPower_neg_mul`, `IsIwasawaCompact.heightPower_mul_neg`:
  `m_P(g)^{-λ} m_P(g)^λ = 1`, from `exp(-x) exp(x) = 1`.
- `weylParameter_parameterRestrict_eq`. Let `jP : P₁ → P` and `jQ : Q₁ → Q` satisfy
  `π₁ ≫ c₁ ≫ l₁ ≫ jP = jQ ≫ π ≫ c ≫ l`. Then the Weyl parameter of the restricted
  parameter is the restriction of the Weyl parameter:
  `weylParameter l₁ c₁ π₁ (parameterRestrict jP λ) = parameterRestrict jQ (weylParameter l c π λ)`.
  On pure tensors both sides are restriction of a character along the two equal composites;
  the general case follows by additivity.
- `IsIwasawaCompact.intertwiningOperator_eq_of_transport`. Suppose that
  - `P₁, Q₁` are related to `P, Q` by maps over `G` (`jP ≫ p = p₁`, `jQ ≫ q = q₁`);
  - the unipotent radicals have the same images (`iU ≫ p` and `iU₁ ≫ p₁`, `iV ≫ q` and
    `iV₁ ≫ q₁`);
  - the Levi data satisfy the identity above.

  Then the operator for `(P, Q)` at `λ` equals the operator for `(P₁, Q₁)` at
  `parameterRestrict jP λ`, with the same `K`, `w` and `φ`. The Weyl parameters correspond by
  the previous lemma, and the target height powers agree by the first lemma. The intertwining
  integrals agree by the published
  `IsIwasawaCompact.intertwiningIntegral_eq_of_range_eq_of_twist` and
  `IsIwasawaCompact.parameterTwist_restrict_of_comp_eq` (module
  `Langlands.Global.AdelicEisensteinParabolicRangeTransport`).
- `parameterRestrictIsoEquiv e`, for an isomorphism `e : H' ≅ H`, is restriction of complex
  parameters along `e.hom`, as a linear isomorphism `X^*(H) ⊗ ℂ ≃ X^*(H') ⊗ ℂ`. Its inverse is
  restriction along `e.inv`. `parameterRestrictIsoEquiv_apply` records that it is restriction
  along `e.hom`.

### Root forms under restriction

`rootFunctional_parameterRestrict_eq_of_comp_eq`. Take two compatible presentations
`⟨T, i, ν, J, f⟩` of `(p, l, a)` and `⟨T, i, ν, J, f'⟩` of `(p', l', a')`. They have the same
maximal split torus, generic cocharacter and set of simple roots. Let `j : P' → P` satisfy
`j ≫ p = p'`, and let `β` be a character of `T`. Then the root form of `f' ≫ β` at
`parameterRestrict j λ` equals the root form of `f ≫ β` at `λ`. Both equal
`B_T(λ|_T, β)`, where `B_T` is the Weyl-invariant form of the common torus.

For a real parameter `x` of `P`, the real root form is `B_A(x|_A, f ≫ β)`. Here `B_A` is the
form `weylInducedCharacterForm` on the split component. The published compatibility
`Langlands.Plancherel.weylInducedCharacterForm_compatible` gives
`B_A(x|_A, f ≫ β) = B_T(L(x|_A), β)`, with `L` the orthogonal lift. The published
`eisensteinAmbientParameterLift` identifies `L(x|_A)` with the restriction `x|_T` of `x` to the
torus through a lift `t : T → M` with `t ≫ l ≫ p = i`
(`ParabolicRootPresentation.exists_leviTorusLift`). The torus lifts of the two presentations
satisfy `(t' ≫ l') ≫ j = t ≫ l`, because `p` is a monomorphism. So the restriction of
`parameterRestrict j λ` to `T` through `t' ≫ l'` is the restriction of `λ` through `t ≫ l`.
The complex root forms are the complex-linear extensions, and the identity follows on pure
tensors and then by additivity.

### Unipotent radicals

`range_comp_unipotentRadical_eq_of_iso`. Let `e : P' ≅ P` satisfy `e.hom ≫ p = p'`. Then
unipotent radicals `iU` of `P` and `iU'` of `P'` have the same image in the ambient group:
`range (iU ≫ p) = range (iU' ≫ p')`. The published uniqueness `IsUnipotentRadical.range_eq`
compares `iU` with `iU' ≫ e.hom` inside `P`, and the result is pushed forward along `p`.

### Rational conjugation onto a standard parabolic and its standard Levi

`StandardParabolicFamily.exists_standardConjugate`. Let `fam` be a standard parabolic family,
`q : Q → G` a parabolic with unipotent radical `iV : V → Q` (`IsGeometricUnipotentRadical`)
and `l' : M' → Q` a rational Levi. Then there are:

- a standard index `I'` and a rational point `s`;
- an isomorphism `eQ : P_{I'} ≅ Q` with `eQ.hom ≫ q ≫ (G.innerIso s).hom = fam.p I'`;
- an isomorphism `κ : M_{I'} ≅ M'` with `κ.hom ≫ l' = fam.l I' ≫ eQ.hom`;

and `range (iV ≫ q ≫ (G.innerIso s).hom) = range (fam.iU I' ≫ fam.p I')`. In words, `sQs⁻¹`
is the standard parabolic `P_{I'}`, and `sM's⁻¹` is its standard Levi.

Proof:

1. The published `parabolicDynamic` (Milne, *Algebraic Groups* (2017), Theorem 25.1) writes the
   image of `q` as a dynamic parabolic `P(χ)`.
2. The published `standardParabolicClassification` (Borel–Tits, *Groupes réductifs* (1965),
   §5.14) gives a set `B` of simple roots and a rational point `g` with
   `P(χ) = g⁻¹ P_B g`. Then `q ≫ (G.innerIso g).hom` and `fam.p I'`, with `I' = B`, have the
   same image, and `IsClosedSubgroup.sourceIsoOfRangeEq` gives `eQ₁ : P_{I'} ≅ Q` over it.
3. `fam.l I' ≫ eQ₁.hom` is a rational Levi of `Q` (`IsRationalLeviSubgroup.comp_iso`). The
   published `rationalLeviConjugacy` (Borel–Tits, Corollary 3.14) gives a rational point `u`
   of `V` and `e' : M' ≅ M_{I'}`, with `x = iV(u)`, such that
   `l' ≫ int_Q(x) = e'.hom ≫ fam.l I' ≫ eQ₁.hom`.
4. Inner automorphisms commute with `q`: `int_Q(x) ≫ q = q ≫ int(q(x))`
   (`innerIso_hom_comp`). With `s = g · q(x)` this gives
   `q ≫ int(s) = int_Q(x) ≫ q ≫ int(g)` (`innerIso_mul_hom`).
5. So `eQ = eQ₁ ≪≫ int_Q(x)⁻¹` and `κ = e'⁻¹` satisfy both identities. The radicals have the
   same image by the previous lemma.

## The main theorem

The setting is that of the statement. `r` is a presentation of `P = MU` through `a : A → M`,
`q : Q → G` is a parabolic with radical `iV` and rational Levi `l'`, `(w, c)` presents an
element of `W(P, Q)`, and `π'` is a retraction of `l'`. The compact `K` satisfies
`P(𝔸)K = Q(𝔸)K = G(𝔸)`, and `φ` is automorphic on `U(𝔸)M(F) \ G(𝔸)` for `K_∞`. The proof
proceeds as follows.

1. **Standard family.** `fam = StandardParabolicFamily.ofMaximalSplitTorus` is built on the
   presentation's maximal split torus and generic cocharacter. With `I = r.data.J`, the
   compatibility fields give `range (fam.p I) = range p` and
   `range (fam.l I ≫ fam.p I) = range (l ≫ p)`. `IsClosedSubgroup.sourceIsoOfRangeEq` gives
   `e : P_I ≅ P` with `e.hom ≫ p = fam.p I` and `δ : M_I ≅ M` with
   `δ.hom ≫ l = fam.l I ≫ e.hom`; the latter identity holds because `p` is a monomorphism. The
   radicals have the same image, so the inducing subgroups agree:
   `parabolicQuotientSubgroup F (fam.p I) (fam.iU I) (fam.l I) = parabolicQuotientSubgroup F p iU l`
   (`parabolicQuotientSubgroup_eq_of_range_eq`). The parameter isomorphism is
   `iota = parameterRestrictIsoEquiv e`, restriction along `e.hom`.
2. **Standard target.** `StandardParabolicFamily.exists_standardConjugate` gives `I'`, `s`, `eQ`
   and `κ`. Put `Q' = sQs⁻¹`, presented by `q ≫ (G.innerIso s).hom`; it is a parabolic
   (`IsParabolicSubgroup.comp_iso`). The published `intertwiningConjugateTarget` (module
   `Langlands.Global.AdelicIntertwiningConjugateTarget`) gives three things:
   `IsWeylConjugation p l (q ≫ (G.innerIso s).hom) l' (s * w) c`, an Iwasawa property `hQ'`
   of `K` for `Q'`, and for all `λ`, `g`
   `M_{Q'}(sw, λ)φ(s g) = m_{Q'}(s)^{-wλ} M_Q(w, λ)φ(g)`. So
   `M_Q(w, λ)φ(g) = m_{Q'}(s)^{wλ} M_{Q'}(sw, λ)φ(s g)`.
3. **The compact `K₀`.** The published `iwasawaWithInfiniteCompact` is applied to the minimal
   standard parabolic `P_∅` and to the archimedean factor `K.comap ofInfinite` of `K`. That
   factor is maximal compact (`isMaximalCompact_comap_ofInfinite`). The result is a maximal
   compact `K₀` with `P_∅(𝔸)K₀ = G(𝔸)` and the same archimedean factor as `K`. Every standard
   parabolic contains `P_∅` (`StandardParabolicFamily.le_iff_range_le`), so
   `P_J(𝔸)K₀ = G(𝔸)` for every `J` (`IsParabolicIwasawaCompact.of_comp`). Through the equal
   images, `K₀` is Iwasawa for `P` and for `Q'` (`IsIwasawaCompact.of_range_eq`). Both compacts
   are maximal, so equal archimedean factors give equal infinite projections
   (`IsMaximalCompactSubgroup.comap_ofInfinite_eq_map_infinite`).
4. **Finite change of compact.** The published `eisensteinFiniteCompactOperatorComparison` is
   applied to `P`, `r`, the target `Q'` with `iV`, `l'`, `(s * w, c)`, `π'`, and the compacts
   `K`, `K₀`. Its hypotheses are those of the statement, together with the facts of steps 2
   and 3. It gives a finite set `S` of real dual elements, functions `cut v` automorphic on
   `U(𝔸)M(F) \ G(𝔸)` for `K₀∞`, and a threshold `R`. For every `R`-regular `λ` and every `y`,
   `M^K_{Q'}(sw, λ)φ(y) m^K_{Q'}(y)^{wλ} = ∑_{v ∈ S} e^{⟨λ, v⟩} M^{K₀}_{Q'}(sw, λ)(cut v)(y) m^{K₀}_{Q'}(y)^{wλ}`.
5. **Heights at the target.** The intersection of `K₀` with `K` is open in `K₀`
   (`IsMaximalCompactSubgroup.isOpen_intersection_of_infinite_eq`). So
   `Δ(y) = H^{K₀}_{Q'}(y) − H^K_{Q'}(y)` takes values in a finite set `D`
   (`IsIwasawaCompact.finite_range_height_sub`). Hence
   `m^{K₀}_{Q'}(y)^{μ} m^K_{Q'}(y)^{-μ} = e^{⟨μ, Δ(y)⟩} = ∑_{d ∈ D} 1[Δ(y) = d] e^{⟨μ, d⟩}`.
6. **Standard operators.** Put `w₀ = s * w`, `c₀ = κ.hom ≫ c ≫ δ.inv` and
   `π₀ = eQ.hom ≫ π' ≫ κ.inv`.
   - `fam.l I' ≫ π₀ = 𝟙`, from `κ.hom ≫ l' = fam.l I' ≫ eQ.hom` and `l' ≫ π' = 𝟙`.
   - `IsWeylConjugation (fam.p I) (fam.l I) (fam.p I') (fam.l I') w₀ c₀` holds because `c₀`
     is an isomorphism and `c₀ ≫ fam.l I ≫ fam.p I = κ.hom ≫ c ≫ l ≫ p`, which is
     `fam.l I' ≫ fam.p I' ≫ (G.innerIso w₀).inv` by step 2 and the properties of `eQ` and
     `κ`.
   - `π₀ ≫ c₀ ≫ fam.l I ≫ e.hom = eQ.hom ≫ π' ≫ c ≫ l`.

   So `IsIwasawaCompact.intertwiningOperator_eq_of_transport`, applied with `jP = e.hom` and
   `jQ = eQ.hom`, identifies `M^{K₀}_{Q'}(sw, λ)ψ(y)` with
   `(hK₀ I).intertwiningOperator (hK₀ I') (fam.iU I) (fam.l I) (fam.iU I') c₀ π₀ w₀ ψ (iota λ) y`.
7. **Assembly.** Index the terms by `S ×ˢ D`, enumerated by `Finset.equivFin`. For the index
   of `(v, d)` put:
   - `E (v, d) λ = exp(⟨λ, v⟩ + ⟨wλ, d + H^K_{Q'}(s)⟩)`;
   - `h (v, d) g = 1[Δ(s g) = d]`, `τ (v, d) g = s g` and `φ₀ (v, d) = cut v`.

   Combining steps 2, 4, 5 and 6 at `y = s g` gives the required identity for every
   `R`-regular `λ` and every `g`.

The remaining clauses:

- The `φ₀ j` are automorphic on `U_I(𝔸)M_I(F) \ G(𝔸)` for `K₀∞`, since the inducing subgroups
  agree (step 1).
- Each `E j` is the exponential of a complex-linear form. Its composite with a linear
  isomorphism `(Fin n → ℂ) ≃ X^*(P) ⊗ ℂ` is the exponential of a continuous linear form on a
  finite-dimensional space, hence differentiable.
- The instances are `Fintype (relativeWeylGroup fam.i)` (that of `r`), closedness of every
  `fam.p J`, and the monomorphism `fam.f J`. The last follows from
  `CommGroupScheme.groupHom (fam.f J) ≫ fam.i = fam.a J ≫ fam.l J ≫ fam.p J`, whose right side
  is a monomorphism.
- **Regularity.** The published `eisensteinRegularityParabolicTransport` along `e.hom`, with
  the same threshold, carries `R'`-regular parameters for `r` to `R'`-regular parameters
  `iota λ` for `fam.rootPresentation I`.
- **Root forms.** A root `β₀` of `fam.rootPresentation I` in the unipotent radical is
  `fam.f I ≫ χ` for a positive relative root `χ`, with `β₀ ≠ 0`. Take `β = r.data.f ≫ χ`. It
  is nonzero, because for both presentations the restriction of `χ` vanishes exactly when
  `χ` lies in the monoid generated by `J` (`restrict_positiveRoot_eq_zero_iff`). By
  `rootFunctional_parameterRestrict_eq_of_comp_eq`, the root form of `β₀` at `iota ν` equals
  the root form of `β` at `ν`. So it vanishes when the latter does.

## Route and provenance

The route differs from the argument in the statement's Markdown. That argument uses a compact
in good position and an archimedean conjugation `K'_∞ = tK_∞t⁻¹`. Here `K₀` is built with the
archimedean factor of `K`, so no archimedean conjugation is needed. The only change of compact
is the finite change of `eisensteinFiniteCompactOperatorComparison`, and it produces the
indicator functions `h j`. The statement does not ask for the further properties of a compact
in good position, and `K₀` is not claimed to have them.

Sources:

- J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer.
  Math. Soc. 37 (2024), registered as
  `bernstein-lapid-2024-meromorphic-continuation-eisenstein`: §2.1, p. 190, standard
  parabolics and a compact with `G(𝔸) = M(𝔸)U(𝔸)K`; §2.2, p. 191, the intertwining operators.
- C. Mœglin and J.-L. Waldspurger, *Spectral decomposition and Eisenstein series* (1995),
  registered as `moeglin-waldspurger-1995-spectral-decomposition`: I.1.4, pp. 4–5, compacts
  in good position; II.1.6, pp. 87–90, intertwining operators.
- Borel–Tits, *Groupes réductifs* (1965), §5.14 and Corollary 3.14, and Milne,
  *Algebraic Groups* (2017), Theorem 25.1, through the published theorems named in the
  conjugation lemma.

Provenance: derived. The passage from an arbitrary parabolic, target and compact to standard
data combines the published results named above. The sources work throughout with standard
parabolics and one compact in good position, and do not state this passage as a separate
result.
