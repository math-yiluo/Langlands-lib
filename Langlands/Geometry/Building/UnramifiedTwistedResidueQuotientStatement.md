# Residue quotient at a twisted-fixed point for a Frobenius lift

This module states `UnramifiedTwistedResidueQuotientStatement.{u}`, a derived and
unproved input for `UnramifiedTwistedChamberQuotientStatement` (Task 6500). It
asserts the reductive-quotient data at a twisted-fixed point `y` of the building
over the maximal unramified extension. The data are a finite-field reductive
group, a reduction map from a subgroup of the fixer of `y`, compatibility with the
twist and with canonical Frobenius descent, fixation of the chambers through `y`
by the kernel, and transitivity on those chambers. This data is asserted for
every automorphism that reduces to the arithmetic Frobenius. The module proves
nothing about the statement; a separate proof task will be published for it.

## Hypotheses (identical to the target)

The binder telescope up to and including the residue-field `letI` block is
copied verbatim from `UnramifiedTwistedChamberQuotientStatement`.

- `F : Type u` is a nonarchimedean local field, `K = inertiaFixedField F`,
  `Γ = Aut(K/F)` (written `K ≃ₐ[F] K`), and `G_K = baseChanged F K G`.
- `G` is a connected reductive `F`-group (`hG`). `iT : T.toGrp ⟶ G` comes from a
  commutative `F`-group `T` whose base change to `K` is a maximal split torus of
  `G_K` (`hiT`).
- `D` is a KP apartment datum for that torus over the integer valuation of `K`,
  `C` is a centralizer datum, `h6` is the V6 (omega) compatibility, and `hD` is
  Galois stability of `D`. Together they give the building
  `B = UnramifiedBuildingDescent.buildingData iT _ hiT D C h6` and the coefficient
  action `A.action σ` of `σ ∈ Γ` on `B.ReducedBuilding`, where
  `A = UnramifiedBuildingDescent.semilinearData iT _ hiT C h6 hD`.
- `c : Γ → G(K)` satisfies the crossed-homomorphism identity
  `c (σ * τ) = c σ * rationalConjugate F K G σ (c τ)`. It is trivial on the fixing
  subgroup of some finite subextension `E` of `K/F`.
- `y : B.ReducedBuilding` is fixed by every twisted action
  `z ↦ c σ • A.action σ z`.
- `κ = 𝓀[F]` is the residue field of `F`, finite through `Fintype.ofFinite`.
  `Ω = IsLocalRing.ResidueField (fixedFieldIntegers F)` is the actual residue field
  of `K`, with the algebra structure `(residueToFixedField F).toAlgebra`. Its
  algebraic-closure structure is `fixedFieldResidueIsAlgClosure F`.

The module also contains a private instance,
`unramifiedTwistedResidueQuotientAffineHom`. It gives `IsAffineHom` for the
structure morphism of `baseChanged F K G` and is the same instance as the
target's private one, under a different name. It is needed only to elaborate
`B.fixer`, the action of `G(K)` and `rationalConjugate`.

## The Frobenius-lift hypothesis

The statement then quantifies over every `φ : K ≃ₐ[F] K` such that, for every
`x` in the valuation ring `fixedFieldIntegers F` of `K`,

`residue (fixedFieldIntegerAut F φ x) = (residue x) ^ Nat.card 𝓀[F]`.

Here `fixedFieldIntegerAut F φ` is the restriction of `φ` to the integer ring
(its coercion to `K` is `φ x`, by `fixedFieldIntegerAut_coe`). So `φ` induces the
arithmetic Frobenius `t ↦ t^q` on `Ω`, with `q = |κ|`. This is the automorphism
that `FiniteField.frobeniusAlgEquivOfAlgebraic κ Ω` uses in the conclusion.
Since `K/F` is unramified, such a `φ` is the Frobenius element of `Γ`.

## Conclusion

With `θ(g) = c φ * rationalConjugate F K G φ g * (c φ)⁻¹`, the statement asserts
that there exist the following.

1. A group scheme `R` over `Spec κ` with `IsConnectedReductive R`.
2. A subgroup `P` of `G(K)` with `P ≤ B.fixer y`.
3. A surjective group homomorphism `q : P →* R_Ω(Ω)`. Here `R_Ω(Ω)` is the group
   of sections `Over.mk (𝟙 (Spec Ω)) ⟶ (R base-changed along κ → Ω).X`, that is,
   the actual `Ω`-points of `R`.
4. A map `θP : P → P` with `(θP g : G(K)) = θ g` for all `g ∈ P`. So `θ`
   preserves `P`.
5. Frobenius compatibility, `q (θP g) = descentBasePoint … R (q g)`. Here the
   right side transports an `Ω`-point of `R` along `Spec` of
   `FiniteField.frobeniusAlgEquivOfAlgebraic κ Ω`, i.e. canonical Frobenius
   descent. These are exactly the expressions in
   `IntegerValuationBuildingData.HasFiniteFieldChamberQuotient`.
6. Kernel fixation. For every `Y ⊆ B.ReducedBuilding` with
   `B.HasChamberClosurePresentation Y y`, and every `g ∈ P` with `q g = 1`,
   `(g • ·) '' Y = Y`.
7. Transitivity. For any two `Y, Y'` with closure presentations through `y`,
   there is `h ∈ P` with `Y' = (h • ·) '' Y`.

`B.HasChamberClosurePresentation Y y` means there are `g ∈ G(K)` and apartment
points `x₀, x` with the following properties: `x₀` is generic, so its facet is
an apartment chamber; `Y = (g • apartmentMap ·) '' facet x₀`;
`x ∈ facetClosure x₀`; and `g • apartmentMap x = y`. In words, `Y` is a chamber
of the building whose closure contains `y`.

The statement does not identify `P` with the parahoric subgroup at `y`, `q` with
a reduction map, or `R` with the reductive quotient of a specified model.

## Relation to the target statement

The target `UnramifiedTwistedChamberQuotientStatement` chooses a `φ` that is a
dense generator of `Γ`. For that `φ` it asks for
`B.HasFiniteFieldChamberQuotient κ Ω θ τ y` with `τ(z) = c φ • A.action φ z`.
That predicate consists of items 1–5 together with one chamber `Y₀` presented
through `y`, kernel fixation of `Y₀`, and some `h ∈ P` with
`τ '' Y₀ = (h • ·) '' Y₀`.

The present statement differs in three ways.

- `φ` is a hypothesis, with the residue condition above, rather than an
  existential with the density condition.
- Kernel fixation is required for every chamber presented through `y`.
- Transitivity (item 7) replaces the single `h`.

The intended reduction from this statement to the target will be a separate
proved unit. It builds a Frobenius lift `φ` from the surjectivity of the residue
map on automorphisms and shows that it is a dense generator. It then takes `Y₀`
from the existence of chamber closure presentations, and checks that `τ '' Y₀`
again has a closure presentation through `y`. Finally it applies item 7 to `Y₀`
and `τ '' Y₀`. Nothing in this module proves that reduction.

## Source and provenance

This is a derived statement, not a numbered assertion of Kaletha–Prasad,
*Bruhat–Tits Theory: A New Approach* (2023), with the authors' corrections and
additions of 1 November 2024. It packages the following source facts for the
twisted group `ᶜG`, the form of `G` given by the cocycle `c`, at the point `y`.

- **Twisted action** (proof of Theorem 10.6.1, printed p. 397, PDF p. 428): "We
  will identify ᶜG(K) with G(K) … the 'twisted' action of Γ on ᶜG(K) is
  described as follows: For x ∈ ᶜG(K), and γ ∈ Γ, γ∘x = c(γ)γ(x)c(γ)⁻¹ …
  Similarly B admits two actions of Γ, an action induced by its action on G(K),
  and the 'twisted action' induced by the twisted action on ᶜG(K)." So `y` is a
  point of `B(ᶜG) = B(G_K)^Γ` for the twisted action, and `θ` is the twisted
  action of `φ`.
- **Bruhat–Tits group schemes** (Axiom 4.1.20, printed p. 163, PDF p. 194): for
  bounded `Ω` there is a smooth affine model `G¹_Ω` with `G¹_Ω(o) = G(k)¹_Ω`, and
  its relative identity component `G⁰_Ω` has `G⁰_Ω(o) = G(k)⁰_Ω`.
- **Descent of these schemes** (9.2.5, printed pp. 327–328, PDF pp. 358–359):
  for `Γ`-stable `Ω` the `O`-group schemes "admit unique descents to smooth
  affine o-group schemes with generic fiber G … The maximal reductive quotient
  of G⁰_Ω will be denoted by G_Ω." For the twisted-fixed `y` this gives a
  connected reductive `f`-group `G_y` (`f = κ`). It is the candidate for `R`, and
  its base change to `Ω` is the reductive quotient of the special fibre of the
  parahoric `O`-model of `G_K`. Under this identification the canonical
  Frobenius of `G_y` corresponds to the reduction of the twisted action of the
  Frobenius `φ`, which gives item 5. The book does not state this last
  identification separately; it is the derived part of the packaging.
- **Reduction and incident facets** (Axiom 4.1.22, printed pp. 163–164, PDF
  pp. 194–195). Item (4): "The inverse image of the subgroup p_F(F′)(f) of
  G⁰_F(f), under the natural homomorphism π_F : G⁰_F(o) → G⁰_F(f) is G⁰_F′(o)."
  Item (5): "F′ ↦ ℘_F(F′) is an order-preserving bijective map of the partially
  ordered set {F′ | F ≺ F′} onto the set of parabolic f-subgroups of G_F". Item
  (7) defines `G(k)⁰⁺_F` as "the preimage of R_u(G⁰_F)(f) under the surjective
  homomorphism π_F". With `P` the parahoric `G(K)⁰_y`, and `q` the composite of
  `π_F` with the projection onto the reductive quotient, items 2–4 hold. Over
  the strictly Henselian `O` with algebraically closed residue field, `π_F` is
  surjective, as (7) states, and so is the projection on `Ω`-points; this gives
  item 3.
- **Kernel fixation** (Remark 4.1.23, printed p. 164, PDF p. 195): "(4) implies
  that the inverse image P⁺_F under π_F of the normal subgroup R_u(G⁰_F)(f)
  (⊂ p_F(F′)(f)) of G⁰_F(f) is contained in G⁰_F′(o). So P⁺_F fixes every facet
  F′, F ≺ F′, pointwise." The kernel of `q` is `P⁺_F` for the facet `F` of `y`.
  A chamber with a closure presentation through `y` is a facet `F′` with
  `F ≺ F′`, so the kernel fixes it pointwise, hence setwise (item 6).
- **Transitivity** (Proposition 9.10.1, proof of (4) ⇒ (1), printed p. 381, PDF
  p. 412): "According to Axiom 4.1.22, the set of f-Borel subgroups is in
  bijection with the set of K-chambers containing F in its closure. This
  bijection is Γ-equivariant". By 4.1.22(4) the bijection is also equivariant
  for `P` acting on chambers by translation and on Borel subgroups by
  conjugation through `q`. All Borel subgroups of `R_Ω` are conjugate under
  `R(Ω)` because `Ω` is algebraically closed. Since `q` is surjective, `P` acts
  transitively on the chambers whose closure contains `y` (item 7).
- **Context only.** Proposition 9.10.4 (printed p. 382, PDF p. 413) gives
  residual quasi-splitness when `dim(f) ⩽ 1`, and the proof of Theorem 10.6.1
  applies it to `ᶜG` to obtain a twisted-stable chamber. That is what the target
  and its Lang-theorem reduction recover; it is not used for items 1–7.

The corrections of 1 November 2024 contain no entry for Axiom 4.1.20,
Axiom 4.1.22, Remark 4.1.23, 9.2.5, Proposition 9.10.1 or Theorem 10.6.1. Their
Chapter 4 entries (PDF p. 27) make Axioms 4.1.20 and 4.1.22 part of the list in
Definition 4.1.26. Their replacement of Proposition 1.3.35(8) (PDF pp. 3–5)
corrects the facet–parabolic combinatorics behind 4.1.22(5).

## Scope and caveats

- Chapter 4 of the book is an axiomatic summary, established in Chapters 6–9;
  `K = inertiaFixedField F` satisfies its hypotheses (Henselian, discretely
  valued, perfect residue field).
- The statement quantifies over arbitrary supplied data `D`, `C`, `h6`, `hD`. A
  proof has to relate the building `B` built from them to the Kaletha–Prasad
  building of `G_K` (for instance through the uniqueness of omega-compatible
  valuations up to equipollence) or argue directly from the data.
- The statement is an interface only. It is not proved here, and this module
  does not prove the target statement either.
