# Conditions of the twisted trace Paley–Wiener theorem

This module defines the objects that appear in the twisted trace
Paley–Wiener theorem for `GL_n(E)`. The theorem itself is stated, not proved,
in `Langlands.BaseChange.TwistedPaleyWienerStatement`. It characterizes the
linear forms `(π, A) ↦ Θ^A_π(φ)` with `φ ∈ C^∞_c(G)` among all linear forms
on twisted characters. In this module such a form is a linear functional
`Φ : Module.Dual ℂ (Distribution G)` on the space of all distributions on
`G`, that is, of all linear functionals on `SchwartzBruhat G = C^∞_c(G)`.
It is evaluated on the twisted characters
`Θ^A_π = twistedDistribution μ π hπ A.toLinearMap` of
`Langlands.BaseChange.TwistedCharacter.Basic`, where `μ` is the measure
used to integrate test functions. The module has two parts.

- A generic part, for a topological group `G` with an automorphism `θ`:
  unramified characters, the θ-intertwiner of a twist by a θ-invariant
  character, the θ-intertwiner of a smoothly induced representation, and
  two conditions on `Φ`.
- A `GL_n` part: continuity of the inverse entrywise action of `σ` on
  `GL_n(E)`, the σ-intertwiner of a representation induced from a standard
  block parabolic subgroup, and the regularity condition on `Φ`.

All declarations are in the namespace `Langlands.BaseChange`, except three
declarations of the `GL_n` part: the continuity lemma, the σ-intertwiner and
its evaluation lemma. These are in `Langlands.BaseChange.TwistedPaleyWiener`. The Library module
`Langlands.BaseChange.SigmaInducedIntertwiner` already uses the names
`Langlands.BaseChange.continuous_entrywiseAut_symm`,
`Langlands.BaseChange.inducedSigmaIntertwiner` and
`Langlands.BaseChange.eval_inducedSigmaIntertwiner`. There, the continuity
lemma assumes that `F` is a field, and the intertwiner acts on the normalized
induction of a tensor product of block representations; see "Lemmas and their
proofs" and "Induction" below. The extra namespace keeps the short names
`inducedSigmaIntertwiner` and `eval_inducedSigmaIntertwiner` and their
argument order, without a clash.

Nothing here is a new result. The definitions transcribe the conditions of
the sources, and the lemmas are elementary facts needed to build them.

## Sources

- J. D. Rogawski, *Trace Paley–Wiener theorem in the twisted case*, Trans.
  Amer. Math. Soc. 309 (1988), 215–229 (PDF page = printed page − 214).
  - Printed p. 215: for an outer automorphism `ε` of `G` of finite order `r`
    and an irreducible admissible `π` equivalent to `ε(π)`, an operator
    `π(ε)`, unique up to `r`-th roots of unity, with
    `π(ε) π(g) π(ε)⁻¹ = π(ε(g))` and `π(ε)^r = 1`. The twisted character is
    `f ↦ Tr(π(f) π(ε))`. So `π(ε)` is an isomorphism of `π` onto `π ∘ ε`, the
    orientation of `A` here.
  - §3, printed p. 218: `i_{M,L}` is unitarily (that is, normalized)
    induction from a standard parabolic subgroup. For a θ-stable Levi `L`
    and an `L*`-module `ρ`, the induced module has
    `(π(ε) φ)(g) = ρ(ε) φ(ε⁻¹(g))`.
  - §11, printed p. 228: the space `F_g(G)` of linear forms `F` on the
    twisted Grothendieck group with (I) support in finitely many ε-stable
    components of the Bernstein variety, and (II) for every ε-stable standard
    Levi `L` and every ε-stable irreducible `ρ` of `L`, the function
    `ψ ↦ F(i_{G,L}(ψρ))` is a regular function on the ε-invariant unramified
    characters `X(L)^ε`. Proposition 11.2 says `F_tr(G) = F_g(G)`: these are
    exactly the forms `π ↦ Tr(π(f) π(ε))`.
- G. Henniart and B. Lemaire, *Changement de base et induction automorphe
  pour `GL_n` en caractéristique non nulle*, Mém. SMF 124 (2011), cited as HL
  (PDF page = printed page + 8).
  - II.3.1, printed p. 78: for a partition `α` of `n`, the block diagonal
    subgroup `G_α`, the block upper triangular parabolic `P_α`, and normalized
    parabolic induction `ι_α`.
  - II.4.4, printed p. 85: for an isomorphism `B` of `Ξ` onto `Ξ^σ`, the
    isomorphism `ι_α(B)` of `ι_α(Ξ)` onto `ι_α(Ξ)^σ` is
    `ι_α(B)(ξ)(g) = B(ξ(σ⁻¹(g)))`.
  - II.5.1, printed p. 100: unramified characters `Ψ(G(E))` and
    `Ψ(G(E))^σ = Ψ(G(E))`.
  - II.2.7, printed p. 67: `Θ^A_Π(φ) = trace(Π(φ) ∘ A)`, the convention of
    `twistedDistribution`.
  - II.5.2, printed p. 101: a σ-representation `(Π, A)` is a smooth σ-stable
    `Π` with an isomorphism `A : Π ≅ Π^σ`, where `Π^σ(g) = Π(σ(g))`, such
    that `A^d` is a nonzero scalar, with `d` the order of `σ`. It is irreducible if no nonzero
    proper `G(E)`-stable subspace is `A`-stable, and strongly irreducible if
    moreover `Π` is irreducible. `G(G(E), σ)` is the free group on the
    irreducible classes, and `G_0(G(E), σ)` its subgroup on the strongly
    irreducible classes.
  - II.5.3, printed p. 102: `(Π_ψ, A_ψ) = (Π ⊗ ψ, A)` for `ψ ∈ Ψ(G(E))`.
  - II.5.4, printed pp. 102–103: the Lemma (after Rogawski): every
    irreducible σ-representation is `ι_s(Π_0, A_0)`, with
    `Π = ⊕_{i<s} Π_0^{σ^i}` and
    `A(v_0, …, v_{s−1}) = (v_1, …, v_{s−1}, A_0 v_0)`, for a divisor `s` of `d`
    and a strongly irreducible `σ^s`-representation `(Π_0, A_0)`. The quotient
    `Ḡ(G(E), σ)` of `G(G(E), σ)` kills the irreducible classes with `s > 1` and
    the sums `∑_{i<t} (Π, μ^i A)` for primitive `t`-th roots of unity `μ`,
    `t > 1`. Remarque: `(Π, A) ↦ Θ^A_Π(φ)` factors through this quotient.
  - II.5.5, printed pp. 103–104: `ι_α(Π, A) = (ι_α(Π), ι_α(A))`, compatible
    with normalized parabolic induction.
  - II.5.7, printed p. 105: Rogawski's theorem, for `Z`-linear forms `Φ` on
    `G_0(G(E), σ)` with `Φ(Π, λA) = λ Φ(Π, A)`. Condition (A): (i) `Φ[Π, A] = 0`
    for every strongly irreducible `(Π, A)` outside a finite set of
    σ-stable Bernstein components; (ii) for every partition `α` of `n` and
    every strongly irreducible σ-representation `(Π, A)` of `G_α(E)`, the
    function `ψ ↦ Φ(ι_α[Π_ψ, A_ψ])` on the complex torus `Ψ(G_α(E))` is
    regular. Here `[·]` is the image in `Ḡ(G(E), σ)`. Condition (B): there is a
    locally constant compactly supported `φ` with `Φ[Π, A] = Θ^A_Π(φ)` for
    every strongly irreducible `(Π, A)`. Remarque (1): (i) may be replaced by
    (i)': there is a compact open subgroup `J` with `Φ[Π, A] = 0` whenever `Π`
    has no nonzero `J`-fixed vector.
- J. Bernstein, P. Deligne and D. Kazhdan, *Trace Paley–Wiener theorem for
  reductive p-adic groups*, J. Analyse Math. 47 (1986), 180–192, cited as
  BDK. §1.2, printed pp. 180–181: the untwisted conditions, (i) regularity
  of `ψ ↦ f(i_{G,M}(ψσ))` on the unramified characters and (ii) domination by
  an open compact subgroup `K`, and the theorem `F_tr = F_good`.

## Definitions

1. `IsUnramifiedCharacter ψ`, for `ψ : G →* ℂˣ`: `ψ` is trivial on every
   compact subgroup of `G`. See "Unramified characters" below.
2. `twistTwistedIntertwiner θ ψ hψ A`: for a θ-intertwiner
   `A : ρ ≅ ρ ∘ θ` and a character `ψ` with `ψ ∘ θ = ψ` (hypothesis `hψ`),
   the θ-intertwiner of the twist `twist ψ ρ = ρ ⊗ ψ` whose underlying linear
   equivalence is `A`. This is HL's `A_ψ = A` of II.5.3.
3. `inducedTwistedIntertwiner θ hθ hθ' P hP p θM hp Ξ B`: data are a
   subgroup `P` of `G` with `θ g ∈ P ↔ g ∈ P` (`hP`), a homomorphism
   `p : P →* M`, an automorphism `θM` of `M` with `p ∘ θ = θM ∘ p` on `P`
   (`hp`), a representation `Ξ` of `M` and an isomorphism `B : Ξ ≅ Ξ ∘ θM`.
   The result is an isomorphism of the Library's smooth induction
   `Induction.smoothInduced P (Ξ ∘ p)` onto its composite with `θ`, given by
   `(ι B f)(g) = B(f(θ⁻¹ g))`, with inverse `f ↦ (g ↦ B⁻¹(f(θ g)))`. The
   continuity hypotheses `hθ` and `hθ'` on `θ` and `θ⁻¹` keep the image
   functions smooth. `Induction.smoothInduced` is unnormalized induction.
   The formula is that of Rogawski §3 and HL II.4.4, which use it for
   normalized induction; see "Induction" below. The definition is the
   Library's transport `Induction.transportSmoothEquiv` of
   `Langlands.BaseChange.SigmaInducedIntertwiner`; see "Lemmas and their
   proofs".
4. `IsCompactlyDominatedFunctional θ μ Φ`, at carrier universe `z`: there
   is a compact open subgroup `J` of `G` such that `Φ(Θ^A_π) = 0` for every
   admissible irreducible representation `π` of `G` on a complex vector
   space in the universe `z` with no nonzero `J`-fixed vector
   (`fixedVectors π J = ⊥`), and every isomorphism `A : π ≅ π ∘ θ`. This is
   condition (i)' of HL II.5.7, Remarque (1), and the twisted form of
   condition (ii) of BDK §1.2.
5. `IsTwistedTraceFunctional θ μ Φ`, at carrier universe `z`: there is
   `φ : SchwartzBruhat G` with `Θ^A_π(φ) = Φ(Θ^A_π)` for every admissible
   irreducible `π` on a space in the universe `z` and every
   `A : π ≅ π ∘ θ`. This is condition (B) of HL II.5.7.
6. `TwistedPaleyWiener.inducedSigmaIntertwiner σ B Ξ BΞ`: for a block
   shape `B` of `n`, a
   representation `Ξ` of the Levi product `B.Levi E = ∏ᵢ GL_{nᵢ}(E)` and an
   isomorphism `BΞ : Ξ ≅ Ξ ∘ leviAut σ B`, the σ-intertwiner
   `inducedTwistedIntertwiner` of the smooth induction of
   `Ξ ∘ B.leviProjection E` from the standard block upper triangular parabolic
   `B.parabolic E`, with `θ = entrywiseAut σ n`. This is HL's `ι_α(A)`
   (II.4.4, II.5.5), with the same formula, on the unnormalized induction.
   It differs from the Library's `Langlands.BaseChange.inducedSigmaIntertwiner`,
   which acts on the normalized induction of a tensor product of block
   representations.
7. `IsSigmaInducedRegularFunctional σ μ Φ`, at carrier universe `z`: for
   every block shape `B` of `n`, every admissible irreducible representation
   `Ξ` of `B.Levi E` on a space `X : Type z`, and every
   `BΞ : Ξ ≅ Ξ ∘ leviAut σ B`, there are a finite set `s ⊆ B.Levi E` and
   coefficients `c : B.Levi E → ℂ` such that, for every unramified character
   `ψ` of `B.Levi E` with `ψ ∘ leviAut σ B = ψ` and every proof `h` that the
   induced representation `Ind(Ξ ⊗ ψ)` is admissible,
   `Φ(Θ^{ι(BΞ_ψ)}_{Ind(Ξ ⊗ ψ)}) = ∑_{m ∈ s} c(m) ψ(m)`. Here
   `BΞ_ψ = twistTwistedIntertwiner (leviAut σ B) ψ hψ BΞ` and
   `ι = TwistedPaleyWiener.inducedSigmaIntertwiner σ B (twist ψ Ξ)`. The
   coefficients do not depend on `ψ`. Block shapes include the shape with
   one block, for which the parabolic is `GL_n(E)` itself. This is condition (A)(ii) of HL II.5.7
   and condition (II) of Rogawski §11.

The two generic conditions and the regularity condition need the hypotheses
of `twistedDistribution`: `G` is a Hausdorff, locally compact, totally
disconnected topological group with a Borel σ-algebra, and `μ` is a left
invariant measure that is finite on compact sets. The automorphism `θ` is
only a group automorphism. The Haar measure of the statement is a special
case.

## Lemmas and their proofs

- `twistTwistedIntertwiner_apply`: `twistTwistedIntertwiner θ ψ hψ A v = A v`.
  It holds by definition. In the construction, the intertwining property is
  `A(ψ(g) ρ(g) v) = ψ(θ g) ρ(θ g)(A v)`. It follows from the linearity of
  `A`, from `ψ(θ g) = ψ(g)`, and from the intertwining property of `A`.
- `eval_inducedTwistedIntertwiner`: `(ι B f)(g) = B(f(θ⁻¹ g))`, by
  definition. The construction is the Library's
  `Induction.transportSmoothEquiv P θ hθ hθ' θP hθP T hT`. That equivalence
  sends `f` to `x ↦ T(f(θ⁻¹ x))`, has inverse `f ↦ (x ↦ T⁻¹(f(θ x)))`, and
  its own evaluation formula `eval_transportSmoothEquiv` holds by definition.
  It is applied with the following data.
  - `θP` is the restriction of `θ` to `P`, a private automorphism
    `stableSubgroupAut θ P hP` of `P`. It is Mathlib's `MulEquiv.subgroupMap`
    followed by `MulEquiv.subgroupCongr` for the equality `θ(P) = P`.
    That equality follows from `hP` and `Subgroup.mem_map_equiv`:
    `g ∈ θ(P)` if and only if `θ⁻¹ g ∈ P`, if and only if `g ∈ P`.
  - `hθP : θP q = θ q` for `q ∈ P` holds by definition.
  - `T` is the linear equivalence of `B`. The hypothesis `hT` asks for
    `B(Ξ(p q) x) = Ξ(p(θ q))(B x)` for `q ∈ P`. By `hp`, `p(θ q) = θM(p q)`,
    and the equation is the intertwining property of `B` at `p q`.
- `TwistedPaleyWiener.continuous_entrywiseAut_symm`: the inverse of
  `entrywiseAut σ n` is continuous. That inverse is, by definition, the
  entrywise action of `σ⁻¹`, so the Library's
  `continuous_entrywiseAut_of_isModuleTopology` (in
  `Langlands.BaseChange.TwistedCharacterRegularValuesReduction`), applied to
  `σ.symm`, proves it. The same Library theorem, applied to `σ`, gives the
  continuity of `entrywiseAut σ n` itself, used in
  `TwistedPaleyWiener.inducedSigmaIntertwiner`. It needs only a commutative
  ring `F` and the module topology of `E`. The Library's
  `Langlands.BaseChange.continuous_entrywiseAut_symm` (in
  `Langlands.BaseChange.SigmaInducedIntertwiner`) and
  `continuous_entrywiseAut` (in `Langlands.BaseChange.CyclicAlgebraTopology`)
  assume that `F` is a field. They therefore do not apply to the commutative
  ring `F` of this section.
- `TwistedPaleyWiener.eval_inducedSigmaIntertwiner`:
  `(ι BΞ f)(g) = BΞ(f(σ⁻¹ g))`, by definition. The construction applies
  `inducedTwistedIntertwiner` to `θ = entrywiseAut σ n`, `P = B.parabolic E`,
  `p = B.leviProjection E` and `θM = leviAut σ B`. The hypotheses `hP` and
  `hp` are `entrywiseAut_mem_parabolic_iff` and `leviProjection_entrywiseAut`
  of `Langlands.BaseChange.PseudoCoefficient`.

## Comparison with the sources

The comparisons below are mathematical explanations. Apart from the
cited Library lemmas, they are not formalized.

**Linear functionals on distributions.** HL and Rogawski state the theorem
for homogeneous linear forms on twisted Grothendieck groups. A functional
`Φ` on `Distribution G` gives such a form on HL's `G_0(G(E), σ)`: the
`Z`-linear map with `(Π, A) ↦ Φ(Θ^A_Π)` on the basis. It is well defined
because `Θ^A_Π` depends only on the isomorphism class of `(Π, A)`
(`twistedDistribution_eq_of_equivariant` of
`Langlands.BaseChange.PseudoCoefficient`). It is homogeneous because
`Θ^{λA}_Π = λ Θ^A_Π` (`twistedDistribution_smul` of
`Langlands.BaseChange.TwistedCharacter.Basic`). The conditions on `Φ` defined
here are the conditions of the sources for this form, and condition (B) for
this form is `IsTwistedTraceFunctional`. This is the only direction needed
for the statement. A homogeneous form on `G_0(G(E), σ)` comes from some `Φ`
when it respects the linear relations among twisted characters, for example
by extending it from their span with Mathlib's `LinearMap.exists_extend`.
This module does not use that converse.

**Strongly irreducible.** HL's conditions range over strongly irreducible
σ-representations `(Π, A)`: `Π` smooth, irreducible and σ-stable, and
`A : Π ≅ Π^σ` with `A^d` a nonzero scalar. Here `π` (or `Ξ`) is admissible
(`IsAdmissible`, which includes smoothness) and irreducible
(`Representation.IsIrreducible`), and every `A : π ≅ π ∘ θ` is allowed.
Smooth irreducible representations of `GL_n(E)` and of the Levi products are
admissible (Jacquet; Bernstein), so the classes of representations agree.
For `θ` of order `d`, as for `θ = entrywiseAut σ n` with `σ` of order `d`,
`A^d` is an automorphism of the irreducible admissible `π`. It is a scalar by
Schur's lemma: it preserves a nonzero finite-dimensional space of fixed
vectors of a compact open subgroup, so it has an eigenvector there, and the
eigenspace is a nonzero subrepresentation. So every `A` allowed here is
allowed by HL. Rogawski normalizes `π(ε)^r = 1` instead. A nonzero rescaling
of `A` brings `A^d` to `1`, and both sides of every condition are homogeneous
in `A`, so his normalization gives the same conditions.

**Induced families.** In (ii), HL evaluate `Φ` on the class
`ι_α[Π_ψ, A_ψ]` of the induced σ-representation in `Ḡ(G(E), σ)`. Since `Φ`
is homogeneous, it factors through this quotient (HL II.5.7). Here `Φ` is
evaluated on the twisted character of the induced representation itself.
The two agree because twisted characters satisfy the same relations:

- The twisted character of a σ-representation of finite length is the sum
  of the twisted characters of its irreducible σ-subquotients, by
  additivity of traces along an `A`-stable composition series.
- The twisted character of an irreducible σ-representation that is not
  strongly irreducible is zero. By the Lemma of HL II.5.4 it is
  `ι_s(Π_0, A_0)` with `s > 1`, and the composite of `Π(φ)` with `A` maps
  each summand `Π_0^{σ^i}` to another summand, so its trace is zero.
- `∑_{i<t} Θ^{μ^i A}_Π = (∑_{i<t} μ^i) Θ^A_Π = 0`, by
  `twistedDistribution_smul`. This is the computation of the Remarque of
  HL II.5.4.

So `Φ(Θ^{ι(A)}_{Ind(Π)})` is the value of the form at `ι_α[Π, A]`. The
induced intertwiner is allowed: `ι(BΞ)^d = ι(BΞ^d)` by the evaluation
formula, and `BΞ^d` is a scalar by the previous remark.
`IsSigmaInducedRegularFunctional` quantifies over all proofs `h` that the
induced representation is admissible. They are needed only to form its
twisted character, which does not depend on the proof. Such a proof exists:
parabolic induction preserves admissibility, as `P \ G` is compact and the
double coset space `P \ G / J` is finite for a compact open `J`. A
`J`-invariant function is determined by its values at the representatives,
each of which lies in the fixed space of an open compact subgroup of the
Levi product.

**Unramified characters.** HL's `Ψ(G_α(E))` is the group of unramified
characters of `G_α(E) = ∏ᵢ GL_{nᵢ}(E)`: the characters trivial on the
subgroup `G_α(E)⁰` of elements with `|det mᵢ| = 1` for every `i`. They are
the maps `m ↦ ∏ᵢ zᵢ^{ord(det mᵢ)}` with `z ∈ (ℂˣ)^{l(α)}`, and `Ψ(G_α(E))` is
the complex torus `(ℂˣ)^{l(α)}`. `IsUnramifiedCharacter` instead asks that
`ψ` be trivial on every compact subgroup. The two agree on `G_α(E)`.

- Every compact subgroup lies in `G_α(E)⁰`, as `m ↦ |det mᵢ|` is a
  continuous homomorphism to the discrete group `q^ℤ`, whose only compact
  subgroup is trivial.
- `G_α(E)⁰` is generated by compact subgroups, since
  `GL_k(E)⁰ = GL_k(O_E) · SL_k(E)` and `SL_k(E)` is generated by elementary
  unipotent matrices `1 + a E_{ij}`. Each lies in the compact subgroup
  `1 + O_E ϖ^{−r} E_{ij}` for a large `r`.

In particular such characters have open kernel, so they are continuous.
This definition uses only the topology of the group. With the module
topology of `E`, the Library supplies neither a valuation on `E` nor a
norm character `|det|` of `GL_n(E)`. Its `Plancherel.unramifiedCharacters ν`
needs such a family `ν` of norm characters, so this module does not use it.

**σ-invariance.** Rogawski uses the ε-invariant unramified characters
`X(L)^ε`, and `IsSigmaInducedRegularFunctional` quantifies over unramified
`ψ` with `ψ ∘ leviAut σ B = ψ`, which is needed to form `BΞ_ψ`. For
`GL_n(E)` with `E/F` finite every unramified character is σ-invariant: `σ`
preserves the normalized valuation of `E` and `det(σ m) = σ(det m)`. HL note
this for `G(E)` in II.5.1 (`Ψ(G(E))^σ = Ψ(G(E))`) and accordingly use all of
`Ψ(G_α(E))`.

**Regular functions.** A regular function on the torus `(ℂˣ)^{l(α)}` is a
Laurent polynomial in the coordinates `zᵢ`. Evaluation at `m` is the
monomial `ψ ↦ ψ(m) = ∏ᵢ zᵢ^{ord(det mᵢ)}`. Every monomial arises this way:
take `mᵢ` diagonal with entries powers of a uniformizer of `E`, which attains
every integer tuple of valuations. So the regular functions are exactly the
finite sums `∑_{m ∈ s} c(m) ψ(m)`.

**Induction.** The Library's `Induction.smoothInduced` is unnormalized
induction, while HL's `ι_α` and Rogawski's `i_{G,L}` are normalized:
`ι_α(Ξ) = Ind(Ξ ⊗ δ^{1/2})`, with `δ` the modulus character of the
parabolic. `δ^{1/2}` is an unramified σ-invariant character of `G_α(E)`
with values in `q^{ℤ/2}`. So the normalized family `ψ ↦ ι_α(Ξ ⊗ ψ)` is the
unnormalized family `ψ ↦ Ind(Ξ ⊗ ψ')` at the translated point
`ψ' = ψ δ^{1/2}`. Translation by a point of the torus preserves regular
functions, so the regularity conditions agree. The intertwiners agree,
since `ι_α(A)` and `TwistedPaleyWiener.inducedSigmaIntertwiner` are given by
the same formula `f ↦ A ∘ f ∘ σ⁻¹` (HL II.4.4; Rogawski §3), and twisting by
`δ^{1/2}` does not change `A`. HL's `G_α(E)` are the block diagonal
subgroups and `P_α(E)` the block upper triangular subgroups (HL II.3.1).
These are `B.Levi E` and `B.parabolic E`, with the Levi product embedded
block-diagonally.

The Library module `Langlands.BaseChange.SigmaInducedIntertwiner` formalizes
the normalized side in a special case. Its `inducedSigmaIntertwiner σ B A` is
the same formula on `normalizedProductInduced B P`, the normalized induction
of a tensor product `P₁ ⊗ ⋯ ⊗ P_r` of block representations, with intertwiner
`A₁ ⊗ ⋯ ⊗ A_r`. Its `parabolicHalfModulus_parabolicAut` proves the
σ-invariance of `δ^{1/2}` used above. It needs `E` to be a nonarchimedean
local field, to form `δ^{1/2}`, and inducing representations that are tensor
products. The definitions here keep the module-topology setting and allow
every irreducible representation `Ξ` of the Levi product, as the conditions
of the sources require.

**Universe.** The conditions quantify over representations on spaces in a
fixed universe `z`. When `E` is a finite extension of a nonarchimedean local
field, `GL_n(E)` and its Levi products are second countable, so `G / K` is
countable for every open subgroup `K`. A nonzero vector `v` of an
irreducible smooth representation is fixed by an open `K`, and the countably
many vectors `π(g) v`, for `g ∈ G / K`, span the representation. So it has
countable dimension and is isomorphic to a representation on a space with a
countable basis in any universe. Twisted characters are invariant under such
isomorphisms (`twistedDistribution_eq_of_equivariant`), so the choice of `z`
does not change the content. The universe `z` restricts the inducing
representations `Ξ`. The induced representation lives in the universe of
functions from `GL_n(E)` to the space of `Ξ`.
