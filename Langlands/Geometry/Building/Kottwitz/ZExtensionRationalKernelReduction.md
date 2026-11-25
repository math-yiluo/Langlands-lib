# Reducing the rational kernel clause of KP Proposition 11.5.3 to named inputs

This module is a conditional step toward
`Langlands.Geometry.Building.Kottwitz.ZExtensionKottwitzKernelSurjectivityStatement`
(module `Kottwitz.ZExtensionKernelStatement`). That statement is the kernel clause of
Kaletha–Prasad, *Bruhat–Tits theory: a new approach* (2023), Proposition 11.5.3,
printed page 431, PDF page 462 (source ID
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`). This module
does not prove it. It proves the second conjunct (`F`-rational points) from six
premises, all unproved when this module was written: four published Library statements
and two propositions written out in full in the statement, because the Library had no
statement of them yet. The first conjunct is reduced separately, in module
`Kottwitz.ZExtensionKernelReduction`.

The module is derived content. It assembles a proof from Library facts and the assumed
statements. It asserts nothing from the literature beyond what those statements and the
published target already assert.

## Declarations

- `map_kernel_eq_of_image_lift` is a group-theoretic snake step. Take group
  homomorphisms `p : H → G`, `κH : H → A`, `κG : G → B` and `q : A → B`, with `p`
  surjective and `κG ∘ p = q ∘ κH`. Suppose that every `h` with `q(κH h) = 1` has some
  `h' ∈ ker p` with `κH h' = κH h`. Then `p(ker κH) = ker κG`. It differs from the
  Library's `map_kernel_eq_of_kernel_lift` (module `Kottwitz.KernelTransport`) in one
  respect: lifts are only required for classes `κH h` in the image of `κH`, not for
  every element of `ker q`. On rational points this matters, because only residually
  invariant classes can be lifted to `Z(F)`.
- `ker_comp_eq_of_injective`: composing with an injective homomorphism does not change
  the kernel.
- `extend_affinePointsTarget`: `GaloisPoint.extend k L` commutes with the point map of
  a homomorphism `f : G ⟶ H`. This is `affinePointsTarget_naturality` at
  `Algebra.ofId k L`.
- The existing `reductiveInvariantInclusion_injective`, imported from
  [`CharacterKernelReduction`](CharacterKernelReduction.md), proves that the inclusion
  `reductiveInvariantInclusion F S hS : π₁(S)_I^Γ → π₁(S)_I` is injective.
- `rationalKottwitz_map_of_inputs`: assume `ReductiveKottwitzFunctorialityStatement`
  and `ReductiveKottwitzDescentStatement`. Let `f : S ⟶ T` be a homomorphism of connected
  reductive groups over `Spec F` and `x ∈ S(F)`. Then the inclusion of
  `reductiveKottwitzRational F T hT (rationalPoints.map f x)` equals
  `fundamentalInertiaMap F K E T hT S hS f` applied to the inclusion of
  `reductiveKottwitzRational F S hS x`. Here `K = UnramifiedClosure F` and
  `E = SeparableClosure F`.
- `ZExtensionRationalKernelReductionStatement` is the implication

  `ReductiveKottwitzFunctorialityStatement → ReductiveKottwitzDescentStatement →
  CentralTorusInertiaExactnessStatement → (Inj) → (Cor) →
  ZExtensionPointSurjectivityStatement → ZExtensionRationalKottwitzKernelStatement`,

  all at universe `u`, where (Inj) and (Cor) are written out in the statement:

  - (Inj): for every nonarchimedean local field `F : Type u`, every group scheme `G`
    over `Spec F` and every `z : ZExtension G`, the map
    `fundamentalInertiaMap F K E z.H _ z.Z.toGrp _ z.i : π₁(Z)_I → π₁(H)_I` is injective.
  - (Cor): for every nonarchimedean local field `F : Type u`, every commutative group
    scheme `T` over `Spec F` and every `hT : IsInducedTorus T`, the map
    `torusKottwitzRational F T hT.isTorus : T(F) → X_*(T)_I^Γ` is surjective.

  The conclusion is the second conjunct of the target, verbatim. It is defined in module
  `Kottwitz.ZExtensionKernelReduction`.
- `zExtensionRationalKernelReduction` proves `ZExtensionRationalKernelReductionStatement`.

The whole target follows from this theorem, `zExtensionUnramifiedKernelReduction`
(module `Kottwitz.ZExtensionKernelReduction`; it also needs
`ReductiveKottwitzExistenceStatement`) and `zExtensionKottwitzKernelSurjectivityStatement_iff`.
This module does not state that combination.

## The premises

Four of the six premises (the first three and the last) are published Library
statements; (Inj) and (Cor) are written out in the statement. All six were unproved when
this module was written.

- `ReductiveKottwitzExistenceStatement`, `ReductiveKottwitzFunctorialityStatement` and
  `ReductiveKottwitzDescentStatement` (module `Kottwitz.ReductiveMapStatement`): KP
  Lemma 11.5.1, printed p.430 / PDF p.461, and the definition after it of `κ_G` on `G(k)`
  as the restriction of `κ_{G_K}`. The existence statement is used only for the first
  conjunct.
- `CentralTorusInertiaExactnessStatement` (module `Kottwitz.CentralTorusExactnessStatement`):
  exactness of `π₁(Z)_I → π₁(H)_I → π₁(G)_I → 0` for a central torus quotient. It is used
  through its `.zExtension` corollary.
- (Inj) is the injectivity in the proof of Proposition 11.5.3: "The torsion-freeness of
  X∗(Z)I implies, as was argued in the proof of Lemma 2.5.20, that in fact the first map
  in this sequence is injective." Here it is taken only for z-extensions over local
  fields, with `K = UnramifiedClosure F` and `E = SeparableClosure F`. The general
  statement `InducedCentralTorusInertiaInjectivityStatement` (module
  `Kottwitz.CentralTorusInertiaInjectivityStatement`), proved as
  `inducedCentralTorusInertiaInjectivity`, has a z-extension corollary that implies (Inj).
- (Cor) is KP Corollary 11.1.9, printed p.425 / PDF p.456: "If T is an induced torus then
  κ : T(k) → X∗(T)Γ_I is surjective", with the Library's local field `F` in place of KP's
  base field. The Library states it as `InducedTorusKottwitzRationalSurjectivityStatement`
  and proves it as `inducedTorusKottwitzRationalSurjectivity` (module
  `Kottwitz.InducedTorusRationalSurjectivityProof`).
- `ZExtensionPointSurjectivityStatement` (module
  `GroupScheme.Torus.InducedQuotientPointSurjectivityStatement`) at `k = K = F`:
  `H(F) → G(F)` is surjective.

The proof also uses three proved Library results: `fundamentalInertiaMapStatement`
(Galois equivariance of `fundamentalInertiaMap`), `torusInertiaComparison_proof`
(bijectivity and equivariance of `torusInertiaComparison`) and `torusKottwitzDescent`
(restriction law of `torusKottwitzRational`).

## The source argument

KP's proof of Proposition 11.5.3 runs as follows:

1. `1 → Z(k) → G̃(k) → G(k) → 1` is exact.
2. `X_*(Z)_I → π₁(G̃)_I → π₁(G)_I → 0` is exact, and its first map is injective.
3. Taking `Gal(K/k)`-invariants keeps the sequence exact, because `X_*(Z)_I` is induced.
4. The snake lemma, together with surjectivity of `Z(k) → X_*(Z)_I^Γ` (Corollary 11.1.9),
   gives surjectivity of `ker κ_{G̃} → ker κ_G`.

The Lean proof does not use step 3. Exactness of invariants on the right would give
surjectivity of `π₁(G̃)_I^Γ → π₁(G)_I^Γ`, which the kernel claim does not need. Only
two facts about invariants are needed:

- an invariant class of `π₁(G̃)_I` in the image of the injective, equivariant map
  `π₁(i)` has an invariant preimage;
- Corollary 11.1.9 lifts that preimage to `Z(k)`.

## The Lean proof of `zExtensionRationalKernelReduction`

Write `p = z.p`, `i = z.i`, `Z = z.Z`, `H = z.H`, `K = UnramifiedClosure F`,
`E = SeparableClosure F`. Write `κ'_S = reductiveInvariantInclusion F S hS ∘
reductiveKottwitzRational F S hS` for `S = H, G`.

The proof first rewrites both kernels with `ker_comp_eq_of_injective` and
`reductiveInvariantInclusion_injective`. So the goal becomes `p(ker κ'_H) = ker κ'_G`.
It then applies `map_kernel_eq_of_image_lift` with `rationalPoints.map p`, `κ'_H`,
`κ'_G` and the multiplicative form `q` of `fundamentalInertiaMap F K E G hG H hH p`.

1. *Surjectivity of `H(F) → G(F)`.* Given `g ∈ G(F)`, `ZExtensionPointSurjectivityStatement`
   at `k = K = F` gives `y` with `p(y) = rationalCoeffEquiv F G g`. Then
   `(rationalCoeffEquiv F H).symm y` maps to `g`. This follows from
   `rationalCoeffEquiv_map` and injectivity of `rationalCoeffEquiv F G`.
2. *The square.* This is `rationalKottwitz_map_of_inputs` for `f = p`. Its proof rewrites
   both sides with the restriction law of `ReductiveKottwitzDescentStatement`, then with
   `rationalCoeffEquiv_map` and `extend_affinePointsTarget`. It closes with the first
   conjunct of `ReductiveKottwitzFunctorialityStatement` at `k = F`.
3. *Lifts.* Let `h ∈ H(F)` with `q(κ'_H h) = 1`, and let `a` be the class `κ'_H(h)` in
   `π₁(H)_I`.
   - `a` is residually invariant, since it is the inclusion of an element of
     `FundamentalInvariants`.
   - `a` lies in the kernel of `π₁(p)`. By the `.zExtension` form of
     `CentralTorusInertiaExactnessStatement`, `a = π₁(i)(b)` for some `b ∈ π₁(Z)_I`.
   - `b` is invariant. For `σ ∈ Gal(K/F)`, equivariance of `π₁(i)` (from
     `fundamentalInertiaMapStatement`) gives `π₁(i)(σ b) = σ a = a = π₁(i)(b)`. The
     premise (Inj) for `G` and `z` then gives `σ b = b`.
   - Let `c = torusInertiaComparison F K E Z hZ b ∈ X_*(Z)_I`. By the equivariance clause
     of `torusInertiaComparison_proof`, `c` is invariant, so it is an element of
     `TorusInvariantTarget F Z`.
   - Premise (Cor) for the induced torus `Z` (`z.isZExtension.induced`) gives
     `x ∈ Z(F)` with `torusKottwitzRational F Z x = c`.
   - The class `κ'_Z(x)` equals `b`. Since `torusInertiaComparison` is injective, it is
     enough to compare images. The restriction law of `ReductiveKottwitzDescentStatement`
     for `Z` rewrites `κ'_Z(x)` as `reductiveKottwitz F F Z` at the extended point.
     The torus conjunct of `ReductiveKottwitzFunctorialityStatement` identifies its image
     with `torusKottwitz F F Z`. The restriction law in `torusKottwitzDescent` and the
     choice of `x` give `c`.
   - The lift is `h' = rationalPoints.map i x`.
     - `p(h') = 1`. After `rationalCoeffEquiv_map` twice, this is `x ≫ i ≫ p = 1`, which is
       `comp_quotient_eq_one` for `z.isZExtension.quotient.2.2.2`.
     - `κ'_H(h') = a`. Apply `rationalKottwitz_map_of_inputs` for `f = i`, then use
       `κ'_Z(x) = b` and `π₁(i)(b) = a`.

The module compiles. Its
theorems use only the standard axioms `propext`, `Classical.choice` and `Quot.sound`. It
sets `backward.isDefEq.respectTransparency false` and raises `maxHeartbeats` to 800000,
as the neighbouring Kottwitz modules do.
