# Quasi-projective representability of the Hilbert-polynomial pieces of the Picard sheaf

Authors: Worker 5705.

Worker 5705 wrote the Lean file and this description for task
`07219dde-fd87-48cf-83be-db16cbb3707c` (Task 5705), after reading pp.27–31 of
Kleiman's survey (Theorem 4.8, its proof, Lemma 4.9 and Exercise 4.10). The
proposition isolates the central step of that proof. Each open piece `P^φ_m`
of the Picard sheaf is represented by a quasi-projective scheme, obtained as
the quotient of an open part of the divisor scheme by the linear-system
equivalence relation. The pieces enter through hypotheses, in exactly the form
in which the accepted companion statement `PicardHilbertPolynomialPiecesStatement`
provides them.

No proof is asserted here.

## Statement

The module defines one declaration,
`Langlands.AlgebraicGeometry.Picard.PicardHilbertPiecesRepresentabilityStatement`,
with the single universe parameter `u`. It is a proposition (`def … : Prop`).

### Setting

It quantifies over a noetherian commutative ring `A : Type u`, with
`S = Spec (CommRingCat.of A)`, a scheme `X`, a morphism `f : X ⟶ S` and a
module `𝓛X : X.Modules`, and assumes that

- `f` is proper (`IsProper`), flat (`Flat`) and geometrically integral
  (`GeometricallyIntegral`);
- `f` has a section: there is `ε : S ⟶ X` with `ε ≫ f = 𝟙 S`;
- `Scheme.Modules.IsInvertible 𝓛X` and
  `Scheme.Modules.ClosedImmersionBySections 𝓛X f`: `𝓛X` is invertible and
  finitely many of its global sections define a closed immersion of `X` into a
  finite projective space over `A`. So `𝓛X` plays the role of Kleiman's
  `O_X(1)`.

Notation, as in `PicardHilbertPolynomialPiecesStatement`: for `s : T ⟶ S`,
`X_T = pullback f s` with projections `pullback.fst f s : X_T ⟶ X` and
`pullback.snd f s : X_T ⟶ T`. For a module `L` on `X_T`,
`L(m) = L ⊗ 𝓛X_T ⊗ ⋯ ⊗ 𝓛X_T` (`m` factors, bracketed to the left, written in
Lean with `Nat.rec`). For a point `t` of `T`, `X_t` is the fibre over
`Spec κ(t)` and `Hⁱ(X_t, -)` is the Library's
`Modules.DerivedSections.relativeCohomology`. The tensor product and unit
elaborate to the FLT port's monoidal structure on module sheaves
(`AlgebraicGeometry.Scheme.Modules.monoidalCategory`).

### Hypotheses on the pieces

It then quantifies over a type `κ : Type`, polynomials
`θ : κ → ℕ → Polynomial ℚ`, and a function `U` assigning to every scheme `T`,
every `s : T ⟶ S`, every module `L` on `X_T` and all `c : κ`, `m : ℕ` an open
`U T s L c m : T.Opens`. It assumes the following four properties, in which
`T`, `T'` are locally noetherian and `L` is invertible.

1. **Twist invariance.** If `L, L'` on `X_T` and `N` on `T` are invertible and
   `L ≅ L' ⊗ (pullback.snd f s)^* N`, then `U T s L c m = U T s L' c m`.
2. **Base change.** For `h : T' ⟶ T`,
   `U T' (h ≫ s) (h_X^* L) c m = h ⁻¹ᵁ U T s L c m`, where
   `h_X = pullback.map f (h ≫ s) f s (𝟙 X) h (𝟙 _) _ _`.
3. **Cohomology on a piece.** If `U T s L c m = ⊤`, then at every point `t`
   of `T`, `H¹(X_t, L(m)_t)` is zero and `H⁰(X_t, L(m)_t)` is not zero.
4. **Hilbert polynomials of divisors.** For a noetherian ring `B`,
   `s : Spec B ⟶ S` and `L` with `U (Spec B) s L c m = ⊤`, let `I` be a relative
   effective Cartier ideal on `X_B` with `O(I) ≅ L(m) ⊗ (pullback.snd f s)^* N`
   for an invertible `N` on `Spec B`. Then for every algebraically closed field
   `k` and every ring map `B →+* k`, `dim_k H⁰(E_k, O_{E_k}(n)) = θ c m (n)` for
   all large `n`, measured by `Scheme.Modules.geomFibreH0Finrank`.

These four hypotheses are, verbatim, properties 1, 2, 4 and 5 of
`PicardHilbertPolynomialPiecesStatement`. Its property 3, the shape of the
decomposition (increasing in `m`, disjoint in `c`, covering), concerns how the
pieces fit together. It is not needed to represent a single piece, so it is
omitted.

### Conclusion

For all `c : κ` and `m : ℕ` there exist an object `Q : Over S` and a natural
transformation

```lean
β : uliftYoneda.{u + 1}.obj Q ⟶ RelativePicard.classSheafPresheaf f
```

from the functor of points of `Q`, with values lifted to `Type (u + 1)`, to the
Library's fppf Picard class sheaf of `f`, such that

- `IsHQuasiProjective Q.hom`: the Library's predicate
  (`Langlands/AlgebraicGeometry/HQuasiProjective.lean`), i.e. `Q.left` admits a
  quasi-compact immersion into a finite projective space `ProjectiveSpace A n`
  that commutes with the maps to `S`;
- for every `T : Over S` with `T.left` locally noetherian:
  - `β.app (op T)` is injective;
  - for every line bundle `L : LineBundle ((relativeSpace f).obj T)`, the class
    `RelativePicard.sheafClassOf f T L` lies in the image of `β.app (op T)` if
    and only if
    `U T.left T.hom ((Scheme.Modules.pullback (relativeSpaceSymmetry f T).inv).obj L.obj) c m = ⊤`.

The Picard sheaf lives on `(relativeSpace f).obj T = pullback T.hom f`
(`T ×_S X`), while `U` takes modules on `pullback f T.hom` (`X ×_S T`). The
module is transported along the Library's symmetry isomorphism
`relativeSpaceSymmetry f T : pullback T.hom f ≅ pullback f T.hom`; its inverse
is a morphism `pullback f T.hom ⟶ pullback T.hom f`, and `L.obj` is pulled back
along it.

In words: on locally noetherian tests, `Q` represents the subfunctor of the
Picard sheaf formed by the classes of line bundles `L` with `U(T, L, c, m) = T`.
That is Kleiman's piece `P^φ_m` (for `c = (φ, ψ)` in the intended instance).

## Source and derivation

The source is S. L. Kleiman, *The Picard scheme*, arXiv math/0504020v1
(2005), registered as `kleiman-2005-picard-scheme-arxiv-math0504020v1`, proof
of Theorem 4.8, pp.29–31. Kleiman's argument (p.30) runs as follows:

- twisting by `O(m)` identifies `P^φ_m` with `P^{φ₀}_0`;
- `Z := P^{φ₀}_0 ×_P Div_{X/S}` is an open subscheme of `Div_{X/S}` and lies in
  `Hilb^θ_{X/S}`, with `θ(n) = ψ(n) − φ₀(n)`. Hence `Z` is quasi-projective;
- the Abel map `α : Z → P^{φ₀}_0` is a surjection of sheaves. Over a
  representative `L′` on `X_{T′}`, the product `T′ ×_{P^{φ₀}_0} Z` is
  `LinSys_{L′}`, which is `P(Q)` by Theorem 3.13 (p.25) and is smooth because
  `H¹(X_t, L_t) = 0`;
- `Z ×_{P^{φ₀}_0} Z` is a scheme whose first projection is smooth and
  projective (take `T := Z` above);
- Lemma 4.9 (pp.30–31) then gives a quasi-projective `Q` representing
  `P^{φ₀}_0`. A flat proper equivalence relation on a quasi-projective scheme
  is effective ([AK80, Thm. 2.9]), and the quotient is the coequalizer of
  sheaves by Exercise 4.10 (p.31).

The proposition is a derived form of this step. It differs from the source as
follows; each difference is justified.

1. **The pieces are hypotheses.** Kleiman defines `P^φ_m` by conditions
   (4.8.1) and (4.8.3) and proves the needed properties in the course of the
   proof. Here any family of opens with properties 1–4 is allowed. The proof
   above uses only these properties:
   - property 1: `Z` and the Abel map depend only on classes modulo `Pic(T)`;
   - property 2: `Z` is an open part of the divisor scheme, and the pieces are
     compatible with pullback;
   - property 3: `H¹ = 0` gives the projective bundle of Theorem 3.13 over each
     point; `H⁰ ≠ 0` makes it surjective. This is the correction recorded in
     `PicardHilbertPolynomialPiecesStatement`: without it `P(Q)` can be empty,
     for example for `O(−1)` on `ℙ¹`;
   - property 4: `Z` lies in the part of the divisor scheme with Hilbert
     polynomial `θ c m`.
2. **The twist is built in.** Instead of identifying `P^φ_m` with `P^{φ₀}_0`,
   property 4 is phrased directly for `L(m)`. So the Abel map sends a divisor
   `W` to the class of `O(W) ⊗ O(−m)`. The `−m` twist uses the inverse of the
   invertible `𝓛X`.
3. **Fppf instead of étale.** The Library's Picard sheaf is the fppf
   sheafification. The surjection `Z → P^{φ₀}_0` can be checked on the fppf
   covering `P(Q) → T′`, which is flat, proper, of finite presentation and
   surjective. So the étale-section step through EGA IV 17.16.3 (used twice on
   pp.30–31) is not needed.
4. **Tests are locally noetherian.** Injectivity and the description of the
   image are asserted only for locally noetherian `T`, Kleiman's standing
   convention (p.15). The map `β` itself is a natural transformation on all
   `S`-schemes.
5. **`ψ` is not split off.** Kleiman makes `χ(X_s, O(n)) = ψ(n)` constant by
   passing to an open and closed part of `S` (p.30). Here the polynomial
   `θ c m` is part of the given data (property 4), so no splitting of `S` is
   needed.
6. **The section.** Kleiman's Theorem 4.8 does not assume a section. It is
   assumed here so that, by Theorem 2.5 (p.18) and Exercise 3.11 (p.25), a
   class in the fppf sheaf is the class of a line bundle up to `Pic(T)`. The
   condition `sheafClassOf L ∈ range` is then governed by the actual line
   bundle `L`; compare the companion statement
   `ProperFlatIntegralSheafClassTwistStatement`.
7. **Conclusion phrased by a map and its image.** Instead of "the subfunctor
   `P^φ_m` is representable", the proposition gives a scheme `Q`, a map `β`
   into the Picard sheaf that is injective on locally noetherian tests, and its
   image on classes of line bundles. That is the form used by the gluing
   statement `NoetherianOpenPiecesGluingStatement`.

The intended proof combines the companion statements
`RelativeEffectiveDivisorHilbertPiecesStatement` (the divisor scheme and its
quasi-projective Hilbert-polynomial pieces; in the Library),
`ProperFlatIntegralLinearSystemStatement` (Theorem 3.13 in the form needed
here; in the Library), `FppfQuotientLocallyNoetherianStatement` (Lemma 4.9
with [AK80, Thm. 2.9], fppf form, on locally noetherian tests; accepted, staged
by Worker 22) and `ProperFlatIntegralSheafClassTwistStatement`. This describes
intended use only; the module imports none of them.

## Conventions and scope

- `S` is the spectrum of a noetherian ring, as in Theorem 4.8(2) after
  Kleiman's reduction (p.28).
- `Q` and `β` are existential and depend on `(c, m)`. Nothing is asserted
  about compatibility between different pieces; that is the job of the
  hypotheses' base-change property and of the gluing statement.
- The description of the image covers classes of actual line bundles on `X_T`.
  By the companion statement `ProperFlatIntegralSheafClassTwistStatement`,
  under the present hypotheses (a section exists) every element of the Picard
  sheaf is of this form.
