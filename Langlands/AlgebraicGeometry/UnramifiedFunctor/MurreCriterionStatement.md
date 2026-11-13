# Murre's criterion for unramified functors

Module `Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreCriterionStatement`
defines Murre's conditions on a presheaf on the slice category `Over S` and the
`Prop`-valued statement
`Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreCriterionStatement.{u, v}`.
It proves nothing beyond the functoriality of the helper `algebraFunctor`.

Throughout, `S : Scheme.{u}` and `F : (Over S)ᵒᵖ ⥤ Type v` is an actual presheaf
on the whole slice category. Following Murre, a ring `A` is *over `S`* when a
morphism `f : Spec A ⟶ S` is given. All rings are commutative rings in `Type u`.

## Helpers

- `algebraOver f B`: for `f : Spec A ⟶ S` and an `A`-algebra `B`, the object
  `Spec B ⟶ Spec A ⟶ S` of `Over S`.
- `algebraOverBase f B : algebraOver f B ⟶ Over.mk f`: the structure morphism
  `Spec B ⟶ Spec A` over `S`.
- `algHomOver f φ`: for an `A`-algebra map `φ : B →ₐ[A] C`, the morphism
  `Spec φ : Spec C ⟶ Spec B` over `S`.
- `algebraFunctor f : CommAlgCat A ⥤ (Over S)ᵒᵖ`: the functor `B ↦ Spec B`
  built from the two previous helpers.
- `restrictQuotient B ξ'`: for an ideal `I` of `A`, an `A`-algebra `B` and
  `ξ' ∈ F(Spec (A/I))`, the restriction of `ξ'` along `Spec (B/IB) ⟶ Spec (A/I)`,
  where `IB = I.map (algebraMap A B)`.
- `LiftsTo B ξ'`: some `η ∈ F(Spec B)` restricts along
  `Spec (B/IB) ⟶ Spec B` to `restrictQuotient B ξ'`.
- `NoLargerLift B ξ'`: for no ideal `J < IB` is there an `η ∈ F(Spec (B/J))`
  restricting along `Spec (B/IB) ⟶ Spec (B/J)` to `restrictQuotient B ξ'`.

## Conditions

Each condition is a `Prop`-valued definition of the presheaf `F`.

- `SmallValues F`: every value `F(T)` is `Small.{u}`.
- `ZariskiSheaf F` (F1a): for every `T : Over S` and every open cover `𝒰` of
  `T.left` (index type in `Type u`), `F` satisfies Mathlib's
  `Presieve.IsSheafFor` for the presieve of the maps `U_i ⟶ T` over `S`.
- `FaithfullyFlatSheaf F` (F1b): for every morphism `g : T' ⟶ T` of `Over S`
  whose underlying scheme morphism is flat, surjective and quasi-compact, `F`
  satisfies `Presieve.IsSheafFor` for the singleton presieve of `g`.
- `FilteredColimits F` (F2): for every ring `R` and open immersion
  `f : Spec R ⟶ S`, the functor `algebraFunctor f ⋙ F` from `R`-algebras to
  `Type v` preserves filtered colimits indexed by categories in `Type u`
  (`PreservesFilteredColimitsOfSize.{u, u}`).
- `AdicLimits F` (F3): for every local noetherian ring `A` complete for its
  maximal ideal `m` (`IsAdicComplete m A`) and every `f : Spec A ⟶ S`, the map
  `F(Spec A) ⟶ lim_n F(Spec (A/mⁿ))` is bijective. This is stated as two parts.
  (i) Elements with equal restrictions to every `Spec (A/mⁿ)` are equal.
  (ii) Every family `s_n ∈ F(Spec (A/mⁿ))`, `n : ℕ`, with `s_{n+1}` restricting
  to `s_n` along `A/m^{n+1} → A/mⁿ`, is the family of restrictions of one
  element of `F(Spec A)`.
- `ArtinianLifting F` (F4′): let `A` be a local artinian ring with
  `f : Spec A ⟶ S` and residue field `k`. Let `A'` be an `A`-algebra with
  injective `algebraMap A A'` and `Module.length A (A' / A) = 1`, where `A' / A`
  is the quotient of `A'` by the image of `A`. Let `ξ₀ ∈ F(Spec k)` and
  `ξ' ∈ F(Spec A')` have the same image in `F(Spec (A' ⊗[A] k))`, along the
  maps induced by `A' → A' ⊗ k` and `k → A' ⊗ k`. Then some `ξ ∈ F(Spec A)`
  restricts to `ξ₀`.
- `NilpotentInjective F` (strong F5, for local artinian rings): for every local
  artinian ring `A`, every nilpotent ideal `I` and every `f : Spec A ⟶ S`, the
  restriction `F(Spec A) ⟶ F(Spec (A/I))` is injective.
- `ValuativeSeparation F` (F6): for every discrete valuation ring `V` and
  `f : Spec V ⟶ S`, the restriction `F(Spec V) ⟶ F(Spec K)` is injective, where
  `K = FractionRing V`.
- `OneDimensionalLifting F` (F7): let `A` be a local noetherian ring, complete
  for its maximal ideal, with `ringKrullDim A = 1` and exactly one associated
  prime (`associatedPrimes A A = {p}` for some `p`). Let `t` be a generic point
  of `Spec A`. Let `I` be a nilpotent ideal with `N · I = 0`, where `N` is the
  nilradical. Let `f : Spec A ⟶ S` and `ξ' ∈ F(Spec (A/I))`. If
  `LiftsTo A_t ξ'` holds for `A_t = Localization.AtPrime t.asIdeal`, then some
  `ξ ∈ F(Spec A)` restricts to `ξ'`.
- `GenericNonLifting F` (F8): let `A` be a noetherian ring and `t` a generic
  point of `Spec A`. Let `I` be a nilpotent ideal with `I · N = 0`, and let
  `f : Spec A ⟶ S` and `ξ' ∈ F(Spec (A/I))`. Suppose `NoLargerLift A_t ξ'`
  holds. Then there is `g₀ : A` with `D(g₀)` nonempty such that
  `NoLargerLift (Localization.Away g) ξ'` holds for every `g` with
  `D(g) ⊆ D(g₀)`.

## Statement

`MurreCriterionStatement.{u, v}` says the following. Let `S : Scheme.{u}` be
locally noetherian. Let `F : (Over S)ᵒᵖ ⥤ Type v` satisfy `SmallValues`,
`ZariskiSheaf`, `FaithfullyFlatSheaf`, `FilteredColimits`, `AdicLimits`,
`ArtinianLifting`, `NilpotentInjective`, `ValuativeSeparation`,
`OneDimensionalLifting` and `GenericNonLifting`. Then there are a scheme
`Y : Scheme.{u}` and a morphism `q : Y ⟶ S` with
`Nonempty (F.RepresentableBy (Over.mk q))`, `IsSeparated q`,
`LocallyOfFiniteType q` and `FormallyUnramified q`. Mathlib's
`Functor.RepresentableBy` is a bijection `(T ⟶ Over.mk q) ≃ F(T)`, natural in
`T`.

## Source

J. P. Murre, *Representation of unramified functors. Applications (according to
unpublished results of A. Grothendieck)*, Séminaire Bourbaki exp. 294
(1964–65), registered as `murre-1965-bourbaki-294-unramified-functors`
(SHA-256 `e36edaf9f965bbc92b0bdc36d8026fd7c87d890b859841d1dd965193385227dd`).
Page numbers: printed p.243 is PDF p.2 (PDF p.1 is the Numdam cover page).

- Setting, printed p.243 (PDF p.2): `S` is a locally noetherian prescheme. A
  ring is over `S` when its spectrum is. Functors are contravariant functors
  `(Sch/S)° → (Sets)`. Representability is a bijection `Hom_S(S', X) → F(S')`.
- (F1a), (F1b): printed pp.243–244 (PDF pp.2–3).
- (F2), (F3), (F4): printed p.244 (PDF p.3).
- (F5), (F6), the diagram (*) and the start of (F7): printed p.245 (PDF p.4).
  (*) is `ξ' : T' = Spec (A/I) → F` over `T = Spec A → S` with `I` nilpotent.
- The rest of (F7), (F8), Theorem 1, Corollary 1 and (F4′): printed p.246
  (PDF p.5).

Theorem 1 says: `S` locally noetherian; `F` is representable by a prescheme
locally of finite type, unramified and separated over `S` if and only if `F`
satisfies (F1)–(F8). Corollary 1 says the theorem holds with (F4) replaced by
(F4′), provided (F5) is taken in the strong form, at least for local artinian
rings `A`. The Lean statement is the sufficiency ("if") direction in the form of
Corollary 1, which the task allows.

## Correspondence and choices

- **Preschemes and unramified.** Murre's preschemes are Mathlib's schemes.
  Murre defines `X` unramified over `S` for `X` locally of finite type
  (printed p.245): `m_s O_{X,x} = m_{X,x}` and `k(x)/k(s)` separable algebraic.
  For a morphism locally of finite type this is equivalent to Mathlib's
  `FormallyUnramified`, so "locally of finite type and unramified" is recorded
  as `LocallyOfFiniteType q ∧ FormallyUnramified q`.
- **Universes and `SmallValues`.** Murre's functors take values in sets of the
  same universe as the schemes. Here `F` takes values in an arbitrary
  `Type v`, and `SmallValues` asks every value to be `u`-small. For `v = u`
  this always holds. It is necessary for representability, since hom-sets of
  `Over S` lie in `Type u`. Without it the statement would be false for
  `v = u + 1`. For example, over a nonempty `S`, the presheaf of locally
  constant functions to a set `E` that is not `u`-small satisfies the
  remaining conditions, as the functor of the étale scheme `∐_E S` would, but
  its value at `S` is not `u`-small, so it is not representable. With it, `F` is isomorphic to a presheaf valued in `Type u`,
  every condition transfers along that isomorphism, and the statement is
  Murre's.
- **(F1).** Murre's (F1a) and (F1b) are exactness of
  `F(T) → ∏ F(U_α) ⇉ ∏ F(U_α ×_T U_β)` and `F(T) → F(T') ⇉ F(T' ×_T T')`.
  Since `Over S` has pullbacks, `Presieve.IsSheafFor` for these presieves is
  equivalent to this exactness. A Zariski open covering is given as a Mathlib
  `OpenCover`, whose maps are open immersions. Faithfully flat is flat and
  surjective.
- **(F2).** "The `Spec (A_α)` are all above an open affine piece of `S`" means
  that the structure maps factor through one open immersion `Spec R ⟶ S`, so
  the `A_α` and the transition maps are `R`-algebras and `R`-algebra maps.
  Preservation of the colimit cocone of a filtered diagram is bijectivity of
  `lim→ F(Spec A_α) → F(Spec A)`.
- **(F3).** The limit of sets over the tower `n ↦ A/mⁿ` is the set of
  compatible families, so bijectivity is the stated pair. The term `n = 0`
  (`A/m⁰ = 0`) only adds a compatible empty-scheme component.
- **(F4′).** Murre's "the image `ξ₀'` of `ξ₀` in `F(Spec (A' ⊗_A k))` can be
  lifted to `ξ' ∈ F(Spec A')`" is the equality of the two images of `ξ'` and
  `ξ₀` in `F(Spec (A' ⊗[A] k))`.
- **(F5).** Strong (F5) asks injectivity for every ring and nilpotent ideal;
  Corollary 1 requires it "at least for local artinian rings", which is the
  form used. It contains Murre's weak (F5) for `k[ε]/(ε²)`.
- **(F6).** "Equal in the generic point" means equal after restriction along
  `Spec K → Spec V`.
- **(F7).** `(A/I)_t` is `A_t/I A_t`, and the restriction of `ξ'` to
  `Spec (A/I)_t` is `restrictQuotient A_t ξ'`. Murre's `t` is the generic point
  of `T`. The Lean condition quantifies over every generic point of `Spec A`;
  with one associated prime, `Spec A` is irreducible, so there is exactly one.
- **(F8).** "Subprescheme of `Spec (A_t)` strictly larger than `Spec (A/I)_t`":
  since `I` is nilpotent, such a subscheme contains every point, so it is a
  closed subscheme `Spec (A_t/J)` with `J < I A_t`. This is `NoLargerLift`.
  Irreducibility of `T` is expressed by a generic point `t`; for a reducible
  `T` there is none and the condition is vacuous. Murre's conclusion concerns
  a nonempty open `W` and every open `W₁ ⊆ W`; the Lean condition uses basic
  opens `W = D(g₀)` and `W₁ = D(g) ≅ Spec A_g`. This is equivalent for any
  presheaf. A nonempty open contains a nonempty basic open. Conversely, if the
  restriction of `ξ'` to some open `W₁ ⊆ D(g₀)` lifts to a closed subscheme of
  `W₁` with ideal sheaf `𝒥` strictly inside `I O_{W₁}`, then `𝒥 ≠ I O` on some
  basic open `D(g) ⊆ W₁`, and restricting the lift to `D(g)` contradicts
  `NoLargerLift A_g ξ'`.
- **Statement form.** The statement is a `Prop`-valued definition quantifying
  over all locally noetherian `S : Scheme.{u}` and all `F`. It is the
  sufficiency direction only; the necessity of the conditions is not stated.

## Use

The conditions are stated for the published presheaf
`Langlands.AlgebraicGeometry.Picard.TwoAxisRigidifiedLineBundle.classPresheaf`
(valued in `Type (u + 1)`) in a companion module, following Raynaud, LNM 119,
Theorem III 4.4, which cites this theorem.
