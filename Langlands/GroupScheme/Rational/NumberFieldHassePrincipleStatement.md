# Statement: the Hasse principle for first cohomology over number fields

Worker 75.

`Langlands.GroupScheme.NumberFieldHassePrincipleStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition with one universe parameter `u`.
This module does not prove it, and it adds no other definitions, theorems or
axioms. It imports:

- [`SimplyConnected.Basic`](../SimplyConnected/Basic.md), for
  `IsSimplyConnected`. Through its imports it also brings in
  [`Reductive.Semisimple`](../Reductive/Semisimple.md), for `IsSemisimple`
  and `IsAdjoint`.
- [`CocycleRelativeTrivialization`](../CocycleRelativeTrivialization.md), for
  `Cocycle.baseChange`. Through its imports it also brings in
  [`TorsorCocycle`](../TorsorCocycle.md), for `Cocycle` and `Cocycle.twist`,
  and the base-change functor `GroupScheme.baseChange`
  ([`AbelianScheme.GroupScheme`](../../AbelianScheme/GroupScheme.md)).
- [`Torus.LatticeGalois`](../Torus/LatticeGalois.md), for `algebraBaseMap`.
- [`Quaternionic.GroupSchemes`](../Quaternionic/GroupSchemes.md), for the
  isometry group `isometryGroup`. Through its imports it also brings in
  [`Quaternionic.Forms`](../Quaternionic/Forms.md), for `QuadraticForms` and
  `IsNondegenerateQuadratic`.
- [`Quaternionic.ScalarInvolution`](../Quaternionic/ScalarInvolution.md), for
  `FirstKindInvolution.scalar`.
- [`Global.AdelicGroupLocalPoints`](../../Global/AdelicGroupLocalPoints.md),
  for `Place` and `placeCompletion`.

## Lean statement

```lean
def NumberFieldHassePrincipleStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F))),
    (IsSimplyConnected G ∨ IsAdjoint G ∨
      ∃ (m : ℕ) (q : (FirstKindInvolution.scalar F).QuadraticForms (Fin m)),
        (FirstKindInvolution.scalar F).IsNondegenerateQuadratic q ∧
          Nonempty (G ≅ (FirstKindInvolution.scalar F).isometryGroup q)) →
    ∀ (L : Type u) [Field L] [Algebra F L] [FiniteDimensional F L] [Algebra.IsSeparable F L]
      (ξ₁ ξ₂ : Cocycle G (Over.mk (algebraBaseMap F L))),
      (∀ i : Langlands.Global.Place F,
        let b := algebraBaseMap F (Langlands.Global.placeCompletion F i)
        let r := (Over.mapPullbackAdj b).counit.app (Over.mk (algebraBaseMap F L))
        ∃ f : (Over.pullback b).obj (Over.mk (algebraBaseMap F L)) ⟶
            ((baseChange b).obj G).X,
          ∀ {Z : Over (Spec (CommRingCat.of (Langlands.Global.placeCompletion F i)))}
            (x y : Z ⟶ (Over.pullback b).obj (Over.mk (algebraBaseMap F L))),
            (ξ₂.baseChange b _ r).toFun x y = ((ξ₁.baseChange b _ r).twist f).toFun x y) →
      ∃ f : Over.mk (algebraBaseMap F L) ⟶ G.X,
        ∀ {Z : Over (Spec (CommRingCat.of F))} (x y : Z ⟶ Over.mk (algebraBaseMap F L)),
          ξ₂.toFun x y = (ξ₁.twist f).toFun x y
```

The declaration sits in namespace `Langlands.GroupScheme`, with
`Langlands.GroupScheme.Quaternionic` open.

## Objects and predicates used

- **Group schemes.** `GroupScheme S` is `Grp (Over S)`. An isomorphism
  `G ≅ H` is an isomorphism of group schemes over `S`.
- `IsSemisimple G` ([`Reductive.Semisimple`](../Reductive/Semisimple.md)):
  `G` is connected reductive and its scheme-theoretic centre is finite.
  `IsConnectedReductive G` ([`Reductive.Basic`](../Reductive/Basic.md))
  includes `Smooth G.X.hom`, `IsAffineHom G.X.hom` and connectedness.
- `IsSimplyConnected G`
  ([`SimplyConnected.Basic`](../SimplyConnected/Basic.md)): `G` is
  semisimple, and every central isogeny `H ⟶ G` from a semisimple group `H`
  over the same field is an isomorphism. This is algebraic simple
  connectedness.
- `IsAdjoint G` ([`Reductive.Semisimple`](../Reductive/Semisimple.md)):
  `IsSemisimple G` and `center G = ⊥`, where `center G`
  ([`Rational.Characters`](Characters.md)) is the subgroup functor of
  points that stay central after every base change. So `IsAdjoint G` says
  that `G` is semisimple with trivial scheme-theoretic centre.
- **Quadratic forms.** For the scalar involution
  `FirstKindInvolution.scalar F` (the identity of `F`), the matrix
  involution `σ.matrix (Fin m)` is the transpose. `QuadraticForms (Fin m)`
  ([`Quaternionic.Forms`](../Quaternionic/Forms.md)) is the quotient of the
  matrix space `M_m(F)` by `{X - Xᵀ}`; a representative `Q` of a class `q`
  gives the quadratic form `x ↦ xᵀ Q x` on `F^m`. `polar q = Q + Qᵀ`, the
  Gram matrix of the polar bilinear form `(x, y) ↦ q(x + y) - q(x) - q(y)`.
  `IsNondegenerateQuadratic q` says that `Q + Qᵀ` is a unit of `M_m(F)`.
- `isometryGroup q`
  ([`Quaternionic.GroupSchemes`](../Quaternionic/GroupSchemes.md)) is an
  affine group scheme over `Spec F`, a closed subgroup of the unit group of
  `M_m(F)`. By `mem_range_isometryGroupι_iff`, for a test scheme `T` with
  global sections `R` and any representative `Q` of `q`, its points over `T`
  are the units `u` of `R ⊗[F] M_m(F)` with
  `u Q uᵀ - Q ∈ R ⊗ {X - Xᵀ}`.
- **Cocycles** ([`TorsorCocycle`](../TorsorCocycle.md)). For `U : Over S`,
  `Cocycle G U` gives, for every test object `Z` over `S` and every pair
  `a b : Z ⟶ U`, a point `ξ.toFun a b : Z ⟶ G.X`, natural in `Z` and
  satisfying `ξ.toFun a c = ξ.toFun a b * ξ.toFun b c`. For
  `f : U ⟶ G.X`, the twist `ξ.twist f` has
  `(ξ.twist f).toFun a b = (a ≫ f)⁻¹ * ξ.toFun a b * (b ≫ f)`.
- `algebraBaseMap F L` ([`Torus.LatticeGalois`](../Torus/LatticeGalois.md))
  is `Spec.map` of `algebraMap F L`, the morphism `Spec L ⟶ Spec F`. So
  `Over.mk (algebraBaseMap F L)` is `Spec L` as a scheme over `Spec F`.
- **Places** ([`Global.AdelicGroupLocalPoints`](../../Global/AdelicGroupLocalPoints.md),
  [`Global.Adelic`](../../Global/Adelic.md)). `Place F` is
  `InfinitePlace F ⊕ FinitePlace F`: Mathlib's archimedean places (complex
  embeddings up to conjugation) and the nonzero prime ideals of the ring of
  integers. `placeCompletion F i` is the completion `F_v` as an `F`-algebra:
  `w.Completion` at an archimedean place `w` and `v.adicCompletion F` at a
  finite place `v`.
- **Base change to a completion.** Write `b = algebraBaseMap F F_v` and
  `U = Over.mk (algebraBaseMap F L)`. `(Over.pullback b).obj U` is the fibre
  product `Spec F_v ×_{Spec F} Spec L`, that is `Spec (F_v ⊗_F L)`, as a
  scheme over `Spec F_v`. `r` is the counit of the adjunction
  `Over.map b ⊣ Over.pullback b` at `U`: the projection of this fibre
  product to `Spec L`, as a morphism over `Spec F`. `(baseChange b).obj G`
  is `G_{F_v}`. `Cocycle.baseChange b ξ V r`
  ([`CocycleRelativeTrivialization`](../CocycleRelativeTrivialization.md))
  is the cocycle of `G_{F_v}` on `V` obtained from `ξ` by composing pairs of
  points of `V` with `r`; by `baseChange_toFun`, its values correspond to
  `ξ.toFun ((Over.map b).map x ≫ r) ((Over.map b).map y ≫ r)` under the
  points equivalence `baseChangePointsEquiv`.

## Statement in words

Let `F` be a number field and `G` a group scheme over `F` such that one of
the following holds:

- (a) `G` is semisimple and simply connected;
- (b) `G` is semisimple with trivial centre;
- (c) `G` is isomorphic to the isometry group `O(q)` of a nondegenerate
  quadratic form `q` on `F^m`, for some `m`.

Let `L` be a finite separable field extension of `F`, and let `ξ₁` and `ξ₂`
be cocycles of `G` on the cover `Spec L → Spec F`. Suppose that, for every
place `v` of `F`, the cocycles obtained by base change to the cover
`Spec (F_v ⊗_F L) → Spec F_v` are cohomologous: one is a twist of the other
by a point of `G` over `Spec (F_v ⊗_F L)`. Then `ξ₁` and `ξ₂` are
cohomologous on `Spec L`: `ξ₂ = ξ₁.twist f` for some point `f` of `G` over
`Spec L`.

## Source

J. S. Milne, *Algebraic Groups: The theory of group schemes of finite type
over a field* (Cambridge University Press, 2017), source ID
`milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`. Page numbers
are printed page numbers; the PDF page is the printed page plus 16.

- Theorem 25.64, p. 562: "Let G be an algebraic group over a global field k.
  The canonical map H^1(k, G) → ∏_v H^1(k_v, G) (169) is injective in each
  of the following cases: (a) G is semisimple and simply connected; (b) G is
  semisimple with trivial centre and k is a number field; (c) G = O(φ) for
  some nondegenerate quadratic space (V, φ) and k is a number field."
  Proof: "In the number field case, (a) was proved in Harder 1966 except
  for the case E8, which was proved in Chernousov 1989. The remaining
  statements can be deduced from (a) by using Theorem 25.63 and a knowledge
  of the cohomology of finite group schemes. See Platonov and Rapinchuk
  1994, Chapter 6. The function field case of (a) is proved in Harder
  1975."
- "Global fields", p. 562: "A global field is a finite extension of Q or
  F_p(T). We let V denote the set of primes (possibly infinite) of a global
  field k, and k_v the completion of k at a v ∈ V."
- Section 25g, p. 559: "Let G be an algebraic group over k. In this
  section, we write H^1(k, G) for the flat cohomology group (2.72). When G
  is smooth, it is canonically isomorphic to the Galois cohomology group
  H^1(Γ, G(k_s)), Γ = Gal(k_s/k) (they both classify the isomorphism
  classes of G-torsors over k; see 3.50)."
- Example 2.72, p. 61: "For an algebraic group G over k, we define
  H^1_flat(S_0, G) to be the set of isomorphism classes of torsors under G
  over S_0. Let R be a faithfully flat R_0-algebra. The torsors under
  G_{R_0} over R_0 having an R-point are classified by the cohomology set
  H^1(R/R_0, G) of the complex G(R) → G(R ⊗_{R_0} R) →
  G(R ⊗_{R_0} R ⊗_{R_0} R)". Proposition 2.69, p. 60: "Let S → S_0 be a
  G-torsor over S_0. If G is affine (resp. smooth, resp. ...) over S_0,
  then the morphism S → S_0 is affine (resp. smooth, resp. ...)."
- Proposition 3.50, p. 80: "If G is smooth, then H^1(k, G) classifies the
  isomorphism classes of G-torsors over k." Remark 3.48, p. 80: "Let (V, q)
  be a nondegenerate quadratic space over a field k of characteristic ≠ 2.
  Then H^1(k, O(q)) classifies the isomorphism classes of nondegenerate
  quadratic spaces over k with the same dimension dim(V)."
- 2.10, p. 42: for `C ∈ GL_n(k)`, the group-valued functor
  "R ⇝ {A ∈ GL_n(R) | A^t C A = C}" is an algebraic group; "If C = (c_ij),
  then an element of GL_n(R) lies in G(R) if and only if it preserves the
  form φ(x, y) = Σ c_ij x_i y_j on R^n." p. 43: "More generally, we write
  SO(V, φ) and O(V, φ) for the groups attached to a bilinear form φ on a
  vector space V."
- 2.43, p. 53: "A quadratic space over k is a pair (V, q) consisting of a
  finite-dimensional vector space over k and a quadratic form on V. Assume
  that char(k) ≠ 2. We define SO(q) to be SO(φ_q), where φ_q is the
  associated bilinear form: φ_q(x, y) = q(x + y) − q(x) − q(y)." It also
  writes `O(q)`.
- Chapter 24, p. 528: a quadratic form is nondegenerate if over `k^a` it
  becomes equivalent to a standard split form; "When char(k) ≠ 2, this is
  equivalent to the polar form φ_q being nondegenerate."
- Conventions, p. 4: "After p. 162, all algebraic groups are affine."
  Chapter 25 opening, p. 544: "Recall that all algebraic groups are affine
  over a base field k."

The 2022 corrected reprint (in the project literature folder, registered as
`milne-2022-algebraic-groups`, SHA-256
`f2ddd8fa4d263085f173934664b246007a2c0bd539739b7c82de39bfb5d21f40`; the PDF page
is the printed page plus 11) has Theorem 25.64 on printed p. 565, with the
same wording and the same proof. Its Section 25g starts on printed p. 563
with the same sentences on flat cohomology. Its Example 2.72 is on printed
p. 61 and its Proposition 3.50 on printed p. 80.

Errata. The errata snapshot of 2026-11-02 for the 2017 book (source ID
`milne-2017-algebraic-groups-errata-2026-11-02`, SHA-256
`a0c3a10dc376e1c9bd1de05b33beaf7d54e5f1ea7b408d594cfd70231a7ba0cf`) has no
entry for printed pp. 4, 42, 43, 53, 61, 528, 544, 559 or 562. Its entry for
p. 60 asks to define torsors over nonaffine bases (the bases here are
affine); its entry for p. 80 concerns 3.52 (equivalence of inner forms); its
entry for p. 563 concerns 25.66 to 25.69. None concerns the sentences quoted
above. The errata snapshot of 2026-11-04 for the 2022 reprint (source ID
`milne-2022-algebraic-groups-errata-2026-11-04`, SHA-256
`78e5f297fb2c80c6dacf413fc5abd7f82ba3dd5e5f83b5a5205dfd93bf160d49`) has two
relevant entries. The entry headed "p.562" says that in Theorems 25.62 and
25.63 (printed p. 565 of the reprint, p. 562 of the 2017 book) "the center
of the simply connected cover should be replaced by the kernel of the
isogeny". This concerns Theorem 25.63, which the proof of 25.64 cites; it
does not change the statement of 25.64. The entry headed "p.563. Section g"
says: "I sometimes write "cohomology group" for "cohomology set" (G is
usually noncommutative)". So `H^1(k, G)` is a pointed set, and (169) is
injective as a map of sets.

## Derivation from the source (provenance: derived)

- **Number fields only.** The statement takes `F` to be a number field.
  Parts (b) and (c) of Theorem 25.64 assume this. The function field case
  of part (a) is not stated: the Library's `Place` and `placeCompletion`
  are defined for number fields only.
- **Algebraic group.** Milne's algebraic groups are of finite type and, in
  chapter 25, affine (p. 4, p. 544). The Lean statement takes an arbitrary
  group scheme `G` over `Spec F` and imposes no separate affineness or
  finiteness hypothesis. Each of the three alternatives implies that `G` is
  affine and of finite type: in (a) and (b) through `IsConnectedReductive`
  (affine and smooth over a field), and in (c) because `isometryGroup q` is
  a closed subgroup of the unit group scheme of `M_m(F)`.
- **(a) Semisimple and simply connected** is `IsSimplyConnected G`, which
  includes `IsSemisimple G`; see
  [`SimplyConnected.Basic`](../SimplyConnected/Basic.md) for its comparison
  with the central-isogeny criterion of Milne, Proposition 19.15.
- **(b) Semisimple with trivial centre** is `IsAdjoint G`; Milne's Remark
  17.63 (p. 373) calls such groups adjoint (see
  [`Reductive.Semisimple`](../Reductive/Semisimple.md)). Milne's centre is
  the scheme-theoretic centre, and `center G = ⊥` says that it is trivial.
- **(c) `G = O(φ)`.** Read "=" as "is isomorphic to". The map (169) is
  functorial in `G`, so its injectivity does not depend on this choice.
  The statement asks for some `m`, some class `q` with `Q + Qᵀ` invertible,
  and an isomorphism `G ≅ isometryGroup q`. This is the same as Milne's
  hypothesis, by the following comparison. Since `F` has characteristic
  zero, every commutative `F`-algebra `R` is a `ℚ`-algebra. Under
  `R ⊗[F] M_m(F) = M_m(R)`, the submodule `R ⊗ {X - Xᵀ}` is the `R`-span of
  the matrices `E_ij - E_ji`, the alternating matrices over `R`; as `2` is
  invertible in `R`, these are exactly the matrices `D` with `D + Dᵀ = 0`.
  For `D = u Q uᵀ - Q` one has `D + Dᵀ = u C uᵀ - C` with `C = Q + Qᵀ`. So
  the points of `isometryGroup q` over `R` are the `u ∈ GL_m(R)` with
  `u C uᵀ = C`. The map `u ↦ (u⁻¹)ᵀ` is an isomorphism of group functors
  from this group onto Milne's group `{A ∈ GL_m(R) | Aᵗ C A = C}` of 2.10,
  since `(u⁻¹)ᵀᵗ C (u⁻¹)ᵀ = u⁻¹ (u C uᵀ) (uᵀ)⁻¹ = C`. That group is
  `O(F^m, φ)` for the bilinear form `φ` with Gram matrix `C`. Conversely,
  if `(V, φ)` is a nondegenerate quadratic space, choose a basis
  `V ≅ F^m`. If `φ` is read as a symmetric bilinear form with Gram matrix
  `C`, take `Q = C/2`, so that `Q + Qᵀ = C`. If it is read as a quadratic
  form `q_V`, Milne's `O(q_V)` is `O(φ_{q_V})` (2.43), and `q_V(x) = xᵀ Q x`
  for some `Q` with `Q + Qᵀ` the Gram matrix of `φ_{q_V}`. In both readings
  `O(φ) ≅ isometryGroup q` for the class `q` of `Q`. Nondegeneracy of the
  quadratic space is invertibility of the polar Gram matrix (p. 528, as
  `char F ≠ 2`), which is `IsNondegenerateQuadratic q`.
- **Places.** `Place F` lists every archimedean and every finite place of
  `F` once, and `placeCompletion F i` is the corresponding completion. This
  is Milne's set `V` of primes, possibly infinite, with the completions
  `k_v`.
- **Cohomology and the map (169).** Milne's `H^1(k, G)` is the set of
  isomorphism classes of `G`-torsors over `k` (Section 25g with 2.72). The
  map (169) sends the class of a torsor `P` to the classes of its base
  changes `P_{k_v}`. The statement expresses the injectivity of this map
  through cocycles on finite separable covers. For a group `G` satisfying
  (a), (b) or (c), injectivity of (169) is equivalent to the Lean statement
  for `G`, by the following facts, which are standard and are not proved in
  this module.
  1. A `G`-torsor `P` over `F` is nonempty, affine and of finite type over
     `F` (Proposition 2.69 for affineness), so it has a point with values in
     a finite field extension `L` of `F`. The extension `L` is separable
     because `F` has characteristic zero.
  2. A cocycle `ξ : Cocycle G U`, for `U = Spec L` over `Spec F`, is by
     naturality determined by its value on the two projections of
     `U ×_{Spec F} U = Spec (L ⊗_F L)`; this value is an element of
     `G(L ⊗_F L)`, and the cocycle identity is the cocycle condition in
     `G(L ⊗_F L ⊗_F L)` of the complex of 2.72. The relation
     `ξ₂ = ξ₁.twist f` with `f ∈ G(L)` is the relation of being cohomologous
     in that complex. By 2.72, cohomology classes of cocycles on `Spec L`
     correspond bijectively to isomorphism classes of `G`-torsors over `F`
     having an `L`-point.
  3. Two torsors with points over finite separable extensions `L₁` and
     `L₂` both have points over a common finite separable extension `L` (for
     example a compositum). Restricting a cocycle along `Spec L → Spec L₁`
     gives a cocycle that describes the same torsor.
  4. For every place `v`, `F_v ⊗_F L` is a nonzero finite product of finite
     separable field extensions of `F_v`, hence faithfully flat over `F_v`,
     and `Spec (F_v ⊗_F L) → Spec F_v` is finite étale and surjective. The
     base-changed cocycle `ξ.baseChange b _ r` describes the torsor
     `P_{F_v}`, with the point obtained from the `L`-point of `P`. So 2.72
     applies over `F_v`: the hypothesis of the statement at `v` says that
     the two torsors become isomorphic over `F_v`.

  Given these facts, injectivity of (169) implies the Lean statement (if
  the base changes agree at every `v`, the two torsors are isomorphic, so
  the cocycles are cohomologous by fact 2), and the Lean statement implies
  injectivity (represent two torsors by cocycles on a common `Spec L`,
  using facts 1 and 3). Injectivity concerns pairs of classes, not only the
  class of the trivial torsor, as `H^1` is only a pointed set.
- **Universe.** `F` and `L` live in `Type u`; the completions
  `placeCompletion F i` are in `CommAlgCat.{u}`.

Sanity check. For `G = O(q)` with `q` nondegenerate, Remark 3.48 identifies
`H^1(F, O(q))` with the isomorphism classes of nondegenerate quadratic
spaces over `F` of dimension `m`. Case (c) then says: two nondegenerate
quadratic spaces over the number field `F` of the same dimension that are
isomorphic over every completion `F_v` are isomorphic over `F`. This is the
Hasse–Minkowski theorem in its form for isometry classes.

## Relation to the Library

- `LocalSimplyConnectedCocycleVanishingStatement`
  ([`SimplyConnected.LocalCocycleVanishingStatement`](../SimplyConnected/LocalCocycleVanishingStatement.md))
  uses the same cocycles on finite separable covers to state the vanishing
  of `H^1` for simply connected groups over nonarchimedean local fields.
- The Library has no statement of Theorem 25.64.

## For the later proof (not part of this unit)

Milne gives no proof. He refers to Harder 1966 and Chernousov 1989 (for
`E_8`) for case (a) over number fields, and to Theorem 25.63 and
Platonov–Rapinchuk 1994, Chapter 6, for the other cases.
