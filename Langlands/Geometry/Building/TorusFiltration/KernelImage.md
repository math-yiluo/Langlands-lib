# Kernels and images of the special-fibre maps between minimal congruent torus models

The module `Langlands.Geometry.Building.TorusFiltration.KernelImage` defines
the comparison homomorphisms between the minimal congruent models of a torus
and their special-fibre maps. It then states Kaletha–Prasad Proposition
B.10.15 as the Prop-valued `MinimalCongruentKernelImageStatement`. The module
supplies no proof of that statement.

## Setting

Let `F : Type u` be a nonarchimedean local field (`IsNonarchimedeanLocalField
F`, with its `ValuativeRel` and topology), of either characteristic. Put
`K = inertiaFixedField F`, the maximal unramified extension, `O =
fixedFieldIntegers F` and `κ = IsLocalRing.ResidueField O`. The ring `O` is a
strictly Henselian discrete valuation ring and `κ` is algebraically closed.

Let `T : CommGroupScheme (Spec (CommRingCat.of K))` with `hT : IsTorus
T.toGrp`. For a depth `a : ℝ≥0` write `𝒯_a = (minimalCongruentModel F T hT
a).val`. By `minimalCongruentModel` it is a smooth model of `T` over `O` with
geometrically connected fibres, and its integral points are exactly
`minimalCongruentPoints F T hT a`, the term `T(K)_a` of the minimal congruent
filtration. Write `𝒯̄_a = 𝒯_a.specialFibre`, an actual group scheme over
`Spec κ`.

## The comparison homomorphisms

For `a ≤ b`, `minimalCongruentModelHom F T hT hab` is a model homomorphism
`𝒯_b → 𝒯_a` extending the identity of `T`. Its type is
`IntegralModel.Hom` over `𝟙 T.toGrp`. Such a homomorphism is a morphism of
group schemes over `O` whose generic fibre, under the identifications of both
generic fibres with `T`, is the identity of `T`.

The definition follows Kaletha–Prasad Corollary 2.10.10: a morphism of
generic fibres extends from a smooth affine model to an affine model exactly
when it carries integral points into integral points. The Lean definition
proceeds as follows.

- `minimalCongruentPoints_antitone` gives `T(K)_b ⊆ T(K)_a`.
- The integral-point equalities recorded by `minimalCongruentModel` turn this
  into the inclusion of the integral points of `𝒯_b` in those of `𝒯_a`.
- `exists_hom_of_map_integralPoints_le`, applied to the published
  `IntegralModel.smoothHomExtension F` and the smoothness of `𝒯_b`, then
  gives a model homomorphism.
- The definition takes an element of this nonempty type by
  `Classical.choice`.

The choice has no effect on the value. The module
`Langlands.GroupScheme.IntegralModel.GenericRigidity` proves
`IntegralModel.Hom.hom_eq` and the instance `Subsingleton (M.Hom N f)`: two
model homomorphisms extending the same generic morphism are equal. Hence
every model homomorphism `𝒯_b → 𝒯_a` extending the identity of `T` equals
`minimalCongruentModelHom F T hT hab`. In particular, the identity of `𝒯_a`
is the comparison for `a ≤ a`. This module does not state these
consequences as separate lemmas.

`minimalCongruentFibreMap F T hT hab : 𝒯̄_b ⟶ 𝒯̄_a` is the special-fibre
map `(minimalCongruentModelHom F T hT hab).specialFibreMap`. It is the
base change of the comparison along the residue map `O → κ`, a homomorphism
of group schemes over `Spec κ`. This is Kaletha–Prasad's map `𝒯̄_b^mc →
𝒯̄_a^mc`, written `f_{ba}` below.

## The statement

`MinimalCongruentKernelImageStatement.{u}` quantifies over every
nonarchimedean local field `F : Type u` with the instances above, every
`T` and `hT : IsTorus T.toGrp` as above, and all depths `r s : ℝ≥0` with
`r < s`. Put `t = max s (r + 1)`, and let

- `f = f_{sr} : 𝒯̄_s ⟶ 𝒯̄_r`, the fibre map for `r ≤ s`;
- `g = f_{ts} : 𝒯̄_t ⟶ 𝒯̄_s`, the fibre map for `s ≤ max s (r + 1)`.

Let `J = kernel f` be the full scheme-theoretic kernel from
`Langlands.AbelianScheme.Kernel`: the pullback of `f` along the unit section
of `𝒯̄_r`, with inclusion `kernelι f : J ⟶ 𝒯̄_s`. No reduced structure is
taken. The statement asserts the following five conjuncts.

1. `Smooth (kernel f).X.hom`: `J` is smooth over `κ`.
2. `ConnectedSpace (kernel f).X.left`: the underlying scheme of `J` is
   nonempty and connected. Since `κ` is algebraically closed, this is the
   same as geometric connectedness.
3. `IsUnipotent (kernel f)`: in the sense of
   `Langlands.GroupScheme.Reductive.Basic`, every nonzero finite-dimensional
   matrix representation of `J` has a nonzero fixed vector.
4. `IsClosedSubgroup (kernelι f)`: the underlying scheme morphism of the
   inclusion `J ⟶ 𝒯̄_s` is a closed immersion.
5. There is a homomorphism `q : 𝒯̄_t ⟶ J` with `q ≫ kernelι f = g` and
   `RelativeRoot.IsFppfQuotient (SubgroupFunctor.range (kernelι g)) q`. The
   predicate says that the underlying scheme morphism of `q` is flat,
   surjective and locally of finite presentation. It also says that the
   actual kernel of `q` has the same subgroup functor of `𝒯̄_t` as the
   actual kernel of `g`, on every test scheme over `Spec κ`.

### The image clause

Conjuncts 4 and 5 say that `J`, with its inclusion `kernelι f`, is the
scheme-theoretic image of `g`. They follow the image vocabulary of
`AffineHomImageStatement` in `Langlands.GroupScheme.AffineHomImageStatement`.
Milne's homomorphism theorem (Theorems 3.34 and 5.39) factors a
homomorphism `g` of algebraic groups as `i ∘ q` with `q` faithfully flat and
`i` a closed immersion. The factorization is essentially unique (Remark 5.40),
and the target of `q` is the image of `g` (Remark 5.42). In diagrammatic
order, Milne's `g = i ∘ q` is the Lean equation `q ≫ kernelι f = g`.

Two parts of conjuncts 4 and 5 hold for every such factorization.

- The group `𝒯̄_r` is affine, hence separated, so its unit section is a
  closed immersion. Its pullback `kernelι f` is therefore a closed immersion
  and a monomorphism. Conjunct 4 is stated so that conjuncts 4 and 5 together
  have the form of the image factorization.
- Because `kernelι f` is a monomorphism preserving the unit, a point is
  killed by `q` exactly when it is killed by `q ≫ kernelι f = g`. Since `J`
  is of finite type over the field `κ`, any `q` that is locally of finite
  type is locally of finite presentation.

Hence conjunct 5 is equivalent to a factorization of `g` through `kernelι f`
whose map `𝒯̄_t → J` is faithfully flat, that is, flat and surjective.
Together with conjunct 1, which makes `J` reduced, this gives
Kaletha–Prasad's equality `ker(𝒯̄_s → 𝒯̄_r) = im(𝒯̄_t → 𝒯̄_s)` of closed
subgroup schemes of `𝒯̄_s`.

### Scope

- Depths are all nonnegative reals with `r < s`. In particular `r = 0` is
  included, where `𝒯̄_0` is the special fibre of the depth-zero model.
- When `s ≥ r + 1`, the depth `max s (r + 1)` equals `s`, though not by
  definition. Then `g` is the comparison of `𝒯_s` with itself, which is the
  identity by the uniqueness above. The statement then says that `J` is all
  of `𝒯̄_s`, that is, `f` is trivial. When `r < s < r + 1`, the depth `t` is
  `r + 1`.
- There is no tameness, weak-inducedness, residue-characteristic or
  splitting hypothesis on `T`. Kaletha–Prasad state the proposition for all
  tori.
- The statement claims unipotence, not that `J` is a vector group. The
  stronger assertion of Kaletha–Prasad Proposition B.10.12, that every
  positive-depth minimal congruent special fibre is a vector group, fails at
  shallow depth for some ramified induced tori. The page of
  `Langlands.Geometry.Building.TorusFiltration.RadicalStatement` gives an
  example: the induced torus `Res_{E/K} G_m` at depth `1/3`, where `K` is the
  maximal unramified extension of the Laurent series field `F₂((ϖ))` and
  `E = K(u)` with `u³ = ϖ`. The polynomial `X³ - ϖ` is Eisenstein, so `E/K`
  is totally ramified of degree three. The degree is prime to the residue
  characteristic two, so this extension is tamely ramified.

## Source and translation

The source is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
registered as `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
Printed page `p` is PDF page `p + 31`.

- Proposition B.10.15 (printed pp. 693–694 / PDF pp. 724–725): for
  `0 ≤ r < s` and `t = max(s, r + 1)`, `ker(𝒯̄_s^mc → 𝒯̄_r^mc) =
  im(𝒯̄_t^mc → 𝒯̄_s^mc)`, and this is a smooth connected unipotent group.
- Corollary 2.10.10 (printed p. 124 / PDF p. 155): extension of a morphism
  of generic fibres from a smooth affine model, characterized by integral
  points, and its uniqueness.
- Lemma 8.1.3 (printed p. 284 / PDF p. 315), Proposition B.10.10 (printed
  p. 690 / PDF p. 721) and Lemma A.5.13(4) (printed pp. 636–637 / PDF
  pp. 667–668) are used in the cited proof. Remark 2.10.8 (printed p. 123 /
  PDF p. 154) gives the identification of special-fibre Lie algebras that
  the proof uses.
- Proposition B.10.12 (printed p. 691 / PDF p. 722) is the vector-group
  assertion that the statement does not include.

Kaletha–Prasad state the proposition for a torus over the base field `k` and
its models over the integers of `k`. Their proof begins by base change to
the maximal unramified extension. The Lean statement is formulated directly
over `K = inertiaFixedField F` and `O = fixedFieldIntegers F`. It makes no
claim over the base field `F`.

The cited proof runs as follows. It first compares `κ`-points: a point of
`𝒯̄_s` lifts to an `O`-point by Lemma 8.1.3. By the congruence property
(Proposition B.10.10) its image in `𝒯̄_r` is trivial exactly when the lift
lies in `T(K)_{r+1}`, hence in `T(K)_t`. This identifies the image of `g`
with the reduced kernel. For `s ≥ r + 1` the reduced kernel is all of `𝒯̄_s`,
which forces the kernel to be all of `𝒯̄_s`. For `r < s < r + 1` a count of
dimensions shows that the kernel has the dimension of its tangent space,
hence is smooth. The count uses the following facts.

- The Lie algebra `t(K)_a` of `𝒯_a` is an integral lattice in the Lie
  algebra of `T`. Since `𝒯_a` is smooth, `t(K)_a ⊗_O κ` is the Lie algebra
  of the special fibre `𝒯̄_a` (Remark 2.10.8, printed p. 123 / PDF
  p. 154).
- The filtration is congruent (Proposition B.10.10), so `𝒯_{r+1}` is the
  first congruence group scheme of `𝒯_r`. Lemma A.5.13(4), applied to
  `𝒯_r`, then gives the lattice identity `t(K)_{r+1} = 𝔪 t(K)_r`, where `𝔪`
  is the maximal ideal of `O`.

The count runs along `𝒯̄_{r+1} → 𝒯̄_s → 𝒯̄_r`. The cokernels of the
Lie algebra maps are `t(K)_s / t(K)_{r+1}` and `t(K)_r / t(K)_s`. Their
dimensions add up to that of `t(K)_r / 𝔪 t(K)_r`, which is `dim T`. This
module records the statement only.

The authors' corrections, `kaletha-prasad-2024-corrections`, version of
1 November 2024, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`, PDF
p. 50, add a separately numbered Remark B.10.15 on Galois stability of the
filtration and descent of the models. That remark does not change
Proposition B.10.15. The same page amends Definition B.10.8 of the
filtration; the pages of the `Points` and `ModelAssembly` modules in
`Langlands.Geometry.Building.TorusFiltration` relate the Library's
filtration to that definition.

The image vocabulary follows J. S. Milne, *Algebraic Groups: The Theory of
Group Schemes of Finite Type over a Field*, corrected reprint, Cambridge
University Press, 2022, registered as `milne-2022-algebraic-groups`, SHA-256
`f2ddd8fa4d263085f173934664b246007a2c0bd539739b7c82de39bfb5d21f40`:
Theorem 3.34 (printed p. 75), Theorem 5.39 and Remarks 5.40 and 5.42
(printed p. 108).
