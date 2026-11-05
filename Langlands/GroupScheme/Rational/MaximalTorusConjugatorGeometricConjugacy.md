# Geometric conjugacy step for the generic semisimple-centralizer case

Author: Worker 1420.

This internal, derived module proves the conjugacy step of the generic
semisimple-centralizer case (Case C) of the dimension induction for
`MaximalTorusParameterUnirationalStatement`. Its main theorem is conditional on two
published but unproved Library propositions, which appear as explicit hypotheses:
`MaximalTorusConjugacyStatement` (conjugacy of maximal tori over an algebraically closed
field, `Absolute/BorelStatement`) and `MaximalTorusBaseChangeStatement` (maximal tori stay
maximal after a field extension, `Torus/MaximalBaseChangeStatement`). Apart from these
hypotheses, the fields are arbitrary.

## Lifting through a monomorphism

`exists_lift_of_forall_mem_range`: let `i : H → G` be a homomorphism of group schemes over
any base `S` whose underlying morphism is a monomorphism. Let `f : T → G` be a homomorphism
such that every point `x ≫ f`, over every test scheme, lies in the all-test range of `i`.
Then `f = f' ≫ i` for some homomorphism `f'`. The proof chooses preimages pointwise. It
checks multiplicativity and naturality by cancelling `i`, and assembles `f'` with the
published `homOfPoints`.

## Conjugacy over an algebraically closed field

`exists_innerIso_comp_eq_of_conj_mem_range` assumes `MaximalTorusConjugacyStatement`. Its
setting is a field `Ω` that is algebraically closed and group schemes `G` and `H` over
`Ω`, with `H` smooth and affine with connected underlying space. It takes a closed
subgroup `i : H → G` (`IsClosedSubgroup i`), maximal tori `j₀ : T₀ → G` and `j : T → H`,
and a rational point `c` of `G`. Suppose conjugation by the constant family of `c` sends
every point of the range of `j₀` into the range of `i`. Then there are a rational point `h`
of `H` and an isomorphism `φ : T₀ ≅ T` with

`j₀ ≫ (innerIso c) ≫ (innerIso (h ≫ i)) = φ ≫ j ≫ i`.

The proof lifts `j₀ ≫ innerIso c` through `i` to `f : T₀ → H`. The published
`IsMaximalTorus.comp_iso_iff` shows that `f ≫ i` is a maximal torus of `G`, and
`IsMaximalTorus.of_comp` shows that `f` is one of `H`. The conjugacy statement for `f`
and `j` in `H` then gives `h` and `φ`. The published `innerIso_hom_comp` moves the inner
automorphism of `H` across `i`.

`mem_range_iff_of_innerIso_comp_eq`: over any base `S`, suppose
`j₀ ≫ innerIso c ≫ innerIso d = φ ≫ j'` for rational points `c, d` and an isomorphism `φ`.
Then a point `t` over a test scheme `U` lies in the range of `j₀` exactly when its conjugate
by the constant family of `d * c` lies in the range of `j'`. The reverse direction applies
`φ⁻¹` and uses injectivity of conjugation.

## Transport along a base morphism

Fix a morphism of schemes `β : S' → S` and a group scheme `M` over `S`.

- `overMapToMk β V'`: for a scheme `V'` over `S'`, viewed over `S` through `β`, the
  morphism to `Over.mk β` given by the structure morphism of `V'`.
- `baseChangePointsEquiv_constantPoint_conj`: let `q : Over.mk β → M` correspond, under
  the published `baseChangePointsEquiv`, to a rational point `q'` of the base change `M_β`.
  Then the equivalence sends conjugation by the constant family of `q'` over `V'` to
  conjugation by `overMapToMk β V' ≫ q`.
- `conj_mem_baseChange_of_forall`: let `F, E` be subgroup functors of `M`. Suppose that,
  for every `V` over `S` and `y : V → Over.mk β`, conjugation by `y ≫ q` maps `F(V)` into
  `E(V)`. Then conjugation by the constant family of `q'` maps the base change of `F` into
  the base change of `E` over every scheme over `S'`.
- `forall_iff_of_baseChange`: conversely, suppose a point lies in the base change of `F`
  exactly when its `q'`-conjugate lies in the base change of `E`, over every scheme over
  `S'`. Then for every `V` over `S`, `y : V → Over.mk β` and point `t` of `M` over `V`,
  `t ∈ F(V)` holds exactly when the conjugate of `t` by `y ≫ q` lies in `E(V)`. The proof
  regards `V` over `S'` through `y`. It compares it with `V` through an isomorphism whose
  underlying scheme map is the identity.

## The geometric conjugacy step

`exists_torusConjugator_of_conj_mem_range` assumes both Library propositions. It takes:

- fields `k, K, Ω` with `k → K → Ω`, where `Ω` is algebraically closed;
- `b = algebraBaseMap k K`, and a smooth affine group scheme `G` over `k` with a maximal
  torus `j₀`;
- a group scheme `H` over `K` that is smooth and affine with connected underlying space,
  with a maximal torus `j : T → H` and a closed subgroup `i : H → G_K` into the base change
  `G_K` along `b`;
- a point `c : Over.mk (algebraBaseMap K Ω) → G_K`.

Suppose that for every `V` over `K` and `y : V → Over.mk (algebraBaseMap K Ω)`,
conjugation by `y ≫ c` maps the base change of the range of `j₀` into the range of `i`.
Then there is a point `h₁ : Over.mk (algebraBaseMap K Ω) → H` with the following
property, for `p = (h₁ ≫ i) * c`. For every such `V` and `y` and every point `t` of `G_K`
over `V`, `t` lies in the base change of the range of `j₀` exactly when its conjugate by
`y ≫ p` lies in the range of `j ≫ i`. This is the conjugation condition of
`IsTorusConjugatorTransfer` for `Y = Spec Ω` and `p`.

The proof works over `Ω`:

1. Apply `MaximalTorusBaseChangeStatement` to `j₀` along `k → K`, then again along
   `K → Ω`, and to `j` along `K → Ω`. This gives maximal tori of `G_{KΩ}` and `H_Ω`.
2. The base change `i_Ω` is closed (published `IsClosedSubgroup.baseChange`). `H_Ω` is
   connected (published `connectedSpace_baseChange_of_smooth_affine`).
3. Turn `c` into a rational point `c'` of `G_{KΩ}` with `baseChangePointsEquiv`.
   `conj_mem_baseChange_of_forall` and the published `range_baseChangeHom` give the
   hypothesis of the previous theorem.
4. Apply it to get `h` and `φ`, and let `h₁` correspond to `h`.
   `mem_range_iff_of_innerIso_comp_eq` and `forall_iff_of_baseChange` give the
   conclusion.

## Provenance

The module is derived from the published `homOfPoints`, `innerIso`, `comp_innerIso_hom`,
`constantPointHom`, `innerIso_hom_comp`, `IsMaximalTorus.of_comp`,
`IsMaximalTorus.comp_iso_iff`, `IsClosedSubgroup.baseChange`, `SubgroupFunctor.baseChange`,
`range_baseChangeHom`, `baseChangePointsEquiv` with its naturality and composition lemmas,
and `connectedSpace_baseChange_of_smooth_affine`. The two hypotheses are the published
`MaximalTorusConjugacyStatement` and `MaximalTorusBaseChangeStatement`. The mathematical
step is the standard use of conjugacy of maximal tori over an algebraic closure (Milne,
*Algebraic Groups* (2017), Theorem 17.10 together with Theorem 17.82) in the
semisimple-centralizer case of the induction modeled on SGA 3, Exposé XIV, Théorème 6.1.
No literature statement is formalized here.
