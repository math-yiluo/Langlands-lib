# Independence of `H(K)^0` from its defining data

`Langlands.Geometry.Building.UnramifiedZeroPointsIndependenceStatement` is the
independence part of Kaletha–Prasad, Lemma 2.6.24 (printed p.104/PDF p.135, proof
printed p.105/PDF p.136), for Definition 2.6.23(1) over the maximal unramified
extension `K = UnramifiedClosure F` of a nonarchimedean local field `F`.

For every `K`-group scheme `H` and any two values `E E' : UnramifiedZeroDatum F H`, it
asserts `E.zeroPoints = E'.zeroPoints`. Here `E.zeroPoints` is the existing subgroup
`H(K)^♮ ⊔ T(K)^0` of `H(K)`:

* `H(K)^♮ = E.simplyConnectedImage` is the image of `C(K) → H(K)` for the supplied simply
  connected cover `π : C → D` of the derived subgroup `d : D → H`
  (`IsSimplyConnectedDerivedCover d π`, KP Definition 2.6.20);
* `T(K)^0 = E.torusIwahori` is the image of the bounded subgroup `T(L)^b` under the norm
  `T(L) → T(K)`, for the supplied maximally split maximal torus `i : T → H` and finite
  Galois splitting field `L ⊆ F^sep` of `T` (KP Definition 2.5.13), mapped into `H(K)`
  by `i`.

The two data may differ in every field: the torus `T`, its embedding, the splitting
field `L`, the derived subgroup and the simply connected cover. The statement asserts
that none of these choices changes the subgroup.

No hypothesis on `H` is added: `IsSimplyConnectedDerivedCover d π`, a field of each
datum, already contains `IsConnectedReductive H`. KP Definition 2.6.23(1) is stated for
quasi-split `H`; over `K` every connected reductive group is quasi-split (KP Corollary
2.3.8), so the definition applies to every connected reductive `K`-group. The datum
asks only for a maximally split maximal torus (KP Definition 2.6.2), as the source does.

## Provenance

KP Lemma 2.6.24 says that Definition 2.6.23 does not depend on the choices of `T` or
`M_0`. Its proof uses the conjugacy of minimal Levi subgroups under `G_sc(k)` and the
fact that conjugation by `g` carries `M_0(k)^0` to `(g M_0 g^{-1})(k)^0`. The
independence of the splitting field `L` is the independence statement of KP Lemma
2.5.12 (printed pp.89–90/PDF pp.120–121), which Definition 2.5.13 invokes with the words
"for any finite Galois extension `L/K` splitting `T`". KP states Lemma 2.5.12 for a
`k`-torus; its proof reduces to `G_m` over `L` and uses the surjectivity of the norm on
units of finite extensions of `K`, so it uses only the `K`-torus, which is how
Definition 2.6.23(1) applies it to tori of `K`-groups. The independence of the simply
connected cover is the published
`Langlands.Geometry.Building.UnramifiedZeroDatum.simplyConnectedImage_eq` (module
`SimplyConnectedImageNormal`, KP Fact 2.6.21 for isomorphisms). This statement combines
these three independences for part (1) of Definition 2.6.23 in one proposition.

Normality and openness of `H(K)^0`, the other claims of Lemma 2.6.24, are not asserted.
This file states the proposition; it does not prove it.

Sources:

- Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), Lemma 2.5.12 and
  Definition 2.5.13, printed pp.89–90/PDF pp.120–121; Definition 2.6.20, Fact 2.6.21,
  Definition 2.6.23 and Lemma 2.6.24, printed pp.104–105/PDF pp.135–136. Registered as
  `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
  `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
