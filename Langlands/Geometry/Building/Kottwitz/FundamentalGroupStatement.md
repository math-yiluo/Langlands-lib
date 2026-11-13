# Inertia descent and torus identification statements

These three Prop-valued declarations are unconditional obligations for the
objects defined in `FundamentalGroup`. No proof of them is included, and none
is supplied as a premise of the selected maps. All fields and connected
reductive groups are allowed, without characteristic or splitting restrictions.

The source is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), Fact
11.3.5, Lemma 11.3.6, and the target groups in §11.5, printed pp. 427–430 /
PDF pp. 458–461, source ID `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
The 2024 corrections do not change these items. The inertia descent assertions
are explicit consequences of the functorial Galois maps in Lemma 11.3.6,
used in KP's definition in §11.5; they are not quotations of a separate lemma.

`TorusFundamentalComparisonStatement` states Fact 11.3.5 as unique existence
of the linear map characterized by actual torus cocharacters, satisfaction of
that law by the selected map, bijectivity, and compatibility with the actual
`Aut_k(E)` actions. The field `E` is a separable closure of `k`.

`FundamentalInertiaMapStatement` works over a normal tower `k → K → E`, where
`E` is a separable closure of `k`. For every reductive morphism, it asserts
unique existence of the map descending the induced fundamental-group map,
the selected map's representative law, equivariance for `Aut_k(K)`, and
preservation of identities and composition. Equivariance of the original map
is a conclusion of the earlier fundamental-group map target, not an additional
hypothesis here.

`TorusInertiaComparisonStatement` asserts that the descent of the torus
comparison to inertia coinvariants exists uniquely, that the selected map
satisfies the representative law, that it is bijective, and that it is
equivariant for the residual action. Its target is the same
`torusInertiaCoinvariants` used by the torus Kottwitz homomorphism.

For the intended local application, `K = UnramifiedClosure F` and
`E = SeparableClosure F`. The generic tower formulation also permits the
coefficient field to be `K` itself. It imposes no local-field instance on `K`
or `E`, and does not assert surjectivity after taking residual invariants.
