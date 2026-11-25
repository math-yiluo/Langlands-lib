# Normal subgroups of multiplicative type are central

This module proves part 1 of Conrad, *Reductive group schemes* (2014), Lemma 3.3.1 (p.96–97):
let `G` be a smooth `S`-affine group over a scheme `S` with connected fibres; a normal closed
subgroup of multiplicative type is central. All declarations are in the namespace
`Langlands.GroupScheme.MultiplicativeTypeNormalCentral`.

Conrad reduces to the finite subgroups `H[n]`, classifies the conjugation action by a
homomorphism `G → Aut(H[n])` to a finite étale scheme, and uses connectedness of the fibres. The
Lean proof instead applies the rigidity theorem of
[`Torus.MultiplicativeTypeRelativeRigidity`](../Torus/MultiplicativeTypeRelativeRigidity.md)
directly to the conjugation family, with no reduction to `H[n]` and no Hom scheme.

## Declarations

- `geometricallyConnected_of_residueFiber`: if `G` is smooth and affine over `S` and every
  residue fibre `RelativeIdentityComponent.residueFiber G s` (the fibre over
  `Spec κ(s)`) has connected underlying space, then `G.X.hom` is geometrically connected. Each
  residue fibre is a group scheme locally of finite type and quasi-compact over the field
  `κ(s)`, so it is geometrically connected by the Library's
  `geometricallyConnected_of_connected` (module
  [`GroupScheme.GeometricConnectedness`](../GeometricConnectedness.md)), and
  `GeometricallyConnected.iff_geometricallyConnected_fiber` concludes.
- `conj h hn V g x : V ⟶ H.X`, for `h : H ⟶ G` with `hn : (SubgroupFunctor.range h).IsNormal`,
  a test scheme `V : Over S`, `g : V ⟶ G.X` and `x : V ⟶ H.X`: a point of `H` whose image is
  `g * (x ≫ h) * g⁻¹` (`conj_comp`). It is chosen from the normality hypothesis.
- If `h.hom.hom` is a monomorphism, the choice is unique, and `conj_mul`, `conj_naturality`
  and `conj_one` show that `conj` is multiplicative in `x`, natural in `V` and the identity at
  `g = 1`. Each is checked after composing with `h.hom.hom`.
- `isCentral_of_isNormal`: let `G H : GroupScheme S` with `[GeometricallyConnected G.X.hom]`,
  `H` of multiplicative type and `h : H ⟶ G` with `[Mono h.hom.hom]` and normal image. Then
  `IsCentral h`. Proof: `conj h hn` is a family of homomorphisms `H → H` parametrized by `G.X`.
  By `MultiplicativeTypeRigidity.eq_of_isMultiplicativeType`, its value at a point `g` equals its
  value at `1`, the identity. So `g * (x ≫ h) * g⁻¹ = x ≫ h` for all points, which is the
  definition of `IsCentral h` (module [`Rational.Characters`](../Rational/Characters.md)).
- `isCentral_of_isNormal_of_isClosedSubgroup`: part 1 of Conrad, Lemma 3.3.1, in the
  hypotheses of `Langlands.GroupScheme.MultiplicativeTypeNormalCentralStatement`: `G` smooth and
  affine over `S` with connected residue fibres, `h : H ⟶ G` a closed subgroup
  (`IsClosedSubgroup h`, a closed immersion and hence a monomorphism in `Over S` by
  `Over.mono_of_mono_left`) of multiplicative type with normal image. Then `IsCentral h`.

`isCentral_of_isNormal` uses neither smoothness, affineness, nor closedness: only a geometrically
connected `G`, a monomorphism `h` and multiplicative type of `H`.
