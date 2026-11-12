# Integrality from a power for models with a torus special fibre

Let `F` be a nonarchimedean local field with integers `𝒪[F]` and residue field
`𝓀[F]`, let `L` be a group scheme over `Spec F`, and let
`Z : IntegralModel 𝒪[F] F L` be a supplied model. All rings and schemes use one
arbitrary universe `u`. The main theorem says: if `L` is connected reductive and
the special fibre of `Z` is a torus, then a rational point of `L` is integral as
soon as some positive power of it is integral. The proof shows that over the
maximal unramified integers the model contains a closed split torus whose generic
fibre is all of the generic group, and then applies the companion module
`UnramifiedTorusPowerIntegrality`, which is part of the same contribution.

## No roots in a commutative group

`roots_eq_empty_of_isCommMonObj` works over a field `k`. Let `G` be an affine
group scheme of finite type over `Spec k` whose underlying monoid object is
commutative (`IsCommMonObj G.X`), and let `i : T ⟶ G` be a homomorphism from a
split torus. Then the Library root set `roots i` is empty. A homomorphism into a
commutative group is central (`isCentral_to_commGroupScheme`), so the weight space
of the zero character is the whole Lie algebra
(`weightSpace_zero_eq_top_of_isCentral`). The weight spaces of distinct characters
are independent (`isInternal_weightSpace_of_isSplitTorus`), so every nonzero
character has the zero weight space and is not a root.

## Splitting by a rational point on a generic split torus

`exists_genericSplitTorusValue_eq_of_isIso` works for a model `N` over a domain `R`
with fraction field `K`. If `i` is a homomorphism from the split torus on a finite
type `I` to `N.group` and the generic homomorphism `N.genericSplitTorusHom i` is an
isomorphism, then every rational point `y` of the generic group equals
`N.genericSplitTorusValue i t` for some coordinates `t : I → Kˣ`. The proof takes the
point `y ≫ inv(N.genericSplitTorusHom i)` of the split torus over `K`, reads its
unit coordinates with `splitTorus.pointsEquiv`, and transports them to `K` along
`Γ(Spec K, ⊤) ≅ K`.

## The residue fibre of the unramified base change

Write `𝒪'` for `fixedFieldIntegers F`, the integers of the maximal unramified
extension `inertiaFixedField F`, and `κ'` for its residue field, an algebra over
`𝓀[F]` through the Library map `residueToFixedField F`. The algebra `𝒪[F] → 𝒪'` is
the valuation-extension algebra used by the Library base change
`Z.baseChangeUnramified`. `unramifiedResidue_specMap_comp` states that the two
composites `Spec κ' → Spec 𝒪' → Spec 𝒪[F]` and `Spec κ' → Spec 𝓀[F] → Spec 𝒪[F]`
are equal, and `unramifiedResidueIso` is the resulting isomorphism between the
fibre of `Z.baseChangeUnramified.group` over `κ'` and the base change along
`𝓀[F] → κ'` of the special fibre of `Z.group`. It is built from the Library
composition isomorphisms `baseChangeCompIso` and this equality.

## A split torus filling the unramified generic fibre

`exists_isIso_genericSplitTorusHom_baseChangeUnramified` assumes that `L` is
connected reductive and that the special fibre of `Z.group` over `𝓀[F]` is a
torus (`IsTorus`). It produces a finite type `I` and a closed subgroup
`j : splitTorus (Spec 𝒪') I ⟶ Z.baseChangeUnramified.group` such that
`Z.baseChangeUnramified.genericSplitTorusHom j` is an isomorphism. The proof:

1. A torus over a field is connected reductive
   (`IsTorus.isConnectedReductive_of_fieldSplitting`), so the published theorem
   `exists_isMaximalSplitTorus_baseChangeUnramified` gives a closed split torus
   `i : T ⟶ Z.baseChangeUnramified.group` whose generic fibre is a maximal torus.
   Since `T` is split, it is isomorphic to `splitTorus (Spec 𝒪') I` for a finite
   `I`; `j` is `i` precomposed with that isomorphism. The base-changed model is
   reductive (`isReductive_baseChangeUnramified`), hence smooth and affine.
2. Over `κ'` the fibre of the model is a torus: the special fibre is a torus, base
   change keeps it a torus (`IsTorus.baseChange`), and `unramifiedResidueIso`
   transports this. A torus is commutative (`IsTorus.isCommMonObj`), so the
   torus `j` has no roots over `κ'` by `roots_eq_empty_of_isCommMonObj`.
3. The published comparison `splitTorus.fieldRootsEquiv` identifies the roots of
   `j` over any two fields that are algebras over the local ring `𝒪'`. Applied to
   `inertiaFixedField F` and `κ'`, it shows that `j` has no roots on the generic
   fibre either.
4. The generic fibre of the model is connected reductive
   (`fieldReductive_of_residueReductive` with the reductive residue fibres), and the
   generic fibre of `j` is a maximal torus there, by transporting the maximality of
   step 1 along the isomorphisms `splitTorus.baseChangeIso`, the base change of the
   isomorphism `T ≅ splitTorus I`, and the generic identification of the model
   (`IsMaximalTorus.of_eq_iso_comp_comp_iso`).
5. A connected reductive group over a field whose split maximal torus has no roots
   is that torus (`IsConnectedReductive.isIso_of_roots_eq_empty`). So the generic
   fibre of `j` is an isomorphism, and composing with the generic identification
   gives that `genericSplitTorusHom j` is an isomorphism.

## Integrality from a power

`mem_integralPoints_of_pow_mem_of_isTorus_special` keeps the hypotheses of the
previous theorem. For a rational point `g` of `L` and `n ≠ 0`, if
`g ^ n ∈ Z.integralPoints` then `g ∈ Z.integralPoints`. By the previous two
results, the extension of `g` to `inertiaFixedField F` is the generic value of the
closed split torus `j` at some coordinates, and
`mem_integralPoints_of_pow_mem_of_unramifiedSplitTorus` from the companion module
concludes.

## Provenance

This is an internal variant of Maculan (2017), Proposition 4.6 (printed p. 11 /
PDF p. 12): for a torus `𝒯` over the integers of a complete discretely valued
field, `𝒯(𝒪)` is the unique maximal bounded subgroup of the rational points of
its generic fibre. Maculan splits the torus over a finite unramified extension and
uses the split case. Here the hypotheses are on the supplied model (connected
reductive generic group, torus special fibre) rather than that the model is a
relative torus, and the conclusion is the power form used for maximality; the
splitting over the maximal unramified integers is obtained from the reductive
model by the root comparison above instead of from the relative torus structure.
The Lean statements are not quoted from the source. The module does not prove that
the model is a relative torus, nor any boundedness or compactness statement.
