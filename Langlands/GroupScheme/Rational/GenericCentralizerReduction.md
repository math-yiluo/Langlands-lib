# Generic centralizers from the structure of dynamic centralizers

This file proves `GenericCentralizerStatement` **conditionally**: it assumes the four
structural statements `DynamicSmoothStatement`, `DynamicConnectedStatement`,
`DynamicLieStatement` and `LieSubgroupEqualityStatement` as hypotheses and proves none of
them. All declarations are at an arbitrary universe `u`.

## Lie algebras along homomorphisms

Let `R` be a commutative ring, `H` and `G` group schemes over `Spec R`, and `A` an
`R`-algebra. `lieKernel H A` is the actual Lie algebra, the kernel of
`H(A[ε]) → H(A)` on points.

- `comp_mem_lieKernel f X`: for a homomorphism `f : H ⟶ G` and `X : lieKernel H A`, the
  composite `X.val ≫ f` lies in `lieKernel G A`. The proof: reduction modulo `ε` commutes
  with composition, and the unit is preserved.
- `mem_lieKernel_of_comp_mem f hY`: if the underlying morphism of `f` is a monomorphism and
  the dual-number point `Y` of `H` has `Y ≫ f ∈ lieKernel G A`, then
  `Y ∈ lieKernel H A`. The proof cancels the monomorphism.

## Subgroup functors and representatives

Here `S` is a scheme and `K`, `H`, `G` are group schemes over `S`.
The identity representative and composite-range inclusion are reused from
`Dynamic/CentralizerReductiveTransport` and `Dynamic/ParabolicLieCriterion`;
the commutative-image centralizer inclusion and factorization are reused from
`Rational/LeviFactorization`.

- `SubgroupFunctor.top_isRepresentedBy_id K`: the identity `𝟙 K` represents the subgroup
  functor `⊤` of all points of `K`.
- `SubgroupFunctor.range_comp_le f g`: `range (f ≫ g) ≤ range g`.
- `SubgroupFunctor.IsRepresentedBy.exists_comp_eq hj f hf`: if `j : H ⟶ G` represents `F`
  and the homomorphism `f : K ⟶ G` has `range f ≤ F`, then `f = f' ≫ j` for some
  homomorphism `f' : K ⟶ H`. The proof uses the published `IsRepresentedBy.factorHom` and its
  `factorHom_comp` equation, which give `f' ≫ j = f`.
- `range_le_torusCentralizer i`: for a commutative group scheme `T` and
  `i : T.toGrp ⟶ G`, `range i ≤ torusCentralizer i`, because the group of points of `T` is
  commutative.

## The comparison lemma over a field

`dynamicCentralizer_le_of_weightSpace_zero_le hS hC hL hE χ ψ hψ hw`. Let `k` be a field
and `G` a group scheme over `Spec k` that is smooth and affine over `Spec k` with connected
underlying space. Let `χ` and `ψ` be cocharacters of `G` (homomorphisms `𝔾_m ⟶ G`).
Assume the four structural statements (`hS hC hL hE`), and suppose that

- `hψ`: `range ψ ≤ Dynamic.centralizer χ`, and
- `hw`: `weightSpace χ (t ↦ t⁰) ≤ weightSpace ψ (t ↦ t⁰)` on the actual Lie algebra
  `lieKernel G k`.

Then `Dynamic.centralizer χ ≤ Dynamic.centralizer ψ` as subgroup functors on all test
schemes.

Proof as implemented:

1. Take the explicit closed representative `j : H ⟶ G` of `Dynamic.centralizer χ` from
   `Dynamic.Affine.centralizerScheme`, `centralizerHom`, `isRepresentedBy_centralizerHom`
   and `isClosedSubgroup_centralizerHom`. Then `H` is affine. By `hS` it is smooth and by
   `hC` its underlying space is connected.
2. By `exists_comp_eq` and `hψ`, `ψ = ψ' ≫ j` for a cocharacter `ψ'` of `H`. Take the closed
   representative `jK : K ⟶ H` of `Dynamic.centralizer ψ'`; `K` is smooth by `hS`.
3. Every `X : lieKernel H k` lifts to `lieKernel K k`. Its image `X.val ≫ j` lies in
   `lieKernel G k` and in `Dynamic.centralizer χ`. By `hL` for `χ` it has weight `0`
   for `χ`. By `hw` it has weight `0` for `ψ`, and by `hL` for `ψ` it lies in
   `Dynamic.centralizer ψ`. Since `j` is a monomorphism, the published
   `Dynamic.centralizer_eq_comap_of_mono` puts `X.val` in `Dynamic.centralizer ψ'`, which
   is the range of `jK`. The preimage `Y` lies in `lieKernel K k` by
   `mem_lieKernel_of_comp_mem`.
4. By `hE`, applied to the closed subgroup `jK` of the smooth affine connected `H`,
   `range jK = ⊤`, that is, `Dynamic.centralizer ψ' = ⊤`.
5. A point of `Dynamic.centralizer χ` is `h ≫ j` for a point `h` of `H`. Now `h` lies in
   `Dynamic.centralizer ψ'`, and the published `Dynamic.centralizer_le_comap` maps it into
   `Dynamic.centralizer (ψ' ≫ j) = Dynamic.centralizer ψ`.

## The conditional generic-centralizer theorem

`genericCentralizerStatement_of hS hC hL hE : GenericCentralizerStatement`. Take a field
`k`, a connected reductive `G` over `Spec k`, a maximal split torus `i : T.toGrp ⟶ G` and a
generic cocharacter `ν` of `T`. The inclusion `torusCentralizer i ≤ Dynamic.centralizer
(groupHom ν ≫ i)` is the published `torusCentralizer_le_dynamicCentralizer`. For the other
inclusion, `le_torusCentralizer_of_le_dynamicCentralizer` (from `CocharacterCentralizers`)
reduces to `Dynamic.centralizer (groupHom ν ≫ i) ≤ Dynamic.centralizer (groupHom c ≫ i)`
for every cocharacter `c` of `T`. That is the comparison lemma with `χ = groupHom ν ≫ i`
and `ψ = groupHom c ≫ i`:

- `hψ` holds since `range ψ ≤ range i ≤ torusCentralizer i ≤ Dynamic.centralizer χ`.
- `hw` holds because `weightSpace χ 0 = weightSpace i 0` for generic `ν` (Worker 74's
  `weightSpace_zero_genericCocharacter`, in `GenericLieWeights`). Also
  `weightSpace i 0 ≤ weightSpace (groupHom c ≫ i) (c ≫ 0) = weightSpace ψ 0`
  (`weightSpace_le_comp`).

The hypotheses smooth, affine and connected for `G` come from `IsConnectedReductive`, and
splitness of `T` from `IsMaximalSplitTorus`. Maximality is not used beyond splitness.

## Provenance

The route follows Conrad–Gabber–Prasad, *Pseudo-reductive groups*, second edition (2015),
Proposition 2.1.8, printed pp.53–54 (PDF pp.79–80), source
`conrad-gabber-prasad-2015-pseudo-reductive`, for the structure of `Z_G(λ)` (smoothness,
connectedness and `Lie(Z_G(λ)) = 𝔤₀`). It also uses Milne, *Algebraic Groups* (2017),
Proposition 10.15, printed pp.190–191 (PDF pp.206–207), source
`milne-2017-algebraic-groups`, for the Lie criterion of equality. The target is Borel–Tits,
*Groupes réductifs* (1965), 4.15(a), printed pp.90–91 (PDF pp.37–38), and Milne,
Theorem 25.6(b), printed p.546 (PDF p.562). There `C_G(S) = C_G(λ(𝔾_m))` for a suitable
cocharacter `λ` of `S`. Comparing two cocharacter centralizers inside the representative
of `Z_G(χ)` by their Lie algebras is a derived argument. A similar comparison appears in
the proof of Theorem 5.1.13 of Conrad, *Reductive group schemes* (2014), printed p.144
(PDF p.144), source `conrad-2014-reductive-group-schemes`. There the inclusion
`T ⊂ Z_G(λ)` of smooth closed subgroups with connected fibers is an equality on Lie
algebras, hence an equality. The four structural statements are hypotheses here, not
proved.
