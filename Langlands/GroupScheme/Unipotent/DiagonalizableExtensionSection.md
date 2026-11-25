# Extensions of a unipotent group by a diagonalizable group

This module supplies the ingredients of the
proof of [`PerfectDiagonalizableUnipotentExtensionSplitStatement`](DiagonalizableExtensionSplitStatement.md)
(Milne, *Algebraic Groups* (2017), Proposition 16.28): centrality of the kernel,
affineness of the quotient, existence of a homomorphic section and its
uniqueness. The final assembly is
[`DiagonalizableExtensionSplitProof`](DiagonalizableExtensionSplitProof.md).

All declarations are in the namespace
`Langlands.GroupScheme.DiagonalizableUnipotentExtension`. Throughout, `k` is a
field, `G`, `D`, `U` are group schemes over `Spec k`, `i : D ⟶ G` and
`q : G ⟶ U` are homomorphisms, and
`hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q` says that `q` is
flat, surjective and locally of finite presentation and that the actual kernel
of `q` has the points of `i` on every test scheme.

## Centrality

* `conjugation_isStable i hq`: conjugation in `G`
  (`AutomorphicAction.conjugation (𝟙 G)`) preserves `range i`, because
  `range i` is the range of the kernel of `q`.
* `isCentral i q hq hD hUt hUq hUc`: assume `i` is a monomorphism, `q` is
  quasi-compact, `D` is of multiplicative type, and `U` is locally of finite type,
  quasi-compact and connected. Then `IsCentral i`: every point of `D`, on every
  test scheme, maps into the centre of `G`.
  1. Conjugation restricts to an action `a₁ : AutomorphicAction G D`
     (`AutomorphicAction.onRepresentedSubgroup`), with
     `a₁.act g d ≫ i = g · i(d) · g⁻¹`.
  2. The kernel of `q` acts trivially through `a₁`
     (`AutomorphicAction.KernelActsTrivially`): a point of the kernel is `i(y)`
     for a point `y` of `D`, and `D` is commutative
     (`IsMultiplicativeType.isCommMonObj`).
  3. `AutomorphicAction.quotientAction` (from
     [`ActionDescent`](../ActionDescent.md)) descends `a₁` along the flat,
     surjective, quasi-compact `q` to an action `a₂` of `U` on `D` with
     `a₂.act (g ≫ q) d = a₁.act g d`.
  4. The published `multiplicativeTypeConnectedAction`
     ([`MultiplicativeTypeConnectedActionStatement`](../Torus/MultiplicativeTypeConnectedActionStatement.md),
     part 1; Milne 12.37) makes `a₂` trivial. Hence `g · i(d) · g⁻¹ = i(d)` for
     all points, which is centrality.

## Affineness of the quotient

* `kernelι_comp_eq_zero q q' h`: if the kernel of `q` is contained in the
  kernel of `q'` (as subgroup functors), then `kernelι q ≫ q' = 0`.
* `quotientIso q q' h`: two flat, surjective, quasi-compact homomorphisms out of
  `G` with the same kernel have isomorphic targets. The two maps are obtained
  from `FpqcHomDescent.hom` (from [`HomDescent`](../HomDescent.md)) and are
  inverse by `FpqcHomDescent.unique`.
* `isAffineHom_quotientMap i hq`: `q` is affine when `D` is affine; this is the
  published `IsFppfQuotient.isAffineHom_of_isAffineHom_kernel`.
* `isAffineHom_quotient i q hi hq`: if `G` is affine and locally of finite type,
  `i` is a closed subgroup and `D` is affine, then `IsAffineHom U.X.hom`. The
  published `affineNormalSubgroupQuotient` gives an affine quotient
  `q' : G ⟶ Q` by `range i` (which is normal, being the range of a kernel), and
  `quotientIso q q'` identifies `U` with `Q`.

## Translation to Hopf algebras and existence of a section

* `isCentralExtension φ π hz hc hq`: for Hopf algebra maps `φ : B ⟶ A` and
  `π : A ⟶ k[Λ]` such that `Spec π` is a central closed subgroup and `Spec φ` is
  an fppf quotient map with kernel `Spec π`, the bialgebra maps satisfy
  `CentralExtensionSectionHopf.IsCentralExtension`
  ([`CentralExtensionSectionHopf`](../../Algebra/CentralExtensionSectionHopf.md)).
  The proof is that of the published
  `CentralExtensionHopfSpec.isCentralExtension_diagonalizable`, with the general
  lemmas of [`CentralExtensionHopfSpec`](../Torus/CentralExtensionHopfSpec.md),
  which do not depend on the quotient Hopf algebra.
* `exists_section_of_hopf eG eU eD i hi hc q hq eB`: let
  `eG : Spec A ≅ G` and `eU : Spec B ≅ U` be group-scheme isomorphisms
  (`Spec = hopfSpec`), `eD : D ≅ D_k(Λ)`, `i` a central closed subgroup and `hq`
  as above. If `eB : B ≃ₐ[k] MvPolynomial I k`, then there is `s : U ⟶ G` with
  `s ≫ q = 𝟙 U`. The maps `i` and `q` are transported to Hopf algebra maps `π`
  and `φ` by full faithfulness of `hopfSpec`; `isCentralExtension` and
  `CentralExtensionSectionHopf.exists_section_of_algEquiv` give a bialgebra map
  `σ` with `σ ∘ φ = id`, and `s = eU⁻¹ ≫ Spec σ ≫ eG`.
* `algEquivOfAffineSpace e`: if the scheme underlying `Spec B` is isomorphic over
  `Spec k` to the affine space `𝔸(I; Spec k)`, then `B ≃ₐ[k] MvPolynomial I k`.
  Mathlib's `AffineSpace.SpecIso` identifies `𝔸(I; Spec k)` with the spectrum of
  the polynomial ring over `Spec k`, and `algSpec` is fully faithful.
* `exists_section`: over a perfect field, if `G` and `U` are affine, `U` is
  smooth, connected and unipotent, `eD : D ≅ D_k(Λ)`, `i` is a central closed
  subgroup and `hq` holds, then `q` has a homomorphic section. The published
  `perfectFieldUnipotentSplit` (Milne 16.24) makes `U` split unipotent, the
  published `splitUnipotentAffineSpaceStatement` (Milne 14.66) gives
  `U.X ≅ 𝔸ⁿ` over `k`, and `algEquivOfAffineSpace` turns this into an
  isomorphism of the coordinate Hopf algebra `AffineCoordinates.hopfAlgebra U`
  with a polynomial ring; then `exists_section_of_hopf` applies with
  `eG = AffineCoordinates.hopfSpecIso G` and `eU = AffineCoordinates.hopfSpecIso U`.

## Uniqueness of the section

* `section_unique hU hD i hc q hq s s' hs hs'`: let `U` be unipotent and `D` of
  multiplicative type, both affine and locally of finite type, `i` a central
  monomorphism and `hq` as above. Two homomorphisms `s s' : U ⟶ G` with
  `s ≫ q = 𝟙 U = s' ≫ q` are equal. The morphism `s' · s⁻¹ : U.X ⟶ G.X` has
  trivial image in `U`, so it factors as `f ≫ i` with `f : U.X ⟶ D.X`.
  Centrality of `i` makes `f` multiplicative on points
  (`Semidirect.isMonHom_of_mul_comp`), so `f` is a homomorphism `U ⟶ D`. The
  published `unipotentMultiplicativeTriviality` (part 3; Milne 14.17) makes its
  range trivial, so `s'` and `s` agree on all points (`hom_ext_points`).

## Provenance

These are internal derivations from the cited published Library results. The
centrality argument is the first sentence of Milne's proof of 16.28 ("Because
`U` is connected, it acts trivially on `D` (see 12.37)"), with the descent of the
conjugation action from `G` to `U` made explicit. Uniqueness follows Milne's
remark that a section is determined, via 14.17 rather than via the subgroup
`G_u`. Existence does not follow Milne's induction on `dim U`; see
[`CentralExtensionSectionHopf`](../../Algebra/CentralExtensionSectionHopf.md).
