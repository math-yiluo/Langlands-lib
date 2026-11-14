# Statement: the pinned Isomorphism Theorem for split reductive groups over an affine base

Worker 75.

`Langlands.GroupScheme.AffinePinnedIsomorphismTheoremStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition. This module does not prove it, and it adds no
other definitions, theorems or axioms. It imports
[`Reductive.FibrewiseRootDatum`](FibrewiseRootDatum.md) (for `IsFibrewiseRootDatumOf`
and, through it, `splitTorus`, `splitTorus.pointsEquiv` and
`splitTorus.exponentWeightSpace`), [`Reductive.Basic`](Basic.md) (for `IsReductive` and
`IsClosedSubgroup`), [`Torus.FieldPointMaximality`](../Torus/FieldPointMaximality.md)
(for `IsFibrewiseMaximalTorus`), [`Lie.KernelTargetMaps`](../Lie/KernelTargetMaps.md)
(for `Lie.targetMapLinear`) and Mathlib's `LinearAlgebra/RootSystem/Base` (for
`RootPairing.Base`).

It states, over an affine base `Spec R`, that the functor from pinned split reductive
groups to based root data in Conrad's Isomorphism Theorem is fully faithful on
isomorphisms: every isomorphism of based root data comes from exactly one isomorphism of
pinned split reductive groups.

## Statement and quantifiers

The proposition quantifies over:

- every commutative ring `R : Type u`, with base scheme `Spec R`. The ring may be zero,
  non-Noetherian, non-local, and `Spec R` may be disconnected;
- group schemes `G H : GroupScheme (Spec R)` with `hG : IsReductive G` and
  `hH : IsReductive H` ([`Reductive.Basic`](Basic.md)): each is smooth and affine over
  `Spec R`, and its geometric fibres are connected reductive groups. The statement takes
  the instances `IsAffineHom G.X.hom` and `IsAffineHom H.X.hom` from `hG.isAffineHom`
  and `hH.isAffineHom` by `haveI`, so it adds no instance argument;
- finite types `I I' : Type u` and homomorphisms `i : splitTorus (Spec R) I ⟶ G` and
  `i' : splitTorus (Spec R) I' ⟶ H` from the coordinate split tori `𝔾_m^I` and
  `𝔾_m^{I'}` over `Spec R`;
- types `J J' : Type u` and Mathlib root data `P : RootDatum J (I → ℤ) (I → ℤ)` and
  `Q : RootDatum J' (I' → ℤ) (I' → ℤ)` on the coordinate character and cocharacter
  lattices.

It has four hypotheses on `(G, i, P)` and the same four on `(H, i', Q)`. They are those of
[`Reductive.AffineSplitIsomorphismTheoremStatement`](AffineSplitIsomorphismTheoremStatement.md)
and of the Library's encoding of Conrad's Definition 5.1.1 in
[`Reductive.EtaleLocalSplitStatement`](EtaleLocalSplitStatement.md). Together they say
that `(G, i, P)` and `(H, i', Q)` are split:

1. `IsClosedSubgroup i`: the underlying morphism of schemes of `i` is a closed immersion.
2. `IsFibrewiseMaximalTorus i`: for every point `s` of `Spec R`, the residue fibre of `i`
   over `κ(s)` satisfies the field predicate `IsMaximalTorus`.
3. `IsFibrewiseRootDatumOf I G i P`: `J` is finite, `P` is reduced, and for every field
   `k` with a ring homomorphism `R → k`, the realization of `P` over `k` is the root datum
   (`IsRootDatumOf`) of the base change of `i` to `k`. Under the realization,
   `m : I → ℤ` is the character `t ↦ ∏ⱼ tⱼ ^ mⱼ` and `n : I → ℤ` is the cocharacter
   `s ↦ (s ^ nⱼ)ⱼ`. So the roots and coroots of every field-valued fibre are the constant
   elements of `P`.
4. For every `α : J`, the weight space `splitTorus.exponentWeightSpace I G i (P.root α)`
   is isomorphic to `R` as an `R`-module, that is, free of rank one. This weight space is
   the `R`-submodule of the Lie algebra `lieKernel G R` (the kernel of
   `G(R[ε]) → G(R)`) of vectors `X` such that, over every `R`-algebra `A` and for every
   point `t ∈ (Aˣ)^I` of the torus, the adjoint action of `i(t)` multiplies the image of
   `X` by `∏ⱼ tⱼ ^ (P.root α)ⱼ`.

The remaining quantifiers are the pinnings and the isomorphism of based root data:

- `b : P.Base` and `b' : Q.Base`: bases of the root pairings in Mathlib's sense
  (`RootPairing.Base`). The simple roots of `b` are `P.root a` for `a` in the finite set
  `b.support`; these roots, and the corresponding coroots, are linearly independent, and
  every root is a sum of simple roots or the negative of one.
- `X : ∀ a : b.support, R ≃ₗ[R] exponentWeightSpace I G i (P.root a)` and
  `Y : ∀ a' : b'.support, R ≃ₗ[R] exponentWeightSpace I' H i' (Q.root a')`:
  trivializations of the simple root spaces. The pinning vector of the simple root `a` is
  `(X a 1).val`, an element of the Lie algebra `lieKernel G R`; it generates the root
  space as an `R`-module, and its multiples by elements of `R` are the whole root space,
  each obtained once. Conversely, every generating vector with this property is
  `(X a 1).val` for exactly one trivialization `X a`. This is the convention of the
  field-level [`Reductive.Pinning`](Pinning.md) (`RootPinning.trivialization` and
  `RootPinning.rootVector`).
- `f : RootPairing.Equiv Q P` (Mathlib, `LinearAlgebra/RootSystem/Hom`). Its weight map
  `f.weightMap : (I' → ℤ) → (I → ℤ)` is a linear bijection from the character lattice of
  `𝔾_m^{I'}` to that of `𝔾_m^I`; its index bijection `f.indexEquiv : J' ≃ J` satisfies
  `f.weightMap (Q.root j') = P.root (f.indexEquiv j')` (`root_weightMap`); its coweight
  map is a linear bijection `(I → ℤ) → (I' → ℤ)` with the transpose property and
  `f.coweightMap (P.coroot j) = Q.coroot (f.indexEquiv.symm j)`. This is the direction
  convention of
  [`Reductive.AffineSplitIsomorphismTheoremStatement`](AffineSplitIsomorphismTheoremStatement.md)
  and of the field-level
  [`Reductive.SplitIsomorphismTheoremStatement`](SplitIsomorphismTheoremStatement.md).
- `hf : ∀ j' : J', j' ∈ b'.support ↔ f.indexEquiv j' ∈ b.support`: `f` matches the bases,
  so `f.indexEquiv` restricts to a bijection from the simple roots of `Q` to those of `P`.

## Conclusion

There is exactly one isomorphism `φ : G ≅ H` of group schemes over `Spec R` such that

1. **compatibility with the splittings:** there is an isomorphism
   `τ : splitTorus (Spec R) I ≅ splitTorus (Spec R) I'` of group schemes with
   `i ≫ φ.hom = τ.hom ≫ i'`, and for every test scheme `U` over `Spec R`, every point
   `x : U ⟶ 𝔾_m^I` and every `m : I' → ℤ`,
   `∏ j', (pointsEquiv I' U (x ≫ τ.hom.hom.hom))_{j'} ^ m j' = ∏ j, (pointsEquiv I U x)_j ^ (f.weightMap m) j`.
   Here `x ≫ τ.hom.hom.hom` is the point `τ(x)` of `𝔾_m^{I'}`, and
   `splitTorus.pointsEquiv I U` identifies the `U`-points of `𝔾_m^I` with families in
   `(Γ(U, 𝒪_U)ˣ)^I`. The left side is the character `χ_m : t ↦ ∏ t_{j'} ^ m_{j'}` of
   `𝔾_m^{I'}` at `τ(x)`, the right side the character `χ_{f m}` of `𝔾_m^I` at `x`. By
   Yoneda the identity says `χ_m ∘ τ = χ_{f.weightMap m}`: the map on character lattices
   induced by `τ` is `f.weightMap`. This first part is the conclusion of
   [`Reductive.AffineSplitIsomorphismTheoremStatement`](AffineSplitIsomorphismTheoremStatement.md);
2. **compatibility with the pinnings:** for every simple root `a'` of `Q`,
   `Lie.targetMapLinear φ.hom R (X ⟨f.indexEquiv a', _⟩ 1).val = (Y a' 1).val`. The map
   `Lie.targetMapLinear φ.hom R` sends a point of `lieKernel G R` (a dual-number point of
   `G` reducing to the identity) to its composite with `φ`; it is the map of Lie algebras
   induced by `φ`. So the differential of `φ` sends the pinning vector of the simple root
   `f.indexEquiv a'` of `G` to the pinning vector of the simple root `a'` of `H`.

The torus isomorphism `τ` is not part of the uniqueness: it is determined by `φ`, since
`i'` is a monomorphism, and also by `f.weightMap` through the identity of points.

## Source

Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I, Panoramas
et Synthèses 42–43, SMF, 2014. It is registered as `conrad-2014-reductive-group-schemes`,
file `Conrad--Reductive group schemes (SGA3 notes)--2014.pdf` (SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`). Page numbers are
the printed page numbers.

- Theorem 6.1.17 (Isomorphism Theorem), p.197: "Let S be a scheme that is non-empty. The
  functor (6.1.2) (G, T, M, {X_a}_{a∈∆}) ↝ (R(G, T, M), ∆) from pinned split reductive
  S-groups to based root data is an equivalence of categories when using isomorphisms as
  morphisms."
- Definition 6.1.14, p.195: an isogeny `f : (G′, T′, M′) → (G, T, M)` compatible with the
  splittings "is compatible with the pinnings if the bijection d : Φ′ → Φ arising from
  R(f) carries ∆′ into ∆ and f(exp_{a′}(X′_{a′})) = exp_{d(a′)}(X_{d(a′)}) for all
  a′ ∈ ∆′."
- Proposition 6.1.13(2), pp.194–195: "f is uniquely determined by R(f) and the pinnings
  {X′_{a′}}_{a′∈∆′} and {X_a}_{a∈∆}", where `X_{d(a′)} = f_{a′}(X′_{a′} ⊗ q(a′))`.
- Corollary 6.1.15 and its proof, pp.195–196: "Let a : T/Z_G → G_m denote the character
  thereby obtained from a … For each a ∈ ∆ there exists a unique unit u_a ∈ G_m(S) such
  that X_a = u_a Y_a, so the necessary and sufficient condition for c_t ∘ F and f to agree
  as isogenies compatible with splittings and pinnings (and hence to be equal) is that
  a(t) = u_a for all a ∈ ∆. Hence, it is necessary and sufficient to show that the subset
  ∆ … is a Z-basis of M̄."
- Theorem 6.1.16(1) (Isogeny Theorem), p.196, from which, with the argument just quoted,
  the source derives Theorem 6.1.17 (p.197: "An immediate consequence of Theorem 6.1.16
  and the arguments with the Z-basis ∆ of X(T/Z_G) in the proof of Corollary 6.1.15").
- Definition 6.1.1, p.186: "A pinning on (G, T, M) is a pair (Φ⁺, {X_a}_{a∈∆})
  consisting of a positive system of roots Φ⁺ ⊂ Φ (or equivalently, a base ∆ of Φ) and
  trivializing sections X_a ∈ 𝔤_a(S) for each simple positive root a ∈ ∆." The text after
  it: "There is an evident notion of isomorphism between pinned split reductive
  S-groups" (p.187).
- Definition 5.1.1, p.136 (split reductive groups; root spaces `𝔤_a` free of rank one).
- Definition 6.1.6, p.190 (compatibility with splittings) and Definition 6.1.8, p.191
  (p-morphisms; "a p-morphism that is an isomorphism must be a 1-morphism").

## Derivation from the source

The proposition is the full faithfulness part of the first sentence of Theorem 6.1.17,
over an affine base, with `(G′, T′, M′, {X′}) = (G, i, ℤ^I, X)` and
`(G, T, M, {X}) = (H, i', ℤ^{I'}, Y)` in Conrad's notation. A functor is fully faithful
on the groupoids of isomorphisms exactly when every isomorphism of the images comes from
exactly one isomorphism of the objects; that is the `∃!` of the conclusion. The terms
translate as follows.

- **Split reductive groups.** Hypotheses 1–4 transcribe Definition 5.1.1 as in
  [`Reductive.AffineSplitIsomorphismTheoremStatement`](AffineSplitIsomorphismTheoremStatement.md),
  whose Markdown gives the details. A torus that is maximal on residue fibres is a
  maximal torus in Conrad's sense (Definition 3.2.1, p.91; Remark A.1.2, p.267).
- **Pinnings.** Conrad's pinning of `(G, T, M)` is a base `∆` of a positive system of
  roots together with a trivializing section `X_a` of the line bundle `𝔤_a` for every
  `a ∈ ∆`. For roots of a reduced root datum, a base of a positive system in the usual
  sense is the same as a Mathlib `RootPairing.Base` (Mathlib's documentation of
  `RootPairing.Base` states this equivalence for reduced root pairings); `P` is reduced
  by hypothesis 3. Over `Spec R` a trivializing section of `𝔤_a` is a generator `X` of the
  global sections with `r ↦ r • X` bijective, which is `(X a 1).val` for a unique
  trivialization `X a : R ≃ₗ[R] 𝔤_a`.
- **Isomorphism of based root data.** An isomorphism `(R(G′, T′, M′), ∆′) ≃ (R(G, T, M), ∆)`
  is a 1-morphism `(h, d, 1)` of root data with `d(∆′) = ∆`. As explained in the Markdown
  of the unpinned sibling, an equivalence `f : RootPairing.Equiv Q P` is exactly such a
  triple, with `h = f.weightMap` and `d` read through `P.root` and `Q.root` from
  `f.indexEquiv.symm : J ≃ J'`. The condition `d(∆′) = ∆` is `hf`.
- **Isomorphisms of pinned groups.** An isomorphism `(G′, T′, M′, {X′}) ≃ (G, T, M, {X})`
  is an isomorphism of groups that is compatible with the splittings (Definition 6.1.6)
  and with the pinnings (Definition 6.1.14). Compatibility with the splittings is part 1
  of the conclusion, as in the unpinned sibling; it makes `R(φ)` the given `(h, d, 1)`.
  For an isomorphism `q = 1`, and by Lemma 6.1.4 (p.188) `f` maps `U′_{a′}` to
  `U_{d(a′)}` by `exp_{a′}(X′) ↦ exp_{d(a′)}(f_{a′}(X′))` for a unique isomorphism of line
  bundles `f_{a′} : 𝔤′_{a′} ≅ 𝔤_{d(a′)}`. Since `exp_a : W(𝔤_a) ≅ U_a` induces the
  identity on Lie algebras, `f_{a′}` is the restriction of the Lie algebra map of `f`, and
  `f(exp_{a′}(X′_{a′})) = exp_{d(a′)}(X_{d(a′)})` says that the Lie algebra map of `f`
  sends `X′_{a′}` to `X_{d(a′)}`. In the present direction (`φ : G → H` with `d` the
  inverse of `f.indexEquiv`) this is part 2 of the conclusion. The Lie algebra map of
  `φ` on global sections is `Lie.targetMapLinear φ.hom R`; it carries the root space of
  the weight `P.root (f.indexEquiv a') = f.weightMap (Q.root a')` of `G` to the root
  space of the weight `Q.root a'` of `H` because `τ` pulls `χ_{Q.root a'}` back to
  `χ_{P.root (f.indexEquiv a')}`.
- **Existence and uniqueness.** Uniqueness is Proposition 6.1.13(2) applied to
  `φ₂⁻¹ ∘ φ₁` for two solutions `φ₁, φ₂`: it is the identity on the torus and fixes the
  pinning. Existence is the derivation of Theorem 6.1.17 quoted above: the Isogeny
  Theorem gives an isomorphism compatible with the splittings, it sends each `X_a` to a
  unit multiple of the corresponding pinning vector, and the action of a point of
  `(T/Z_G)(S)` with prescribed values on the ℤ-basis `∆` of `X(T/Z_G)` corrects these
  units.
- **Affine base.** `splitTorus.exponentWeightSpace` is defined only over an affine base
  `Spec R`, so pinnings are stated only there. Conrad's theorem allows any non-empty
  scheme `S`. This proposition is a specialization of the source's statement to affine
  bases, not a reformulation of it.
- **Empty base.** Non-emptiness of `S` is not assumed. For `R = 0` the proposition holds
  trivially: every scheme over `Spec 0` is empty, so there is exactly one isomorphism
  `G ≅ H` and exactly one isomorphism of the tori; the identity of points is an identity
  in the trivial group of units of the zero ring; and the Lie algebras are zero.

## Scope

All objects are in universe `u`. The proposition does not state:

- essential surjectivity in Theorem 6.1.17, that every based root datum comes from a
  pinned split reductive group; over `Spec R` this is the Existence Theorem 6.1.16(2)
  together with the existence of pinnings, and is not stated here;
- the "in particular" clause of Theorem 6.1.17 on its own; its existence half is
  [`Reductive.AffineSplitIsomorphismTheoremStatement`](AffineSplitIsomorphismTheoremStatement.md),
  and its uniqueness half (uniqueness up to `(T/Z_G)(S)`) is not stated;
- the full functor on all morphisms (Corollary 6.1.15, faithfulness for isogenies
  compatible with splittings and pinnings), or the Isogeny Theorem.

## Relation to the Library

- [`Reductive.PinnedIsomorphismStatement`](PinnedIsomorphismStatement.md) records the
  same assertion over a field, for split pinnings in the sense of
  [`Reductive.Pinning`](Pinning.md) with actual character lattices and the covariant
  convention for `RootPairing.Equiv`. Over a field the present hypotheses describe a split
  maximal torus with its root datum and a pinning, but the two propositions are stated on
  different lattices; this module does not prove either from the other.
- [`Reductive.PinnedRigidityStatement`](PinnedRigidityStatement.md)
  (`PinnedAutomorphismRigidityStatement`) and
  [`Reductive.PinnedRootScalingStatement`](PinnedRootScalingStatement.md) record the
  field-level forms of the uniqueness and the unit-correction steps.
- [`Reductive.AffineSplitIsomorphismTheoremStatement`](AffineSplitIsomorphismTheoremStatement.md)
  (unpinned existence over `Spec R`) follows from the present proposition whenever the
  root data admit bases and the simple root spaces are trivialized; the latter holds by
  hypothesis 4. This module does not prove that implication.

This module proves none of these relations.
