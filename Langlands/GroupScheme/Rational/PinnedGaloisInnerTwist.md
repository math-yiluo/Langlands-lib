# Galois twists of pinned descents are inner

Module `Langlands.GroupScheme.Rational.PinnedGaloisInnerTwist`.

This supporting unit is a step toward the inner-discrepancy part of the
quasi-split inner-form existence theorem. Fix a finite Galois extension `K/k`,
a group scheme `H` over `Spec k`, a split pinning `p` of `H_K` and a homomorphism
`ρ` from `K ≃ₐ[k] K` to the based root-datum automorphisms of `p`. Let `s` be a
descent solution of the pinned Galois datum `p.galoisDatum ρ` (supporting
module `Reductive.PinnedGaloisDatum`), so that
`s.iso : (s.obj)_K ≅ H_K`. The main theorem shows that the local group
isomorphism over `Spec K → Spec k` induced by `s.iso` has all-test inner
discrepancy for every actual adjoint quotient of `s.obj`. Its hypotheses are:

- the full Galois action on the root datum of `p` is the canonical character
  pullback through supplied torus comparisons lying over the descent
  identifications; and
- `ρ` agrees with this action modulo the Weyl group.

Nothing here builds the pinning, the torus comparisons or the Galois action on
the root datum. Nothing here constructs a quasi-split inner form or proves the
host existence theorem.

## Notation

For `σ : K ≃ₐ[k] K`, `galoisBaseMap k K σ = Spec σ` and `fieldMap k K` is the
structure map `Spec K → Spec k`. For a group scheme `X` over `Spec k`,
`descentBaseChangeIso (fieldMap k K) (galoisBaseMap k K σ) _ X` is the Library's
canonical identification `(X_K)^σ ≅ X_K` of the pullback along `Spec σ` of a
base change from `k`. `Descent.pullIso r hf hg E` is the Library's pullback of
an isomorphism `E` of base changes along a base map `r`.

For the split pinning `p`, `p.torus`, `p.inclusion` and `p.rootDatum` are its
split torus, its inclusion into `H_K` and its root datum.
`p.semilinearPinnedIso σ.toRingEquiv (ρ σ)` (supporting module
`Reductive.SemilinearPinning`) is the pinned isomorphism from the pullback of `p` along `Spec σ` to `p` with based root-datum
automorphism `ρ σ`. Its group and torus components are `groupIso` and
`torusIso`. The semilinear lift `φ_σ := p.galoisSemilinearIso ρ σ :
(H_K)^σ ≅ H_K` is its group component. It is not itself the overlap component
of `p.galoisDatum ρ`. By `pullIso_galoisDatum` and `semilinearComponent`
(supporting modules `Reductive.PinnedGaloisDatum` and `Descent.SemilinearDatum`),
the restriction of the overlap of `p.galoisDatum ρ` to the Galois component of
`σ` is the map `baseChangeIdIso (H_K) ≪≫ φ_σ.symm`, from the identity pullback
of `H_K` to `(H_K)^σ`.

`characterAut e` for a torus automorphism `e` is the induced automorphism
`χ ↦ e.inv ≫ χ` of the character lattice. `weylImage i` is the image of the
Library Weyl action of the normalizer of a torus `i` on characters.

## Statements

### Inner automorphisms and isomorphisms (namespace `IsAdjointQuotient`)

- `basePointIso_trans`: for adjoint quotients `hq : IsAdjointQuotient q` with
  `q : G ⟶ A` and `hp : IsAdjointQuotient p` with `p : H ⟶ B` over a field `k`,
  an isomorphism `e : G ≅ H` and a rational point `x` of `A`,
  `hq.innerAction.basePointIso x ≪≫ e =
  e ≪≫ hp.innerAction.basePointIso (x ≫ (hq.mapIso hp e).hom.hom.hom)`. So
  conjugating an inner automorphism along `e` gives the inner automorphism of
  the image point under the Library's induced isomorphism of adjoint quotients.

### Galois twists of a split pinning (namespace `SplitPinning`)

Here `k K` are fields in universe `u` with `Algebra k K`, `H` is a group scheme
over `Spec k` whose base change `H_K` has affine structure map, `p` is a split
pinning of `H_K` and `ρ : (K ≃ₐ[k] K) →* p.basedRootDatumAut`.

- `galoisTwistIso p ρ σ` (definition): the automorphism
  `(p.galoisSemilinearIso ρ σ).symm ≪≫ descentBaseChangeIso (fieldMap k K)
  (galoisBaseMap k K σ) _ H` of `H_K`.
- `pullIso_solution_iso`: assume `[FiniteDimensional k K] [IsGalois k K]`. For
  every descent solution `s` of `p.galoisDatum ρ` and every `σ`,
  `Descent.pullIso (galoisBaseMap k K σ) _ _ s.iso =
  s.iso ≪≫ p.galoisTwistIso ρ σ`.
- `inclusion_comp_galoisTwistIso σ τ hτ`: let
  `τ : (p.torus)^σ ≅ p.torus` be a torus isomorphism. Assume `hτ`: the pullback
  of `p.inclusion` along `Spec σ`, followed by the descent identification of
  `H`, equals `τ` followed by `p.inclusion`. Then
  `p.inclusion ≫ (p.galoisTwistIso ρ σ).hom` equals the torus automorphism
  `(p.semilinearPinnedIso σ.toRingEquiv (ρ σ)).torusIso.symm ≪≫ τ` followed by
  `p.inclusion`.
- `characterAut_galoisTwistTorus_mem_weylImage σ τ δ hδ hw`: assume
  `[Mono p.inclusion.hom.hom.left]`, a full root-datum automorphism
  `δ : p.rootDatum.Aut` and:
  - `hδ`: `δ.weightEquiv χ = τ.inv ≫ characterLattice.baseChange
    (galoisBaseMap k K σ) p.torus χ` for every character `χ`, so `δ` is the
    canonical character pullback along `Spec σ` transported by `τ`;
  - `hw`: `(ρ σ).val * δ⁻¹` lies in `p.rootDatum.weylGroup`.

  Then
  `characterAut ((p.semilinearPinnedIso σ.toRingEquiv (ρ σ)).torusIso.symm ≪≫ τ)`
  lies in `weylImage p.inclusion`.
- `exists_adjointPoint_galoisTwistIso hq σ τ hτ δ hδ hw`: under the hypotheses of
  the two previous items, for every adjoint quotient `hq : IsAdjointQuotient q`
  of `H_K` with `q : H_K ⟶ A`, there is a `K`-point `x` of `A` with
  `hq.innerAction.basePointIso x = p.galoisTwistIso ρ σ`.
- `hasInnerDiscrepancy_solution τ hτ δ hδ hw hq' s hq`: assume
  `[FiniteDimensional k K] [IsGalois k K] [Mono p.inclusion.hom.hom.left]`. Let
  `τ σ` be torus isomorphisms satisfying `hτ σ` for every `σ`, and let `δ σ` be
  full root-datum automorphisms satisfying `hδ σ` and `hw σ` for every `σ`. Let
  `hq'` be an adjoint quotient of `H_K`. Let `s` be a descent solution of
  `p.galoisDatum ρ` and `hq : IsAdjointQuotient q` an adjoint quotient
  `q : s.obj ⟶ A` over `k`. Then
  `(LocalGroupIso.ofBaseChangeIso (U := ringTest k K) s.iso).HasInnerDiscrepancy
  hq.innerAction` holds. This is the Library's all-test inner-discrepancy
  property for the inner action of the ground-field adjoint quotient.

## Proofs

`basePointIso_trans` is checked on points by `hom_ext_points`. The Library
lemma `AutomorphicAction.comp_basePointIso_hom` writes composition with
`basePointIso` as the action of a constant point on both sides. The Library
lemma `IsAdjointQuotient.mapIso_innerAction` moves the action across `e`, and
`constantPoint_comp` identifies the transported constant point.

`pullIso_solution_iso` reduces to an index `j` with `σ = galoisIndexEquiv k K j`
and pulls the compatibility equation `s.compatible` back along the Galois
component `finiteGaloisComponent k K j` with `pullHom`. Write `X = (s.obj)_K`,
`Y = H_K`, `E = s.iso`, `b = Spec σ`, `I_X`, `I_Y` for `baseChangeIdIso`, `φ`
for the semilinear lift `p.galoisSemilinearIso ρ σ` and `c_X` for
`descentBaseChangeIso (fieldMap k K) b _ s.obj`. The equations
`pullIso_galoisDatum` (supporting module `Reductive.PinnedGaloisDatum`) and the
Library's `pullIso_canonicalOverlap_eq` (module `Rational.UnipotentRadicalDescent`)
rewrite the restricted overlaps as `I_Y ≪≫ φ.symm` and `I_X ≪≫ c_X.symm`. The
restricted compatibility then reads
`(baseChange (𝟙 _)).map E.hom ≫ I_Y.hom ≫ φ.inv =
I_X.hom ≫ c_X.inv ≫ (baseChange b).map E.hom`. Naturality of `baseChangeIdIso`
rewrites the left side as `I_X.hom ≫ E.hom ≫ φ.inv`, and cancelling the
isomorphism `I_X.hom` gives `E.hom ≫ φ.inv = c_X.inv ≫ (baseChange b).map E.hom`.
Unfolding `pullIso` as `c_X.inv`, followed by the base change of `E` along `b`
and the descent identification `c_H` of `H`, this gives
`pullIso b _ _ E = E ≪≫ φ.symm ≪≫ c_H`, which is the stated equation. A private
`rfl` lemma
identifies `pullbackComparison` with `descentBaseChangeIso`; using it through
`simp` avoids a kernel timeout from direct unfolding.

`inclusion_comp_galoisTwistIso` uses the torus square of the pinned isomorphism
`p.semilinearPinnedIso σ.toRingEquiv (ρ σ)`. It gives
`p.inclusion ≫ (p.galoisSemilinearIso ρ σ).inv = torusIso.inv ≫` the pullback
of `p.inclusion`. Composing with the descent identification and `hτ` gives the
claim.

`characterAut_galoisTwistTorus_mem_weylImage` applies the Library lemma
`IsRootDatumOf.abstractWeylImage_le`, which says the abstract Weyl group of the
root datum acts on characters inside `weylImage p.inclusion`, to the Weyl
element `δ * (ρ σ).val⁻¹` obtained from `hw`. It remains to check that this
element's weight action is `characterAut` of the twist torus automorphism. The
Library lemma `isoOfRootDatumEquiv_character` identifies the character action
of `torusIso` with the weight map of the semilinear root-datum equivalence
`(ρ σ).val ∘ (base-change equivalence)⁻¹`. This gives
`torusIso.hom ≫ χ = characterLattice.baseChange (galoisBaseMap k K σ) p.torus
((ρ σ).val⁻¹.weightEquiv χ)`. The claim then follows from `hδ`.

`exists_adjointPoint_galoisTwistIso` is `exists_adjointPoint_of_weylImage` (module
`Reductive.PinnedWeylInner`): an automorphism of `H_K` that preserves the
pinned torus through a torus automorphism acting by the Weyl image is inner by
a `K`-point of any adjoint quotient. Its two inputs are the two preceding
lemmas.

`hasInnerDiscrepancy_solution` applies
`IsAdjointQuotient.hasInnerDiscrepancy_of_galois_baseChange` (module
`Rational.FiniteGaloisBaseChangeDiscrepancy`) to `E = s.iso`. For each `σ` it
needs a `K`-point `x` of the base-changed adjoint quotient `hqK` of `s.obj` with
`hqK.innerAction.basePointIso x ≪≫ s.iso = Descent.pullIso (Spec σ) s.iso`. Let
`M = hqK.mapIso hq' s.iso` be the induced isomorphism of adjoint quotients. Take
the point `y` of the adjoint quotient of `hq'` from
`exists_adjointPoint_galoisTwistIso`, and set `x = y ≫ M.inv`. Then
`basePointIso_trans` rewrites the left side as
`s.iso ≪≫ hq'.innerAction.basePointIso y = s.iso ≪≫ p.galoisTwistIso ρ σ`, and
`pullIso_solution_iso` identifies this with the right side.

## Provenance

Internal. The argument follows the standard proof that the quasi-split form
obtained by twisting a split group with a based Galois action is an inner form.
Each Galois twist of the descent identification differs from the identity by an
automorphism that preserves the pinned torus and acts on characters by a Weyl
element. Such an automorphism is inner by a rational point of the adjoint
quotient. The host statement cites Conrad, *Reductive group schemes* (2014),
Proposition 7.2.11 (printed/PDF p.258; source
`conrad-2014-reductive-group-schemes`), for the pinned construction of
quasi-split inner forms. The Lean statements and route, including the explicit
torus-comparison and Weyl-agreement hypotheses, are internal to this Library.
