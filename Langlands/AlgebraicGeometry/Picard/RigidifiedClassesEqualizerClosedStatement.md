# The locus where two rigidified classes agree is closed

`Langlands.AbelianScheme.RigidifiedClassesEqualizerClosedStatement.{u}` is the proposition:

```lean
∀ (S : Scheme.{u}) (A : AbelianScheme S) (T : Over S) (q r : RigidifiedClasses A T),
  ∃ (Z : Scheme.{u}) (ι : Z ⟶ T.left), IsClosedImmersion ι ∧
    ∀ (T' : Over S) (h : T' ⟶ T), (∃ g : T'.left ⟶ Z, g ≫ ι = h.left) ↔
      RigidifiedLineBundle.classesPullback A.X.hom (unitSection A)
          (unitSection_comp A) h q =
        RigidifiedLineBundle.classesPullback A.X.hom (unitSection A)
          (unitSection_comp A) h r
```

This unit only defines the proposition. It proves nothing.

## Meaning

Let `A` be an abelian scheme over an arbitrary scheme `S` and `T` a scheme over `S`. For any
two rigidified isomorphism classes `q` and `r` on `T ×_S A`, the proposition gives a closed
immersion `ι : Z ⟶ T`. A morphism `h : T' ⟶ T` over `S` factors through `ι` exactly when the
pullbacks of `q` and `r` to `T'` are equal classes. The closed subscheme `Z` therefore
represents the subfunctor of `T` on which the two rigidified classes agree.

## Exact interface

All names below are the published ones; nothing is redefined.

- `AbelianScheme S` is the published bundle: a commutative group scheme over `S` whose
  structure morphism `A.X.hom` is smooth, proper and geometrically connected.
- `unitSection A : S ⟶ A.X.left` is the identity point of the group, and
  `unitSection_comp A` is the identity `unitSection A ≫ A.X.hom = 𝟙 S`.
- `RigidifiedClasses A T` is `RigidifiedLineBundle.Classes A.X.hom (unitSection A)
  (unitSection_comp A) T`. This is the quotient by isomorphism of the actual category of line
  bundles on the chosen total space `T ×_S A`, each with a rigidification along the section
  `(id_T, unitSection A ∘ T.hom)`. Its isomorphisms are module isomorphisms compatible with the
  rigidifications.
- `RigidifiedLineBundle.classesPullback … h` is `Quotient.map` of the actual relative rigidified
  pullback functor along `h : T' ⟶ T`. Thus the right-hand side of the equivalence says: there
  is an isomorphism of rigidified line bundles between the pullbacks of representatives of `q`
  and `r` to `T' ×_S A`.
- `IsClosedImmersion` is Mathlib's closed-immersion property of a morphism of schemes.

The quantifiers carry no hypotheses. `S` is arbitrary; it need not be quasi-separated,
noetherian or reduced. `T` and the test objects `T'` are arbitrary objects of `Over S`. The
classes `q` and `r` are arbitrary; in particular there is no Picard-zero condition. The scheme
`Z` lies in the same universe `u` as the base. The definition has the single universe
parameter `u`.

The left-hand side of the equivalence asks for some `g : T'.left ⟶ Z` with
`g ≫ ι = h.left`. Since `ι` is a monomorphism, such a `g` is unique when it exists.

## Provenance

This is a derived specialisation of two lemmas of the Stacks Project, *More on Morphisms*,
Section 37.33 "Theorem of the cube" (tag 0BEZ). The source is registered as
`stacks-picard-diagonal-seesaw-0bdp-0bf0-a04446e5`: Git commit
`a04446e57ec1fbc252a871afcec7752fb2807b14`, file `more-morphisms.tex`, labels
`lemma-diagonal-picard-flat-proper` (Lemma 37.33.1, tag 0BDP) and `lemma-get-a-closed`
(Lemma 37.33.4, tag 0BF0). The tag numbers were checked against the pinned `tags.txt` and the
fetched tag pages. The comment thread of 0BDP reports two typographical errors in the proof,
marked fixed on 2025-07-22, before the pinned commit; they do not affect the statement. Tag 0BF0
has no comments.

- Lemma 0BDP. Let `f : X → S` be flat, proper and of finite presentation, and let `E` be a
  finite locally free `O_X`-module. For `g : T → S` write `p : X_T → T` and `q : X_T → X` for
  the base change. Assume that `O_T → p_* O_{X_T}` is an isomorphism for every `g`. Then there
  is an immersion `j : Z → S` of finite presentation such that `g` factors through `Z` if and
  only if `p^* N ≅ q^* E` for some finite locally free `O_T`-module `N`.
- Lemma 0BF0. If moreover `E` is invertible and the geometric fibres of `f` are integral, then
  `Z` is closed in `S`.

### Derivation of the present statement

Apply both lemmas with base `T` to the projection `p : T ×_S A → T`.

- `p` is a base change of `A.X.hom`, so it is smooth and proper. A smooth morphism is flat and
  locally of finite presentation; a proper morphism is quasi-compact and separated. Hence `p` is
  flat, proper and of finite presentation.
- Its geometric fibres are geometric fibres of `A.X.hom`. They are smooth, hence regular, and
  connected, hence integral.
- The global-functions hypothesis holds for every base change. Every further base change of `p`
  is again smooth, proper and geometrically connected. For such morphisms the published theorem
  `Langlands.AlgebraicGeometry.smoothProperConnectedGlobalFunctions` gives an isomorphism on
  sections over every open of the base. That is exactly `O_T ≅ p_* O`. The published
  `Langlands.AbelianScheme.universalGlobalFunctions` records the global-sections case for the
  relative family.

Take `E = L ⊗ M⁻¹` for rigidified representatives `L` and `M` of `q` and `r`. This is
invertible, so Lemma 0BF0 makes `Z` closed in `T`. For a `T`-scheme `T'`, the resulting closed
subscheme is the agreement locus:

- Suppose `(L ⊗ M⁻¹)_{T'} ≅ p^* N`. Pulling back along the unit section of `T' ×_S A` and using
  both rigidifications gives `N ≅ O_{T'}`. Hence `L_{T'} ≅ M_{T'}` as ordinary line bundles.
- An ordinary isomorphism `φ : L_{T'} ≅ M_{T'}` is compared with the two rigidifications along
  the unit section. This gives an automorphism of `O_{T'}`, that is, a unit `u` of
  `Γ(T', O)`. The composite of `φ` with the automorphism `p^* u⁻¹` is an isomorphism of
  rigidified line bundles. So the two classes agree after pullback.
- Conversely, an equality of the pulled-back rigidified classes gives
  `(L ⊗ M⁻¹)_{T'} ≅ O = p^* O_{T'}`.

The Lean statement differs from the source in form only.

- Test schemes are objects `T'` of `Over S` with morphisms `h : T' ⟶ T` over `S`. These are the
  same data as schemes over `T`.
- Factorisation through the immersion is phrased as existence of `g` with `g ≫ ι = h.left`.
- The source's condition on `E = L ⊗ M⁻¹` is replaced by the equivalent equality of rigidified
  classes, by the derivation above. No tensor product, inverse or ordinary Picard group occurs
  in the Lean statement.
- The source's finite presentation of `Z → T` is not asserted.

## Proof obligations

They belong to a separate exact-target proof task, not to this unit. Mathlib at the pinned
commit has no coherent cohomology and no cohomology and base change, so Stacks' perfect-complex
proof of Lemma 0BDP is not directly available. Lemma 0BF0's proof also uses Lemma 0EX8
(`lemma-triviality-generic-fibre-valuation-ring`, same registered source) and a valuation-ring
criterion for the scheme-theoretic image (Morphisms, `lemma-reach-points-scheme-theoretic-image`).
