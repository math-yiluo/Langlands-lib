# Restriction of apartment valuations to a standard Levi subgroup

`Langlands.Geometry.Building.LeviApartmentRestrictionStatement` is a
Prop-valued `def` at every universe `u`. It states parts (1)–(4) of
Kaletha–Prasad Lemma 6.7.1 for the actual standard Levi subgroups of a
connected reductive group over a nonarchimedean local field, at the same
maximal split torus. A valuation of the root datum of `(G, S)` restricts to
one of `(M, S)`, the restrictions form one apartment class, and two points
have the same restriction exactly when they differ by a central direction of
`M`. The module supplies no proof.

## Statement

The proposition quantifies over:

- every nonarchimedean local field `F`, of either characteristic
  (`[Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]`), with its normalized valuation
  `ω = localFieldOrder F : Fˣ → ℝ`, whose values are the integers;
- every group scheme `G` over `Spec F` with `hG : IsConnectedReductive G`;
  the instance `IsAffineHom G.X.hom` is taken from `hG`;
- every commutative group scheme `S` and every `i : S.toGrp ⟶ G` with
  `hi : IsMaximalSplitTorus i`; the instance `Mono i.hom.hom.left` is taken
  from `hi`;
- every cocharacter `ν` of `S` with `IsGenericCocharacter i ν`. It selects
  the positive relative roots and their simple roots
  `simpleRelativeRoots i ν`;
- every set `J ⊆ simpleRelativeRoots i ν`;
- every `D : KPApartmentData i (localFieldOrder F)`.

For such `J`, `M_J = Standard.leviScheme i ν J` is the published closed
representative of the standard Levi subgroup of `G` attached to `J`, with
its inclusion `j = Standard.leviHom i ν J : M_J ⟶ G` and the same torus
`iM = Standard.leviTorusHom i ν J : S ⟶ M_J`, so that `iM ≫ j = i`. The
instances `IsAffineHom` on `M_J` and `Mono` on `iM` are the published ones
(`Standard.isClosedSubgroup_leviHom`, `Standard.isMaximalSplitTorus_leviTorusHom`).

`KPApartmentData i ω` is an equipollence class `A` of valuations of the
root datum of `(G, S)` (KP Definition 6.1.2, axioms V 0–V 5 on the actual
relative root groups `U_a(F)`). These valuations are compatible with `ω` on
`S(F)`, and the class is stable under the actual normalizer points `N(F)` of
`S`. Its points `D.Apartment` are the valuations of the class.

The conclusion is that there are apartment data
`DM : KPApartmentData iM (localFieldOrder F)` for `(M_J, S)` with:

1. every point `x : D.Apartment` has some `xM : DM.Apartment` with
   `IsLeviRestriction j x xM`;
2. every point `xM : DM.Apartment` has some `x : D.Apartment` with
   `IsLeviRestriction j x xM`;
3. for all `x x' : D.Apartment` and `xM xM' : DM.Apartment` with
   `IsLeviRestriction j x xM` and `IsLeviRestriction j x' xM'`,
   ```
   xM = xM' ↔ ∃ v : V S, x'.val = v +ᵥ x.val ∧
     ∀ a ∈ relativeRoots iM, eval S a v = 0
   ```

Here `IsLeviRestriction j x xM` is the published relation
(`Langlands.BruhatTits.SpecialCompact.IsLeviRestriction`):
`xM_a(m) = x_a(j m)` for every relative root `a` of `(M_J, S)` and every
`m ∈ M_J(F)`. Valuations of `(M_J, S)` take the value `∞` off the roots of
`(M_J, S)` and off their root groups, so `xM` is determined by `x`. In
clause 3, `V S = ℝ ⊗ X_*(S)` is the real cocharacter space, `v +ᵥ x.val` is
the translation `(v + φ)_a = φ_a + a(v)` of KP Lemma 6.1.6, and
`eval S a v = a(v)`.

## Source correspondence

The source is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`,
§6.7 "Projection to a Levi Subgroup" and Lemma 6.7.1, printed p.233 /
PDF p.264. KP take a Levi subgroup `M ⊂ G` and a maximal split torus
`S ⊂ M`, which is also maximal split in `G`, so `Φ(M, S) ⊂ Φ(S, G)`. For an
equipollence class `A(S, G)` of valuations of the root datum of `(G, S)`
they write `φ_M = (φ_a)_{a ∈ Φ(M,S)}` and `A(M, S) = {φ_M | φ ∈ A(S, G)}`.
Lemma 6.7.1 states:

1. each `φ_M` is a valuation of the root datum of `(M, S)`;
2. if `φ` is compatible with `ω`, so is `φ_M`;
3. `A(M, S)` is an equipollence class;
4. `φ ↦ φ_M` descends to an isomorphism of affine spaces
   `A(S, G)/V(A) → A(M, S)` over `V(S′_G)/V(A) = V(S′_M)`, where `A` is the
   maximal torus in `S′_G ∩ Z(M)`;
5. for quasi-split `G`, the restriction of a Chevalley valuation is a
   Chevalley valuation.

The standing hypotheses of Chapter 6 (printed p.195 / PDF p.226) are a
Henselian field with a discrete valuation `ω` normalized by `ω(k^×) = ℤ`,
and a connected reductive `G`. The residue field need not be perfect. The
authors' corrections of 1 November 2024, `kaletha-prasad-2024-corrections`,
SHA-256 `23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`,
list no change to §6.7. Their Chapter 6 entries (PDF p.32) correct
Lemma 6.1.12 (the action of `N(k)`), which the published normalizer action
on root-function families already follows.

The clauses match the source as follows.

- Parts (1)–(3): `DM` is an equipollence class of `ω`-compatible
  valuations of `(M_J, S)` (it is `KPApartmentData`), and clauses 1 and 2
  say that its points are exactly the restrictions `φ_M` of the points of
  `D`. So `DM` is `A(M_J, S)`.
- Part (4): if `xM` restricts `x`, then `v +ᵥ xM` restricts `v +ᵥ x` for
  every `v ∈ V(S)`, directly from the definitions. The restriction is
  therefore the affine map of the source, and clause 2 is its surjectivity.
  Clause 3 identifies its fibres: two points have the same image exactly
  when they differ by a vector on which every root of `(M_J, S)` vanishes.
  The apartment `D.Apartment` is an affine space over `V(S)` modulo the
  common kernel of `Φ(S, G)` (`TranslationSpace i`, KP's `V(S′_G)`, not
  identified with it in the Library). Modulo that kernel, the common kernel
  of `Φ(M_J, S)` is the space KP denote `V(A)`. Clauses 2 and 3 therefore
  say that the restriction induces a bijection `A(S, G)/V(A) → A(M_J, S)`
  compatible with the translations. The Library does not formalize the
  torus `A` itself, and the statement does not mention it.
- Part (5) is not formalized here.

## Derived scope and provenance

This is a derived formulation of parts (1)–(4), not a literal transcription.
It differs from the source as follows.

- **Field.** KP work over a Henselian discretely valued field. The
  statement covers nonarchimedean local fields of either characteristic
  with their normalized valuation, which are fields of that kind. This
  matches the Library's consumers of `IsLeviRestriction`
  (`SpecialLeviRestriction`, `SpecialLeviInheritance` and the
  availability-level Levi targets), which all use `localFieldOrder F`.
- **Levi subgroups.** KP allow any Levi subgroup `M` containing `S`. The
  statement covers the standard Levi subgroups `M_J` for a generic `ν` and
  `J ⊆ simpleRelativeRoots i ν`, through the published representatives
  `Standard.leviScheme`, `Standard.leviHom` and `Standard.leviTorusHom`.
  These are the Levi subgroups that the Library's consumers use. Other Levi
  subgroups containing `S` are not covered.
- **Compatibility and normalizer stability.** `KPApartmentData` records
  compatibility with `ω` only on `S(F)` (the `S(F)` part of KP axiom V 6),
  and in addition `N(F)`-stability of the class, the hypothesis on `A(S)` of
  the opening paragraphs of KP Chapter 7. Part (2) is used in this form.
  The existence of `DM` as `KPApartmentData` also asserts that `A(M_J, S)`
  is stable under the normalizer points of `S` in `M_J`. KP do not state
  this in Lemma 6.7.1. It follows from the `N(F)`-stability of `D`, because
  every normalizer point of `S` in `M_J` maps to one of `S` in `G`, and the
  two actions on root-function families correspond under restriction.
- **Part (4).** The isomorphism is expressed by surjectivity and the fibre
  description, with `V(A)` replaced by the common kernel of the roots of
  `(M_J, S)`, as explained above.

The route expected for a proof follows KP. Axioms V 0–V 5 and the
compatibility for `φ_M` follow from those for `φ`. For this one needs that,
for a root `a` of `(M_J, S)`, the root group of `M_J` is the preimage of the
root group `U_a(F)` of `G` under `j` and `U_a(F)` lies in `M_J(F)`, that the
roots of `(M_J, S)` are the roots of `(S, G)` in the integral span of `J`
(so the root combinations of V 3 and the multiples of V 2, V 4 and V 5
stay inside `Φ(M_J, S)`), and that normalizer points of `S` in `M_J` are
normalizer points in `G` with the same Weyl action on characters. Each
valuation of `(M_J, S)` in the class takes a finite value on its root group
(axiom V 0). Hence a translation fixing all restricted values is killed by
every root of `(M_J, S)`, which gives the forward direction of clause 3.
The backward direction and clause 2 follow from the translation
compatibility above. No existence of `D` or of any building is asserted.
