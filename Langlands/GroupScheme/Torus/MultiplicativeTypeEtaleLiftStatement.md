# Statement: lifting a multiplicative-type subgroup of a fibre to an étale neighbourhood

Worker 75.

`Langlands.GroupScheme.MultiplicativeTypeEtaleLiftStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition. This module does not prove it, and it adds no
other definitions, theorems or axioms. It imports:

- [`Torus.RelativeMultiplicativeType`](RelativeMultiplicativeType.md), for the relative
  predicate `RelativeMultiplicativeType.IsMultiplicativeType` (Conrad, Definition B.1.1)
  and, transitively, the base-change functor `GroupScheme.baseChange`;
- [`AbelianScheme.Tate.BaseChangeCoherence`](../../AbelianScheme/Tate/BaseChangeCoherence.md),
  for `baseChangeCompIso`;
- Mathlib's `Mathlib.AlgebraicGeometry.ResidueField`,
  `Mathlib.AlgebraicGeometry.Morphisms.Etale` and
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`, for residue fields, `Etale` and
  `IsClosedImmersion`.

`GroupScheme S` is `Grp (Over S)`. Inside the definition the namespace
`RelativeMultiplicativeType` is open, so `IsMultiplicativeType` is the relative predicate,
applied both over the residue field and over `U`.

## Objects and predicates used

- `S.residueField s` is the residue field `κ(s)`, and
  `S.fromSpecResidueField s : Spec κ(s) ⟶ S` is the canonical morphism. The fibre `G_s` is
  `(baseChange (S.fromSpecResidueField s)).obj G`.
- `IsMultiplicativeType H`: there is an fppf cover of the base (a jointly surjective family
  of flat morphisms locally of finite presentation) over each member of which `H` becomes
  isomorphic to `D(Λ)` for a finitely generated abelian group `Λ`. Over the field `κ(s)`
  this is the usual notion of a `κ(s)`-group of multiplicative type.
- `baseChangeCompIso p b G` is the canonical isomorphism `G_{b ≫ p} ≅ (G_U)_b` of group
  schemes over `Spec κ(s)`, and the `eqToIso` term transports along the equality
  `b ≫ p = S.fromSpecResidueField s`. Their composite identifies `(G_U)_b` with `G_s`.

## Statement and quantifiers

For every scheme `S`, every group scheme `G` over `S` with `G → S` smooth and affine, every
point `s ∈ S`, every group scheme `H₀` over `Spec κ(s)` of multiplicative type and every
homomorphism `i₀ : H₀ ⟶ G_s` that is a closed immersion, there exist:

- a scheme `U` and an étale morphism `p : U ⟶ S`;
- a morphism `b : Spec κ(s) ⟶ U` with `b ≫ p = S.fromSpecResidueField s`;
- a group scheme `H` over `U` of multiplicative type and a homomorphism `i : H ⟶ G_U` that
  is a closed immersion;
- an isomorphism `e : H_b ≅ H₀` of group schemes over `Spec κ(s)`,

such that the fibre `i_b : H_b ⟶ (G_U)_b`, followed by the identification `(G_U)_b ≅ G_s`
above, equals `e.hom ≫ i₀`.

## Source

Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I,
Panoramas et Synthèses 42–43, SMF, 2014. It is registered as
`conrad-2014-reductive-group-schemes`, file
`Conrad--Reductive group schemes (SGA3 notes)--2014.pdf` (SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`). Page numbers are the
printed page numbers.

- Proposition 3.1.6, p.83: "Let G → S be a smooth S-affine group scheme, and H₀ a
  multiplicative type subgroup of the fiber G_s over some s ∈ S. There exists an étale
  neighborhood (S′, s′) of (S, s) with k(s′) = k(s) and a multiplicative type subgroup
  H′ ⊂ G_{S′} such that H′_{s′} = H₀ inside (G_{S′})_{s′} = G_s." Conrad adds: "This result
  is [SGA3, XI, 5.8(a)]. Note that by Lemma B.1.3, the monomorphism H′ → G_{S′} must be a
  closed immersion."
- Definition B.1.1, p.280, defines groups of multiplicative type.

Conrad's proof (p.84) reduces to `S` of finite type over `ℤ`, lifts `H₀` over the
completion of the local ring at `s` with Corollary B.3.5, descends the lift to a finite type
subalgebra, and uses Artin approximation to find it over a residually trivial local-étale
extension, which spreads out to an étale neighbourhood. This is explanation only.

## Derivation from the source

- **Hypotheses.** "Smooth S-affine group scheme" is `Smooth G.X.hom` and
  `IsAffineHom G.X.hom`. "A multiplicative type subgroup of the fiber G_s" is a closed
  subgroup scheme of `G_s` of multiplicative type, given here by a group `H₀` with
  `IsMultiplicativeType H₀` and a homomorphism `i₀` that is a closed immersion.
- **Étale neighbourhood with `k(s′) = k(s)`.** An étale neighbourhood `(S′, s′)` is an
  étale `p : U ⟶ S` with a point `s′` over `s`. The condition `k(s′) = k(s)` is encoded by
  the morphism `b : Spec κ(s) ⟶ U` with `b ≫ p = S.fromSpecResidueField s`. Its image
  `s′` lies over `s`, and `b` makes `κ(s′) → κ(s)` a retraction of the field extension
  `κ(s) → κ(s′)`, so that extension is trivial. Conversely, a point `s′` over `s` with
  `κ(s) → κ(s′)` an isomorphism gives such a `b`. This is the encoding of the Library's
  `RelativeSplitTorusLiftingStatement`.
- **The lift.** "A multiplicative type subgroup H′ ⊂ G_{S′}" is `H` with
  `IsMultiplicativeType H` and `i : H ⟶ G_U`. The conclusion that `i` is a closed immersion
  is the closing remark of the source (Lemma B.1.3).
- **`H′_{s′} = H₀` inside `(G_{S′})_{s′} = G_s`.** The identification `(G_U)_b = G_s` is
  `baseChangeCompIso` followed by the `eqToIso` along `hb`. Equality of subgroups is
  expressed by an isomorphism `e : H_b ≅ H₀` under which the fibre of `i` agrees with `i₀`.

## Scope and omissions

All schemes are in universe `u`. No noetherian or finite-type hypothesis on `S` is imposed,
as in the source. The étale morphism `p` need not be surjective; only a neighbourhood of
`s` is asserted.

## Related Library statements

- `RelativeSplitTorusLiftingStatement`
  ([`Torus.RelativeLiftingStatement`](RelativeLiftingStatement.md)) is the special case in
  which `H₀` and the lift are split tori, and it is proved in the Library
  ([`Torus.RelativeLiftingProof`](RelativeLiftingProof.md)). The present statement allows
  any multiplicative-type subgroup and does not ask the lift to be split.
