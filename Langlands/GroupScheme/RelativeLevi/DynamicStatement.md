# Statement: dynamic parabolic, unipotent and centralizer subgroups over a base

Worker 75.

`Langlands.GroupScheme.DynamicRelativeLeviStatement.{u} : Prop` is a statement-only,
`Prop`-valued definition. This module does not prove it, and it adds no other definitions,
theorems or axioms. It imports [`RelativeLevi.Basic`](Basic.md) (for the three relative
predicates) and [`Dynamic.Basic`](../Dynamic/Basic.md) (for `Dynamic.parabolic`,
`Dynamic.unipotent` and `Dynamic.centralizer`).

## Statement and quantifiers

The proposition quantifies over:

- every scheme `S : Scheme.{u}`;
- group schemes `G P U Z : GroupScheme S`;
- every homomorphism `χ : (Gm S).toGrp ⟶ G`, a 1-parameter subgroup of `G`;
- homomorphisms `iP : P ⟶ G`, `iU : U ⟶ G` and `iZ : Z ⟶ G`.

It has four hypotheses:

1. `IsReductive G` ([`Reductive.Basic`](../Reductive/Basic.md)): `G` is smooth and affine
   over `S` with connected reductive geometric fibres.
2. `(Dynamic.parabolic χ).IsRepresentedBy iP`: `iP.hom.hom` is a monomorphism and the
   image of `iP` on every test scheme is the dynamic parabolic subgroup functor `P_G(χ)`.
   A point `g ∈ G(T)` lies in `P_G(χ)` when its orbit map `t ↦ χ(t) g χ(t)⁻¹`, defined on
   `T ×_S 𝔾_{m,S}`, extends to `T ×_S 𝔸¹_S`.
3. `(Dynamic.unipotent χ).IsRepresentedBy iU`: the same for `U_G(χ)`, the points whose orbit
   map extends with value `1` at `0`.
4. `(Dynamic.centralizer χ).IsRepresentedBy iZ`: the same for `Z_G(χ)`, the points whose
   orbit map is constant.

(`SubgroupFunctor.IsRepresentedBy F f` is `Mono f.hom.hom ∧ SubgroupFunctor.range f = F`;
see [`SubgroupFunctor`](../SubgroupFunctor.md).)

The conclusion is the conjunction of three assertions:

- `IsRelativeParabolicSubgroup iP`: `P` is smooth and affine over `S`, `iP` is a
  monomorphism, and every residue fibre of `iP` is a parabolic subgroup;
- for every `r : U ⟶ P` with `r ≫ iP = iU`, `IsRelativeUnipotentRadical r`;
- for every `l : Z ⟶ P` with `l ≫ iP = iZ`, `IsRelativeLeviSubgroup l`.

Since `U_G(χ)` and `Z_G(χ)` are subfunctors of `P_G(χ)` and `iP` is a monomorphism, the
factorizations `r` and `l` exist and are unique; the statement quantifies over them
instead of constructing them.

## Source

Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I, Panoramas
et Synthèses 42–43, SMF, 2014; registered as `conrad-2014-reductive-group-schemes`, file
`Conrad--Reductive group schemes (SGA3 notes)--2014.pdf` (SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`). Page numbers are the
one-based PDF pages, which agree with the printed page numbers of this file.

- Example 5.2.2, p.151: "Let T ⊂ G be a maximal S-torus, and λ : G_m → T a cocharacter.
  The smooth closed S-subgroup P_G(λ) is parabolic."
- Paragraph after Definition 5.4.2, p.174: "If λ : G_m → G is a 1-parameter subgroup and P
  is the parabolic subgroup P_G(λ) then Z_G(λ) is a Levi subgroup because
  R_u(P) = U_G(λ)."
- Proof of Corollary 5.2.5, p.153: in the case `P = P_G(λ) = Z_G(λ) ⋉ U_G(λ)`, "U_G(λ)
  satisfies the requirements to be R_u(P)" (smooth, closed, normal, with the unipotent
  radicals as geometric fibres).
- Section 4.1 (the dynamic method): `P_G(λ)`, `U_G(λ)` and `Z_G(λ)` are represented by
  smooth closed subgroups; Example 4.1.9, cited in Example 5.2.2, gives parabolicity of
  `P_G(λ)` over an algebraically closed field.

## Derivation from the source

The paragraph after Definition 5.4.2 asserts, for an arbitrary 1-parameter subgroup
`λ : 𝔾_m ⟶ G`, that `P_G(λ)` is a parabolic subgroup, that `R_u(P_G(λ)) = U_G(λ)`, and
that `Z_G(λ)` is a Levi subgroup of `P_G(λ)`. These are the three conjuncts. In the Lean
version:

- The parabolicity assertion is Example 5.2.2 for a cocharacter of `G` itself. The source
  example takes `λ` valued in a maximal torus; the paragraph after Definition 5.4.2 uses
  the same conclusion for any 1-parameter subgroup, and the Lean statement follows that
  paragraph. (Étale-locally every `λ` lands in a maximal torus of the reductive group
  `Z_G(λ)`, so the two formulations agree.)
- "`R_u(P) = U_G(λ)`" is stated as: the inclusion of `U_G(λ)` into `P_G(λ)` satisfies the
  characterization `IsRelativeUnipotentRadical` of Corollary 5.2.5.
- "`Z_G(λ)` is a Levi subgroup" is stated with `IsRelativeLeviSubgroup` from
  [`RelativeLevi.Basic`](Basic.md), the transcription of Definition 5.4.2.

The representing group schemes `P`, `U`, `Z` are hypotheses rather than constructions: the
proposition applies to any representatives, and existence of representatives is the
separate representability theorem of Section 4.1.

## Scope

All objects are in universe `u`. The base `S` is an arbitrary scheme. The cocharacter `χ`
is arbitrary, including the trivial one, for which `P = G`, `U` is trivial and `Z = G`. No
maximal torus or splitting is assumed.

## Relation to the Library

- Over a field, the published theorems `isParabolicSubgroup_of_isRepresentedBy` and
  `isGeometricUnipotentRadical_of_isRepresentedBy`
  ([`Rational.AffineWeilParabolicRadicalTransportProof`](../Rational/AffineWeilParabolicRadicalTransportProof.md))
  prove the analogous assertions for a connected reductive group with the ground-field
  predicates `IsParabolicSubgroup` and `LeviSubgroup.IsGeometricUnipotentRadical`.

This module proves none of these relations.
