# Determinants and twists of weakly associated pairs

Worker 35 authored this statement unit for task
`91266440-3276-48dc-ab77-8d1c1fa386e8`. All declarations lie in the namespace
`Langlands.ClassField.Global.RelativeWeilGroup`.

The module states the second and third consequences of association in
Henniart 2000, §2.2. Let `S` be a representation of the Weil group, `Π` an
automorphic representation and `ω_Π` its central character. If `S` and `Π`
are associated, then `det S = ω_Π ∘ τ_F`. Moreover, for a character `χ` of
`𝔸_F^×/F^×`, `(χ ∘ τ_F) ⊗ S` and `(χ ∘ det) ⊗ Π` are associated. Here
`τ_F` is the reciprocity map onto the idele class group. The first
consequence, for contragredients, is the published
`Langlands.Automorphic.AssociatedContragredientStatement`.

The statements are made for representations `S` of the published
class-indexed extension `RelativeWeilGroup c F E`, at class families `c`
satisfying the published `IsArithmeticClassFamily c`. For such `c` this
extension is the relative Weil group `W_{E/F}` of the sources. The map
`τ_F` is realized at this finite level as the pointwise inverse of the
transfer `W_{E/F} → C_F`. The twist is stated only for finite-order
characters `χ`.

The module contains one definition with its evaluation lemma, and four
`Prop`-valued definitions:

- `reciprocityCharacter c F E χ`, the character `χ ∘ τ_F` of
  `RelativeWeilGroup c F E`, and its evaluation lemma
  `reciprocityCharacter_apply`;
- `PresentedDeterminantAssociationStatement`, for the determinant;
- `PresentedTwistAssociationStatement`, for twists of realizations with
  given spectral presentations;
- `ClassTwistAssociationStatement`, for twists of cuspidal classes;
- `AssociatedDeterminantTwistStatement`, the conjunction of the three.

The statements are not proved. No representation, twist, presentation or
local map is constructed. Apart from the conclusion of the class form,
discussed below, no existence statement is made.

## Objects

- **Fields and arithmetic class family.** Number fields `F E : Type u` with
  `[Algebra F E]` and `[IsGalois F E]`, and a class family
  `c : FundamentalClass.ClassFamily.{u}` with `IsArithmeticClassFamily c`.
  That predicate, from `Langlands.Automorphic.AssociatedFactorStatement`,
  says that some family `I` of local invariant maps satisfies
  `RelativeClassFormation` and `ArithmeticNormalization` at every prime, and
  that `c` satisfies `Generates`, `Restriction`, `Inflation` and
  `LocalCompatibility I`. These are the hypotheses of the published
  `GlobalFundamentalClassStatement` that identify `c F E` as the arithmetic
  fundamental class `u_{E/F}` of Artin–Tate XV §1. For such `c` the
  published `RelativeWeilGroup c F E`, the extension
  `ClassExtension (K := F) (c F E)` of `E ≃ₐ[F] E` by the idele class group
  `C_E`, is the relative Weil group `W_{E/F}`.
- **Transfer.** `transfer c F E : RelativeWeilGroup c F E →* C_F`, from the
  published `Langlands.ClassField.Global.RelativeWeilTransfer`, where
  `C_F = IdeleClassGroup (𝓞 F) F`. It is the group-theoretic transfer
  (Verlagerung) to the finite-index subgroup `C_E`, descended to `C_F`
  through the injective map `C_F → C_E`. That module proves
  `transfer c F E (inclusion c F E a) = ideleClassNorm a` for `a ∈ C_E`.
- **The character `χ ∘ τ_F`.** For a continuous character
  `χ : C_F →ₜ* ℂˣ`, `reciprocityCharacter c F E χ` is the homomorphism
  `w ↦ (χ (transfer c F E w))⁻¹` from `RelativeWeilGroup c F E` to `ℂˣ`.
  Since `χ` is a homomorphism, this is `χ ∘ τ_F` with
  `τ_F (w) := (transfer c F E w)⁻¹`. The section "The sign" explains this
  inverse.
- **Weil-side representation.** `S : FiniteRepresentation.{0, u, uV} ℂ
  (RelativeWeilGroup c F E)` is a finite-dimensional complex representation
  with carrier in universe `uV`.
- **Determinant.** `FiniteRepresentation.determinantCharacter S` is the
  published determinant character
  (`Langlands.Weil.Representation.Determinant`), `g ↦ det S(g)` as a unit.
- **Twist.** `FiniteRepresentation.twist ψ S` is the published twist
  (`Langlands.Weil.Representation.Twist`) of `S` by a character
  `ψ : G →* ℂˣ`. It has the same carrier, with `g` acting by
  `ψ(g) S(g)`.
- **Cuspidal realizations and classes.** Under the explicit assumption
  `[CompactSpace (AdeleQuotient F)]`, which the published automorphic-form
  constructions require, `T T' : Automorphic.CuspidalOperatorRealization F r`
  are actual irreducible cuspidal realizations of `GL_{r+1}` over `F`, and
  `π π'` are classes in `Automorphic.CuspidalOperatorRealization.IsoClass F r`.
  The compactness is the conclusion of the published
  `AdeleQuotientCompactStatement` (Cassels §14), which this module neither
  proves nor uses as a theorem.
- **Central character.** `T.HasCentralCharacter ω`, for
  `ω : C_F →ₜ* ℂˣ`, is the published condition that every form `f` in the
  image of `T` satisfies `f(z x) = ω(z) f(x)` for every idele `z`, embedded
  as a scalar matrix (`OperatorRealization.centralCharacter_evaluate`).
- **Finite-order determinant twists.**
  `Automorphic.CuspidalOperatorRealization.IsFiniteOrderDeterminantTwist χ T T'`,
  from the published `Langlands.Automorphic.FiniteOrderDeterminantTwist`,
  says that the Hecke character `χ` has finite order and that a complex
  linear equivalence `e` from the space of `T` to the space of `T'`
  satisfies `T'(d)(e f) = χ(det d) · e(T(d) f)` for finite adelic matrices
  `d`, the same equation for the standard compact subgroup at infinity, and
  leaves the action of the whole archimedean enveloping algebra unchanged.
  So `T'` realizes `(χ ∘ det) ⊗ T`. For classes,
  `π.IsFiniteOrderDeterminantTwist χ π'` is its published descent.
- **Spectral presentations.** `P : Automorphic.CuspidalSpectralPresentation.{u,
  uP} T` is the published presentation of a nonzero finite slice of `T` as a
  restricted tensor product of local smooth factors, with supplied
  unramified spectral data. Its local factors have carriers in universe
  `uP`. `P.spectralSystem` is the resulting
  `SpectralSystem (FinitePlace F) (r + 1)`. At each finite place `v` outside
  a finite exceptional set it gives eigenvalues `z_1, …, z_{r+1}`. The
  embedded local component of `T` at `v` has the standard spherical Hecke
  operators acting on its whole spherical fixed space by
  `q_v^{i(r+1-i)/2} e_i(z)`, where `e_i` is the `i`-th elementary symmetric
  function. Its Euler polynomial at `v` is `∏ (1 - z_i X)`. The same holds
  for a presentation `P'` of `T'`, in universe `uQ`.
- **Weak association.** The published `IsWeaklyAssociated S s`, from
  `Langlands.Automorphic.Unramified.RelativeWeilAssociation`, says that `S`
  is continuous of rank `n` and that, at cofinitely many finite places `v`,
  the spectrum of `s` is defined and `IsUnramifiedMatchAt S v` holds for its
  Euler polynomial. `IsUnramifiedMatchAt S v Q` says that for every place `w`
  of `E` above `v`, a local map `ι : W_{F_v} →ₜ* RelativeWeilGroup c F E`
  with `IsLocalRelativeWeilMap` exists. It also says that every such map
  makes `S ∘ ι` trivial on inertia with `det(1 - X S(ι Fr)) = Q`, where `Fr`
  is the published geometric Frobenius lift of `W_{F_v}`. The published
  `IsWeaklyAssociatedClass.{u, uV, uP} S π` says that some spectral system
  attached to `π` by a cuspidal spectral presentation in universe `uP` is
  weakly associated with `S`.

## Declarations

- `reciprocityCharacter c F E χ := ((χ : C_F →* ℂˣ).comp (transfer c F E))⁻¹`.
  `reciprocityCharacter_apply` proves
  `reciprocityCharacter c F E χ w = (χ (transfer c F E w))⁻¹` by `rfl`.
- `PresentedDeterminantAssociationStatement`: for every class family `c`
  with `IsArithmeticClassFamily c`, all `F` and `E` as above with
  `[CompactSpace (AdeleQuotient F)]`, every `r`, every `S`, every cuspidal
  realization `T`, every presentation `P` of `T` in universe `uP` and every
  continuous character `ω` of `C_F`, the following holds. If
  `T.HasCentralCharacter ω` and `IsWeaklyAssociated S P.spectralSystem`, then
  `FiniteRepresentation.determinantCharacter S = reciprocityCharacter c F E ω`.
  This is an equality of homomorphisms on all of `RelativeWeilGroup c F E`.
- `PresentedTwistAssociationStatement`: for every such `c`, `F`, `E`, `r`
  and `S`, all cuspidal realizations `T T'`, every presentation `P` of `T`
  in universe `uP`, every presentation `P'` of `T'` in universe `uQ` and
  every Hecke character `χ`, the following holds. If
  `IsFiniteOrderDeterminantTwist χ T T'` and
  `IsWeaklyAssociated S P.spectralSystem`, then
  `IsWeaklyAssociated (FiniteRepresentation.twist (reciprocityCharacter c F E χ) S)
  P'.spectralSystem`.
- `ClassTwistAssociationStatement`: for every such `c`, `F`, `E`, `r` and
  `S`, all cuspidal classes `π π'` and every Hecke character `χ`, the
  following holds. If `π.IsFiniteOrderDeterminantTwist χ π'` and
  `IsWeaklyAssociatedClass.{u, uV, uP} S π`, then
  `IsWeaklyAssociatedClass.{u, uV, uQ}
  (FiniteRepresentation.twist (reciprocityCharacter c F E χ) S) π'`.
- `AssociatedDeterminantTwistStatement` is the conjunction of the three
  statements, at the same universe levels.

A class form of the determinant statement is not stated separately. For a
realization `T`, the published `isWeaklyAssociatedClass_isoClass_iff` says
that `IsWeaklyAssociatedClass S T.isoClass` holds exactly when some
presentation `P` of `T` has `IsWeaklyAssociated S P.spectralSystem`. With it,
the presented form gives `det S = reciprocityCharacter c F E ω` whenever
`IsWeaklyAssociatedClass S T.isoClass` and `T.HasCentralCharacter ω`.

## Universe levels

The universe parameters are `u` for the fields and the automorphic
realizations, `uV` for the carrier of `S`, and `uP` and `uQ` for the local
factors of the presentations on the two sides. They are independent, and
each statement is asserted at every choice of levels:
`PresentedDeterminantAssociationStatement.{u, uV, uP}`,
`PresentedTwistAssociationStatement.{u, uV, uP, uQ}`,
`ClassTwistAssociationStatement.{u, uV, uP, uQ}` and
`AssociatedDeterminantTwistStatement.{u, uV, uP, uQ}`.

## The sign

The identity `det S = ω ∘ τ_F` fixes the normalization of `τ_F`. Within the
Library's conventions it holds with `τ_F = transfer⁻¹`, not with `transfer`
itself. This explanation is not formalized.

- **Automorphic side.** At an unramified place `v` with spectrum
  `z_1, …, z_{r+1}`, the operator for `i = r + 1` is the double coset of
  the scalar matrix `ϖ_v · 1`, which acts as right translation by that
  scalar. By the central character it acts by `ω_v(ϖ_v)`. The standard
  scalar for `i = r + 1` is `e_{r+1}(z) = z_1 ⋯ z_{r+1}`, so
  `z_1 ⋯ z_{r+1} = ω_v(ϖ_v)`.
- **Weil side.** If `det(1 - X S(ι Fr)) = ∏ (1 - z_i X)`, then the
  eigenvalues of `S(ι Fr)` are the `z_i`, so `det S(ι Fr) = z_1 ⋯ z_{r+1}`.
  Here `Fr` is a geometric Frobenius.
- **The local maps.** Condition 3 of the published `IsLocalRelativeWeilMap`
  says that `ι(y) = (inclusion c F E (i_w(e[y])))⁻¹` for `y ∈ W_{E_w}`, where
  `e` is the geometrically normalized local reciprocity of condition 1, and
  `i_w : E_w^× → C_E` is the coordinate map. So a geometric Frobenius `y` of
  `W_{E_w}` maps to the class of `ϖ_w⁻¹`. The published
  `LocalRelativeWeilMap.md` explains this inverse by Tate's geometric
  normalization (1.4.1), opposite to the arithmetic normalization of
  Artin–Tate on which the Library's classes are based.
- **The transfer.** At a place `v` that splits completely in `E`, `E_w = F_v`
  and `W_{E_w} = W_{F_v}`. Then `transfer (ι Fr) = transfer (inclusion
  (i_w(ϖ_w)⁻¹)) = N(i_w(ϖ_w))⁻¹ = [ϖ_v]⁻¹`, because the norm of the idele
  with component `ϖ_w` at `w` and `1` elsewhere is the idele with component
  `ϖ_v` at `v`.

So `det S(ι Fr) = ω(ϖ_v) = ω(transfer(ι Fr)⁻¹) = reciprocityCharacter c F E ω (ι Fr)`.
With `τ_F = transfer` the right side would be `ω_v(ϖ_v)⁻¹`. The same
computation explains the twist. A spherical vector of `T` gives one of `T'`
with each spectral parameter multiplied by `χ_v(ϖ_v)`, and
`reciprocityCharacter c F E χ (ι Fr) = χ_v(ϖ_v)`. The rank-one check in the
published `RelativeWeilAssociation.md` (`E = F`, `τ_F(inclusion x) = x⁻¹`) is
the special case `E = F`, where `transfer` is the identification of
`RelativeWeilGroup c F F` with `C_F`.

This agrees with Tate 1979. There the reciprocity map `r_F` of (1.4.1)
sends uniformizers to geometric Frobenius elements, and `τ_F = r_F⁻¹`
sends a geometric Frobenius to the class of a uniformizer. In the Library's
arithmetic convention the transfer sends a geometric Frobenius to the class
of the inverse of a uniformizer, so `τ_F` is its inverse.

## Why the arithmetic hypothesis is needed

The computation above uses only places that split completely in `E`. Two
characters of `C_F` that agree at almost all such places can still differ by
a character of `C_F / N C_E`. Such a character comes from a nontrivial
character of the Galois group when `E ≠ F`, for instance the quadratic
character `η_{E/F}` of a quadratic extension. So the split places do not
determine `det S`. At the other unramified places the computation needs the
local–global compatibility of the transfer: `transfer ∘ ι` agrees on `W_{F_v}`
with local reciprocity for `F_v` followed by `F_v^× → C_F`. Classically this
follows from the decomposition of the transfer over the double cosets of the
decomposition group, together with local class field theory, when `c F E` is
the arithmetic fundamental class. The reciprocity law `W_{E/F}^{ab} ≅ C_F`
used below is also a property of the arithmetic class. For other class
families neither fact is available. For the zero family and `E ≠ F`, for
instance, the extension `RelativeWeilGroup c F E` splits, whereas the Weil
group extension does not. So all three statements assume
`IsArithmeticClassFamily c`, and the module claims nothing for other
families. Neither the compatibility nor the reciprocity law is proved in
the Library.

## Why the statements are true

This explanation is not formalized. Fix an arithmetic class family `c`.

- **Determinant.** By the reciprocity law for `W_{E/F}` (Tate 1979 §1.2;
  Artin–Tate XV Theorem 1), `transfer` identifies the abelianization of
  `W_{E/F}` with `C_F`, also topologically. The determinant of the
  continuous representation `S` is a continuous character of `W_{E/F}`, so
  `det S = χ' ∘ transfer` for a continuous character `χ'` of `C_F`. At
  almost every finite place `v`, `S ∘ ι` is unramified. By local–global
  compatibility, `χ'` is then unramified at `v` and
  `χ'(ϖ_v)⁻¹ = det S(ι Fr) = ω_v(ϖ_v)`. So the Hecke characters `χ'⁻¹` and
  `ω` agree on `F_v^×` for all `v` outside a finite set `Σ`. By weak
  approximation, `F^×` times the ideles with component `1` at the places of
  `Σ` is dense in the ideles, so `χ'⁻¹ = ω`. Hence
  `det S = ω ∘ transfer⁻¹`.
- **Twist.** The twist has the rank of `S`. It is continuous because `S` and
  `χ ∘ transfer` are. At almost every place `χ` is unramified, so by
  local–global compatibility the twist stays unramified along `ι`, and its
  Frobenius eigenvalues are the `z_i` multiplied by `χ_v(ϖ_v)`. The finite-order twist `T'` has local components
  `(χ_v ∘ det) ⊗ T_v`. On a spherical vector the double coset of
  `diag(ϖ, …, ϖ, 1, …, 1)` with `i` uniformizers has determinant
  `ϖ^i` times a unit, so its scalar gains the factor `χ_v(ϖ_v)^i`. That is,
  the spectral parameters of `T'` are the `z_i χ_v(ϖ_v)`.

## Source correspondence

The statements follow Henniart 2000, §2.2, printed p.444 (PDF p.6),
registered as `henniart-2000-simple-proof`. In §2.1 (same page) Henniart
fixes the Weil group `W_F` of `F̄` over the number field `F` and writes
`τ_F : W_F → 𝔸_F^×/F^×` for the reciprocity map. In §2.2, `S` is a
continuous complex representation of degree `n` of `W_F` and `Π` an
automorphic representation of `GL_n(𝔸_F)`. They are associated if
`L(S_v, s) = L(Π_v, s)` at almost every finite place `v` where `S_v` and
`Π_v` are unramified. Henniart then writes:

> Cela implique immédiatement que S^∨ et Π^∨ sont associées et qu'on a
> det S = ω_Π ∘ τ_F, où ω_Π est le caractère central de Π. De plus, si χ
> est un quasicaractère de 𝔸_F^×/F^×, alors (χ ∘ τ_F) ⊗ S et (χ ∘ det) ⊗ Π
> sont associées.

This module formalizes the determinant assertion and the twist assertion
for finite-order `χ`. The formalization differs from the source in the
following derived choices.

1. **Finite level.** Henniart's `S` is a representation of the absolute Weil
   group `W_F`. Here `S` is a representation of
   `RelativeWeilGroup c F E`, as in the published association relation. The
   Library has no absolute global Weil group and no maps between levels.
   With `c` arithmetic, this group is `W_{E/F}`, a quotient of `W_F`, and
   Tate's `τ_F` on `W_F` factors through `W_{E/F}` (Tate 1979 §1.2; the
   abelianization of `W_F` is that of `W_{E/F}`). So the statements are the
   special case of Henniart's assertions for representations of `W_F` that
   factor through `W_{E/F}`. This comparison also needs the local maps `ι`
   to be compatible with the local embeddings `W_{F_v} → W_F`. It is not
   formalized.
2. **Arithmetic class.** The hypothesis `IsArithmeticClassFamily c`
   restricts the statements to the arithmetic fundamental class, where
   Henniart's assertions apply. Unlike the contragredient statement, these
   statements are not asserted for every class family. The previous section
   explains why.
3. **`τ_F` as an inverse transfer.** At finite level, `τ_F` is
   `w ↦ (transfer c F E w)⁻¹`. The section "The sign" derives this
   normalization from the Library's conventions.
4. **Cuspidal realizations only.** Henniart's `Π` is any automorphic
   representation. Here it is an actual irreducible cuspidal realization or
   class, the only kind that the published association relation covers.
5. **Central character as a hypothesis.** Henniart's `ω_Π` is the central
   character of `Π`. Here `ω` is any continuous character of `C_F` with
   `T.HasCentralCharacter ω`. The Library does not prove that a cuspidal
   realization has a central character. Since the forms of `T` are not all
   zero, such an `ω` is unique if it exists; this is not formalized either.
6. **Finite-order twists only.** Henniart's `χ` is any quasicharacter. Here
   `χ` is a Hecke character with the published finite-order twist relation.
   That relation leaves the action of the archimedean enveloping algebra
   unchanged, which is right exactly when `χ ∘ det` is locally constant at
   infinity. For a general `χ`, the twist changes the infinitesimal action,
   and the Library has no relation that describes it. Henniart uses the
   twist assertion in 2.8 (printed p.448, PDF p.10) to prove the twist
   property of his Proposition 2.6 a) (printed p.446) for every character of
   `F_0^×`, where `0` is a fixed finite place. He extends such a character to
   a character of `𝔸_F^×/F^×`. A character of `F_0^×` of finite order has an
   extension of finite order (Grunwald–Wang, Artin–Tate X Theorem 5), so
   for such characters this use is covered. For characters of infinite
   order, such as unramified characters `|·|^s`, it is not covered.
7. **Two twist forms.** Henniart's sentence does not distinguish
   presentations. The presented form fixes a presentation `P'` of `T'` and
   claims that the twist of `S` matches its spectral system. It makes no
   existence claim. The class form claims that some presentation of a
   realization in `π'`, in universe `uQ`, has a spectral system weakly
   associated with the twist of `S`. Its conclusion includes the existence
   of such a presentation. This is true because a cuspidal representation
   decomposes by the tensor product theorem into local factors of countable
   dimension, which can be realized in every universe. This existence is not
   formalized, and neither form is proved to imply the other. The
   conjunction asserts both.

## Scope

The module states three unproved theorems and their conjunction. It does
not assert:

- the reciprocity law that `transfer` induces `W_{E/F}^{ab} ≅ C_F`, which is
  the separate statement unit
  `Langlands.ClassField.Global.RelativeWeilGroup.RelativeWeilTransferReciprocityStatement`
  and is not imported here;
- the local–global compatibility of `transfer` with the local maps `ι`;
- the existence of any weakly associated pair, of local maps `ι`, of a
  central character or of a twisted realization;
- outside the conclusion of the class form, the existence of spectral
  presentations;
- twists by characters of infinite order;
- anything for class families that are not arithmetic;
- anything about the absolute Weil group `W_F`, isobaric representations
  or archimedean places.

## Sources

- G. Henniart, *Une preuve simple des conjectures de Langlands pour GL(n)
  sur un corps p-adique*, Invent. Math. 139 (2000), 439–455. Literature ID
  `henniart-2000-simple-proof`, SHA256
  `be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.
  §§2.1–2.2, printed p.444 (PDF p.6): the reciprocity map `τ_F`,
  association, and the consequences quoted above. PDF page = printed page −
  438.
- J. Tate, *Number theoretic background*, in Automorphic Forms,
  Representations and L-Functions, Proc. Sympos. Pure Math. 33, Part 2
  (1979). Literature ID `tate-1979-number-theoretic-background`. §1.2,
  printed pp.4–5 (PDF pp.13–14): `W_{E/F}^{ab} ≅ C_F` through the transfer;
  (1.4.1), printed p.6 (PDF p.15): uniformizers correspond to geometric
  Frobenius elements, opposite to Artin–Tate. PDF page = printed page + 9.
- E. Artin and J. Tate, *Class Field Theory*, AMS Chelsea (2009). Literature
  ID `artin-tate-2009-class-field-theory`. Chapter XV §1, Theorem 1 and its
  proof, printed pp.167–169 (PDF pp.176–178): the Weil group of the
  fundamental class and its transfer isomorphism.
