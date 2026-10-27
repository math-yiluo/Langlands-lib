# Contragredients of weakly associated pairs

Worker 35 authored this statement unit for task
`91266440-3276-48dc-ab77-8d1c1fa386e8`. All declarations lie in the namespace
`Langlands.ClassField.Global.RelativeWeilGroup`.

The module states the first consequence of association in Henniart 2000,
§2.2: if a representation `S` of the Weil group and an automorphic
representation `Π` are associated, then so are their contragredients `S^∨` and
`Π^∨`. It is stated for representations `S` of the published class-indexed
extension `RelativeWeilGroup c F E`, for every class family `c`, and for
actual cuspidal realizations and classes of `GL_{r+1}` over the number field
`F`. This extension is the relative Weil group `W_{E/F}` of the sources only
when `c F E` is the arithmetic fundamental class. Only that arithmetic
specialization corresponds to Henniart's assertion; the statement for other
class families is a derived generalization (see "Source correspondence").
There are three `Prop`-valued definitions:

- `PresentedContragredientAssociationStatement`, for realizations with given
  spectral presentations;
- `ClassContragredientAssociationStatement`, for cuspidal classes;
- `AssociatedContragredientStatement`, their conjunction.

The statements are not proved. No representation, contragredient realization,
presentation or local map is constructed, and no existence statement is made
apart from the conclusion of the class form, discussed below.

## Objects

- **Fields, class family and extension.** Number fields `F E : Type u` with
  `[Algebra F E]` and `[IsGalois F E]`, any class family
  `c : FundamentalClass.ClassFamily.{u}`, and the published group
  `RelativeWeilGroup c F E`. By its definition this is
  `ClassExtension (K := F) (c F E)`, the extension of `E ≃ₐ[F] E` by the
  idele class group `C_E` with class `c F E`. A class family is a family of
  arbitrary classes in `H²`; the zero family is one. As the published
  `Langlands.ClassField.Global.RelativeWeilGroup` documents, the extension is
  the relative Weil group `W_{E/F}` of the sources only when `c F E` is the
  arithmetic fundamental class `u_{E/F}`. This module assumes nothing about
  `c`, so for general `c` the group is a class-indexed extension, not a Weil
  group.
- **Weil-side representation.** `S : FiniteRepresentation.{0, u, uV} ℂ
  (RelativeWeilGroup c F E)` is a finite-dimensional complex representation
  with carrier in universe `uV`.
- **Dual representation.** `FiniteRepresentation.dual S` is the published
  algebraic dual, from `Langlands.Weil.Representation.Dual`. Its carrier is
  `Module.Dual ℂ` of the carrier of `S`, with Mathlib's
  `Representation.dual` action `g · l = l ∘ S(g⁻¹)`. Its carrier universe is
  `max 0 uV = uV`. The published `rank_dual` and `isContinuous_dual_iff`
  (`Langlands.Weil.Representation.DualClasses`) say that it has the same rank
  as `S` and is continuous exactly when `S` is.
- **Cuspidal realizations and classes.** Under the explicit assumption
  `[CompactSpace (AdeleQuotient F)]`, which the published automorphic-form
  constructions require, `T T' : Automorphic.CuspidalOperatorRealization F r`
  are actual irreducible cuspidal realizations of `GL_{r+1}` over `F`, and
  `π π' : Automorphic.CuspidalOperatorRealization.IsoClass F r` are their
  classes up to the published equivalence of realizations. The compactness
  is the conclusion of the published `AdeleQuotientCompactStatement`
  (Cassels §14), which this module neither proves nor uses as a theorem.
- **Contragredients.** `T'.realization.IsContragredientOf T.realization` is
  the published relation of `Langlands.Automorphic.Contragredient` between
  the underlying full-operator realizations. It says that a bilinear pairing
  `B` between the spaces of `T` and `T'` is invariant under the finite adelic
  group, the standard compact subgroup and the real Lie algebra, and that
  `x ↦ B(·, x)` is a linear bijection from the space of `T'` onto the
  contragredient functionals of `T`. So `T'` realizes the contragredient of
  `T`. For classes, `π'.IsContragredientOf π` is the published
  `CuspidalOperatorRealization.IsoClass.IsContragredientOf`: some
  realization in `π'` is a contragredient of some realization in `π`.
- **Spectral presentations.** `P : Automorphic.CuspidalSpectralPresentation.{u,
  uP} T` is the published presentation of a nonzero finite slice of `T` as a
  restricted tensor product of local smooth factors, with supplied unramified
  spectral data. Its local factors have carriers in universe `uP`.
  `P.spectralSystem` is the resulting `SpectralSystem (FinitePlace F) (r + 1)`.
  At each finite place `v` outside a finite exceptional set it gives
  eigenvalues `z_1, …, z_{r+1}`, and the embedded local component of `T` at `v`
  has the standard spherical Hecke operators acting on its whole spherical
  fixed space by `q_v^{i(r+1-i)/2} e_i(z)`. Its Euler polynomial at `v` is
  `∏ (1 - z_i X)`. The same holds for `P'` of `T'`, in universe `uQ`.
- **Weak association.** The published `IsWeaklyAssociated S s`, from
  `Langlands.Automorphic.Unramified.RelativeWeilAssociation`, says that `S` is
  continuous of rank `n` and that, at cofinitely many finite places `v`, the
  spectrum of `s` is defined and `IsUnramifiedMatchAt S v` holds for its Euler
  polynomial. `IsUnramifiedMatchAt S v P` says that for every place `w` of
  `E` above `v` a local map `ι : W_{F_v} →ₜ* RelativeWeilGroup c F E` with
  `IsLocalRelativeWeilMap` exists, and every such map makes `S ∘ ι` trivial on
  inertia with `det(1 - X S(ι Fr)) = P`, where `Fr` is the published
  geometric Frobenius lift of `W_{F_v}`. The published
  `IsWeaklyAssociatedClass.{u, uV, uP} S π` says that some spectral system
  attached to `π` by a cuspidal spectral presentation in universe `uP` is
  weakly associated with `S`.

## Declarations

- `PresentedContragredientAssociationStatement`: for every class family `c`,
  all `F`, `E` as above with `[CompactSpace (AdeleQuotient F)]`, every `r`,
  every `S` as above, all cuspidal realizations `T T'`, every presentation
  `P` of `T` in universe `uP` and every presentation `P'` of `T'` in universe
  `uQ`: if `T'.realization.IsContragredientOf T.realization` and
  `IsWeaklyAssociated S P.spectralSystem`, then
  `IsWeaklyAssociated (FiniteRepresentation.dual S) P'.spectralSystem`.
- `ClassContragredientAssociationStatement`: for every class family `c`, all
  `F`, `E` as above with `[CompactSpace (AdeleQuotient F)]`, every `r`, every
  `S` as above and all cuspidal classes `π π'`: if `π'.IsContragredientOf π`
  and `IsWeaklyAssociatedClass.{u, uV, uP} S π`, then
  `IsWeaklyAssociatedClass.{u, uV, uQ} (FiniteRepresentation.dual S) π'`.
- `AssociatedContragredientStatement` is the conjunction of the two
  statements, at the same universe levels.

Neither statement assumes anything about the class family `c`. In
particular, neither assumes the published `IsArithmeticClassFamily c` of
`Langlands.Automorphic.AssociatedFactorStatement`, which makes
`RelativeWeilGroup c F E` the Weil group of the arithmetic fundamental class.

## Universe levels

The universe parameters are `u` for the fields and the automorphic
realizations, `uV` for the carrier of `S`, and `uP` and `uQ` for the local
factors of the presentations on the two sides. They are independent, and
each statement is asserted at every choice of levels:
`PresentedContragredientAssociationStatement.{u, uV, uP, uQ}`,
`ClassContragredientAssociationStatement.{u, uV, uP, uQ}` and
`AssociatedContragredientStatement.{u, uV, uP, uQ}`.

## The two forms

The two forms make different claims, and neither is proved to imply the
other.

- The presented form fixes a presentation `P'` of `T'` and claims that the
  dual of `S` matches its spectral system. It makes no existence claim.
  Deriving it from the class form would need that two presentations of one
  cuspidal realization have equal spectra at almost every place.
- The class form claims that some presentation of a realization in `π'`, in
  universe `uQ`, has a spectral system weakly associated with the dual of
  `S`. Its conclusion therefore includes the existence of such a
  presentation. Deriving it from the presented form needs exactly that
  existence. It is true, but deep: a cuspidal representation is irreducible
  and admissible, so the tensor product theorem decomposes it into local
  factors that are spherical at almost every place. These factors have
  countable dimension, so they can be realized in every universe. None of
  this is formalized in the Library, and this module does not state it
  separately.

## Why the statements are true

This explanation is not formalized.

- **Rank and continuity.** The dual of `S` has the same rank as `S` and is
  continuous because `S` is, by `rank_dual` and `isContinuous_dual_iff`.
- **Weil side.** The local maps `ι` at a place `v` do not depend on the
  representation. The dual acts on `ι Fr` by the inverse transpose of
  `S(ι Fr)`, and inertia acts trivially on the dual exactly when it acts
  trivially on `S`. So if `S ∘ ι` is unramified with `det(1 - X S(ι Fr)) =
  ∏ (1 - z_i X)`, then the dual is unramified along `ι` with Euler polynomial
  `∏ (1 - z_i^{-1} X)`. The eigenvalues `z_i` are nonzero because `S(ι Fr)`
  is invertible.
- **Automorphic side.** At almost every place `v`, the local component of
  `T'` is the contragredient of the local component of `T`, because the
  invariant pairing restricts to the local tensor factors. The Satake
  parameters of the contragredient of an unramified representation are the
  inverses of the original ones. So the spectrum of `P'` at `v` is
  `z_1^{-1}, …, z_{r+1}^{-1}` when that of `P` is `z_1, …, z_{r+1}`.

Combining the two sides, the dual of `S` matches the spectrum of `P'` at
almost every place. No arithmetic property of `c` enters, because both sides
change by the same inversion of eigenvalues.

## Source correspondence

The statements follow Henniart 2000, §2.2, printed p.444 (PDF p.6),
registered as `henniart-2000-simple-proof`. There `S` is a continuous
complex representation of degree `n` of the absolute Weil group `W_F` and
`Π` an automorphic representation of `GL_n(𝔸_F)`. They are associated if
`L(S_v, s) = L(Π_v, s)` at almost every finite place `v` where `S_v` and
`Π_v` are unramified. Henniart then writes:

> Cela implique immédiatement que S^∨ et Π^∨ sont associées et qu'on a
> det S = ω_Π ∘ τ_F, où ω_Π est le caractère central de Π.

Henniart's §2.1 fixes the arithmetic absolute Weil group `W_F` of the number
field `F`. This module formalizes the first assertion. The formalization
differs from the source in the following derived choices. Items 1 and 2
separate the part that corresponds to Henniart's assertion from the part that
generalizes it.

1. **Arithmetic specialization.** Henniart's `S` is a representation of the
   absolute Weil group `W_F`. Here `S` is a representation of the
   finite-level group `RelativeWeilGroup c F E`, as in the published
   association relation; the Library has no absolute global Weil group and
   no maps between levels. The comparison with Henniart applies only when
   `c F E` is the arithmetic fundamental class, for instance when `c`
   satisfies `IsArithmeticClassFamily c`, so that `RelativeWeilGroup c F E`
   is the relative Weil group `W_{E/F}`. It also needs the local maps `ι`
   of the association relation to be compatible with the local embeddings
   `W_{F_v} → W_F`. For such `c`, pulling back along the surjection
   `W_F → W_{E/F}` takes the dual of a representation of `W_{E/F}` to the
   dual of its pullback. So the specializations of the two statements to an
   arithmetic class family are the special case of Henniart's assertion for
   representations of `W_F` that factor through `W_{E/F}`. This comparison
   is not formalized, and this module does not assume
   `IsArithmeticClassFamily c`.
2. **Generalization to every class family.** The Lean statements quantify
   over every class family `c`, including families that are not arithmetic.
   For example, for the zero family and `E ≠ F` the extension
   `RelativeWeilGroup c F E` splits, whereas the Weil group extension does
   not, since the fundamental class has order `[E : F]`. For such `c`
   Henniart's assertion says nothing, and the statements do not inherit the
   arithmetic interpretation of item 1. They are a derived generalization,
   justified only by the argument in "Why the statements are true": the
   dual preserves continuity and rank, it is unramified along every supplied
   local map `ι` along which `S` is, it inverts the Frobenius eigenvalues,
   and the contragredient inverts the Satake eigenvalues. None of this uses
   a property of `c`.
3. **Cuspidal realizations only.** Henniart's `Π` is any automorphic
   representation. Here it is an actual irreducible cuspidal realization or
   class, the only kind that the published association relation covers.
4. **Contragredient.** `Π^∨` is the published contragredient relation. It
   identifies a realization `T'` with the space of smooth `K_∞`-finite
   functionals on `T` by an invariant pairing. No realization of `Π^∨` on
   automorphic functions is constructed. The statements apply to any `T'`
   or `π'` that realizes it.
5. **Dual of `S`.** `S^∨` is the published algebraic dual
   `FiniteRepresentation.dual S`. For a finite-dimensional representation it
   is the contragredient.
6. **Two forms.** Henniart's sentence does not distinguish presentations.
   The presented form and the class form are the two readings described
   above, and the conjunction asserts both.

## Scope

The module states two unproved theorems and their conjunction. It does not
assert:

- the existence of a contragredient realization, of any weakly associated
  pair, or of local maps `ι`;
- outside the conclusion of the class form, the existence of spectral
  presentations;
- the comparison of spectra of different presentations of one realization;
- the remaining consequences of Henniart §2.2: the determinant and central
  character relation `det S = ω_Π ∘ τ_F`, and twists by characters;
- that `RelativeWeilGroup c F E` is a Weil group for any particular class
  family `c`;
- anything about the absolute Weil group `W_F`, isobaric representations or
  archimedean places.

## Sources

- G. Henniart, *Une preuve simple des conjectures de Langlands pour GL(n)
  sur un corps p-adique*, Invent. Math. 139 (2000), 439–455. Literature ID
  `henniart-2000-simple-proof`, SHA256
  `be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.
  Section 2.2, printed p.444 (PDF p.6): association, and the consequence for
  contragredients quoted above. PDF page = printed page − 438.
