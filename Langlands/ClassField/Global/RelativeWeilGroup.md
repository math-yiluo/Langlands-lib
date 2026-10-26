# Relative global Weil groups at a supplied class family

Worker 675 authored this definition unit. All declarations lie in
`Langlands.ClassField.Global` and its namespace `RelativeWeilGroup`.
It specializes published constructions; it selects no fundamental-class family.

## The finite-level group and its scope

For `c : FundamentalClass.ClassFamily.{u}` and number fields `F E : Type u`
with `[Algebra F E] [IsGalois F E]`, the abbreviation
`RelativeWeilGroup c F E` is exactly `ClassExtension (K := F) (c F E)`.
The definition accepts every such family. This extension has the interpretation
of the sources' relative Weil group `W_{E/F}` only when `c F E` is the
arithmetic fundamental class `u_{E/F}`. No conclusion that an arbitrary
family has this property is asserted. In particular, `Generates` by itself
does not choose the arithmetic normalization.

The carrier, multiplication, product topology, and `IsTopologicalGroup`
instance are inherited from `ClassExtension`. There is no new carrier,
quotient, supplied extension, or packaged Weil-group structure. The
arithmetic action and discrete topology on `E ≃ₐ[F] E` are the published
`relativeIdeleClassAction` and `relativeGaloisTopology`. The idele class
group `C_E = NumberField.IdeleClassGroup (𝓞 E) E` keeps its quotient topology.
As in the imported modules, these action and Galois-topology instances are
installed locally; a consumer mentioning the quotient topology can install
`relativeGaloisTopology`.

The namespace exposes the published maps through `inclusion`, `projection`,
`continuousInclusion`, and `continuousProjection`. It reuses the existing
proofs in `inclusion_injective`, `projection_surjective`, `exact`,
`isOpenEmbedding_inclusion`, `isOpenQuotientMap_projection`, `conjugation`,
and `index_range_inclusion`. Thus the coefficient inclusion is an open
embedding, its range is the kernel of the surjective open quotient
projection, conjugation on coefficients is the arithmetic automorphism
action `ideleClassEquiv`, and the coefficient subgroup has index
`Module.finrank F E`. All these facts hold for every class; they require
none of the fundamental-class predicates.

## Intermediate fields

Take number fields `F ⊆ F' ⊆ E` in the same universe, with the three
algebra structures, `[IsScalarTower F F' E]`, and `[IsGalois F E]`.
Each relevant declaration installs
`IsGalois.tower_top_of_isGalois F F' E` locally; no additional Galois assumption on
`F' / F` is needed. Every declaration in this construction explicitly takes
`h : FundamentalClass.Restriction c`.

`restrictedClass_eq` applies `FundamentalClass.restriction_iff_classes`
to identify `ClassExtension.restrictedClass F' (c F E)` with `c F' E`.
`restrictionEquiv` applies `ClassExtension.equivOfRepresentative` to the
chosen representative of `c F' E`, using its class identity and this
equality. It is a continuous multiplicative equivalence

`RelativeWeilGroup c F' E ≃ₜ* ClassExtension (ClassExtension.restrictedClass F' (c F E))`.

`restrictionEquiv_inclusion` proves that it fixes `C_E`, and
`projection_restrictionEquiv` proves that it commutes with the projections
to `E ≃ₐ[F'] E`. These follow from the corresponding representative
independence lemmas; this construction is not a bare transport of carriers.

`restrictionInclusion c F E F' h` composes that equivalence with the published
`ClassExtension.restrictionInclusion F' (c F E)`. The theorems
`restrictionInclusion_inclusion` and `projection_restrictionInclusion`
show that it fixes the coefficients and covers `AlgEquiv.restrictScalars F`.
The inherited `restrictionInclusion_injective` and
`isOpenEmbedding_restrictionInclusion` follow by composition.
`range_restrictionInclusion` identifies its range with the subgroup

`(AlgEquiv.restrictScalarsHom F).range.comap (projection c F E)`.

The range proof transports witnesses along `restrictionEquiv` and applies
the published range theorem. This realizes the inverse-image subgroup of
Artin–Tate XV. The representative comparison chooses a cochain; neither a
canonical inclusion nor coherence of independently chosen inclusions through
longer towers is claimed.

## Finite places and the local-to-relative map

Let `v : Langlands.Global.FinitePlace F` and
`w : Langlands.Global.FinitePlace E`, with
`[w.asIdeal.LiesOver v.asIdeal]`. Besides global Galoisness, all declarations
in this construction have the explicit instance hypothesis

`[IsGalois (padicField v).Carrier (w.adicCompletion E)]`.

This module does not prove completed-local Galoisness from global
Galoisness. It retains the hypothesis as permitted by the interface.
The following identifications and instances are used explicitly:

- `FinitePlace F` abbreviates `HeightOneSpectrum (𝓞 F)`; the proof passes
  both places to the published criterion with this type displayed.
- `(padicField v).Carrier` is definitionally `v.adicCompletion F`. The
  compatibility proof installs the given local Galois instance with the
  latter base written explicitly.
- The completed algebra is the scoped published
  `AdelicFunctoriality.FiniteExtension` algebra.
- `Normal F E` is provided by `IsGalois.to_normal`.
- The local `FiniteDimensional (padicField v).Carrier (w.adicCompletion E)`
  instance is exactly `FiniteExtension.local_finite v w`.

Let `I : ∀ (p : ℕ) [Fact p.Prime], InvariantFamily.{u,u} p`.
Take `h : FundamentalClass.LocalCompatibility I c`,
`a : CompletionH2 v w`, and an explicit proof `ha` of

`IsFundamentalClass (padicField v).Carrier (w.adicCompletion E)
  ((I (residuePrime v)).relative (padicField v) (w.adicCompletion E)) a`.

Here `CompletionH2 v w` is the published actual relative degree-two
cohomology of the completed-field unit representation. The local class is
normalized by the supplied invariant family, as in the published predicate.
`localGlobalCompatible c v w I h a ha` applies the forward direction of
`FundamentalClass.localCompatibility_iff_classes`. Its conclusion is exactly
`CompletionClassExtension.GlobalCompatible v w a (c F E)`, that is

`localIdeleClassMap v w 2 a = decompositionRestriction v w 2 (c F E)`.

`localToRelative c v w I h a ha` is exactly the published
`CompletionClassExtension.toGlobal` with this derived compatibility proof,
and has type

`CompletionClassExtension v w a →ₜ* RelativeWeilGroup c F E`.

Write `i_w = IdeleClassGroup.ofAdicCompletion (𝓞 E) E w`,
`d = FundamentalClass.decompositionHom v w`, and let `b` be the published
`CompletionClassExtension.globalCochain` for the compatibility proof.
The coordinate formulas `localToRelative_left` and `localToRelative_right`
give

`(x, σ) ↦ (i_w(x) * b(σ), d(σ))`.

Theorems `localToRelative_inclusion` and `projection_localToRelative`
prove respectively that the coefficient map is exactly `i_w` and that the
quotient map is exactly `d`. Continuity and multiplicativity are inherited
from `toGlobal`. No injectivity, independence of the chosen cochain, or
uniqueness up to conjugation is asserted.

## Provenance and remaining prerequisites

This is a derived specialization of the published modules `ClassExtension`,
`ClassExtensionRestriction`, `CohomologyMaps`, and `LocalClassExtension`.
Its proofs reuse those constructions and their end-compatibility lemmas;
the only arithmetic input used for restriction or the finite-place map is
the corresponding explicitly supplied predicate. `FundamentalClass.Generates`
and `Inflation` are not needed by any construction here. The module does not
use `GlobalFundamentalClassStatement` as a proof or choose a family from it.

The originals supporting the intended fundamental-class specialization are:

- J. Tate, *Number theoretic background*, Proc. Sympos. Pure Math. 33,
  Part II (1979), source `tate-1979-number-theoretic-background`, SHA256
  `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
  Section 1.2, printed pp.4–5 (PDF pp.13–14), describes the extension
  `W_{E/F} = W_F / W_E^c` of `Gal(E/F)` by `C_E`, identifies its class with
  the fundamental class, states restriction of these classes in (1.2.4),
  and conversely constructs finite extensions from such classes.
  Section 1.6, Proposition (1.6.1) and its proof, printed pp.8–9
  (PDF pp.17–18), specifies the one-coordinate idele-class map and uses
  the relationship between local and global canonical classes.
- E. Artin and J. Tate, *Class Field Theory* (2009), source
  `artin-tate-2009-class-field-theory`, SHA256
  `af7ba934904a3c10012e6fd326cea493ffb6200d885d97583277bb45f935c3dd`.
  Chapter XV §1, Definition 1 and Theorem 1 with the beginning of its proof,
  printed pp.167–168 (PDF pp.176–177): the proof starts from an extension
  belonging to the fundamental class and realizes intermediate fields as
  inverse-image subgroups whose extension class is the restricted
  fundamental class. The proof continues on printed p.169 (PDF p.178)
  with transfer and the Weil-group axioms, which are outside this unit.
  In both sources PDF page equals printed page plus nine.

The following remain prerequisites for the broader Weil-group construction:

- Proving or instantiating the fundamental-class family, task
  `fb66219f-83c6-4b76-8bed-63bc57c07205`.
- Identifying `CompletionClassExtension v w a` at a local fundamental class
  with the actual local relative Weil group `W_{F_v} / W_{E_w}^c`, or
  constructing a map `W_{F_v} → CompletionClassExtension v w a`.
  Worker 53 owns the actual local Weil group and has been contacted about
  this boundary. The map here starts from the class extension.
- Archimedean places.
- Norm and tower transition maps `W_{L/F} → W_{E/F}` and the absolute
  inverse limit `W_F`, retained by Worker 2 in task
  `6c50b2fd-cb4a-47b3-8f5d-d464916d69fb`.
- Transfer and abelianization isomorphisms and the full Artin–Tate XV
  properties W1–W4.
