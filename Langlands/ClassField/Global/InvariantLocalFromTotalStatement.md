# Local compatibility from agreement with total idele invariants

Author: Worker 369.

This module states a conditional implication for supplied global invariant maps.
It defines propositions only. It does not prove the implication, construct
global or local invariants, or prove any of its hypotheses.

## Complete scope

`Langlands.ClassField.Global.GlobalInvariantLocalFromTotalStatement.{u}` is a
closed proposition with one arbitrary universe parameter `u`. Its internal
quantifiers supply:

- Every local family `I : ∀ (p : ℕ) [Fact p.Prime], InvariantFamily.{u,u} p`.
- Every witness `hI : ∀ (p : ℕ) [Fact p.Prime], (I p).RelativeImages`.
- Every `inv : FundamentalClass.GlobalInvariantMaps.{u}`.

It assumes, in order, `FundamentalClass.InvariantImages inv`,
`FundamentalClass.InvariantRestrictionOnClasses inv`, and
`FundamentalClass.InvariantTotalAgreement I hI inv`. Its conclusion is exactly
the published `FundamentalClass.InvariantLocalOnClasses I inv`.

The first premise says that each global invariant homomorphism is injective
with range `denominatorSubgroup (Module.finrank F E)`. The second is the
published class-level restriction law over compatible number-field towers:
restriction multiplies the invariant by the base-extension degree.

The new helper proposition `FundamentalClass.InvariantTotalAgreement` has
explicit parameters `I`, `hI`, and `inv` with the types above. It quantifies
every `F : Type u` with `[Field F] [NumberField F]`, every `E : Type u` with
`[Field E] [NumberField E] [Algebra F E] [IsGalois F E]`, every

```lean
wf : ∀ v : HeightOneSpectrum (𝓞 F), FinitePlacesAbove E v
wi : ∀ v : InfinitePlace F, InfinitePlacesAbove E v
a : relativeIdeleCohomology F E 2
```

and requires

```lean
inv F E (ideleQuotientCohomologyMap F E 2 a) =
  totalIdeleInvariant I hI wf wi a.
```

Thus agreement is required for all choices of places above all finite and
infinite base places, not merely a selected choice. The sum is the actual
published total idele invariant, including its archimedean terms. The quotient
map and cohomology carriers are the published constructions.

The conclusion retains every binder of `InvariantLocalOnClasses`: number
fields `F,E : Type u` with their field, number-field, algebra, and Galois
instances; finite places `v` of `F` and `w` of `E`; the `LiesOver` instance;
and the Galois instance for `w.adicCompletion E` over `(padicField v).Carrier`.
The local finite-dimensional instance is supplied by the published
`FiniteExtension.local_finite v w`. For every local class
`a : relativeCohomology (padicField v).Carrier (w.adicCompletion E) 2` and global
class `b : relativeIdeleClassCohomology F E 2`, the conclusion is

```lean
localIdeleClassMap v w 2 a = decompositionRestriction v w 2 b ↔
  (Module.finrank F E /
    Module.finrank (padicField v).Carrier (w.adicCompletion E)) • inv F E b =
      (I (residuePrime v)).relative (padicField v) (w.adicCompletion E) a.
```

Division is natural-number division, exactly as in the imported predicate.
The local inclusion and decomposition restriction are the actual published
maps. This module leaves `InvariantStatement` and all existing imported pairs
unchanged.

## Provenance and boundary

This is a derived conditional formulation of the semilocal and global
invariant formalism, not a verbatim theorem in the literature. The original
source inspected is E. Artin and J. Tate, *Class Field Theory*, AMS Chelsea
edition (2009), registered as `artin-tate-2009-class-field-theory`, SHA256
`af7ba934904a3c10012e6fd326cea493ffb6200d885d97583277bb45f935c3dd`.
The retained file is
`/home/taskhub/central-library/Artin-Tate--Class Field Theory--2009.pdf`;
one-based PDF pages equal printed pages plus nine.

Preliminaries §1, printed pp.1–2, describes the idele and idele-class modules,
the semilocal Shapiro isomorphism, and its restriction and transfer behavior.
Chapter VII §3, printed pp.42–43, defines the total invariant on idele
cohomology and records its restriction and transfer formulas. Printed
pp.47–48 explain agreement on quotient images and the construction via
inflation; p.47 explicitly observes that the idele-to-class cohomology map
need not be surjective. Lemma 4 on p.49 and the general case on p.50 provide
the global restriction and image laws.

The Library dependencies supply the precise class-level conclusion
(`InvariantClassConditions`) and total sum (`IdeleTotalInvariant`). The
statement isolates a proposed implication from their stated hypotheses.
Its later proof must establish the necessary comparison between the actual
local section, quotient map, and transfer, and use the global image and
restriction laws to obtain the class equality criterion. Those comparisons
are not asserted as proved here.

No local `RelativeConjugacy`, arbitrary change-of-base naturality, local
compatibility, transfer injectivity, or surjectivity of the idele-to-class
cohomology map is added as a premise. No inflation law or local class-formation
normalization is assumed. Existence of families satisfying the premises and
the proof of this implication remain separate obligations.
