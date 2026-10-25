# Poincaré pullback trivializations for points of a dual kernel

This is an internal construction from the published conditional dual-scheme
classification API. It supplies the actual line bundle and pullback
trivialization needed before constructing an intrinsic character of a kernel.
Its mathematical input is classification by rigidified Poincaré families, not
an arbitrary pairing or character.

The motivating source is Edixhoven–van der Geer–Moonen, *Abelian Varieties*,
preliminary version dated 2012-02-08, Chapter VII, proof of Theorem 7.5,
printed page 100 (PDF page 104). That proof represents a point of the dual
isogeny's kernel by a line bundle with trivial pullback. The source theorem is
about abelian varieties over a field. The present conditional adapter over an
arbitrary base is an internal consequence of the existing universal-property
interface; it does not establish or generalize the source's kernel-duality
theorem.

## Parameters and actual representatives

Let `A` and `B` be abelian schemes over any scheme `S`, and let `f : A ⟶ B`.
Assume `hA : HasDualScheme A` and `hB : HasDualScheme B`. These are existence
propositions for actual universal rigidified Picard-zero families on all test
schemes over `S`. The selected dual parameter schemes, Poincaré families and
dual map are the existing constructions. Their existence is retained explicitly.

For `p : T ⟶ dualScheme B hB`, `dualPointFamily B hB p` is the actual
parameter pullback of `poincareFamily B hB`. Its underlying line bundle lives
on `T ×_S B`, with the parameter first, and its rigidification is along the
unit section of this family. `dualPointFamily_class` identifies its class
with the existing `dualPointClass`. With the explicit proposition
`stability : PicardZeroPullbackStatement`, `dualPointFamily_picardZero`
proves that this representative satisfies the geometric Picard-zero condition.

The family itself needs no `stability` proof. This proof enters the
classification and trivialization arguments. Homomorphism pullback preserves
Picard zero by the already proved `homPicardZeroPullback`, which is supplied
to `dualSchemeMap` rather than added as another unproved assumption.

## The origin criterion and trivializations

`dualSchemeMap_eq_origin_iff` proves, for every test scheme `T` and point `p`,

```text
p ≫ dualSchemeMap homPicardZeroPullback f hA hB = T → S → dualOrigin A hA
  ↔
Nonempty (f_T^*(dualPointFamily B hB p) ≅ O_(T ×_S A)).
```

Here `f_T` is exactly `(homFamilySpaceMap f).app T`, and the isomorphism on
the right is in the category of rigidified line bundles, with the canonical
rigidification on the structure sheaf. The structural map on the left is
`Over.homMk T.hom` followed by `dualOrigin A hA`.

The implemented proof applies the injectivity of `dualPointClass`, rewrites
composition with the dual map as actual homomorphism pullback, and rewrites
the origin's class as the trivial class. Equality in the Picard-zero subtype
is equality of its underlying rigidified classes. `Quotient.eq` identifies
this equality with the existence of an actual rigidified isomorphism.
Both directions of the criterion are proved.

`dualKernelPullbackIso` chooses such an isomorphism from a proof of the
origin equation. `dualKernelPullbackLineBundleIso` forgets the rigidification
and gives an isomorphism of the actual line-bundle pullback with the trivial
line bundle. `dualKernelPullbackModuleIso` additionally forgets local rank
one and gives

```text
(Scheme.Modules.pullback f_T).obj (dualPointFamily B hB p).obj.carrier
  ≅ structureSheaf (T ×_S A).
```

The choice uses `Classical.choice` on a proved existence proposition. The
module does not assert uniqueness or naturality of this chosen isomorphism.
Independence of a kernel character from the trivialization is a separate
obligation of the character construction.

## Parameter change

`dualPointFamilyPullbackIso` is the canonical composition comparison
between pulling the representative back along `a : T ⟶ U` and the
representative classified by `a ≫ p`. It uses the published rigidified
pullback coherence theorem.

`dualKernelPoint_restrict` proves that the origin equation persists under
precomposition with every `a`, using associativity and the structure-map
identity `a.w`. This assertion itself needs no `stability` proof.

`dualPointHomFamilyPullbackIso` combines
`homFamilyPullbackNaturality` with `dualPointFamilyPullbackIso` to compare
parameter pullback of `f_U^*(dualPointFamily p)` with
`f_T^*(dualPointFamily (a ≫ p))`. This is a statement about the actual
families and the canonical pullback comparisons, not equality of chosen
trivializations.

## Actual group-scheme kernel

The final declarations specialize to
`dualCommGroupSchemeMapFromEvaluation`. They retain exactly the existing
constructor inputs: `hA`, `hB`, the two actual inverse line bundles and
evaluation isomorphisms for the Poincaré families, and the seven fixed-map
propositions for tensor pullback, Picard-zero stability, composition, unit
coherence, associativity, the left-unitor comparison and symmetry. No
additional geometry or dual-isogeny hypothesis is introduced.

Write `df` for the underlying group-scheme homomorphism of this constructed
dual map. For an actual point `x : T ⟶ (GroupScheme.kernel df).X`,
`dualKernelPoint_eq_origin` proves the required origin equation for
`x ≫ (GroupScheme.kernelι df).hom.hom`. The proof uses
`kernelPointsEquiv` for the actual scheme-theoretic pullback kernel. It
identifies the constructed dual map with `dualSchemeMap` and the target
unit with `dualOrigin`; the remaining terminal-map equality is `Over`
morphism extensionality and the structure-map identity.

`dualKernelPointPullbackIso` and `dualKernelPointPullbackModuleIso` apply
the earlier constructions to this proved equation. In particular, the
module-sheaf isomorphism can be passed as the concrete trivialization input
to the intrinsic kernel-character construction.

## Scope

There is no isogeny, finiteness, characteristic or separatedness assumption
on the base in this adapter. Existence of the dual families and the explicit
constructor propositions remain hypotheses; this file does not prove them.
It constructs no character, Cartier-duality isomorphism or finite Weil
pairing, and asserts neither perfectness nor independence of a character
from choices. These remain subsequent mathematical steps.
