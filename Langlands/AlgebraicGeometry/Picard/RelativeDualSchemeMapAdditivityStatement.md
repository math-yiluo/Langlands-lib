# Additivity of actual dual maps over a quasi-separated base

`Langlands.AbelianScheme.RelativeDualSchemeMapAdditivityStatement` is the
proposition that, over every quasi-separated scheme `S`, dualization carries
addition of homomorphisms to tensor addition on the chosen dual parameter
scheme. For abelian schemes `A`, `B` over `S`, actual universal-family
existence proofs `hA : HasDualScheme A`, `hB : HasDualScheme B`, and
homomorphisms `f g : A ⟶ B`, its equation is

`dualSchemeMap (f + g) =
  prod.lift (dualSchemeMap f) (dualSchemeMap g) ≫ dualTensor`.

All three dual maps use the published `homPicardZeroPullback` proof and
the displayed representability witnesses. The equality is in
`Hom_Over(S)(dualScheme B hB, dualScheme A hA)`. Its product is the chosen
categorical product in `Over S`; `dualTensor` is the actual morphism
classifying tensor product of the two pullbacks of the Poincare family.

`DualSchemeMapAdditivity` names this equation for fixed endpoints and
fixed tensor and pullback hypotheses over any scheme `S`. It is a
`Prop`-valued predicate, not an assertion that the equation holds.
The universal statement retains `[QuasiSeparatedSpace S]`.

## Source and derived provenance

The relative source is Kai-Wen Lan, *Arithmetic compactifications of
PEL-type Shimura varieties*, thesis revision dated March 14, 2021:

- Conventions, printed p.xxvi (PDF p.26): schemes are quasi-separated.
- Definition 1.3.2.1 and Lemma 1.3.2.2, printed pp.73–74 (PDF pp.101–102):
  relative Picard-zero classes and their rigidified interpretation.
- Theorem 1.3.2.3 and Definition 1.3.2.5, printed p.74 (PDF p.102):
  the dual abelian scheme represents this functor, with its Poincare sheaf.
- Lemma 1.3.2.8, Definition 1.3.2.9 and Lemma 1.3.2.10, printed p.75
  (PDF p.103): biduality, dual maps by pullback, and their Poincare
  compatibility.

Registered source: `lan-2008-pel-thesis-revision-2021`, SHA-256
`a7a454f5d0735f4bf11f00a8afc14c361c5fc2cefd691d7466f7620ab4c3a079`.
The author's errata dated March 14, 2021, registered
`lan-2008-pel-thesis-errata-2021`, SHA-256
`18e66df9fefa6c3d6c2ee799ec8d5c208263a22a51847032d85ccbeb6947861d`,
were checked at pp.1 and 8–9. They retain quasi-separatedness and correct
the base-pulled line bundles in the original Picard definition to come
from the test scheme `T`.

The displayed addition equation is a derived consequence, not a
verbatim theorem in these passages. Pullback and its identity and
composition laws give the contravariant duality functor; biduality and
Poincare compatibility give its natural double-dual identification.
Finite products of abelian schemes are also coproducts: a map out of
`A × B` is determined by its restrictions to the two factors, since a
group homomorphism sends `(a,b) = (a,0) + (0,b)` to the sum of their
images. The zero abelian scheme and these finite biproducts determine
addition categorically by diagonal and codiagonal. A duality preserves
this diagram, exchanging diagonal and codiagonal, and therefore
preserves addition of homomorphisms. This yields the addition equation
for the source's duality. This categorical argument is provenance for
the target; it is not implemented as a Lean proof in this module.

To reach the exact Library target, one must compare the source's
fibrewise algebraic-equivalence functor with the Library's geometric-fibre
translation-invariance predicate. The fibrewise comparison is supported
by Edixhoven–van der Geer–Moonen, *Abelian Varieties*, preliminary draft,
Corollary (7.22), printed p.106 (PDF p.110). Registered source:
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
The comparison must respect actual rigidified families and pullbacks on
all test schemes, including nonreduced ones. Restricting to affine tests
and using gluing suffices to detect equality of scheme morphisms when
comparing with the source's quasi-separated test category. Universal
uniqueness then identifies the source dual maps and addition with
`dualSchemeMap` and `dualTensor`. These comparisons remain proof
obligations.

The field addition theorem is explicitly stated in the same EGM source,
Lemma (7.16)(i) and Corollary (7.17), printed p.104 (PDF p.108).
That field result alone is not the justification for the relative
scope asserted here.

## Explicit inputs and proved specialization

The proposition universally quantifies proofs of
`pullbackTensorComparisonIsIsoStatement` and
`PicardZeroPullbackStatement`, needed to form the concrete tensor
classifying map. It does not assume the desired addition equation,
dual geometry, inverse bundles, or arbitrary choices of dual morphisms.
`HasDualScheme` concerns only the two specified abelian schemes.

The lemma `RelativeDualSchemeMapAdditivityStatement.field` proves that
this target implies the existing `FieldDualSchemeMapAdditivityStatement`.
Its proof specializes to `Spec k` and uses the affine
quasi-separatedness instance. This implication is the only theorem
proved here; relative additivity itself remains an exact proof target.

The existing `dualSchemeMap_tensor` states that each fixed dual map
preserves the tensor operation. Additivity as the input homomorphism
varies is a separate assertion. This module does not construct the
rational extension or complete the Picard and polarization development.
