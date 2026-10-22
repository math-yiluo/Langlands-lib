# Image filtrations in character localization

This module supplies an elementary construction for the fixed support filtration
in Bernstein--Zelevinsky (1977), sections 5.3–5.4. It imports the actual
character-relation quotient from `Jacquet.Localization` and the actual
subfunctor and filtration structures from `Filtration.Definitions`.

For a commutative ring `R`, a group `G`, subgroups `U` and `M`, a character
`θ : U →* Rˣ`, and a representation `ρ`, assume that `M` normalizes `U`
and fixes `θ` under conjugation. Write `q` for the canonical surjection
onto the quotient by the span of `ρ(u)v - θ(u)v`.
For a `G`-subrepresentation `S`, `imageSubrepresentation` is the concrete
submodule `q(S)` of that quotient, with its descended `M`-action.
Its invariance is proved by sending the witness `v ∈ S` to `ρ(m)v ∈ S`.

`mem_imageSubrepresentation` identifies membership with the existence of a
representative in `S`. `mk_mem_imageSubrepresentation` equivalently requires
`s - v` to lie in the ambient character-relation span for some `s ∈ S`.
This formula uses the ambient relation span, not the relation span formed
inside `S`.

The construction preserves inclusions, zero, the full representation, and
binary sums. These facts use linear images and the surjectivity of `q`.
They do not assert preservation of intersections.

For any actual functor `F : C ⥤ Rep R G` and actual subfunctor `S` of `F`,
`imageSubfunctor` applies this image construction at every object. Naturality
follows from the already proved formula for localization of an intertwiner
on a quotient representative. The category `C`, its morphisms, and the
coefficient, group, and carrier universes are independent.

`imageFiltration` takes any actual finite filtration of `F` to a filtration
of `F ⋙ Localization.functor U θ M hMU hθ`. It retains exactly the same
ordered index set. Monotonicity is inherited through linear images, the
zero endpoint follows from the image of zero, and the full endpoint follows
from surjectivity of the quotient. `mem_imageFiltration_step` records that
the kth step consists precisely of classes with a representative in the
original kth step. Repeated steps and zero successive quotients are allowed.

## Provenance and remaining geometric-lemma obligations

The original source is I. N. Bernstein and A. V. Zelevinsky, *Induced
representations of reductive p-adic groups I* (1977), section 1.8(b),
printed 444–445 (PDF 5–6), and sections 5.3–5.4, printed 461 (PDF 22).
Literature ID: `bernstein-zelevinsky-1977-induced-i`.
SHA-256: `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.

Section 5.3 applies normalized character localization to the representation
on functions supported in an invariant open subset. It uses exactness to
identify the localized subrepresentation with a subrepresentation of the
ambient localization. Section 5.4 uses the resulting ordered support
filtration.

The present module implements the elementary image in the ambient quotient,
which is defined before exactness is proved. Its generality over arbitrary
commutative rings and groups follows from the explicit linear image
construction. No topology, local constancy, semidirect decomposition,
compactness, or limit-of-compact-subgroups assumption is needed for this
algebraic construction.

The module does not identify the localization of `S` with this image.
That identification requires injectivity of the induced localization map;
it is a separate exactness obligation. The source's inverse-half Haar
normalization, concrete support subspaces, intersection formula, and natural
geometric-lemma identifications of successive quotients remain separate
constructions or theorem statements. None is supplied as an input field here.

Author: Worker 14.
