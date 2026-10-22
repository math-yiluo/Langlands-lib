# Smooth contragredients of bundled representations and of the smooth dual

Author: Worker 23.

This module packages the published smooth contragredient
`smoothContragredient ρ` (module `Smooth/Contragredient/Definitions`) as an
operation on the bundled smooth category `Langlands.SmoothRep R G` of
`Category/Basic`. Its carrier `SmoothDual ρ` is the space of smooth linear
functionals: elements of the algebraic dual fixed by some open subgroup, with
the action `ℓ ↦ ℓ ∘ ρ(g⁻¹)`. Over `ℂ`, and when compact open subgroups are
cofinal among open subgroups, the module restricts the contragredient to the
irreducible admissible objects. There it is an involution of the smooth dual
`SmoothDualClass`. For `GL_n(F)` the cofinality hypothesis is proved here as
`GeneralLinear.compactOpen_cofinal`.

## General coefficients (namespace `Langlands.SmoothRep`)

Here `R` is a commutative ring and `G` a topological group. No topology or
dimension on the carrier is assumed.

- `isOpen_ker_inv` (namespace `Langlands`): the inverse `χ⁻¹` of a character
  `χ : G →* Rˣ` has the same kernel as `χ`, so it inherits an open kernel.
- `SmoothRep.contragredient A` is `SmoothRep.of (smoothContragredient
  A.representation)`. Its smoothness comes from the published
  `isSmooth_smoothContragredient`. The carrier of `A` lies in `Type uV` and the
  carrier of the contragredient in `Type (max uR uV)`, the universe of linear
  functionals `A →ₗ[R] R`. `contragredient_representation` records the action.
- `contragredientHom f`, for `f : A ⟶ B`, is the morphism
  `B.contragredient ⟶ A.contragredient` given by the published
  `contragredientMap`, which pulls a smooth functional back along `f`.
- `contragredientFunctor : (SmoothRep R G)ᵒᵖ ⥤ SmoothRep R G` (target carrier
  universe `max uR uV`) has object map `contragredient` and morphism map
  `contragredientHom`. Identity and composition come from the published laws
  `contragredientMap_id` and `contragredientMap_comp`.
- `contragredientIso e` is the image of an isomorphism `e : A ≅ B`. It points
  from `B.contragredient` to `A.contragredient`.
- `contragredientTwistIso χ hχ A : (A.twist χ hχ).contragredient ≅
  A.contragredient.twist χ⁻¹ _` is the published `smoothContragredientTwistEquiv`.
  Its linear map is the identity on functionals: `ℓ ∘ (χ(g⁻¹) ρ(g⁻¹)) =
  χ⁻¹(g) · (ℓ ∘ ρ(g⁻¹))`.
- `IsoClass.contragredient` is the induced map on isomorphism classes, from
  carrier universe `uV` to `max uR uV`. `IsoClass.contragredient_isoClass`
  computes it on a representative. `IsoClass.contragredient_twist` states that
  dualizing the twist by `χ` gives the twist of the dual by `χ⁻¹`.

## Complex coefficients and admissible objects

Here `G` is a topological group and `hG : CompactOpenCofinal G`, where

    CompactOpenCofinal G := ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G,
      IsCompact (L : Set G) ∧ L ≤ K.

This is the same hypothesis that the published admissible-duality theorems
take, written out inline there. Carriers are in a fixed universe `uV`.
Representations are over `ℂ`, so the contragredient again has carriers in `uV`.

- `SmoothRep.isAdmissible_contragredient_iff hG A`: `A.contragredient` is
  admissible if and only if `A` is. The forward direction is the published
  `isAdmissible_of_smoothContragredient` (module
  `Classification/SupercuspidalContragredientAux`). The converse is the
  published `isAdmissible_smoothContragredient_of_compact_cofinal` (module
  `Smooth/Contragredient/AdmissibleDualityProof`).
- `SmoothRep.smoothBidual_bijective hG A hA`: for admissible `A`, the canonical
  evaluation map `smoothBidual` into the smooth bidual is bijective. Injectivity
  holds for every smooth `A`; surjectivity uses admissibility. Both come from
  `AdmissibleDualityProof`.
- `SmoothRep.bidualIso hG A hA : A ≅ A.contragredient.contragredient` is that
  evaluation map as an isomorphism. `hom_bidualIso_hom` records that its forward
  map is `smoothBidual`.
- `SmoothRep.isIrreducible_contragredient_iff hG A hA`: an admissible `A` is
  irreducible if and only if its contragredient is. This is the published
  `isIrreducible_smoothContragredient_iff_of_bidual`, applied with injectivity
  of evaluation for all smooth representations in universe `uV` and with
  bijectivity for `A`.
- `IrreducibleAdmissibleRep.contragredient hG A` is the contragredient of an
  irreducible admissible object, again irreducible and admissible by the two
  results above. `contragredient_obj` records its underlying object.
- `IrreducibleAdmissibleRep.contragredientFunctor hG` is the contragredient
  functor on the full subcategory, from its opposite to itself. It is the lift
  of `SmoothRep.contragredientFunctor`. `contragredientIso` is its action on
  isomorphisms.
- `IrreducibleAdmissibleRep.bidualIso hG A : A ≅ contragredient hG
  (contragredient hG A)` is the evaluation isomorphism.
- `IrreducibleAdmissibleRep.contragredientTwistIso hG χ hχ A` is the twist
  compatibility for the published `IrreducibleAdmissibleRep.twist`.
- `SmoothDualClass.contragredient hG` is the induced map on the smooth dual.
  `contragredient_mk` computes it on a representative. The following facts are
  proved about it:
  - `contragredient_mk_eq_mk_iff`: the class of `B` is the contragredient of the
    class of `A` exactly when there is an actual equivariant linear equivalence
    `(smoothContragredient A.obj.representation).Equiv B.obj.representation`.
  - `contragredient_contragredient` and `contragredient_involutive`: the map is
    an involution, by `bidualIso`.
  - `contragredient_bijective`: it is a bijection.
  - `contragredient_twist`: `(a ⊗ χ)~ = ã ⊗ χ⁻¹` on classes.

## The general linear group (namespace `Langlands.GeneralLinear`)

`GeneralLinear.compactOpen_cofinal F T n` proves `CompactOpenCofinal` for
`GL_n(F)` with the topology `T.topology`, for every p-adic field `F`, every
topological realization `T`, and every `n`. Every open subgroup `K` is a
neighbourhood of `1`. The published `T.generalLinearCompactOpen` (module
`Group/GL/CompactOpen`) provides a compact open subgroup inside any such
neighbourhood. So, for instance,
`SmoothDualClass.contragredient (GeneralLinear.compactOpen_cofinal F T n)` is
the contragredient involution of the smooth dual of `GL_n(F)`.

## Sources

W. Casselman, *Introduction to the theory of admissible representations of
p-adic reductive groups*, draft of 1 May 1995 (registered source
`casselman-1995-admissible-representations`, SHA-256
`78b921fc6331ad2b75389f37d15bd5ac3399e6cfc2d7555e1a4d666e0d42612a`; PDF page =
printed page):

- p. 21: "If (π, V) is any smooth representation and χ is a character, one
  defines (π ⊗ χ, V), or sometimes (π · χ, V), to be the representation of G on
  the same space, taking g to π(g) · χ(g)." The same page defines the dual
  `π̂(g) = ᵗπ(g⁻¹)` on the algebraic dual `V̂`.
- p. 22: "… define its contragredient (π̃, Ṽ) to be the restriction of π̂ to the
  subspace Ṽ of elements of V̂ fixed by some open subgroup. Thus, π̃ is smooth."
- Proposition 2.1.10, p. 22: "The following are equivalent: (a) π is
  admissible; (b) π̃ is admissible; (c) the contragredient of π̃ is isomorphic
  to π." It is followed by "One has, of course, the canonical embedding of π
  into π̃̃."
- Proposition 2.1.11, p. 22: "The functor π ⇝ π̃ is contravariant and exact."
- Corollary 2.1.13, p. 22: "The admissible representation π is irreducible if
  and only if π̃ is."

The text layer renders the tilde accents detached from their letters. The
quotations restore them.

Casselman's group is a p-adic reductive group, in which compact open subgroups
form a neighbourhood basis of the identity. The hypothesis `CompactOpenCofinal`
isolates the part of that structure the proofs use. Casselman's justification
is "For any compact open subgroup K, V̂^K is the algebraic dual of V^K, and of
course also equal to Ṽ^K." Under this hypothesis, the published
`AdmissibleDualityProof` proves the consequences used here: the contragredient
of an admissible representation is admissible, and evaluation into the bidual
is bijective. That module leaves cofinality for particular groups as a separate
obligation, which `GeneralLinear.compactOpen_cofinal` discharges for `GL_n(F)`.

| Source | Lean |
| --- | --- |
| contragredient `π̃`, p. 22 | `SmoothRep.contragredient` |
| contravariant functor, 2.1.11 | `SmoothRep.contragredientFunctor` |
| 2.1.10 (a) ⇔ (b) | `SmoothRep.isAdmissible_contragredient_iff` |
| 2.1.10 (a) ⇒ (c), canonical embedding | `SmoothRep.bidualIso`, `smoothBidual_bijective` |
| Corollary 2.1.13 | `SmoothRep.isIrreducible_contragredient_iff` |
| `π̃` on irreducible admissible classes | `SmoothDualClass.contragredient`, `contragredient_contragredient` |
| `π ⊗ χ`, p. 21, and its contragredient | `contragredientTwistIso`, `SmoothDualClass.contragredient_twist` |

## Provenance and scope

The constructions are derived: they bundle published unbundled results and
follow the Casselman statements quoted above. The twist identity
`(π ⊗ χ)~ ≅ π̃ ⊗ χ⁻¹` is not stated by Casselman. It is the published
`smoothContragredientTwistEquiv`, with a one-line verification given above.

Two points are not covered. Exactness in Proposition 2.1.11 is the separate
published statement in `Smooth/Contragredient/ExactStatement` and is not
restated here. The implication (c) ⇒ (a) of Proposition 2.1.10 is not
formalized. Only the canonical evaluation map is proved to be an isomorphism
for admissible objects.

Supercuspidality of the contragredient is the separate published statement
`Classification/SupercuspidalContragredientStatement`. This module does not
construct a contragredient on supercuspidal classes.
