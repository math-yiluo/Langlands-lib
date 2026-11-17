# Free representables from global lifts

This internal construction equips an ordinary representable with the
equivariant structure supplied by a lift of the entire acting group. It
constructs a free equivariant module sheaf, identifies its maps with fixed
sections, and identifies its ordinary restriction with the actual ordinary
free representable sheaf.

Work in a category `C : Type u` with morphisms in `Type v`, a morphism
property `P`, a base object `X`, a group `G : Type z`, and
`ρ : G →* Aut X`. `GlobalLift` consists of an object `U` of `P.Over ⊤ X`
and an action `G →* (End ((ι P ρ).obj U))ᵐᵒᵖ` whose value at `g` has
twist `g⁻¹`. The inverse convention agrees with the existing
`TwistedOver.IsLift` convention and makes restriction on sections a left
action. No topology or smallness assumption on `G` is needed here.

For a twisted arrow `f : V ⟶ W` and an ordinary arrow `k : W.obj ⟶ U`,
`GlobalLift.precomp f k` is the ordinary arrow with underlying map
`f.left ≫ k.left ≫ (action (twist f)).unop.left`. Its total twist is
trivial. Multiplicativity of the supplied action proves functoriality.
On ordinary arrows this is ordinary precomposition; on the lifted action
arrows it fixes the identity generator.

Assuming `LocallySmall.{w} (P.Over ⊤ X)`, `GlobalLift.presheaf` has
values `Shrink.{w} (V.obj ⟶ U)`, with restriction given by `precomp`.
`GlobalLift.restrictionIso` identifies its restriction along `ι` with
`shrinkYoneda.{w}.obj U`. This uses small ordinary Hom sets, without
requiring small twisted Hom sets.

For a type-valued presheaf `F`, `GlobalLift.FixedSections F` is the
subtype of sections at `U` fixed under every supplied action arrow.
`GlobalLift.homEquivFixedSections` identifies maps from the lifted
presheaf with these fixed sections. In one direction it evaluates at the
identity generator; in the other it sends `k` to the restriction of the
given section along `ι(k)`. The factorization
`ι(precomp f k) = f ≫ ι(k) ≫ action(twist f).unop` proves naturality
using fixedness. Naturality along ordinary arrows proves one inverse,
and evaluation at the identity proves the other.

For a translation-invariant Grothendieck topology `J`, assume
`P.RespectsIso`, a commutative ring `R : Type w`, and module
sheafification on the twisted site. `GlobalLift.freeSheaf J R` applies
the existing `SiteCech.freeSheafFunctor` to this presheaf.
`GlobalLift.freeSheafHomEquivFixedSections` composes the existing
free-module/sheafification adjunction with the preceding equivalence.
Its value is explicitly evaluation at the sheafified identity
generator, as recorded by `freeSheafHomEquivFixedSections_val`.

Also assume ordinary module sheafification and pointwise right Kan
extensions along `ι.op` for every ordinary module presheaf.
`GlobalLift.freeSheafRestrictionIso` identifies the ordinary restriction
of `freeSheaf J R` with
`(freeSheafFunctor J R).obj (shrinkYoneda.{w}.obj U)`. It composes
Mathlib's compatibility of continuous pushforward with sheafification,
using cocontinuity of `ι`, with the sheafification of
`restrictionIso`. The lemma `freeSheafRestrictionIso_inv_unit` matches
the ordinary and twisted sheafification units.
`freeRepresentableHomEquiv_restriction` consequently states that an
equivariant map, transported along this isomorphism and restricted to
the ordinary site, represents exactly its fixed section under
`SiteCech.freeRepresentableHomEquiv`.

The provenance is internal: this is a categorical construction from the
published twisted category and the free representable adjunction,
together with Mathlib's sheafification compatibility. It asserts no
analytic existence theorem. Existence of the global lift is supplied
data. No discreteness of the resulting sheaf, compatible action on a
Čech nerve, exact equivariant cochain model, or global cohomological
comparison is asserted.
