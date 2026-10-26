# The exact Grothendieck group of finite-length smooth representations

Worker 503 constructs
`Langlands.SmoothRep.FiniteLengthGrothendieckGroup R G` from actual smooth
representations. The elementary integral-presentation proofs adapt the published
pattern in `Langlands.VirtualRepresentation.Exact` by Worker 20. The latter
module is not imported: its finite-dimensional objects do not supply the objects
of the present construction. `Langlands.VirtualRepresentation.Integral`, authored
by Worker 24, is reused through its published interface.

## Objects and exact sequences

The coefficient ring `R : Type uR` is commutative. The group `G : Type uG` has a
topology, and representation carriers belong to `Type uV`. These universes are
independent. `FiniteLengthObject R G` is the subtype of the canonical
`Langlands.SmoothRep R G` consisting of objects satisfying its existing
`HasFiniteLength` predicate. Explicitly, this is

```
IsFiniteLength R[G] A.representation.asModule.
```

It is finite length of the actual representation as a group-algebra module.
Neither finite dimension over `R` nor a proposed list of simple factors is part
of the object. The complex specialization is `R = ℂ`. No topology on the carrier,
admissibility, central character or irreducibility is required.

`finiteLengthIsoSetoid R G` relates two such objects when there exists an
isomorphism of their underlying actual smooth representations.
`FiniteLengthIsoClass R G` is its quotient, and `finiteLengthIsoClass` is the
canonical map. `finiteLengthIsoClass_eq_iff` proves that equality of these classes
is precisely existence of that isomorphism. The canonical smooth category's
`mkIso` and `equivOfIso` identify these with actual equivariant linear
equivalences. The proof of finite length is a proposition, so it introduces no
additional object label.

`SmoothRep.IsShortExact f g` uses actual intertwining linear maps between three
smooth representations. It asserts injectivity of `f`, surjectivity of `g`, and

```
LinearMap.range f.toLinearMap = LinearMap.ker g.toLinearMap.
```

These are exactly the endpoint and middle conditions for
`0 -> A --f--> B --g--> C -> 0`. In particular they imply that the composite is
zero. This definition allows three independent carrier universes. For an actual
categorical morphism one uses the published `SmoothRep.hom` to obtain its
intertwiner; conversely `SmoothRep.ofHom` takes every such intertwiner to a
morphism, with their inverse laws proved in the canonical category module. Thus
no opaque exactness predicate or assumed categorical bridge enters the
relations.

## Integral presentation and canonical classes

`FiniteLengthPresentation R G` is the free integral module
`FiniteLengthIsoClass R G →₀ ℤ`. It is free on all genuine finite-length smooth
isomorphism classes. `finiteLengthRelationSet R G` contains exactly the elements
`[B] - [A] - [C]` witnessed by actual short exact sequences with all three terms
in `FiniteLengthObject R G`. It includes nonsplit exact sequences.
`finiteLengthRelations R G` is the integral submodule spanned by this set.
`FiniteLengthGrothendieckGroup R G` is the quotient by that submodule, with its
inherited additive commutative group and integer module structures.

The namespace `SmoothRep.FiniteLengthGrothendieckGroup` supplies `quotientMap`,
`ofClass`, `ofObject`, and `ofRepresentation A hA`. The last takes an actual
smooth representation and its group-algebra finite-length proof separately.
`ofObject_eq_of_iso` and `ofRepresentation_eq_of_equiv` establish isomorphism
invariance. `ofObject_shortExact` and `ofRepresentation_shortExact` give
`[B] = [A] + [C]` for every actual sequence in the defining family. Their proof
puts the displayed relation in the span, applies the quotient's zero criterion,
and rearranges the resulting equality. No equivariant splitting is chosen.

The presentation is the exact Grothendieck-group presentation for the
finite-length smooth family. It needs no theorem identifying this group with a
free group on irreducibles. Closure theorems for an abstract exact category are
not assumed as structure fields or needed to form this quotient by the actual
sequences.

## Universal additive lift and elementary proof correspondence

Let `M` be any abelian group in an independent universe, carrying its canonical
integer module structure. `IsExactAdditive R G a` for a function on genuine
classes means that `a(B) = a(A) + a(C)` for every actual short exact sequence of
finite-length smooth objects.

`relations_le_ker_extend` proves that the free integral linear extension of `a`
annihilates the defining submodule. On each generating relation this is exactly
the assumed equality, rewritten as a zero difference; the span property handles
all integral consequences. `lift R G a ha` is the resulting quotient linear map.
The proved equations `lift_ofClass`, `lift_ofObject`, and
`lift_ofRepresentation` compute it on the canonical generators.

`hom_ext` proves uniqueness by precomposing two quotient maps with
`quotientMap`. A single-coordinate finitely supported vector is an integral
multiple of its generator, so the generator hypothesis identifies these
composites. Surjectivity of the quotient map then identifies the original maps.
`hom_ext_object` reduces the same question to values on actual finite-length
objects by quotient induction on an isomorphism class.

`isExactAdditive_of_linearMap` applies any quotient homomorphism to the proved
short-exact-sequence identity. `existsUnique_lift_iff` proves both directions of
the universal property: exact additivity gives `lift` and its uniqueness by
`hom_ext`, while the existence of such a homomorphism implies exact additivity.
Integer-linear maps here are additive homomorphisms in their canonical
integer-linear form. These laws provide the generator computation and
extensionality needed to construct later maps from exact functors after those
functors' hypotheses have been proved. This unit does not construct those
functors or assume their exactness or finite-length preservation.

## Universe accounting and actual GL and Levi specialization

`SmoothRep R G`, `FiniteLengthObject R G` and `FiniteLengthIsoClass R G` lie in
`Type (max uR uG (uV + 1))`. The free integral module and its quotient remain in
that universe. In particular, the quotient is not silently resized to `Type uV`
and no smallness theorem or canonical choice of representative is asserted.
Relations inside a fixed presentation have all three carriers in its specified
`Type uV`. The independent-universe exactness predicate does not claim an
identification between Grothendieck groups formed at different carrier
universes.

For `F : Type uF`, `[Field F]`, `[TopologicalSpace F]`, the module defines:

| Actual group | Specialized quotient and class map |
| --- | --- |
| `Langlands.GeneralLinear n F` | `GeneralLinear.FiniteLengthGrothendieckGroup n F`, `GeneralLinear.finiteLengthClass n F` |
| `B.Levi F = ∀ i, GeneralLinear (B.size i) F` | `B.FiniteLengthGrothendieckGroup F`, `B.finiteLengthClass F` |

Both use complex coefficients and carriers in `Type (max uF uV)`, preserving
independent field and vector-space universes. They use the existing actual
matrix-unit topology and product topology, respectively. Their quotient universe
is `Type (max (uF + 1) (uV + 1))`. The specializations' explicit universe parameter
order is `.{uV, uF}`; the generic quotient's order is `.{uR, uG, uV}`. This order
is determined by the elaborated declarations, and does not identify the levels.

For example, for `V : Type (max uF uV)`, an action
`ρ : Representation ℂ (GeneralLinear n F) V`, smoothness `hs`, and actual
finite-length proof `hl : IsFiniteLength ℂ[GeneralLinear n F] ρ.asModule`, the term

```
GeneralLinear.finiteLengthClass n F (SmoothRep.of ρ hs) hl
```

has type `GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} n F`.
The identical construction with `B.Levi F` uses
`B.finiteLengthClass F (SmoothRep.of ρ hs) hl`. There is no finite-dimensionality
assumption in either specialization. They therefore apply in particular to
actual general linear groups and their product Levi groups over a
non-archimedean local field with its given topology.

## Source correspondence and derived provenance

The original category context is Anne-Marie Aubert, *Dualité dans le groupe de
Grothendieck de la catégorie des représentations lisses de longueur finie d'un
groupe réductif p-adique*, Transactions of the AMS **347** (1995), 2179–2189,
Introduction and §1, printed pp.2179–2181 (PDF pp.1–3). On p.2180, Aubert takes
smooth representations on complex vector spaces and the Grothendieck group of
those of finite length. Definition 1.5 on p.2181 then uses that group for a
separate operator. These three original pages and the complete retained audit
and citation guide were read for this unit.

- Literature ID: `aubert-1995-duality`.
- Original SHA-256: `57af9c46769f6edd8e142ddaf465e89acfa2f2147db222d26879a28a06df9693`.
- Retained original: `/home/taskhub/central-library/Aubert--Dualite dans le groupe de Grothendieck des representations lisses de longueur finie--1995/Aubert--Dualite dans le groupe de Grothendieck des representations lisses de longueur finie--1995.pdf`.

The precise integral exact-relations presentation, universe accounting,
generalization to a commutative coefficient ring and arbitrary group topology,
and all elementary construction laws here have explicit **derived/internal**
provenance. They implement the defining universal presentation of an exact
Grothendieck group using the accepted project objects and Mathlib's free modules,
spans and quotients. Aubert is cited for the original finite-length smooth
category context, not as if she printed these Lean definitions or the broader
ring/topology generality. The p.2180 assertion of an irreducible basis is not
formalized or used here.

The original irreducibility proof and the erratum have the issues described by
the retained audit and `notes/henniart/aubert-duality-route.md`. No assertion of
Aubert's Proposition 3.2, irreducible preservation, involutivity or any formal
operator identity is used in this construction.

## Dependency and independence audit

The complete project-module import closure, apart from the new entry module, is:

- `Langlands.Representation.Category.Basic`, which imports only the following
  smoothness module and Mathlib representation/category/finite-length sources;
- `Langlands.Representation.Smooth.Definitions`, which imports only Mathlib;
- `Langlands.VirtualRepresentation.Integral`, which imports only Mathlib;
- `Langlands.Group.GL.Blocks`, which imports the following basic GL module and
  Mathlib;
- `Langlands.Group.GL.Basic`, which imports only Mathlib matrix/unit topology.

This closure was checked recursively from the actual import lines against
Library base `e1201b385046b1d6f5ccf890b06e77850c129b81`. No project classification,
filtration/Jordan–Holder proof, parabolic induction or Jacquet module is imported.
The constructions and elementary proofs use only these actual object/map
interfaces, categorical isomorphism equivalence, integral presentations,
submodule spans and quotient laws. Mathlib's generic irreducibility interface
is inherited through the canonical category; no irreducible decomposition or
basis result is invoked.

Consequently none of the prohibited conclusions or their project proof
successors supplies an input: analytic segment classification
`aca8805b-054f-4d56-8045-12db7f623404`, special-head exhaustion
`3bfb61fa-1129-4fc9-83fd-7fcfec22106e`, ordered special-head existence
`ebea9a8a-9b21-4208-aa31-98c2dea1f8a3`, quotient coverage
`20e4e1c6-0f4f-4ca7-96b9-a214ba1a7584`, tempered block uniqueness
`52e97845-36bb-457d-b76f-70753334b88c`,
`SquareIntegrableLanglandsClassification` / `1cb45da2-7007-4351-a694-594fb148b8d1`,
square-integrable exhaustion `cd8ab97c-0b78-4bce-97c4-d307a28159a4`, or regular
exhaustion `bf433f0a-921a-428c-b0c0-6475438125ac`. No assertion that a proposition
definition or citation constitutes a proved mathematical input is made.

An irreducible-basis or Jordan–Holder identification, comparisons between carrier
universes, actual induction/Jacquet maps on this quotient, their finite-length
preservation, and the Aubert operator remain separate units.

## Development validation

`lean_check` in environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` compiled the
entry module and inspected `SmoothRep.FiniteLengthGrothendieckGroup` successfully
(diagnostic `974bdb70-5539-40e3-9bac-999b5381406e`), with no errors or warnings and
only `propext`, `Classical.choice`, and `Quot.sound` in its reported assumptions.
A separate private module constructed the GL and product-Levi classes directly
from arbitrary saturated-carrier actions and actual `IsFiniteLength` proofs,
and checked the specialized quotient universe; it also compiled without errors
or warnings (diagnostic `d6f97535-9c59-427f-aebf-9eb2ce854ae3`). These are development
checks; independent semantic acceptance and Library publication are separate.
