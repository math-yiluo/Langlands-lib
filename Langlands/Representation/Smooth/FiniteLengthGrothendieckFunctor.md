# Maps of finite-length smooth Grothendieck groups induced by functors

This module constructs the integer-linear map
`Langlands.SmoothRep.FiniteLengthGrothendieckGroup.map Φ hl hx` between the
published exact Grothendieck groups of finite-length smooth representations. Its
input is an actual functor `Φ` between actual smooth representation categories,
with proofs `hl` and `hx` of the two preservation properties defined below. The
published module `Langlands.Representation.Smooth.FiniteLengthGrothendieck`
is imported and used only through its published interface. Its
Lean/Markdown pair and import closure are unchanged.

## Setting and universes

On the source side, `R : Type uR` is a commutative ring and `G : Type uG` is a
group with a topology. The source carriers lie in `Type uV`. On the target side,
`S : Type uS` is a commutative ring and `H : Type uH` is a group with a topology,
with carriers in `Type uW`. All six universes are independent; the inspected
level parameters of `map` are exactly `uR, uG, uV, uS, uH, uW`. The functor is

```
Φ : SmoothRep.{uR, uG, uV} R G ⥤ SmoothRep.{uS, uH, uW} S H.
```

It is an ordinary `CategoryTheory.Functor` between the canonical full
subcategories of Mathlib `Rep`. No additivity, linearity, adjoint, or
abelian-category structure is assumed. The two coefficient rings are
genuinely independent, because the construction only uses the abelian group
structure of the target quotient. No obstruction to the two-ring form arose.

The source quotient `FiniteLengthGrothendieckGroup.{uR, uG, uV} R G` lies in
`Type (max uR uG (uV + 1))`. The target quotient
`FiniteLengthGrothendieckGroup.{uS, uH, uW} S H` lies in
`Type (max uS uH (uW + 1))`. Neither is resized. Each object is sent to its actual
image object `Φ.obj A`, in the target carrier universe determined by `Φ`. No
comparison between Grothendieck groups at different carrier universes is used
or claimed.

## The preservation predicates

Both predicates are Prop-valued definitions in the namespace `Langlands.SmoothRep`.

- `PreservesFiniteLength Φ` states that for every actual source object `A`,
  `A.HasFiniteLength` implies `(Φ.obj A).HasFiniteLength`. Thus finite length
  is the published finite composition length of the representation as a
  group-algebra module, on each side over that side's own group algebra.
- `PreservesFiniteLengthShortExact Φ` considers categorical morphisms
  `f : A ⟶ B` and `g : B ⟶ C` between source objects. It assumes that all three
  objects have finite length and that `IsShortExact (hom f) (hom g)`. It then
  requires `IsShortExact (hom (Φ.map f)) (hom (Φ.map g))`. Here `hom` is the
  published `SmoothRep.hom`, which gives the underlying intertwiner of a
  morphism. `IsShortExact` is the published predicate: injectivity of the first
  map, surjectivity of the second map, and equality of the first map's range
  with the second map's kernel. Only finite-length sequences are required to be
  preserved, so this is the weaker of the two possible
  forms.

`preservesFiniteLength_id` and `preservesFiniteLengthShortExact_id` prove both
properties for the identity functor `𝟭`. `PreservesFiniteLength.comp` proves that
the property passes to a composite `Φ ⋙ Ψ`.
`PreservesFiniteLengthShortExact.comp` proves the same for exactness, using the
exactness of `Φ` and `Ψ` and the finite-length preservation of `Φ`. The last
hypothesis is needed because `Ψ`'s exactness is only assumed for finite-length
terms. Each proof applies the hypotheses directly; the composite's action on a
morphism is definitionally `Ψ.map (Φ.map f)`.

## The construction

All declarations below lie in the namespace
`Langlands.SmoothRep.FiniteLengthGrothendieckGroup`.

1. `mapObject Φ hl A` is the actual object `Φ.obj A.val`, paired with the
   finite-length proof `hl A.val A.property`, as an element of the published
   `FiniteLengthObject S H`. It introduces no new data.
2. `mapClass Φ hl` is the function on the published `FiniteLengthIsoClass R G`
   sending the class of `A` to the canonical generator `ofObject (mapObject Φ hl A)`
   of the target group. It is defined by `Quotient.lift` on the published setoid
   `finiteLengthIsoSetoid R G`. It is well defined because an actual isomorphism
   `e : A.val ≅ B.val` gives the actual image isomorphism `Φ.mapIso e`, so the
   published `ofObject_eq_of_iso` identifies the two image classes.
   `mapClass_finiteLengthIsoClass` records the defining equation; it holds by
   definition. No representative or image label is chosen.
3. `isExactAdditive_mapClass Φ hl hx` proves that `mapClass Φ hl` satisfies the
   published `IsExactAdditive R G`. A defining relation of the source group is
   given by intertwiners `f`, `g` between finite-length objects with
   `IsShortExact f g`. The proof views them as morphisms `ofHom f`, `ofHom g`.
   The published `hom (ofHom f) = f` holds by definition, so `hx` applies and
   gives exactness of the image sequence. The image terms are the finite-length
   objects `mapObject Φ hl A`, `mapObject Φ hl B`, `mapObject Φ hl C`. The
   published `ofObject_shortExact` then gives `[Φ B] = [Φ A] + [Φ C]` in the
   target group.
4. `map Φ hl hx` is the published universal lift
   `lift R G (mapClass Φ hl) (isExactAdditive_mapClass Φ hl hx)`. It is an
   integer-linear map from `FiniteLengthGrothendieckGroup R G` to
   `FiniteLengthGrothendieckGroup S H`. No second quotient is introduced.

## Generator computation and elementary laws

- `map_ofClass`, `map_ofObject`, and `map_ofRepresentation` are generator
  computations, obtained by specializing the published `lift_ofClass`,
  `lift_ofObject` and `lift_ofRepresentation`. On an actual representation `A`
  with finite-length proof `hA`, the law is

  ```
  map Φ hl hx (ofRepresentation A hA) = ofRepresentation (Φ.obj A) (hl A hA).
  ```

- `map_id hl hx` states that `map (𝟭 _) hl hx = LinearMap.id`.
- `map_comp Φ Ψ hΦl hΦx hΨl hΨx hl hx` states that
  `map (Φ ⋙ Ψ) hl hx = (map Ψ hΨl hΨx).comp (map Φ hΦl hΦx)`. It covers three
  independent sets of rings, groups and carrier universes.
- `map_eq_of_iso e hΦl hΦx hΨl hΨx` states that `map Φ hΦl hΦx = map Ψ hΨl hΨx`
  for an actual natural isomorphism `e : Φ ≅ Ψ`.

Each law holds for arbitrary proofs of the preservation hypotheses, including
those for the identity and the composite. No hypothesis is transported along a
change of objects or universe levels. Each proof applies the published
`hom_ext_object`, which reduces equality of two maps out of the quotient to
equality on the generators `ofObject A`. It then rewrites with `map_ofObject`. For
the identity and the composite, the two resulting generators are definitionally
equal. Their objects are `(𝟭 _).obj A.val = A.val` and
`(Φ ⋙ Ψ).obj A.val = Ψ.obj (Φ.obj A.val)`, and the finite-length proofs agree by
proof irrelevance, so `rfl` closes the goal. For a natural isomorphism, the
component `e.app A.val` is an actual isomorphism `Φ.obj A.val ≅ Ψ.obj A.val`, and
`ofObject_eq_of_iso` closes the goal.

## Worked GL and product-Levi specialization

Let `F : Type uF` be a field with a topology, `n : ℕ` and `B : BlockShape n`.
Consider functors between saturated-carrier categories, both
`SmoothRep.{0, uF, max uF uV}` with complex coefficients. The namespace
`Langlands.GeneralLinear.BlockShape` defines:

| Declaration | Functor | Map |
| --- | --- | --- |
| `B.finiteLengthMapToGeneralLinear F Φ hl hx` | `B.Levi F` to `GeneralLinear n F` | `B.FiniteLengthGrothendieckGroup.{uV, uF} F →ₗ[ℤ] GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} n F` |
| `B.finiteLengthMapFromGeneralLinear F Φ hl hx` | `GeneralLinear n F` to `B.Levi F` | `GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} n F →ₗ[ℤ] B.FiniteLengthGrothendieckGroup.{uV, uF} F` |

Both are defined as the generic `FiniteLengthGrothendieckGroup.map Φ hl hx`. The
codomain annotation in each declaration is the published specialized quotient
abbreviation. Both declarations therefore type-check against the published
specialized K0 quotients without universe resizing; their inspected level
parameters are `uV, uF`. The companion theorems
`finiteLengthMapToGeneralLinear_finiteLengthClass` and
`finiteLengthMapFromGeneralLinear_finiteLengthClass` give their generator
computations. These are written with the published class maps
`B.finiteLengthClass F` and `GeneralLinear.finiteLengthClass n F`, for example

```
B.finiteLengthMapToGeneralLinear F Φ hl hx (B.finiteLengthClass F A hA) =
  GeneralLinear.finiteLengthClass n F (Φ.obj A) (hl A hA).
```

No finite-dimensionality, admissibility, or field-specific hypothesis is
imposed. The functor `Φ` and its two preservation proofs are arbitrary inputs.
In particular, no parabolic induction or Jacquet functor is constructed here,
and no preservation property of such a functor is asserted.

## Source correspondence and derived provenance

The original context is Anne-Marie Aubert, *Dualité dans le groupe de
Grothendieck de la catégorie des représentations lisses de longueur finie d'un
groupe réductif p-adique*, Transactions of the AMS **347** (1995), 2179–2189,
§1, printed pp.2180–2181 (PDF pp.2–3, read for this module; literature ID
`aubert-1995-duality`). On p.2180 Aubert writes `𝓡(G)` for the Grothendieck group
of finite-length smooth complex representations. She states that the
Bernstein–Zelevinsky induction and restriction functors `i` and `r` (citing
[BZ, 2.3]) define homomorphisms `𝓡(L_I) → 𝓡(G)` and `𝓡(G) → 𝓡(L_I)`. Properties
(1.1)–(1.4) and Definition 1.5 on p.2181 then use those homomorphisms.

The present module implements the general mechanism behind such homomorphisms. It
has explicit **derived/internal** provenance: it is the standard universal-property
argument that a functor preserving finite length and short exact sequences
induces a homomorphism of exact Grothendieck groups. It is written for the
published project objects, with independent rings, groups and universes, and with
exactness read through actual intertwiners. Aubert is not cited as printing these
Lean definitions or this generality. Her p.2180 claim that `𝓡(G)` is free on
irreducible classes is neither formalized nor used. Exactness and finite-length
preservation of the Bernstein–Zelevinsky functors, and Aubert's (1.1)–(1.4),
Definition 1.5 and later results, are not proved or assumed here. They are not
part of this module, and neither is the Aubert operator itself.

No code was adapted from `Langlands.VirtualRepresentation.ExactInduction`,
`ExactRestriction` or `ExactTensor`, and none of those modules is imported. They
concern finite-dimensional representation families, not the actual smooth
finite-length quotient used here.

## Dependency and independence audit

The entry module imports only
`Langlands.Representation.Smooth.FiniteLengthGrothendieck`. Its complete project
import closure, checked recursively from the actual import lines at Library base
`d82ec7582eecc70a116cb73c7d40f31827c4b023`, is:

- `Langlands.Representation.Smooth.FiniteLengthGrothendieck` (Lean SHA-256
  `a1b5669d4ae1725028298034c53630bae21f8a97c2a9d7b32b71019891d19b6e`, Markdown
  SHA-256 `95cc767e8c97fbb0c5fe56e620aa42837eba0b9b15b3c35a9e459d831636223c`);
- `Langlands.Representation.Category.Basic`, which imports the next module and
  Mathlib only;
- `Langlands.Representation.Smooth.Definitions`, which imports Mathlib only;
- `Langlands.VirtualRepresentation.Integral`, which imports Mathlib only;
- `Langlands.Group.GL.Blocks`, which imports the next module and Mathlib;
- `Langlands.Group.GL.Basic`, which imports Mathlib only.

No project classification, Jordan–Hölder, filtration, parabolic induction,
Jacquet module, or Aubert-operator module is imported. The proofs use only the
published K0 interface (`finiteLengthIsoSetoid`, `ofObject`, `ofRepresentation`,
`ofObject_eq_of_iso`, `ofObject_shortExact`, `IsExactAdditive`, `lift` and its
generator equations, `hom_ext_object`), the published `SmoothRep.hom` and
`SmoothRep.ofHom`, and Mathlib's functor, isomorphism and quotient laws.

Consequently none of the following classification results, their conclusions,
proofs, or transitive proof dependencies supplies an input:

- analytic segment classification;
- special-head multisegment exhaustion;
- ordered special-head existence;
- quotient coverage;
- tempered block uniqueness;
- `SquareIntegrableLanglandsClassification`;
- square-integrable exhaustion;
- regular exhaustion.

This module is a conditional construction. `PreservesFiniteLength` and
`PreservesFiniteLengthShortExact` are hypotheses, not proved instances for any
particular functor. No statement definition or citation is
treated as a proved representation-theoretic theorem.

## Development validation

The entry module compiled with no errors or warnings. Inspection of
`SmoothRep.FiniteLengthGrothendieckGroup.map` reported level parameters
`uR, uG, uV, uS, uH, uW` and only the assumptions `propext`, `Classical.choice` and
`Quot.sound`. Inspection of
`GeneralLinear.BlockShape.finiteLengthMapToGeneralLinear` reported level
parameters `uV, uF` and the same assumptions. A recheck of the identical sources
by Lake build again inspected `map` with the same
result. These are development checks.
