# The integral split torus of a descended parahoric model

`Langlands.BruhatTits.IntegralModels.UnramifiedTorusClauseStatement.{u}` is
an unproved, Prop-valued target at arbitrary universe `u`. It derives the
torus clause of KP Axiom 4.1.20(3) for a supplied model over the local
integers from its integral points over the maximal unramified integers.
The combined formulation is derived from several source results; it is
not the verbatim statement of any one of them.

The Lean formulation is adapted from the revision-9 shared draft of
Task 5429 (`cd2ad671-3edf-4905-a0e2-e7aa2b160b91`). This unit publishes
the interface; its proof is a separate obligation.

## Sources and exact comparison

The main source is Tasho Kaletha and Gopal Prasad, *Bruhat–Tits Theory:
A New Approach* (2023), registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
The page numbers below are printed pages and one-based pages of the
retained PDF. KP works over a Henselian discretely valued field `k` with
perfect residue field, writing `o` for its integers, `K` for its maximal
unramified extension and `O` for the integers of `K`. Here these specialize
to the nonarchimedean local field `F`, `𝒪[F]`, `inertiaFixedField F` and
`fixedFieldIntegers F`. Equal and mixed characteristic are both included.

| Source | Source assertion and role in this target |
| --- | --- |
| §9.2.2, printed p.326 / PDF p.357 | A special `k`-torus contains a maximal `k`-split torus and becomes maximal split over `K`; its `K`-apartment is called special. No special torus is supplied in the Lean statement. |
| §9.2.5, torus paragraph, printed pp.327–328 / PDF pp.358–359 | For a nonempty bounded, Galois-stable subset of the apartment of `T_K`, the integral torus descends into the neutral model. If `T` contains a maximal `k`-split torus `S`, the maximal split integral subtorus has generic fibre `S` and maximal split special fibre. This is the desired conclusion in the source's geometric situation. |
| Proposition 9.3.4, printed p.332 / PDF p.363 | Every maximal `k`-split torus lies in a special `k`-torus. Its proof takes a point fixed by `S(K)^1` and Galois, forms the schematic closure of `S` in a descended model, and invokes B.2.4 and 8.2.1(1). The present target reuses that closure argument for the given neutral model and a subset fixed by `S(K)^1`. It does not construct a special torus or a fixed point. |
| Proposition 8.3.14(1), printed p.299 / PDF p.330, proof on PDF p.331 | Over `O`, the integral torus associated with the apartment's maximal `K`-split torus is a maximal closed torus of the neutral model. Together with 8.2.1(1), this gives the upstairs maximal-torus clause used by §9.2.5. Here `S_K` need not be maximal `K`-split: the conclusion asks for a split torus over `o` with maximal split special fibre over the residue field of `o`. |
| Proposition 8.2.1(1), printed p.286 / PDF p.317 | A torus of the special fibre containing that of a closed integral torus lifts to a closed integral torus containing it. In particular, maximal integral split tori have maximal split special fibres. This applies to the supplied smooth affine neutral model. |
| Proposition B.2.4, printed p.656 / PDF p.687 | In a smooth affine `o`-group scheme, a generic torus split over `K` whose maximal bounded `K`-point subgroup lies in the model's `O`-points has toric schematic closure over `o`. This criterion applies directly over `o`; the proof need not first construct an unrelated upstairs model. |
| Axiom 4.1.20(3), printed p.163 / PDF p.194 | For the maximal split torus of the apartment, the neutral model contains a closed integral split torus with that generic fibre and a maximal split torus as special fibre. `IntegralTorusData` and `SatisfiesTorusClause` encode precisely these maps and properties. |

The registered 1 November 2024 corrections,
`kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`,
PDF p.42, explicitly recall from §8.3.6 and §9.2.5 the existence, in
every parahoric integral model, of an integral split torus with maximal
split generic fibre. That passage supports the same source conclusion.
The present statement does not use the fixed-point argument of §9.2.1.

## Exact Lean scope

The target quantifies over every `F : Type u` with
`[Field F] [ValuativeRel F] [TopologicalSpace F]` and
`[IsNonarchimedeanLocalField F]`, and every
`G : GroupScheme (Spec (CommRingCat.of F))` with
`[IsAffineHom G.X.hom]` and `IsConnectedReductive G`.
Put `K = inertiaFixedField F` and `G_K = baseChanged F K G`.
The two local instances use the same published valuation-extension
constructions as `UnramifiedModelDescent` for
`Algebra 𝒪[F] (fixedFieldIntegers F)` and its scalar tower into `K`.
A private instance supplies affineness of `G_K` by pullback stability.
These instances add no mathematical hypotheses.

Further inputs are:

- `S : CommGroupScheme (Spec (CommRingCat.of F))` and
  `iS : S.toGrp ⟶ G`, with `IsMaximalSplitTorus iS`.
- Any `C : MaximalUnramified.BuildingData F G_K` and any
  `E : UnramifiedZeroDatum F G_K`. The former is the published supplied
  apartment and valuation-building data; this target assumes no further
  apartment or building axioms. The latter defines `E.zeroPoints` by
  the published simply connected image and torus norm-image construction
  for KP's `G(K)^0`. No compatibility between the choices in `C` and `E`
  is assumed.
- `Ya : Set C.Apartment`, with `Ya.Nonempty` and
  `∀ f : C.Apartment →ᵃ[ℝ] ℝ, BddAbove (f '' Ya)`.
  This is the exact boundedness predicate used here.
- Pointwise fixedness of `C.apartmentMap '' Ya` under
  `characterValuationKernel (MaximalUnramified.valuation F) S_K`,
  through the base change of `iS`. Since `S_K` is split, this is the
  subgroup `S(K)^1 = S(K)^b` of points with valuation zero under every
  character. The statement uses the actual integer-valued valuation on
  `K` and the actual rational-point map.
- `g : rationalPoints G` and any
  `D : RelativeComponentModelData 𝒪[F] F G`.
  This structure supplies smooth affine full and neutral models, connected
  neutral fibres and the relative-component inclusion. Its only additional
  constraint here is the equality
  ```text
  D.neutral.baseChangeUnramified.integralPoints =
    E.zeroPoints ⊓ C.pointwiseFixer
      ((fun x => rationalExtend F K G g • C.apartmentMap x) '' Ya).
  ```
  Thus the base change of the given neutral model, with its given generic
  identification, realizes `G(K)^0 ∩ Fix(Y)`, where
  `Y = (fun x => rationalExtend F K G g • C.apartmentMap x) '' Ya`.
  No particular construction of `D` is assumed.

The conclusion is exactly

```text
∃ T : IntegralTorusData D S (iS ≫ (G.innerIso g).hom),
  T.SatisfiesTorusClause.
```

It supplies an actual commutative group scheme over `𝒪[F]`, a generic
isomorphism to `S`, and an inclusion into `D.neutral` whose generic square
commutes with `Int(g) ∘ iS`. `SatisfiesTorusClause` requires integral
splitness, closedness of this inclusion and maximal splitness of its
special-fibre inclusion. The ambient special fibre is
`D.neutral.specialFibre` itself, before taking a reductive quotient.

## Derived provenance and expected proof

KP's Galois stability of the subset is used in §9.2.5 to descend the
models from `O` to `o`. Here the model is already given over `𝒪[F]`;
the subgroup of `G(K)` realized by its unramified integral points is
therefore Galois stable. This does not imply or require Galois stability
of the particular subset `Y`. Its pointwise fixer enters only through
the displayed equality.

KP places the subset in the apartment of `T_K` for a special torus
`T ⊇ S`. The maximal bounded subgroup of `T(K)`, hence `S(K)^1`,
fixes that apartment pointwise. The present hypothesis retains the
specific consequence needed for the closure of `S`: the given subset
is fixed by `S(K)^1`. It does not assert that this fixedness produces
such a special apartment. No identification of `S` with the maximal
`K`-split torus defining `C.Apartment` is needed.

The expected proof proceeds as follows; none of these steps is proved
by this statement unit.

1. Let `H = Int(g)(S)`, with generic inclusion
   `iS ≫ (G.innerIso g).hom`. The image of `S(K)^1` in `G(K)` lies in
   `G(K)^0`, and its conjugate fixes `Y` by the supplied fixedness.
   The integral-point equality therefore places the maximal bounded
   subgroup `H(K)^1` in the `O`-points of `D.neutral`.
   A proof must justify the intrinsic zero-subgroup functoriality,
   conjugation invariance and independence of the arbitrary datum `E`,
   as well as the valuation-kernel identification; these are obligations,
   not additional premises of the Lean target.
2. Apply Proposition B.2.4 directly to `D.neutral` and `H`. Their
   schematic closure is a closed `o`-torus with generic fibre `H`.
   It is split because its generic fibre is split and `o` is a normal
   Henselian DVR: the étale character lattice has trivial monodromy
   detected at the generic point. This generic-to-integral splitness
   is a formulation step beyond B.2.4's conclusion that the closure
   is a torus.
3. Any larger closed integral split torus would have a split generic
   fibre containing `H`, contradicting maximality of the conjugate
   of `S`. Generic equality determines equality of the closed tori
   by schematic closure. Hence the closure is a maximal integral
   split torus.
4. Proposition 8.2.1(1) makes its special fibre maximal split in
   `D.neutral.specialFibre`. The closure's generic identification,
   transported along `Int(g)`, provides the required identification
   with `S` and the commuting square in `IntegralTorusData`.

This explains the generalization from the source's constructed descended
model and special apartment to an arbitrary supplied model satisfying the
point equality and fixedness. In particular the algebraic closure route
needs no further building axioms on `C`. The target remains unproved.

## Consumer

Task 5429 (`cd2ad671-3edf-4905-a0e2-e7aa2b160b91`) needs this target for
the `torus` field of `BuildingModelFamily` and the `torus_clause` field
of `ModelAxiomClauses`. Their generic inclusion for the chart `g · A(S)`
is exactly `B.i ≫ (G.innerIso g).hom`. Its unramified descent inputs
supply the displayed point equality and the required fixedness for
images of apartment subsets. The full `IntegralModelAxiomsStatement`
proof remains on that task.
