# Smooth Picard charts from versal charts and smooth neighbourhoods

Module: `Langlands.AlgebraicGeometry.Picard.FiniteTypePointSmoothChartReduction`.

Author: Worker 1420, for task `3fa23029-256e-47ed-ad64-e5ea33971b1a`.

The main theorem is `PicardGroupoid.finiteTypePointSmoothChart_of_versal`. It
proves the published `FiniteTypePointSmoothChartStatement.{u}` from the
statements `FiniteTypeVersalChartStatement.{u}` and
`VersalSmoothNeighbourhoodStatement.{u}`, which are hypotheses here and are
not proved. This is the structure of the proof of Stacks Lemma 98.13.8
(Tag 07XY): first a chart versal at a point with residue field `k`
(Lemma 98.12.7), then shrinking it to a smooth open neighbourhood (openness
of versality and Lemmas 98.13.3 and 98.13.7). All declarations are in the
namespace `Langlands.AlgebraicGeometry.Picard.PicardGroupoid`, and all
schemes are in one universe `u`.

## Lifting points into an open subchart

Fix a scheme `S` and schemes `U`, `V`, `W` over `S`.

- `pointLift j p h`: for `j : V ⟶ U` over `S` with `j.left` an open
  immersion, and `p : W ⟶ U` over `S` whose image is contained in the image
  of `j.left` (`h`), the map `W ⟶ V` over `S` given by Mathlib's
  `IsOpenImmersion.lift`. It lies over `S` because `j` and `p` do.
- `pointLift_comp`: `pointLift j p h ≫ j = p` (from
  `IsOpenImmersion.lift_fac`).
- `pointLiftBundleIso f L j p h`: for `f : X ⟶ S` and an actual line bundle
  `L` on `U ×ₛ X`, an isomorphism between the pullback along
  `(relativeSpace f).map (pointLift j p h)` of the pullback of `L` along
  `(relativeSpace f).map j`, and the pullback of `L` along
  `(relativeSpace f).map p`. It is the published
  `LineBundle.pullbackComp` followed by the equality coming from
  functoriality of `relativeSpace` and `pointLift_comp`.

## The reduction

`finiteTypePointSmoothChart_of_versal (hA : FiniteTypeVersalChartStatement.{u})
(hB : VersalSmoothNeighbourhoodStatement.{u}) : FiniteTypePointSmoothChartStatement.{u}`.

Let `R` be of finite type over `ℤ`, `X` proper and flat over `Spec R`, `K`
a field of finite type over `R` and `L₀` an actual line bundle on
`Spec K ×_R X`.

1. `hA` gives `U` locally of finite type over `Spec R`, an actual line
   bundle `L` on `U ×_R X`, a point `u₀` with `e : κ(u₀) ≅ K`, a point
   `p : Spec K ⟶ U` over `Spec R` equal to `Spec e ≫ (Spec κ(u₀) ⟶ U)`,
   versality of `L` at `p`, and an isomorphism `c` of the pullback of `L`
   along `p` with `L₀`.
2. `p.left` is locally of finite type: its composite with `U → Spec R` is
   `Spec K → Spec R`, which is locally of finite type because `K` is of
   finite type over `R` (Mathlib's `HasRingHomProperty.Spec_iff` and
   `RingHom.finiteType_algebraMap`), and Mathlib's
   `locallyOfFiniteType_of_comp` cancels `U → Spec R`.
3. `hB` applied to these data gives `j : V ⟶ U` over `Spec R` with `j.left`
   an open immersion, `u₀` in its image, and smooth point fibres for the
   pullback `L'` of `L` along `(relativeSpace X.hom).map j`.
4. The image of `p.left` is `{u₀}`, since `p.left` factors through
   `Spec κ(u₀) ⟶ U` (Mathlib's `Scheme.fromSpecResidueField_apply`), so it
   lies in the image of `j.left`.
5. The chart is `V`, locally of finite type over `Spec R` as the composite
   of the open immersion `j.left` with `U → Spec R`. Its line bundle is
   `L'`, its point is `pointLift j p _`, and the residue isomorphism is
   `pointLiftBundleIso` followed by `c`.

## Source

The Stacks Project, registered as
`stacks-artin-axioms-approximation-2026-11-06`, `artin.pdf` (Chapter 98
"Artin's Axioms"), proof of Lemma 98.13.8 (Tag 07XY), printed p. 24: by
Lemma 98.12.7 there are `U`, `x` and a finite type point `u₀` with residue
field `k` such that `x` is versal at `u₀` and `x|_{Spec k} ≅ x₀`; by
openness of versality one shrinks `U` so that `x` is versal at every finite
type point, and then `x` is smooth. The Lean proof composes the two
statements that formalize these two steps. The open subscheme of the source
is represented by an open immersion `j`. The source's point `u₀` with residue
field `k` becomes a `K`-valued point of the shrunken chart, which is what
the published chart statement asks for.
