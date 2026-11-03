# An almost-everywhere integral Iwasawa family on actual local points

Worker 695.

`Langlands.Global.IntegralIwasawaFamily.ExistenceStatement` is an unproved
proposition definition at every universe `u`. For each number field `F : Type u`,
each actual `F`-group scheme `G` satisfying the published
`IsConnectedReductive G`, and each actual morphism `p : P ⟶ G` satisfying the
published `IsParabolicSubgroup p`, it asks for one family of subgroups
`K v ≤ G.affinePoints (CommAlgCat.of F (FiniteCompletion F v))`. The family is
existentially chosen after `F`, `G`, `P` and `p`, before the adelic point or
regular function quantified in its properties.

The auxiliary proposition `IsIntegralIwasawaFamily F G P p K` consists of
three conclusions:

1. At cofinitely many finite places, `K v` is compact, every compact subgroup
   `L` containing `K v` equals `K v`, and the literal pointwise set product
   `Set.range (P.affinePointsTarget p (CommAlgCat.of F (FiniteCompletion F v))) *
   (K v : Set _)` is the whole actual local point group. The parabolic factor
   is on the left. The overgroup `L` ranges over all subgroups; no openness,
   normality or origin from a model is required.
2. For every actual `x : FiniteAdelicGroupPoints F G`, its projection belongs
   to `K v` at cofinitely many finite places. This projection is the actual
   `G.affinePointMap` induced by evaluating the finite adele coefficient ring
   at `v`. Its algebra homomorphism has underlying ring homomorphism
   `RestrictedProduct.evalRingHom (FiniteCompletion F) v`; compatibility with
   `F` is definitional. The exceptional set here may depend on `x`.
3. For every global regular function `a : Γ(G.X.left, ⊤)`, at cofinitely many
   finite places every `k ∈ K v` has integral value under
   `G.affinePointEvaluation (CommAlgCat.of F (FiniteCompletion F v)) k a`.
   The exceptional set may depend on `a` and is uniform in `k ∈ K v`.

All three cofinite filters are on `FinitePlace F`, the published type of
nonzero prime ideals of `𝓞 F`. The first cofinite assertion imposes its
compactness, maximality and covering conditions simultaneously. At its
exceptional places the target imposes none of those three local conditions.
The family still consists of subgroups at every finite place. There is no
splitness, positive rank, proper-parabolic or extra affineness hypothesis.
In particular the non-split, anisotropic and improper-parabolic cases are
retained under the published predicates.

The local carrier is the existing scheme-morphism carrier `G.affinePoints`.
Its topology is the existing topology induced by evaluating all global
regular functions into the canonical topological field `FiniteCompletion F v`.
The local instance `localPointsTopology` explicitly specializes
`G.affinePointsTopologicalSpace` to that coefficient algebra.
The integral subring is exactly `v.adicCompletionIntegers F`, the valuation
subring used by Mathlib's actual finite adele ring. The second conclusion uses
actual extension of coefficients, and the covering uses the actual target
morphism on points. No representation, replacement local carrier or chosen
ring of integers is part of the statement.

## Source and derived provenance

The source is J. R. Getz and H. Hahn, *An Introduction to Automorphic
Representations* (2024), registered
`getz-hahn-2024-automorphic-representations`, SHA256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.
The relevant passages are Theorem 2.4.3, printed p.59 (PDF p.76);
Propositions 2.4.8 and 2.4.10 and the latter's proof, printed pp.61–62
(PDF pp.78–79); and Appendix B, Lemmas B.2.3–4 and Theorem B.2.5,
printed pp.543–544 (PDF pp.548–549), Proposition B.3.1 and its proof,
printed pp.544–547 (PDF pp.549–552), and Proposition B.4.2 and
Theorem B.4.3, printed p.548 (PDF p.553). Appendix B's pagination offset
differs from Chapter 2's. The complete five-page October 2026 errata,
registered `getz-hahn-2024-errata-2026-10`, SHA256
`e641ec2a5485443f792935afe5ae4940323755968f784ce290a96d9cd76fc1c2`,
contains no correction to these passages.

The proposed mathematical route chooses a finite-type affine model of `G`
over a ring of `S`-integers and enlarges the finite set `S` so that it is
reductive. Proposition 2.4.8 supplies the good reductive reductions. The
spreading argument of Proposition B.3.1 extends the actual parabolic to a
parabolic subgroup scheme after a further finite enlargement. At the remaining
finite places one takes the image of the model's integral points inside the
actual completion points.

Theorem B.2.5 obtains the local covering through the proper quotient by the
parabolic. The valuative criterion extends a quotient point to the valuation
ring; its fibre is a parabolic torsor. Lemma B.2.4 combines smooth lifting over
a Henselian local ring with Lang's theorem over its finite residue field to
give an integral point of the torsor. Passing from a right-coset expression
to its inverse gives the displayed parabolic-left product. This argument
requires the quotient, smooth connected parabolic fibres and their comparisons
with the published parabolic predicate. It does not by itself establish
maximal compactness. Theorem 2.4.3 supplies maximal compactness for a good
reductive integral model. Proposition B.4.2 and Theorem B.4.3 give the separate
special-point route at general nonarchimedean places; no such assertion is
required at the exceptional places of this target.

The last two conclusions are derived implementation requirements, rather
than verbatim additional assertions of Theorem B.2.5. For adelic absorption,
choose finitely many affine coordinate generators for the fixed integral
model. Evaluating those generators at an actual adelic point gives finitely
many finite adeles, each integral away from finitely many places. Outside
their union the actual local point factors through the integral model. This
is the finite-coordinate comparison underlying Proposition 2.4.10. For
uniform regular-function integrality, extend each fixed global regular
function to the same model after clearing finitely many denominators. At
every remaining place its evaluation at every integral model point lies in
the same valuation subring. The denominator set depends on the function,
independently of the integral point.

## Remaining proof obligations and consumer boundary

This module proves neither existence nor any of these structural inputs.
A proof still has to construct the reductive and parabolic models from the
published hypotheses, prove the integral quotient/torsor argument and good
integral maximality, and compare model points with the actual
scheme-morphism carrier, evaluation topology and canonical valuation subring.
It must also prove the finite-coordinate factorization and denominator
arguments giving the explicit second and third conclusions.

The third conclusion applies to arbitrary selections from the full product
of the `K v`: for each regular function the selected values form an actual
finite adele. Constructing the corresponding algebra/scheme point and proving
continuity of that product lift are further adapters owned by the actual
adelic coordinate development. The second conclusion supplies the
elementwise cofinite membership needed for finite-support parabolic assembly.
The generic `CoordinateCompactAssembly` results alone do not establish these
actual adapters or this existence target. The full adelic
`AdelicGroupPoints.ParabolicIwasawaStatement`, including the remaining local
places and archimedean places, remains a separate proof target.
