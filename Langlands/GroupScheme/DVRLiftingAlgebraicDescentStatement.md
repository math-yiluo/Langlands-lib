# Statement: the DVR lifting property descends along algebraic field extensions

Authors: Worker 254 (original draft) and Worker 1620 (source comparison and documentation).

`Langlands.GroupScheme.DVRLiftingAlgebraicDescentStatement` is a proposition at
universe `u`. This unit defines the proposition and proves nothing.

## The statement

For all fields `k L : Type u` with `[Algebra k L]` and
`[Algebra.IsAlgebraic k L]`, and every `X : Over (Spec (CommRingCat.of k))`:
if the base change
`(Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj X`
satisfies `PseudoComplete.HasDVRLifting` over `L`, then `X` satisfies
`PseudoComplete.HasDVRLifting` over `k`.

`PseudoComplete.HasDVRLifting` is the published predicate in
`Langlands.GroupScheme.PseudoComplete`. For `X` over `Spec k` it says: for
every discrete valuation ring `R : Type u` that is a `k`-algebra and whose
residue field is geometrically reduced over `k`, every relative morphism
`algebraSpec k (FractionRing R) ⟶ X` extends along
`genericPoint R : algebraSpec k (FractionRing R) ⟶ algebraSpec k R`. The base
change is Mathlib's `Over.pullback` along the morphism `Spec L ⟶ Spec k`
induced by `algebraMap k L`. Its underlying scheme is the fibre product
`pullback X.hom (Spec.map (CommRingCat.ofHom (algebraMap k L)))`.

No hypothesis is placed on `X`. It need not be separated or of finite type.
The proposition concerns only `HasDVRLifting`, not the full predicate
`IsPseudoComplete` (which also requires separatedness and finite type), and it
states only descent, not the converse.

## Provenance

Conrad–Gabber–Prasad, *Pseudo-reductive groups*, second edition (2015),
Proposition C.1.2(2), printed pp.582–583 (PDF pp.608–609), registered as
`conrad-gabber-prasad-2015-pseudo-reductive`. The first assertion of C.1.2(2)
is that, for any field extension `k'/k`, a `k`-scheme `X` is pseudo-complete
over `k` if `X_{k'}` is pseudo-complete over `k'`. The source first notes that
separatedness and finite type descend through a ground field extension. The
remaining content of the proof is the descent of the valuative criterion. This
proposition isolates the existence part of that argument and specializes it to
algebraic extensions `L/k`. It is a derived formulation of the first assertion,
not a verbatim restatement of the full pseudo-completeness assertion.

The source works with separated schemes of finite type and writes the valuative
criterion as an equality of sets of points. Here `HasDVRLifting` retains only
existence of extensions. That existence argument applies to arbitrary schemes:
a local injection from the test valuation ring `R` into a local domain `R'`
gives `R = R' ∩ Frac R` inside `Frac R'`. Choose an affine open neighborhood of
the image of the closed point of `Spec R'`; the morphism from `Spec R'` and the
compatible fraction-field morphism factor through this open. The intersection
identity then factors its coordinate map through `R`, giving the required
extension. No uniqueness assertion is included, so no separatedness assumption
on `X` is needed. The single universe and Mathlib pullback are formal packaging
of this valuative statement.

The proof of CGP Proposition C.1.6 (printed p.586, PDF p.612) uses C.1.2(2) to
reduce to a separably closed ground field. A separable closure is algebraic, so the specialization covers this use. The source's argument is
valid for arbitrary extensions; restricting to algebraic ones is a choice of
this statement, not a hypothesis of the source.

The registered source PDF has SHA256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.
