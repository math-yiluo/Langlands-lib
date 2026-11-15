# Murre's Lemma 2: the étale locus of a chart is open

Module `Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreEtaleLocusOpen`
states Murre's Lemma 2 (Bourbaki exp. 294) over the spectrum of a noetherian
ring. It defines one `Prop`-valued statement, `MurreEtaleLocusOpenStatement`,
and proves nothing.

The conditions `MurreConditions`, the predicate `UnramifiedRepresentable` and
the base change `baseChange` are those of the published module
`Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreProofSteps`; the helper
`InfinitesimallyEtaleAt` is that of the published module
`Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreLocalToGlobalSteps`, whose
Markdown explains it (SGA 3, XI, Remarks 1.6–1.8). An element `ξ ∈ F(U)`, for
`U : Over S`, is the same as a morphism `U → F` of presheaves on `Over S`
(Yoneda).

## Statement

`MurreEtaleLocusOpenStatement.{u, v}`: let `R : CommRingCat.{u}` be a
noetherian ring (`[IsNoetherianRing R]`) and let
`F : (Over (Spec R))ᵒᵖ ⥤ Type v` satisfy `MurreConditions F`. Suppose that

- for every point `s : Spec R`, the base change
  `baseChange ((Spec R).fromSpecStalk s) F` of `F` to `Spec 𝒪_{Spec R, s}`
  satisfies `UnramifiedRepresentable`, that is, it is represented by a
  separated, locally of finite type, formally unramified scheme over
  `Spec 𝒪_{Spec R, s}`;
- for every ideal `I : Ideal R` with `I ≠ ⊥`, the base change
  `baseChange (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) F` of `F`
  to the closed subscheme `Spec (R/I)` satisfies `UnramifiedRepresentable`.

Let `U : Over (Spec R)` be such that `U.hom` is locally of finite type,
quasi-compact, separated and formally unramified, and let
`ξ : F.obj (op U)`. Then the set
`{y : U.left | InfinitesimallyEtaleAt F ξ y}` of points of `U` at which
`ξ : U → F` is infinitesimally étale is open in `U.left`.

## Correspondence with Murre's Lemma 2

Murre's text (printed p.250, PDF p.9): "LEMMA 2. — Let `F` be as in
proposition 2. Assume moreover that `F` is representable on all closed
subschemes of `S` (strictly contained in `S`). Let `ξ : Y → F` be given with
`Y` non-ramified, separated and of finite type over `S`. Then the set of
points `U` where `ξ` is étale is open."

- **Base.** In Proposition 2, `S` is locally noetherian. The statement is made
  for `S = Spec R` with `R` noetherian, which is the case used in Murre's
  proof of Proposition 2: that proof is a noetherian induction, and the
  Library's reduction of Proposition 2 to its steps
  (`MurreLocalToGlobalReduction`, `MurreLocalToGlobalSteps`) runs this
  induction over affine noetherian bases `Spec R`.
- **"`F` as in proposition 2".** The conditions of Theorem 1 are
  `MurreConditions F`, and the hypothesis of Proposition 2 is the
  representability of the base change of `F` to `Spec 𝒪_{S,s}` for every
  `s ∈ S`, by a scheme with the properties of Murre's remark after
  Proposition 2 (locally of finite type, unramified and separated), as in the
  Library statement `MurreLocalToGlobalStatement`.
- **"Representable on all closed subschemes of `S` (strictly contained in
  `S`)".** The closed subschemes of `Spec R` are the `Spec (R/I)`, and
  `Spec (R/I)` is strictly contained in `Spec R` exactly when `I ≠ 0`.
  Representability of `F` on `Spec (R/I)` is representability of the base
  change of `F` along `Spec (R/I) → Spec R`, by a scheme of the same kind as
  above, as in `MurreNoetherianChartsStatement`.
- **"`Y` non-ramified, separated and of finite type over `S`".** Murre's `Y`
  is `U.left` with structure morphism `U.hom`. "Of finite type" is
  `LocallyOfFiniteType U.hom` together with `QuasiCompact U.hom`; "separated"
  is `IsSeparated U.hom`; "non-ramified" (unramified, EGA IV 17.3.1: locally
  of finite presentation and formally unramified; over the noetherian base
  this is locally of finite type and formally unramified) is
  `FormallyUnramified U.hom` together with the finiteness already assumed.
- **"The set of points where `ξ` is étale".** In the remark after Lemma 2
  Murre defines "`ξ` is étale in `y`" through the scheme representing the base
  change of `F` to `Spec 𝒪_{S,s}`, `s` the image of `y`, and notes that the
  notion can be defined entirely in terms of the functor (SGA 3, XI,
  Remarks 1.6 and 1.7). The statement uses the functorial notion in the
  infinitesimal form of SGA 3, XI, Remark 1.8 (`InfinitesimallyEtaleAt`), as
  `MurreLocalToGlobalSteps` does for Lemma 3. The comparison of the two
  notions (SGA 3, XI, Remark 1.5 with Remark 1.7) is not formalized here and
  is not used by the statement.
- **Conclusion.** "Open" is `IsOpen` in the underlying topological space of
  `U.left`.

Murre's proof (printed pp.250–252, PDF pp.9–11) reduces to the case of a
closed immersion `Y → S`, uses the constructibility criterion EGA 0_III
9.2.6, and distinguishes whether the image of a point is a generic point of
an irreducible component of `S` (using (F8)) or not (using the formal
completion along the closure of the point and the induction hypothesis).
None of this is formalized here.

## Sources and provenance

Provenance is derived: the statement is Murre's Lemma 2, specialized to an
affine noetherian base and with the functorial notion of étaleness at a
point, as explained above.

- J. P. Murre, *Representation of unramified functors. Applications (according
  to unpublished results of A. Grothendieck)*, Séminaire Bourbaki exp. 294
  (1964–65), registered as `murre-1965-bourbaki-294-unramified-functors`
  (SHA-256 `e36edaf9f965bbc92b0bdc36d8026fd7c87d890b859841d1dd965193385227dd`).
  Printed page `p` is PDF page `p − 241`. Proposition 2, its remark, Lemma 2
  and the remark after it: printed p.250 (PDF p.9). Proof of Lemma 2: printed
  pp.250–252 (PDF pp.9–11).
- A. Grothendieck, SGA 3, Exposé XI, provisional recomposition by P. Gille
  and P. Polo (version of 5 December 2008), registered as
  `sga3-exposes-xi-xii-xiv-gille-polo-2008` (folder SHA-256
  `dd37c114bfb569a0d39c1cce727a0d87a8d40abf545d13e0b1a2d886d03b7498`), file
  `Expo11.pdf`. Printed page `p` is PDF page `p − 84`. Remark 1.5: printed
  pp.87–88 (PDF pp.3–4). Remarks 1.6–1.8: printed pp.88–89 (PDF pp.4–5).
