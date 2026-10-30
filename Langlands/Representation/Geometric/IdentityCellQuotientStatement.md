# The identity-cell quotient of the normalized geometric lemma

This module states Zelevinsky's Corollary 1.3: the identity geometric piece is a
quotient of the normalized Jacquet module of a normalized parabolically induced
representation. `Langlands.Geometric.PadicIdentityCellQuotientTheorem` is a
proposition definition. This module does not prove it.

## Data and conclusion

The statement quantifies over every prime `p`, actual finite p-adic extension
`F : PadicField p`, compatible topology `T`, positive rank `n`, and pair of ordered
positive block shapes `B C : BlockShape n`. Field and representation-carrier
universes `uF` and `uV` stay independent. Write `M = B.Levi F.Carrier` and
`N = C.Levi F.Carrier`.

It then takes any source and target block refinements `S` and `R` for the identity
permutation. `hS : IsIntersectionRefinement B C 1 S` says that the three actual
intersection subgroups `M ∩ Q_C`, `M ∩ N` and `M ∩ V_C` equal the standard
refinement subgroups of `S`. `hR : IsIntersectionRefinement C B 1⁻¹ R` is the same
on the target side. These hypotheses only identify the subgroups. The statement
quantifies over every such pair of refinements and equality witnesses, rather
than selecting refinements existentially.

The conclusion is a natural transformation

`η : jacquetInductionFunctor T B C ⟶ geometricPieceFunctor T B C 1 S R hS.2.1 hR.2.1`

of functors `SmoothRep.{0,uF,uV} ℂ M ⥤ Rep.{max uF uV} ℂ N` whose component at
every smooth representation `A` of `M` is surjective. Both functors are the actual
Library composites from `GeometricLemmaStatement`:

- `jacquetInductionFunctor` is normalized parabolic induction from `M` to
  `GL(n,F)` followed by the normalized Jacquet functor to `N`, that is
  `r_{N,G} ∘ i_{G,M}`;
- `geometricPieceFunctor` at `w = 1` is the normalized Jacquet functor from `M` to
  `M ∩ N`, equality relabeling, transport along the identity, and normalized
  induction from `M ∩ N` to `N`, that is `i_{N,M∩N} ∘ r_{M∩N,M}`.

Both functors carry their built-in normalizing characters. No extra character
appears in the conclusion. No admissibility, finite-length, irreducibility or
cuspidality hypothesis is imposed on `A`.

## Source correspondence and provenance

The source is A. V. Zelevinsky, *Induced representations of reductive p-adic groups
II* (1980), registered as `zelevinsky-1980-induced-ii`. Corollary 1.3 is on printed
page 171 (PDF page 8). It says that for any `ρ ∈ Alg G_β` the
representation `r_{γ,(n)} ∘ i_{(n),β}(ρ)` has a quotient isomorphic to
`i_{γ,γ∩β} ∘ r_{γ∩β,β}(ρ)`. Zelevinsky derives it from Theorem 1.2 (printed
p. 170), the GL form of Bernstein–Zelevinsky 1977, 2.12. He uses Bernstein–Zelevinsky
1977, Theorem 5.2 (printed p. 460; PDF page 21), to choose an orbit
ordering whose initial unions are open with the identity coset `P_β P_γ` last. That coset is closed, so its
graded piece is the top quotient of the filtration.

Here Zelevinsky's `β` and `γ` are the shapes `B` and `C`, and `β ∩ γ` is the common
refinement encoded by `S` and `R` at `w = 1`. The quotient map is a natural
transformation with surjective components. This is the functorial form that
Bernstein–Zelevinsky 1977, 2.12 (printed p. 448; PDF page 9) and
5.2 provide; the support subfunctors are constructed explicitly in 5.3–5.4
(printed p. 461; PDF page 22). Composing the projection onto the last
quotient with its natural graded-piece isomorphism gives the asserted natural
transformation, and each component is surjective. Zelevinsky states only the
isomorphism class of the quotient for each `ρ`. The naturality and the use of arbitrary identity refinements `S`, `R`
are a derived restatement, not a separate printed result.

The identity refinement hypotheses identify the same actual intersection groups;
the equality-relabeling functors in the published composite express those
identifications for each supplied pair `S`, `R`. The Lean assertion does not add a
geometric-lemma assumption or a chosen orbit ordering as a premise. The assertion
is restricted to actual finite p-adic fields, within the local non-archimedean
scope of the sources.

The registered source fingerprints are
`663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`
for `zelevinsky-1980-induced-ii` and
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`
for `bernstein-zelevinsky-1977-induced-i`.

## Dependency boundary

The sole direct import is `Langlands.Representation.Geometric.GeometricLemmaStatement`.
Its project import closure uses the actual normalized induction, Jacquet,
intersection transport and filtration definitions. It contains no classification
or derivative modules. In particular, this statement uses none of the segment
socle arrangement, segment irreducibility, socle gluing or commutation,
multisegment exhaustion, square-integrability classification or special-head
criterion results excluded by its task. It supplies a statement for a separate
exact proof; it does not prove the quotient map from the unordered
`IsGluedFrom` assertion alone.
