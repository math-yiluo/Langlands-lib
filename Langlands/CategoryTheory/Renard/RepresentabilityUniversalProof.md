# Renard A.III.2: proof of representability and left universal problems

The theorem
`Langlands.Renard.RepresentabilityUniversal.representabilityUniversalStatements`
proves the existing proposition
`Langlands.Renard.RepresentabilityUniversal.RepresentabilityUniversalStatements.{w,vA,vB,uA,uB}`,
imported unchanged from
[RepresentabilityUniversalStatements](RepresentabilityUniversalStatements.md).
That companion explains the three components, the costructured-arrow form
of the left universal problem and the universe conventions. This file
describes the implemented proof.

Worker 1187 authored the Lean proof. Worker 709 supplied an additional
proof-documentation draft, portions of which Worker 1193 adapted to this
implementation. Worker 1193 also checked the source/formulation alignment
and prepared the final English documentation. These are author contributions;
independent review is separate.

## Source and provenance

The governing source is David Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The final remark of A.III.2 is on printed p.254 / one-based PDF260; its
proof and the corollary are on printed p.255 / PDF261. Worker 1193 read
both pages and verified the source fingerprint.

The book proves both directions of the first assertion. For the converse
it constructs the inverse of each component of the transformation by
factoring the Yoneda transformation of an element through the universal
arrow. It leaves the Hom-presheaf assertion to the reader and states
the corollary without proof. The Lean proof follows the book's argument
for the first assertion in elementwise form. The other two proofs are
internal derivations using the natural representation equivalences and
Mathlib's fully faithful Yoneda embedding.

The supplementary registered source
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
corrects identity evaluation for the universal arrow and factorization
through the representing transformation on PDF18–19. Worker 1193 read
those pages and verified that the governing 2026 passage already uses
both corrected forms. The supplementary edition does not replace the
governing source or supply a separate mathematical hypothesis.

## Declarations

All names are in `Langlands.Renard.RepresentabilityUniversal`.

| Declaration | Content |
| --- | --- |
| `yonedaUniversalStatement` | `YonedaUniversalStatement.{w,vA,uA}`: invertibility of the chosen transformation iff universality |
| `homPresheafUniversalStatement` | `HomPresheafUniversalStatement.{vA,vB,uA,uB}`: universality of the specified identity-evaluation arrow |
| `compatibleUniquenessStatement` | `CompatibleUniquenessStatement.{w,vA,uA}`: unique isomorphism respecting the chosen representations |
| `representabilityUniversalStatements` | the conjunction of the three components in source order |

## First component: invertible iff universal

Fix an arbitrary
`ω : uliftYoneda.{w}.obj X ⟶ F ⋙ uliftFunctor.{vA}`.
The first theorem proves both directions for this transformation.

Suppose `ω` is invertible. The proof applies
`Limits.IsTerminal.ofUniqueHom` to `CostructuredArrow.mk ω`.
For a costructured arrow `c`, full faithfulness of `uliftYoneda.{w}`
gives the preimage of `c.hom ≫ inv ω`. Its image followed by `ω` is
`c.hom`, so `CostructuredArrow.homMk` makes it a morphism to the
chosen costructured arrow. If `m` is any such morphism, its defining
law is `uliftYoneda.map m.left ≫ ω = c.hom`. Cancellation of the
invertible `ω` and faithfulness of `uliftYoneda` identify its left
component with the constructed preimage. `CostructuredArrow.hom_ext`
then gives equality of the costructured-arrow morphisms.

Conversely, extract terminality data `h` from the `Nonempty` witness.
The proof establishes bijectivity of `ω.app (op Y)` for every `Y : C`.
The evaluation identity used in both halves is

```text
uliftYonedaEquiv (uliftYoneda.map a ≫ ω)
  = ω.app (op Y) (ULift.up a).
```

In Lean this is obtained directly by simplifying with Mathlib's
`uliftYonedaEquiv_comp` and `uliftYonedaEquiv_uliftYoneda_map`.

- For injectivity, let `a` and `b` be lifted morphisms whose images under
  `ω.app (op Y)` agree. Injectivity of `uliftYonedaEquiv` and the
  evaluation identity show that the Yoneda transformations of `a.down`
  and `b.down`, followed by `ω`, agree. The universal-arrow lemma
  `h.hom_ext` gives `a.down = b.down`, and `ULift.ext` gives `a = b`.
- For surjectivity, let `b` be a lifted element of `F.obj (op Y)`.
  Put `θ := uliftYonedaEquiv.symm b` and take the factor
  `h.lift (CostructuredArrow.mk θ) : Y ⟶ X`. Its factorization law
  `h.fac (CostructuredArrow.mk θ)` says that its Yoneda image followed
  by `ω` is `θ`. Applying `uliftYonedaEquiv` gives
  `ω.app (op Y) (ULift.up (h.lift (CostructuredArrow.mk θ))) = b`.

Mathlib's `isIso_iff_bijective` turns each component's bijectivity into
`IsIso`, and `NatIso.isIso_of_isIso_app` proves `IsIso ω`.
The converse starts with universality alone. This is the book's inverse
construction expressed using the lifted Yoneda evaluation equivalence.

## Second component: represented Hom presheaf

Let `r : (F.op ⋙ yoneda.obj Y).RepresentableBy X` and
`j = r.homEquiv (𝟙 X) : F.obj X ⟶ Y`. Mathlib's naturality consequence
`r.homEquiv_eq` specializes for this actual Hom presheaf to

```text
r.homEquiv m = F.map m ≫ j.
```

The proof again applies `Limits.IsTerminal.ofUniqueHom`. The factor of
a costructured arrow `c`, whose structure map is
`c.hom : F.obj c.left ⟶ Y`, is `r.homEquiv.symm c.hom`.
The displayed identity and the equivalence inverse law prove
`F.map (r.homEquiv.symm c.hom) ≫ j = c.hom`, giving a
costructured-arrow morphism. Any other such morphism `m` satisfies
`F.map m.left ≫ j = c.hom`. Rewriting by `r.homEquiv_eq` and using
injectivity of `r.homEquiv` identifies `m.left` with the factor;
`CostructuredArrow.hom_ext` finishes uniqueness. The resulting
terminality data are wrapped in `Nonempty` as required by the statement.

## Third component: compatible uniqueness

For representations `ω` and `ω'`, the witness is

```text
e := uliftYoneda.{w}.preimageIso (ω ≪≫ ω'.symm) : X ≅ X'.
```

Its image under `uliftYoneda` has forward morphism
`ω.hom ≫ ω'.inv`. Consequently its composite with `ω'.hom` is
`ω.hom`, proving the required compatibility. If `e' : X ≅ X'`
satisfies the same law, cancellation of `ω'.hom` shows equality of
the Yoneda images of `e'.hom` and `e.hom`. Faithfulness gives equality
of the forward morphisms, and `Iso.ext` gives equality of the
isomorphisms. Thus uniqueness includes precisely the compatibility
with both chosen representations that the statement specifies.

## Universe packaging and scope

The first and third components use the actual `uliftYoneda.{w}`.
For each object `Y`, its value is `ULift.{w} (Y ⟶ X)`, while the
lifted presheaf has value `ULift.{vA} (F.obj (op Y))`; both lie in
`Type (max w vA)`. Their evaluation equivalence and the `ULift.up`
and `ULift.down` operations work with independent `w` and `vA`.
The Hom presheaf in the second component takes values in `Type vB`
and its representation equivalences compare those values with
`Type vA` morphisms directly; no lift or universe inequality is used.

Finally, `representabilityUniversalStatements` combines the three
closed component theorems. Its complete type is exactly the published
aggregate, with independent parameters `w`, `vA`, `vB`, `uA`, and `uB`
and no additional mathematical parameters or hypotheses. Categories,
functors, presheaves, objects and transformations remain arbitrary.
The statement pair and its imports are unchanged. This proof covers
only the final remark and corollary of A.III.2; the other Appendix A
passages and the whole-book program retain their separate obligations.
