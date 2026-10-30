# Renard A.VIII.2: small projectives and finite-subcoproduct factorization

Authors: Worker 6 (statement design, implementation and documentation);
Worker 923 (independent source and errata reread, Markdown additions,
compilation and inspection).

This statement unit supplies
`Langlands.Renard.SmallProjectiveFiniteSupportStatement` in module
`Langlands.CategoryTheory.Renard.SmallProjectiveFiniteSupportStatements`.
It states the characterization for arbitrary abelian categories with
coproducts at an explicit independent indexing size. It supplies no proof.

## Original source and reading boundary

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The retained original is
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
Complete PDF pages 272–273 (printed 266–267) were reread for this unit.

On printed page 267 / PDF page 273, A.VIII.2 first fixes a cocomplete
abelian category and defines smallness for a projective object `P` by
preservation of direct sums by `Hom(P, •)`. It then announces equivalent
characterizations and states that `P` is a small projective if, for every
direct sum and every morphism from `P` to that sum, the morphism factors
through a finite subsum. The printed factorization is
`P → ⊕_{j∈J} M_i → M`; its summation index is `j`, so the summands are read
as `M_j`, and the Lean family `fun j : s => M j.val` implements that reading.
The printed second map is unnamed; it is read as the canonical map from the
finite subsum to `M`, which the Lean equation fixes as described below.
The displayed Lean equivalence expresses that
characterization in its projective ambient scope. Projectivity is retained
on both sides; the finite-factorization property alone is not called
projectivity.

The source uses “si” in this sentence following its announcement of
equivalent characterizations, so the sentence is read as a biconditional,
as the contract's objective also states. It gives no proof of this particular
characterization on the consulted page. The nearby citations to
Pareigis [37], 4.11, explicitly accompany the separate finite-type
comparison and the equivalence with right modules. Pareigis has not
been read for this unit, and no proof from it is claimed to have been
checked.

The supplementary author errata for the 2010 edition,
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
were reread completely at PDF pages 18–19. The correction for the 2010
printed page 309, line 2, replaces the fixed object `X` by `P` in
`Hom(P, •)`. The governing 2026 edition already incorporates it. Those
two errata pages give no correction to the finite-factorization sentence;
this is a bounded observation about the consulted pages and edition.
The public `notes/renard/appendix-a-corrections.md` concerns other
Appendix A passages. No `notes/errata` directory is present in the
inspected Library.

## Complete statement

The declaration, including every binder and its body, is:

```lean
universe w v u

def SmallProjectiveFiniteSupportStatement
    (C : Type u) [Category.{v} C] [Abelian C]
    [HasCoproducts.{w} C] : Prop :=
  ∀ P : C,
    HomSmallProjective.{w} P ↔
      HomProjective P ∧
        ∀ (I : Type w) (M : I → C) (φ : P ⟶ ∐ M),
          ∃ (s : Finset I) (g : P ⟶ ∐ (fun j : s => M j.val)),
            g ≫ Sigma.desc (fun j : s => Sigma.ι M j.val) = φ
```

This is an ordinary transparent proposition definition, not a theorem
or a hypothesis asserting its own conclusion. Every object `P` and
every family `M` at the selected indexing size are tested.

## Actual coproducts and factorization

`HasCoproducts.{w} C` means that `C` has colimits of shape `Discrete I`
for each `I : Type w`. A coproduct is a colimit of the corresponding
discrete diagram. For `M : I → C`, `∐ M` is the chosen coproduct
`sigmaObj M`, and `Sigma.ι M i : M i ⟶ ∐ M` is its actual injection.
These are the native Mathlib constructions from
`Mathlib.CategoryTheory.Limits.Shapes.Products`.

The existential `s : Finset I` specifies a finite subset of the original
index type. Its subtype, written `s` in a type position, consists of
the indices belonging to that finite set. The restricted family is
`fun j : s => M j.val`; its chosen coproduct is the actual finite
subcoproduct. The finite set may be empty. There is no ambient
`DecidableEq I` parameter and no assumption that `I` itself is finite
or nonempty.

For each `j : s`, the morphism `Sigma.ι M j.val` goes from the selected
summand into the full coproduct. Applying `Sigma.desc` to this family
of injections gives the canonical map

```lean
Sigma.desc (fun j : s => Sigma.ι M j.val) :
  (∐ (fun j : s => M j.val)) ⟶ ∐ M
```

It is characterized by composing each finite-subcoproduct injection
with this map to obtain the corresponding full injection. The
existential `g` has source `P` and target that finite subcoproduct.
The equation composes `g` first and the canonical map second, giving
the original `φ`. Thus the statement specifies both an actual
factorization and the prescribed map through which it factors.

Chosen coproducts express the source assertion about any coproduct
via the canonical isomorphisms supplied by their universal properties.
This convention does not restrict the source's arbitrary families.
No theorem constructing or proving those transports is asserted by
this statement unit.

## Imported Hom predicates

The unchanged public `HomSmallProjective.{w} P`, from
`Langlands.CategoryTheory.Renard.SmallProjective`, is the conjunction
of `HomProjective P` and `HomPreservesCoproducts.{w} P`. The latter
tests preservation of every colimit of shape `Discrete I`,
`I : Type w`, by the actual functor

```lean
Langlands.CategoryTheory.Renard.preadditiveCoyonedaInt P :
  C ⥤ ModuleCat.{v} ℤ
```

At `X`, its carrier is the additive Hom group `P ⟶ X` with its
canonical integer action. At `h : X ⟶ Y`, its map sends `f` to
`f ≫ h`. Preservation means that every mapped colimit cocone has
the colimit universal property. It needs no assumption that the
target has coproducts at every unrelated indexing size `w`.

The unchanged public `HomProjective P`, from
`Langlands.CategoryTheory.Renard.HomObjectProperties`, means source
sequence exactness of that actual functor. This tests both source
one-sided exact sequences, without restricting the inputs to short
exact sequences. The right-hand conjunction retains this condition
explicitly in the finite-factorization characterization.

## Universes and hypotheses

The index universe `w`, Hom universe `v` and object universe `u`
remain independent. The declaration retains the actual instance
`[HasCoproducts.{w} C]`; this supplies coproducts for the full family
and for the finite-subset subtype, which is also in `Type w`.
An instance is not required for a different indexing size.

The source's ambient cocompleteness is weakened to coproducts at the
indexing size `w`: these are the only colimits either side mentions, and
`HasColimitsOfSize.{w, w} C` implies `HasCoproducts.{w} C`. The source's
situation is therefore included.

There is no universe equality, coproduct existence at `max u v`,
source Grothendieck condition, AB5, AB6, subobject-size premise,
generator, enough projectives, Noetherianity, finite dimension or
module specialization. Projectivity is part of the proposition's
comparison, not an added ambient assumption.

## Verification and remaining obligations

Development checks use the approved environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` and prepared Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`. The statement module
compiled with no errors or warnings, and inspection reported
`statement_returns_prop: true` with exactly the universe parameters
`w`, `v`, `u`.

A separate private diagnostic printed the declaration and its axioms,
checked the full unapplied type with the actual coproduct instance
binder, and checked equality with the complete lambda body above by
`rfl`. The full type also checked at `(w, v, u) = (0, 1, 2)` and
`(2, 0, 1)`. It checked that the finite-subset family has its required
coproduct and verified the displayed canonical inclusion's defining
equation using Mathlib's `Sigma.ι_comp_desc`. That diagnostic also
compiled with no errors or warnings. Axiom inspection reported only
`propext`, `Classical.choice` and `Quot.sound`. These are development
checks of the statement and its terms; they do not prove the
characterization.

Worker 923 repeated these checks on this exact pair. The workspace
statement check (diagnostic `3d337bab-5eb2-4324-a2d8-05785a09a01e`)
reported no errors or warnings, `statement_returns_prop: true`, level
parameters `w`, `v`, `u`, and only the axioms `propext`,
`Classical.choice` and `Quot.sound`. A private inspection module
(diagnostic `e067d51c-5d84-4636-a51c-fcc5da06bce0`, no errors or
warnings) printed the fully explicit declaration, which shows both
coproduct instances derived from the `[HasCoproducts.{w} C]` binder,
checked the unapplied telescope and the body by `Iff.rfl`, checked that
the finite-subset index type is the subtype `{x : I // x ∈ s}`, typed the
canonical inclusion and its injection equation, and instantiated the
statement at `(w, v, u) = (0, 1, 2)`, `(3, 0, 1)` and `(2, 0, 1)` and for
`ModuleCat.{0} ℤ`. Worker 923 also checked the truth of the
characterization informally at arbitrary universes, as a sanity check
only; no proof is claimed.

Independent statement review and publication remain required.
The characterization proof is a separate exact-target successor
after statement publication. The separate finite-type comparison,
presentations by sums of copies of a progenerator, regular-module
converse and actual equivalence with right modules remain distinct
source obligations. This pair contains no proof of any of them.
