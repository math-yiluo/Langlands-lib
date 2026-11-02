# Smooth automorphisms and the etale sheaf of Picard classes

This is a derived statement of the quotient step in Artin's correction to
Picard representability. It is a proposition to be proved; no quotient or
representability theorem is proved in this module.

The original source is M. Artin, *Versal deformations and algebraic stacks*,
Inventiones Mathematicae 27 (1974), Appendix, item 2, printed pages 186–187
(PDF pages 22–23), registered as
`artin-1974-versal-deformations-algebraic-stacks`, SHA-256
`9bf1a078bdfa3b3d3dbad8152e408238b2ce367692a0bc1957ed8c255f47ff35`.
The correction describes the etale sheaf of isomorphism classes of the
relative Picard stack. For a presentation with object scheme `P₀` and arrow
scheme `P₁`, it uses the relation
`R = P₁ ×_(P₀ ×ₛ P₀) P₁`. Smoothness of the automorphism groups makes the
projections `R → P₁` smooth. The quotient `P₁/R` is an algebraic space
relation on `P₀`; its quotient is the etale sheaf of Picard classes.

The general quotient and local finite type ingredients are documented in the
Stacks Project, Theorem 80.10.1 (tag 04S6), Section 80.12 (tag 076L,
especially Lemmas 80.12.3–4), and Remark 74.20.5 (tag 06FC, item 3).
The original pages `04S6.html`, `076L.html` and `06FC.html` are retained in
the registered folder `stacks-smooth-quotient-local-finite-type-2026-11-01`,
SHA-256 `ea18197c7ff281b249564e51225bb653f30bbf175c60df3c275a9a3c15e14072`.
They supply, respectively, algebraic-space quotients by flat locally
finitely presented equivalence relations, etale sheaf criteria using smooth
presentations, and smooth-local descent for local finite type. These are
source ingredients for the derived assertion, not Lean proofs of its inputs.

`SmoothAutomorphismEtaleAtlasStatement` isolates these geometric inputs on
the actual relative Picard pseudofunctor for an arbitrary morphism `f : X → S`.
Its three hypotheses are:

- `(PicardGroupoid.relative f).IsStack (Scheme.fpqcTopology.over S)`,
  including effective descent and descent for actual bundle isomorphisms.
- `HasLocallyFiniteTypeSmoothSchemeAtlas f`: an actual scheme `P₀` over `S`,
  locally of finite type, and an actual line bundle whose point fibres over
  every relative test and bundle are represented by smooth surjective schemes.
  In particular, applying the condition to the atlas family itself gives the
  arrow scheme used in the presentation.
- `HasSmoothRelativeAutomorphismSchemes f`: the full coherent automorphism
  presheaf of every bundle on every relative test has a smooth scheme
  representative over that test.

The statement uses fpqc descent to match the existing line-bundle descent
prerequisite. This is stronger than the descent for the etale topology needed
in the quotient argument. The point-fibre and automorphism hypotheses use
the actual relative pseudofunctor, with all its pullback comparisons.
The group operations of automorphisms are retained by the represented
presheaves; smoothness is the ordinary property of their representing
scheme projections.

The conclusion is that the published ordinary
`RelativePicard.etaleClassSheafPresheaf f` has a scheme-representable diagonal
and an actual scheme atlas `U → S` with a representable etale surjective
transformation into this presheaf, with `U → S` locally of finite type.
These are exactly the geometric parts of algebraic-space representability.
The natural isomorphism `PicardGroupoid.relativeEtaleClassSheafIso f`
identifies the sheaf of groupoid classes in the source argument with this
ordinary etale class sheaf. Its unit and scheme-family compatibility
lemmas identify the canonical class maps as whole natural transformations.
The statement concerns every section of the sheaf, whether or not it has
a global line-bundle representative.

This formulation extracts the quotient argument from Artin's proper
cohomologically flat setting: descent, a scheme presentation and smooth
automorphism schemes are explicit hypotheses, so properness and
cohomological flatness are not separately assumed here. Establishing the
smooth equivalence relations, their algebraic-space quotients and the
represented diagonal and atlas on all scheme tests remains a proof
obligation. The local finite type conclusion is a derived addition: a
smooth presentation with object scheme locally of finite type gives a
quotient locally of finite type, and etale scheme atlases then have
structure morphisms locally of finite type.

No fppf descent for the etale class sheaf, invertibility of its canonical
map to fppf sheafification, or closedness of its diagonal is asserted.
Those are separate inputs to the final field theorem. This proposition
imposes no restriction on the base scheme or test schemes, and assumes
no section, universal bundle, identification of global functions with the
base, or prior representability of a Picard sheaf.
