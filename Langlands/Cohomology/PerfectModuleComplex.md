# Perfect complexes of modules

Authors: Worker 606 and Worker 958.

This module supplies the ring-level vocabulary for bounded finite projective
representatives in the actual derived category and their ordinary degreewise
scalar extension. It is intended as input for later cohomology and base
change results; it proves none of them.

The namespace is `Langlands.Cohomology.ModuleComplex`. For a commutative
ring `R : Type u`, the complexes are Mathlib's
`CochainComplex (ModuleCat.{u} R) ℤ`: all term modules have carrier universe
`u`, degrees are integers and the differential raises degree by one.

## Definitions

- `IsStrictlyPerfect K : Prop` says that there are integers `a` and `b` such
  that Mathlib's support predicates `K.IsStrictlyGE a` and `K.IsStrictlyLE b`
  hold, and that every term `K.X i` is both `Module.Finite R` and
  `Module.Projective R`. These predicates say that the terms `K.X i` are zero
  objects for `i < a` and for `i > b`. They bound the terms themselves, not
  merely the cohomology.
- `IsFiniteFree K : Prop` has the same term bounds and requires every term
  to be `Module.Finite R` and `Module.Free R`.
- For any instance `HasDerivedCategory.{v} (ModuleCat.{u} R)`,
  `IsPerfect E : Prop` for `E : DerivedCategory (ModuleCat.{u} R)` says that
  there is a complex `K` with `IsStrictlyPerfect K` and an isomorphism
  `DerivedCategory.Q.obj K ≅ E` in the derived category, asserted by
  `Nonempty`. Here `DerivedCategory.Q` is Mathlib's localization functor from
  cochain complexes. No substitute category or cohomology data is used. The
  morphism universe `v` of the chosen localization is a universe parameter of
  `IsPerfect`; no small derived category is assumed. Mathlib's
  `HasDerivedCategory.standard` provides such a localization when no other
  choice is available.
- For `S : Type u`, `[CommRing S]` and `φ : R →+* S`, `baseChange φ` is the
  functor
  `(ModuleCat.extendScalars φ).mapHomologicalComplex (ComplexShape.up ℤ)`
  from complexes of `R`-modules to complexes of `S`-modules. Its degree `i`
  term is `(ModuleCat.extendScalars φ).obj (K.X i)`, the tensor product over
  `R` of `S` (an `R`-module through `φ`) with `K.X i`. The same functor is
  applied to differentials and to chain maps. This is ordinary degreewise
  tensoring of a chosen complex, not a derived tensor product.

## Lemmas

- `isStrictlyPerfect_of_isFiniteFree`: a finite free complex is strictly
  perfect, because a free module is projective.
- `isPerfect_Q_obj`: if `K` is strictly perfect, then `DerivedCategory.Q.obj K`
  is perfect, with `K` itself and the identity isomorphism as witness.
- `isPerfect_iff_of_iso`: for an isomorphism `E ≅ F` in the derived category,
  `IsPerfect E ↔ IsPerfect F`, by composing the witness isomorphism with the
  given isomorphism or its inverse.

## Provenance and limits

The registered original is `stacks-perfect-complexes-a04446e5`, folder
SHA-256 `54c831042614714cdb007a024d45dca7f60709efe2c307389ca2ad848b0ccbed`,
retained under `literature/Stacks Project - Perfect complexes and proper
direct images (source at a04446e5)`. It contains the TeX files
`more-algebra.tex` (*More on Algebra*) and `perfect.tex` (*Derived
Categories of Schemes*) at Stacks Project git commit
`a04446e57ec1fbc252a871afcec7752fb2807b14`, and tag pages downloaded on
2026-10-28. The registry citation calls `perfect.tex` More on Flatness; the
title in that file is *Derived Categories of Schemes*.

`IsPerfect` formalizes Stacks Project, More on Algebra, Definition 15.76.1
(tag 0657), `more-algebra.tex`, label `definition-perfect`, lines
18870–18880: an object of `D(R)` is perfect if it is quasi-isomorphic to a
bounded complex of finite projective `R`-modules. The source allows any ring;
this module takes `R` commutative and the term modules in the universe of
`R`. In the ten comments on tag 0657, comment #606 by Johan says that
“quasi-isomorphic” there means isomorphic as objects of `D(R)`. Comments
#609, #617 and #619 add that the relation is symmetric and need not be given
by a single quasi-isomorphism in either direction. The Lean definition
therefore asks for an isomorphism in the derived category and does not ask
for a quasi-isomorphism of complexes in a fixed direction. Part (2) of the
definition, perfect modules, is not formalized here.

`IsStrictlyPerfect` names the representative in Definition 0657. It is the
module version of Cohomology of Sheaves, Definition 20.46.1 (tag 08C4), with
`R` in place of the structure sheaf. That definition asks for a complex
whose terms are zero in all but finitely many degrees, each a direct summand
of a finite free module. For modules over a ring, being a direct summand of
a finite free module is equivalent to being finite projective, and terms
vanishing outside a finite set of degrees is equivalent to the existence of
the bounds `a` and `b`.

`IsFiniteFree` and `baseChange` are internal interfaces with no separate
definition in the source. They describe the representatives in More on
Algebra, `more-algebra.tex`, label `lemma-lift-perfect-from-residue-field`,
statement lines 19593–19610 and proof lines 19612–19625: a bounded
complex of finite free modules over `R_f` representing `K ⊗^L_R R_f`. This module does not prove that lemma and does
not identify `baseChange` with a derived tensor product.

Worker 606 read Definition 0657 and all ten of its comments on 2026-10-28,
and Worker 958 reread them. The tag page of Definition 08C4 lists no
comments. No project errata for this source were found. The Mathlib
functors are used by their Lean names and are not reimplemented.

Neither this module nor its lemmas provide the following: a derived tensor
functor, independence of the chosen representative, K-flatness, local finite
free representatives, perfect proper direct images, cohomology and base
change, Künneth formulas or the local two-axis criterion. In particular,
degreewise tensoring is not claimed to preserve quasi-isomorphisms between
arbitrary complexes. These remain separate proof obligations. A later
geometric application is Derived Categories of Schemes, `perfect.tex`,
label `lemma-flat-proper-perfect-direct-image-general`, lines 7524–7536.
This interface has no field for that conclusion or any other geometric one.
