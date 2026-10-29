# Artinian strong indecomposability and the actual socle

Authors: Worker 864 (initial Lean and Markdown draft) and Worker 185.

`Langlands.Classification.StrongIndecomposabilitySocleStatement` is a closed,
Prop-valued definition with independent universes `uK`, `uG`, `uH`, `uV`, in
that order. It states four algebraic clauses. This module contains no proof of
them.

## The four clauses

1. Let `k : Type uK` be a field, `G : Type uG` a group, and `V : Type uV` a
   nontrivial additive commutative group with a `k`-module structure. For any
   `ρ : Representation k G V` with `IsArtinian k[G] ρ.asModule`,
   `IsStronglyIndecomposable ρ` holds if and only if
   `∃! S : Subrepresentation ρ, IsAtom S`.
2. For any group `G : Type uG` and nontrivial complex module `V : Type uV`,
   an Artinian `ρ : Representation ℂ G V` satisfies
   `IsStronglyIndecomposable ρ →
   IsIrreducibleSocle ρ (socleRepresentation ρ)`.
3. For any group `G : Type uG` with a `TopologicalSpace G` and any
   `A : SmoothRep.{0, uG, uV} ℂ G`, the hypotheses `Nontrivial A`,
   `IsArtinian ℂ[G] A.representation.asModule`, and
   `IsStronglyIndecomposable A.representation` imply the existence of an actual
   `π : SmoothRep.{0, uG, uV} ℂ G` with
   `IsIrreducibleSocle A.representation π.representation`. The witness has the
   same carrier universe `uV` as `A`. The statement asks only for the displayed
   topology instance; it adds no continuity instance for the group operations.
4. For any field `k : Type uK`, groups `G : Type uG` and `H : Type uH`,
   `k`-module `V : Type uV`, representation `ρ : Representation k G V`, and
   homomorphism `f : H →* G`,
   `IsStronglyIndecomposable (ρ.comp f) → IsStronglyIndecomposable ρ`.
   This clause has no nontriviality, Artinianity, topology, or surjectivity
   premise.

Here `ρ.asModule` is the actual group-algebra module associated to the
representation. Artinianity is the descending chain condition on its
submodules, rather than a condition on the coefficient vector space alone.
`Subrepresentation ρ` is the lattice of actual invariant `k`-submodules. An
atom is a nonzero subrepresentation with no proper nonzero subrepresentation;
`∃!` requires equality of these subrepresentations.

## Canonical objects and image uniqueness

The predicate `IsStronglyIndecomposable` is imported from
`StrongIndecomposability`. It requires each pair of nonbottom
subrepresentations to have nonbottom intersection. The canonical
`socleRepresentation ρ`, imported from `CanonicalConstituents`, is the
restriction of `ρ` to the sum of the images of all irreducible embeddings
whose source carriers lie in `Type uV`.

The existing relation `IsIrreducibleSocle ρ π` requires that `π` be irreducible,
an actual injective intertwiner `j : π.IntertwiningMap ρ`, and equality
`LinearMap.range j'.toLinearMap = LinearMap.range j.toLinearMap` for every
irreducible embedding `j'` with source carrier in `Type uV`. Thus clauses 2
and 3 retain equality of images as subspaces of the ambient representation.
The published `StrongConstituentExtremaStatement` and its proof
`strongConstituentExtrema` already connect a unique actual atom to this
canonical strong socle. This module reuses their vocabulary and introduces
no replacement constituent relation or canonical construction. For the
smooth clause, `A.socleSubrepresentation` is the existing canonical smooth
object on the socle and has carrier universe `uV`.

## Source and derived content

A. V. Zelevinsky, *Induced representations of reductive p-adic groups II. On
irreducible representations of GL(n)*, Ann. Sci. ENS (4) 13 (1980), 165–210,
§5.4, printed p.188 / PDF p.25. Registered source:
`zelevinsky-1980-induced-ii`, SHA256
`663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`.
The original defines strong indecomposability by nonzero intersections of
nonzero submodules and then gives the finite-length criterion in terms of a
unique nonzero irreducible submodule. Its setting is smooth complex
representations of an l-group. The cited original page was read for this
statement; no source-specific errata note was present in the supplied public
notes.

The general field and group universes, the weakening from finite length to
Artinianity, and the restriction and canonical-socle adapters are internal
derived content, not assertions that Zelevinsky states in this form. The
rationale for the first extension is that Artinianity supplies a minimal
nonzero invariant subspace inside every nonzero invariant subspace. Under the
intersection condition two such minimal subspaces must coincide. Conversely,
a unique atom lies in each nonzero subrepresentation by the same existence
property, so every two nonzero subrepresentations intersect nontrivially.
This explains the intended criterion; it is not a Lean proof in this module.

The complex clause combines that criterion with the existing unique-atom
characterization of the canonical strong socle. The smooth clause uses the
existing smooth socle subrepresentation. The restriction clause is motivated
by the fact that every `G`-invariant subspace is also invariant under `ρ.comp f`,
with the same underlying intersections and zero subspace. None of these
adapters asserts a new classification or analytic theorem.

## Nonzero hypothesis and scope

The zero representation satisfies `IsStronglyIndecomposable` vacuously and is
Artinian, but its lattice has no atom and its socle is not irreducible. This
is why clauses 1–3 retain a separate `Nontrivial` hypothesis. The same
nonzero qualification is needed for the forward direction of the source's
finite-length remark. This is an internal reading observation, not an
author-issued erratum. Clause 4 preserves the vacuous zero case.

No Artinianity or nonzero hypothesis for an induced product is asserted or
proved. The derivative and homogeneity proposition that follows the source's
elementary remark, and its classification applications, are separate
obligations. Existing Library definitions and pairs are preserved.
