# Actual absolute and abelianized upper ramification

Worker 68 authored the original construction. Worker 849 generalizes it in
place and names wild inertia. Public declarations remain in
`Langlands.Ramification.Padic`. The module imports `Herbrand.GeneralAbsolute`,
the in-place finite wrappers in `Herbrand.Finite`, and the unchanged
`ClassFieldTheory.Local.Galois` (formerly at `LocalClassField.Galois`).
It uses the actual algebraic closure, finite Galois intermediate fields,
automorphism groups, restriction maps and Krull topologies of Mathlib.

## Sources and scope

Jean-Pierre Serre, *Local Fields*, translated by Marvin Jay Greenberg,
GTM 67, Springer (1979), Chapter IV, §3, supplies the real lower indexing
and inverse Herbrand function on p.73 (PDF p.80), upper numbering and its
endpoint on p.74 (PDF p.81), and the infinite Galois construction in
Remark 1 following Proposition 14 on p.75 (PDF p.82). These pages were
read, including the original page images. The registered source is
`serre-1979-local-fields`, retained at
`/home/taskhub/central-library/Serre--Local Fields--1979.pdf`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
The registered author corrections, `serre-book-corrections-2019`, PDF
pp.2–3, correct phi glyphs on pp.74–75 without changing the cited
infinite-extension construction.

Serre describes the infinite upper group by the inverse limit of the
finite Galois upper groups. Inside the actual absolute Galois group it is
the intersection of all finite restriction preimages. An absolute
automorphism already has compatible restrictions. Arithmetic equality of
its upper-group image with a prescribed finite upper group remains a
later theorem obligation.

Here `p` is any prime and `F : PadicField.{u} p` is any finite extension
of the actual `Padic p`. The real parameter is unrestricted. Lower
numbering uses the ceiling, and upper numbering evaluates at the actual
inverse Herbrand function. This retains the left-continuous convention
at breaks. The full group is retained at every index at most −1; no
claim of absolute eventual triviality is made.

## In-place specialization and characteristic zero

`absoluteFiniteRestriction F L` directly specializes
`Local.absoluteFiniteRestriction F.Carrier (AlgebraicClosure F.Carrier) L`.
Its underlying map is `AlgEquiv.restrictNormalHom`, and continuity is
Mathlib's `InfiniteGalois.restrictNormalHom_continuous`. Its finite target
`Gal(L/F.Carrier)` has the existing discrete Krull topology.

`absoluteUpperRamificationGroup F v` directly specializes
`Local.absoluteUpperRamificationGroup` at `K₀ = Padic p`, `K = F.Carrier`,
and `Ω = AlgebraicClosure F.Carrier`. Norm/valuation compatibility is
`Padic.norm_lt_norm_iff_mulValuation_lt` expressed non-strictly. Every
finite level therefore uses exactly the original spectral integer ring
over `Padic p` and the original finite upper group, by unfolding.

The local instance `Algebra.charZero_of_charZero (Padic p) F.Carrier`
supplies characteristic zero and hence perfectness. Mathlib then supplies
`IsSepClosure.of_isAlgClosure_of_perfectField` for the chosen algebraic
closure. This is the characteristic-zero input at the absolute level;
the general construction replaces it by a specified separable closure.
No characteristic hypothesis is imposed by that general construction.

Every original public declaration retains its name, type and meaning.
The subgroup unfolds to the original intersection; no comparison theorem
between two theories is introduced. `GeneralAbsolute.md` contains the
full table of general declarations and their p-adic specializations.
All published statement files retain their text.

## Concrete finite fields

`finiteGaloisPadicField F L` still packages an actual finite Galois
intermediate field in an ambient `Ω : Type v`, with independent base and
ambient universes. Its carrier is the existing subtype `L`, with its
inherited field and specified algebra structures. Finite dimensionality
follows through `Padic p → F.Carrier → L`. Its algebra structures must
form that scalar tower; this is algebraic packaging, not arithmetic data.

`absoluteFiniteExtension F L` is the specialization to the existing
algebraic closure. Each such field uses its canonical topological data,
which now unfolds to the same general spectral constructor. These two
packaging helpers are otherwise unchanged.

## Elementary lemmas

`mem_absoluteUpperRamificationGroup_iff` specializes the general universal
membership formula, proved there by infimum and comap membership. The
`_iff_lower` variant expands each finite upper group into the integer
lower group at `ceil(herbrandPsi ... v)` by definitional equality.
`absoluteUpperRamificationGroup_le_comap` is the defining infimum bound,
and `absoluteUpperRamificationGroup_map_restriction_le` applies the
map/comap adjunction. Only image containment is asserted.

Normality pulls back the finite normal subgroups and takes their
intersection. Closedness specializes the general closedness lemma,
proved by intersecting continuous preimages of subsets of finite
discrete targets. Antitonicity applies finite antitonicity to every
restriction. The −1 endpoint specializes the general endpoint, proved
by the finite endpoint and lattice simplification; antitonicity yields
the endpoint below −1. These are elementary construction proofs and use
no arithmetic quotient theorem.

## Named wild inertia

`wildInertia F` specializes `Local.wildInertia`. By unfolding, it is
exactly
`(⨆ (w : ℝ) (_ : 0 < w), absoluteUpperRamificationGroup F w).topologicalClosure`,
the left-hand side of the unchanged published proposition definition
`AbsoluteUpperWildInertia F`. The closure uses the original absolute
Krull topology. `wildInertia_normal` uses normality of indexed suprema
and `Subgroup.is_normal_topologicalClosure`.

The named definition follows the registered operator plan,
`operator-external-inputs-plan-2026-11-16`, §4.2, lines 513–570, which
specifies the closure of the union of the positive upper groups. The
finite description by `G_1` is Serre IV §2, Corollaries 1–4 to
Proposition 7, pp.67–68. Its equality with this absolute subgroup is
still a later arithmetic theorem, as in `AbsoluteUpperWildInertia`.

## Abelianized image

`localAbelianUpperRamificationGroup F v` retains its original definition:
the image of the absolute upper group under
`Langlands.LocalClassField.localAbelianGaloisProjection F`. The target
`Field.absoluteGaloisGroupAbelianization F.Carrier` is the actual quotient
by the closed commutator subgroup. This is an internal derived interface
obtained by applying the existing quotient projection to Serre's subgroup.
No reciprocity map or principal-unit subgroup is involved.

`mem_localAbelianUpperRamificationGroup_iff` is subgroup map membership:
one absolute upper-group element has the prescribed image. Its
`_iff_finite` variant expands that same witness's membership into all
finite conditions. `localAbelianUpperRamificationGroup_antitone` follows
by monotonicity of subgroup image. These definitions and proofs are
unchanged apart from the generalized definition they consume.

Finite-image equality, inertia at zero, the finite-lower-group
characterization of wild inertia, right-limit images, left continuity,
and comparison with finite abelian quotients remain separate theorem
obligations.
