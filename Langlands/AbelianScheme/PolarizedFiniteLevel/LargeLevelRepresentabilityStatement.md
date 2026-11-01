# Eventual fine representability of ordinary polarized full-level moduli

`Langlands.AbelianScheme.PolarizedFiniteLevel.LargeLevelRepresentabilityStatement`
is a proposition-valued definition. It states eventual fine representability
of the existing ordinary functor; this module does not prove the proposition
or construct a moduli scheme.

## Quantifiers and geometric conclusion

For every `P : Prerequisites.{0}`, every `g d : ℕ` with `0 < g` and
`hd : 0 < d`, there is an integer `N : ℕ`. For every `n : ℕ` satisfying
`N ≤ n` and `hn : 3 ≤ n`, the conclusion supplies all of the following:

1. An actual object `X : LevelBase n`. Its underlying scheme `X.obj` is
   universe zero and locally noetherian, and `n` is a unit in its ring of
   global sections. These properties are part of the existing full
   subcategory, rather than additional premises.
2. An actual morphism
   `π : X.obj ⟶ Spec (CommRingCat.of (Localization.Away (n : ℤ)))`,
   with `QuasiCompact π`. The ring `Localization.Away (n : ℤ)` is
   `ℤ[1/n]`, the localization at powers of the integer `n`.
3. A natural number `m` and an actual scheme morphism
   `i : X.obj ⟶ Langlands.AlgebraicGeometry.ProjectiveSpace
     (Localization.Away (n : ℤ)) m`,
   with Mathlib's actual `IsImmersion i` and
   `i ≫ projectiveSpaceToSpec (Localization.Away (n : ℤ)) m = π`.
   This projective space is the existing polynomial-Proj scheme.
   `IsImmersion` means a locally closed immersion, including the
   surjectivity condition on stalk maps. The factorization is an equality
   of actual scheme morphisms over the specified affine base.
4. A natural isomorphism
   `CategoryTheory.uliftYoneda.{1}.obj X ≅ moduliFunctor P g d n hd hn`
   in `(LevelBase n)ᵒᵖ ⥤ Type 1`. The assertion is wrapped in
   `Nonempty` to obtain a proposition.

The immersion into finite projective space expresses quasi-projectivity
over `Spec ℤ[1/n]`. Together with `QuasiCompact π`, this has the usual
finite-type geometric content: an immersion is locally of finite type,
finite projective space is of finite type over the affine base, and a
quasi-compact locally finite type morphism is of finite type. The integer
localization is noetherian. These sentences explain the chosen condition;
this module adds no proof or typeclass instance of finite type.

The bound may depend on `P`, `g`, and `d`. It is chosen before `n`, `hn`,
the representing object, and the geometric and representing witnesses.
There is no condition that `d` and `n` be coprime or that `d` be
invertible, and no extra hypothesis on test schemes or their morphisms.

## The exact functor being represented

The statement imports `PolarizedFiniteLevel.Functor` unchanged and uses
its exact `moduliFunctor P g d n hd hn`. A value at `S : LevelBase n`
is the existing quotient of actual dimension-`g` abelian schemes with
an actual polarization of constant degree `d²` and an ordered full
level-`n` tuple. The same global `2g` torsion sections restrict to a
`ZMod n` basis at every geometric fibre. Equivalence is actual
polarized isomorphism preserving the ordered tuple, and restriction is
the functor's constructed pullback.

At `S`, `uliftYoneda.{1}.obj X` has value `ULift (S ⟶ X)`.
The existing `LevelBase.homEquiv S X` identifies these Hom types with
all actual scheme morphisms `S.obj ⟶ X.obj`. Its restriction maps are
precomposition. Thus the isomorphism asserts classification compatible
with every actual base change in the full category, including nonreduced
locally noetherian tests where `n` is invertible. It asserts naturality,
beyond separate bijections on points or fibres. The universe lift
matches the existing quotient's `Type 1` values and assumes no
shrinking or choice of a smaller test category.

`P` is precisely the existing named tensor, Picard, dual base-change,
and polarization base-change prerequisites. Each datum retains its
existing `DualWitness`; the statement adds no universal dual-existence
premise, supplied universal family, representation/comparison premise,
or PEL representability premise. All moduli and geometric witnesses
above occur in the conclusion.

## Original source and conventions

The source is Mumford, Fogarty and Kirwan, *Geometric Invariant Theory*,
third edition (1994), Chapter 7, Definitions 7.1–7.3 (printed p.129 /
one-based PDF p.142), Definitions 7.5–7.6 (printed p.130 / PDF p.143),
and Corollary 7.8 and Theorem 7.9 (printed p.139 / PDF p.152).
The registered source is
`provided-ec58cb66687d0d54d9e39b6ec21281b651fe3a6d039f9b5d099c79791671233f`,
SHA256 `3eed7c31fd64936e20a41d85c85ebaeebc3f2631b01f561417b85bdf33b1af16`.
The supplied file is
`literature/Mumford, Fogarty, Kirwan - Geometric Invariant Theory, 3rd edition (1994), Chapter 6.pdf`;
despite its filename it contains the complete book scan.

Definition 7.1 uses ordered full torsion sections, with no symplectic
restriction. Definition 7.2 forms their ordinary polarized
isomorphism-class functor on locally noetherian bases; Definition 7.3
calls a representing scheme its fine moduli scheme. These are the
ordinary objects and notion of fine representability targeted here,
expressed using the published functor and its explicit prerequisites.
The characteristic restriction for level structure is expressed by
invertibility of `n` on the base. Such schemes have their canonical
map to `Spec ℤ[1/n]`; the statement includes this structure map for
the representing scheme. The source's quasi-projectivity over
`Spec ℤ` specializes to this open affine base.

Theorem 7.9 gives the strict sufficient bound
`n > 6^g * d * sqrt(g!)`. Choosing a natural number strictly larger
than this real bound gives the eventual quantifier pattern used here.
The proposition retains only existence of such an `N` and the existing
functor's range `3 ≤ n`; it does not formalize or canonize that
numerical bound. The following Serre-lemma sentence mentions the
stronger range `n ≥ 3` and omits its proof; that stronger assertion
is not this proposition.

The theorem's prose says polarization degree `d`, whereas
Definitions 7.2, 7.3, 7.5 and 7.6 use degree `d²`. This statement
follows the indexed ordinary functor of those definitions and
preserves the published functor's degree-`d²` convention. It neither
silently changes that degree nor reads the theorem's isolated
degree-`d` wording as a new definition.

A proof of geometric existence, an actual universal-family construction,
rigidity, PEL loci, rational-isogeny comparison, smoothness, projectivity,
and representability of the parent CM presheaf remain separate
obligations. Ordinary isomorphism classes here are not identified with
the parent's rational-isogeny quotient. No suspended Picard/fppf,
duality, torsion-rank, relative-End, or other geometric infrastructure
is resumed by publication of this statement.
