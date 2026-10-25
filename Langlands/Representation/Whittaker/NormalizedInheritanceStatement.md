# Nonzero Whittaker inheritance for normalized block induction

Authors: Worker 357; Worker 90 supplied the checked consumer interface and
its equality-transport design.

`Langlands.Whittaker.NormalizedInheritanceStatement.{uF,uV} F T` is a
proposition definition, not a proof or an assumption. It states the nonzero
functional consequence of Rodier heredity for the Library's actual normalized
upper block induction.

## Exact scope

The outer parameters are an arbitrary prime `p`, `F : PadicField.{uF} p`,
and arbitrary compatible `T : F.TopologicalData`. After installing
`T.topology`, the proposition quantifies over `n : ℕ`, an ordered positive
block shape `B` of `n + 1`, smooth complex block representations
`σ i : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier)`,
and a continuous nontrivial unitary additive character `ψ` of `F.Carrier`.
Continuity, nontriviality and unitarity are encoded by the existing bundled
character; they are not omitted hypotheses. The field and representation
universes are independent.

For each block the hypothesis supplies witnesses `m` and
`h : B.size i = m + 1`, then asserts
`IsGeneric ψ m (h ▸ σ i).representation`. This is actual equality elimination
on the smooth representation before projecting its action. It does not
replace a block representation by a new arbitrary representation. Every block
size is positive by `B.positive`; this interface includes size one by taking
`m = 0`. `IsGeneric` supplies irreducibility, admissibility and a nonzero
standard Whittaker functional, but does not include multiplicity one or an
explicit finite-type assumption.

The conclusion is exactly `HasFunctional` for the representation of
`(T.normalizedProductInductionFunctor B).obj σ`, subgroup
`upperUnipotent (n + 1) F.Carrier`, and `standardCharacter ψ n`.
Thus it asks for a linear functional `ℓ` that is nonzero and satisfies
`ℓ(π(u)v) = ψ(∑ a, u[a,a+1]) ℓ(v)` on the actual upper-unitriangular
subgroup. The existing `HasFunctional` packages this as a nonzero member of
the functional submodule. Rank one is retained: its unipotent character is
trivial and the superdiagonal sum is empty.

There is no conclusion that the induced representation is irreducible or
generic in the Library's stronger `IsGeneric` sense. Arbitrary generic factors
can have reducible induction. There is no square-integrability,
unitarizability, ordering of exponents, nonlinkage or induced-functional
hypothesis.

## Induction and source conventions

`normalizedProductInductionFunctor_obj` identifies the action with
`T.normalizedProductInduced B (fun i => (σ i).representation)`. Its vectors
are the existing smooth induced functions on `GL_(n+1)(F)`, covariant on the
left under `B.parabolic F.Carrier`, the standard upper block parabolic.
The diagonal-block projection acts through the external tensor product, and
`normalizedProductInduced_covariant` gives the positive half-modulus factor.
The group acts by right translation: `(π(g)f)(x) = f(xg)`.

Kudla, §1.1, printed pp.367–368, defines the standard upper parabolic and,
in (1.1.3)–(1.1.4), exactly this positive-half covariance and right action.
Jacquet–Shalika §1.2, printed pp.108–109, uses the upper parabolic and the
same upper-unipotent character for induced Whittaker models. Its particular
Langlands-type hypotheses are not used to restrict the present target, and
its square-integrable irreducibility discussion is not a claim about arbitrary
generic factors.

The general inheritance source is JPSS §2.3, printed pp.386–387: for admissible
finite-type factors, the induced representation has a one-dimensional
Whittaker-functional space if and only if each factor does. The proposition
is attributed there to Rodier. JPSS §2.1, printed p.385, defines this functional
condition and recalls multiplicity at most one for irreducible representations.
JPSS uses normalized induction from a lower parabolic in §2.3; its p.377,
(9)–(11), specifies half-modulus covariance, right translation and tensor
inducing data. Its character on p.377 is the product of additive-character
values on first-superdiagonal entries.

The existing `Langlands.InducedWhittakerTypeStatement`, imported here without
assuming its truth, is the reusable upper, unnormalized formulation of that
Rodier equivalence. Its source comparison accounts for lower-to-upper passage
by the long Weyl element, reversed block order and inner equivalence of each
block action. This statement is not restated as a new iff. The present target
is a derived consequence, and it is not definitionally equal to that existing
target.

## Derivation and remaining proof obligations

A future proof must establish the following composition; none of these steps
is silently a premise of this proposition.

1. Eliminate each rank equality and extract admissibility, irreducibility and
   functional existence from block genericity. Derive finite generation over
   the block group algebra from irreducibility: the associated module is simple
   and hence finitely generated. This is finite type, not finite dimension
   over the complex numbers. Multiplicity one then upgrades nonzero existence
   to the one-dimensional functional condition required by Rodier. The separate
   `Whittaker.MultiplicityOneStatement` is a target, not a theorem supplied here.
2. Absorb the upper half modulus into the factors. If `r_i = B.size i`, the
   block character is `χ_i(g) = |det g|^c_i`, with
   `c_i = (∑_{j>i} r_j - ∑_{j<i} r_j)/2`, for the normalized local absolute
   value. Intrinsically this is `T.blockHalfModulus B i`, the restriction of
   `T.leviHalfModulus B` to coordinate `i`. The published
   `Induction.BlockCharacterAbsorption` supplies the actual equivalence
   `T.normalizedProductHalfAbsorptionEquiv B` from normalized induction of
   `σ_i` to unnormalized induction of `χ_i ⊗ σ_i`. Its underlying maps preserve
   every function value. It also supplies open kernels, factorization,
   triviality on each block's upper unipotents and admissibility transport.
   Thus the required twist is the positive half character.
3. Apply the existing twist invariance to those concrete characters.
   `Langlands.finite_asModule_twist_iff` in
   `RankinSelberg.WhittakerTypeTwist` preserves group-algebra finite type;
   `Whittaker.twistFunctionalEquiv` in `Whittaker.AlgebraicTwist` identifies
   functional spaces when the twisting character is trivial on the unipotents.
   Consequently the factor hypotheses needed by the unnormalized Rodier
   statement follow from the original genericity data and multiplicity one.
   These component constructions are available; assembling them at the
   transported ranks remains part of the future proof.
4. Reconcile the canonical topology in `InducedWhittakerTypeStatement` with
   the arbitrary compatible `T` here. The published
   `topology_eq_canonicalModule` and `canonicalTopologicalData_topology`
   identify the field topologies, and `leviHalfModulus_eq` compares compatible
   half moduli. The proof must actually transport smooth objects, character
   continuity, admissibility and induction across these equalities. Merely
   citing topology uniqueness does not perform that transport.
5. Use a proof of the existing unnormalized Rodier statement on the twisted
   factors. Translate its double product of character values to the character
   of the superdiagonal sum. The published
   `Whittaker.entrywiseCharacter_eq_standardCharacter` and
   `mem_functionals_entrywiseCharacter_iff` in `Whittaker.EntrywiseCharacter`
   provide the character and matrix-equivariance comparisons. Retain the
   nonzero part of its induced conclusion and transport the functional along
   the actual absorption equivalence, using `Whittaker.Transport`.

The full unnormalized heredity proof remains a separate obligation owned by
Worker 174. The Library's `inducedWhittakerTypeReduction` proves a conditional
reduction from `InducedLocalizationStatement`; it does not eliminate that
geometric heredity premise. The published `Whittaker.LocalizationDual` and
`Tensor.CharacterLocalization` supply quotient-dual and finite-tensor
comparisons, not an unconditional induction theorem. This module does not
change `TemperedBlockStatement` or any imported pair and does not duplicate
those bridge constructions.

## Original sources and reading

The registered originals below were read directly. JPSS printed pp.377 and
385–387 were read visually; Jacquet–Shalika pp.107–109 and Kudla pp.367–368
were read from their PDF text, with Kudla's normalization formula checked
visually. No source-specific erratum was found in the supplied project and
Library notes or in the retained source index. The source statements support
the mathematical derivation above, not a claim that its Lean proof exists.

- `jpss-1983-rankin-selberg`: H. Jacquet, I. I. Piatetski-Shapiro and
  J. A. Shalika, *Rankin–Selberg Convolutions*, Amer. J. Math. 105 (1983),
  367–464, §0.3 p.377 and §§2.1–2.3 pp.385–387 (PDF pp.12,20–22).
  SHA256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
- `jacquet-shalika-1983-whittaker`: H. Jacquet and J. A. Shalika,
  *The Whittaker models of induced representations*, Pacific J. Math. 109
  (1983), 107–120, §§1.1–1.2 pp.107–109 (PDF pp.2–4).
  SHA256 `e171831da6c064fdcb55efe79381ba1f85daa4efd7f3a79071589ffee9527f98`.
- `kudla-1994-local-langlands-nonarchimedean`: S. S. Kudla,
  *The local Langlands correspondence: the non-archimedean case*, in
  *Motives*, Part 2, Proc. Sympos. Pure Math. 55 (1994), 365–391,
  §1.1 pp.367–368 (whole-volume PDF pp.377–378).
  SHA256 `0e1f9bc9986fc136081f0eed1aaafb50302acacb5a23e9538581f2f5b533198b`.
