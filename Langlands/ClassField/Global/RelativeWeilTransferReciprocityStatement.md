# Transfer reciprocity for relative global Weil groups

Worker 35 wrote this statement unit, item 6 of task
fe42e5e4-f578-4b3e-a8b5-efb4ea3a0cc6. On the operator's instruction it is
submitted under task 91266440-3276-48dc-ab77-8d1c1fa386e8. The module
`Langlands.ClassField.Global.RelativeWeilTransferReciprocityStatement` contains
one proposition definition,
`Langlands.ClassField.Global.RelativeWeilGroup.RelativeWeilTransferReciprocityStatement : Prop`.
It is not proved here. It imports the definition unit
`Langlands.ClassField.Global.RelativeWeilTransfer`, which supplies
`transfer c F E : RelativeWeilGroup c F E →* IdeleClassGroup (𝓞 F) F`, and
`Langlands.ClassField.Global.FundamentalClassStatement`, which supplies the
fundamental-class predicates. The proposition lives in universe `u`.

## The statement

The proposition fixes a family `I : ∀ (p : ℕ) [Fact p.Prime], InvariantFamily.{u, u} p`
of local invariant families with

`∀ (p : ℕ) [Fact p.Prime], (I p).RelativeClassFormation ∧ (I p).ArithmeticNormalization`,

and a class family `c : FundamentalClass.ClassFamily.{u}` with

`FundamentalClass.Generates c ∧ FundamentalClass.Restriction c ∧ FundamentalClass.Inflation c ∧ FundamentalClass.LocalCompatibility I c`.

For all number fields `F E : Type u` with `[Algebra F E] [IsGalois F E]`, it
asserts

- `Function.Surjective (transfer c F E)`, and
- `(transfer c F E).ker = commutator (RelativeWeilGroup c F E)`.

Here `commutator` is the algebraic commutator subgroup, as in Artin–Tate. So
`transfer c F E` induces an isomorphism `W_{E/F}^{ab} ≅ C_F` of abstract
groups. This equivalent form is explained here and is not stated in Lean.

## Scope of the hypotheses

`transfer c F E` is defined for every class family. This statement asserts
reciprocity only for the families satisfying its hypotheses. These
hypotheses are sufficient, not necessary. The hypotheses on `I` and `c` are
exactly those of the published `GlobalFundamentalClassStatement` and
`LocalRelativeWeilMapExistenceStatement`. They identify `c` as the arithmetic
fundamental-class family: local invariant families forming class formations
with the arithmetic normalization, and global classes that generate, are
compatible with restriction and inflation, and have the local invariants of
`I`. The statement neither uses `GlobalFundamentalClassStatement` nor chooses
a family from it. That proposition is proved in
[FundamentalClassProof](FundamentalClassProof.md); existence of the global
class family is conditional on a local invariant family satisfying the displayed
hypotheses. This statement does not instantiate that local family. If no `I`
and `c` satisfy the hypotheses, the statement holds vacuously.

Nothing is claimed for other class families, but some of them also give a
transfer isomorphism. The criterion of Artin–Tate XIII §2 used below only
needs cup product with the class to be an isomorphism. This is preserved
when the class is negated. So the negated classes `-u_{E/F}`, which form
Tate's normalization (see below), also give a surjective transfer whose
kernel is the commutator subgroup. For a cyclic cubic extension `E/F` the
class `u_{E/F}` has order three, so `-u_{E/F} ≠ u_{E/F}`.

## Why it is true

Artin–Tate XV §1, proof of Theorem 1 (printed pp.168–169, PDF pp.177–178),
takes a group extension `U` of `G_{K/F}` by `A_K` belonging to the fundamental
class. By Chapter XIII §2 the transfer lands in `A_K^{G_{K/E}} = A_E`, so it is
a homomorphism `V_{K/E} : U_E/U_E^c → A_E`. By the corollary to XIII §2
Theorem 4 (printed p.133, PDF p.142), its kernel and cokernel are controlled
by cup product with the class of the extension in degrees `-3` and `-2`. That
class is the fundamental class of the layer, and these cup products are
isomorphisms by the main theorem of class field theory. Hence the transfer is
an isomorphism, `V_{K/E} : U_E/U_E^c ≈ A_E`. For the idele-class formation,
with Artin–Tate's layer `K/F` our `E/F` and `E = F`, `U` is
`RelativeWeilGroup c F E` and `V_{K/F}` is `transfer c F E`. Tate 1979 §1.2
((1.2.2)–(1.2.4), printed pp.4–5, PDF pp.13–14) explains the same fact from
the Weil-group side: the class `a_{E/F}` of `W_{E/F}` is the fundamental class
in Tate's normalization, and `W_{E/F}^{ab} ≅ C_F`.

Tate's class `a_{E/F}` is the negative of the arithmetic class `u_{E/F}`. The
two extensions differ by pushout along inversion on `C_E`. This changes the
induced isomorphism only by inversion, so it does not affect surjectivity or
the kernel. The Markdown of `RelativeWeilTransfer` explains the comparison.

## Out of scope

The proof needs the Tate–Nakayama and class-formation cohomology of Artin–Tate
XIII §2 for the idele-class formation, which is not in the Library. It also
needs the fundamental-class family to be instantiated (task
fb66219f-83c6-4b76-8bed-63bc57c07205). Compatibility with local reciprocity,
the global Artin map, tower transitions and the absolute Weil group is not
stated.

## Sources

- E. Artin and J. Tate, *Class Field Theory* (2009), source
  `artin-tate-2009-class-field-theory` (PDF page = printed page + 9):
  Chapter XV §1, Theorem 1 and its proof, printed pp.167–169 (PDF
  pp.176–178); Chapter XIII §2, Theorem 4 and its corollary, printed p.133
  (PDF p.142).
- J. Tate, *Number theoretic background*, Proc. Sympos. Pure Math. 33,
  Part II (1979), source `tate-1979-number-theoretic-background`: §1.2,
  (1.2.2)–(1.2.4), printed pp.4–5 (PDF pp.13–14).
