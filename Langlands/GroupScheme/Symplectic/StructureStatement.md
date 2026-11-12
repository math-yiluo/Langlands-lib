# Simple connectedness and absolute almost-simplicity of standard symplectic groups

Author: Worker 118.

`Langlands.GroupScheme.Symplectic.StructureStatement.{u}` is a proposition
definition. For every field `K : Type u` and every natural number `n ≥ 2`, it
asserts

`IsSimplyConnected (Symplectic.groupScheme K n) ∧
 IsAbsolutelyAlmostSimple (Symplectic.groupScheme K n)`.

There is no restriction on the characteristic or on the field. This file states
the proposition and proves none of it. It supplies a general classical-group
prerequisite for the quaternionic rank-one proof.

The group is the actual isometry group of the standard alternating Gram matrix
`Matrix.J (Fin n) K`, as defined and compared with symplectic matrix points on all
test schemes in `Symplectic.Basic`. That module uses row vectors and
`J = [[0,-I],[I,0]]`. Milne uses column vectors and the matrix `-J`.
Changing the sign of the Gram matrix preserves its isometry equation, and
Mathlib's `SymplecticGroup.mem_iff'` identifies the two matrix-equation
orientations. The group in the statement is therefore the standard `Sp_{2n}`.

`IsSimplyConnected` is the Library's semisimple, central-isogeny definition.
`IsAbsolutelyAlmostSimple` requires almost simplicity both over `K` and after
base change to its algebraic closure; the Library's almost-simple predicate
uses Milne's corrected Definition 19.7 (semisimple, noncommutative, and with
no proper nontrivial smooth connected closed normal subgroup). Thus the
conclusion includes semisimplicity and connected reductivity.

## Source

J. S. Milne, *Algebraic Groups* (2017), registered as
`milne-2017-algebraic-groups`:

- Example 2.10(c), printed p.42 / PDF p.58, defines the standard symplectic
  group by its alternating-form equation.
- The type `C_n` example and Summary 21.98, printed pp.459–460 /
  PDF pp.475–476, compute the roots `±2e_i` and `±e_i±e_j`, the full
  character lattice `ℤ^n`, and identify the split symplectic group as
  geometrically almost-simple and simply connected.
- Section 24.g, opening paragraph, printed p.526 / PDF p.542, identifies
  `Sp_{2n}` as the split simply connected almost-simple group of type `C_n`.
  The low-rank coincidence `C_2 = B_2` does not change the symplectic-group
  assertion; the `n ≥ 3` label in the example separates nonisomorphic
  Dynkin types. The present statement includes `n = 2`.

The complete official errata snapshot of 2 November 2026 was read. It corrects
Definition 19.7 and the stray `SO_{2n+1}` in the type `C_n` example. The
typographical `Sp_n` in Summary 21.98 refers to the `Sp_{2n}` defined in the
preceding paragraph. The statement follows the alternating-form group,
including characteristic two.
