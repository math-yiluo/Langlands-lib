# Vanishing of a natural map on the steps of a functor filtration

This module is an internal helper. It is not a result of the literature. It supports the Lean
proof `inducedProgeneratorCenterInclusion` of the centre inclusion for the induced progenerator
(Renard 2026, VI.10.4, second Lemma), whose route differs from Renard's. In that proof the
geometric-lemma filtration of the Jacquet module of an induced representation is used to show
that a map commuting with all endomorphisms vanishes on all steps below the top one
(`CuspidalSupport/InducedKernelVanishing`).

## Setting

`F D : C ⥤ Rep R G` are functors to representations of a monoid `G` over a commutative ring `R`.
`s : RepFunctorFiltration F n` is a finite increasing filtration of `F` by subfunctors, with
steps `s.step k` for `k : Fin (n + 1)` and graded pieces `s.graded i` for `i : Fin n`. The
graded piece `i` is the quotient of step `i.succ` by step `i.castSucc`. We fix an object `X` and
a morphism `h : F X ⟶ D X` with `F.map a ≫ h = h ≫ D.map a` for every `a : X ⟶ X`.

## Declarations

- `stepDescent s X h i hi`: if `h` vanishes on step `i.castSucc` at `X` (hypothesis `hi`), the
  restriction of `h` to step `i.succ` descends to a morphism `(s.graded i).obj X ⟶ D.obj X`. It
  is the linear map `Submodule.liftQ` of `h` composed with the inclusion of the step. The
  descent is again `G`-equivariant.
- `stepDescent_projection`: the descent of `h` sends the class of `v` to `h v`. This holds by
  definition.
- `stepDescent_natural`: if `h` commutes with every endomorphism `a` of `X`, so does its
  descent, that is `(s.graded i).map a ≫ stepDescent = stepDescent ≫ D.map a`. The proof checks
  this on classes of vectors `v`. There it is the given identity `h (F.map a v) = D.map a (h v)`.
- `hom_apply_eq_zero_of_mem_step`: suppose that for every `i`, every morphism
  `(s.graded i).obj X ⟶ D.obj X` commuting with all endomorphisms of `X` is zero. Then `h`
  vanishes on every step `s.step k`.
- `hom_apply_eq_zero_of_mem_step_of_lt`: the same conclusion for one fixed step `k`, assuming
  the hypothesis only for graded pieces `i` with `i < k`.

## Proofs

Both vanishing theorems use induction from the bottom of the filtration. Step `0` is zero at
every object (`s.zero`), so `h` vanishes there. Suppose `h` vanishes on step `i.castSucc`.
Then `stepDescent` is defined. By `stepDescent_natural` it commutes with all endomorphisms of
`X`, so by hypothesis it is zero. For `v` in step `i.succ`, `stepDescent_projection` gives
`h v = stepDescent (class of v) = 0`. The first theorem uses `Fin.induction`. The second uses
induction on the natural number `j`, with the statement "for `j ≤ k`, `h` vanishes on step
`j`". The bound `j ≤ k` guarantees that only graded pieces below `k` are used.

`stepDescent` reuses `gradedDescent` from `HomVanishingFiltration` with target `D.obj X`; its projection formula remains definitional.
