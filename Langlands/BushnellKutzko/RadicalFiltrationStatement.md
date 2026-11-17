# The radical filtration of a hereditary order (Bushnell–Kutzko 1993, §1.1, pp. 21–22)

Source: C. J. Bushnell and P. C. Kutzko, *The admissible dual of GL(N) via compact open
subgroups*, Annals of Math. Studies 129 (1993), `bushnell-kutzko-1993-admissible-dual-gln`,
§1.1, printed pp. 21–22 (PDF pp. 33–34; PDF page = printed page + 12). BK93 recalls these facts
without proof from the structure theory of hereditary orders (Reiner, *Maximal orders*;
Bushnell–Fröhlich 1985 [BF2] §1; Bushnell 1987 [Bu1]).

`RadicalFiltrationStatement : Prop` is an unproved statement. A later `lean.proof@1` task will
prove it. It uses the definitions of `Langlands.BushnellKutzko.LatticeChain`.

## Quantifiers

For every nonarchimedean local field `F : Type u` (`[Field F] [ValuativeRel F]
[TopologicalSpace F] [IsNonarchimedeanLocalField F]`), every `F`-vector space `V : Type v`, and
every `𝔬_F`-lattice chain `𝓛 : LatticeChain 𝒪[F] F V`. The universes of `F` and `V` are
independent.

There is no `FiniteDimensional F V` hypothesis: a space carrying a lattice chain is
finite-dimensional (`LatticeChain.finiteDimensional`). There is no `dim V ≥ 1` hypothesis: for
`V = 0` no lattice chain exists, because the lattices must strictly decrease. So the statement
covers exactly BK93's setting.

Notation: `A = Module.End F V`, `𝔄 = 𝓛.order`, `𝔓^n = 𝓛.endFiltration n` (BK93's
`End^n_{𝔬_F}(𝓛)` of (1.1.2)) and `e(𝓛) = 𝓛.period`.

## Conclusions

The statement is a conjunction of five parts.

1. **`𝔓^m 𝔓^n = 𝔓^{m+n}` for all `m, n ∈ ℤ`.** The left side is the product
   `𝓛.endFiltration m * 𝓛.endFiltration n` of `𝒪[F]`-submodules of the `𝒪[F]`-algebra `A`, the
   `𝒪[F]`-span of all products `xy`. BK93 (p. 21) states that the radical `𝔓 = End^1(𝓛)` is an
   invertible fractional ideal of `𝔄` and that `𝔓^n = End^n(𝓛)` for all `n ∈ ℤ`. This part,
   with `𝔓^0 = 𝔄` (which holds by definition) and part 4, says the same thing: `End^n(𝓛)` is
   the `n`-th power of `End^1(𝓛)` for `n ≥ 1`, and `End^{-n}(𝓛)` is a two-sided inverse of it
   (`End^n End^{-n} = End^{-n} End^n = 𝔄`).
2. **`𝔓^n L_i = L_{i+n}` for all `n, i ∈ ℤ`** (BK93 p. 21). Here `𝔓^n L_i` is the
   `𝒪[F]`-span of the vectors `x v` with `x ∈ 𝔓^n` and `v ∈ L_i` (`Submodule.span` of
   `Set.image2`).
3. **`𝔭_F 𝔄 = 𝔓^{e(𝓛)}`** (BK93 p. 21). The left side is `𝓂[F] • 𝔄`, the product of the
   ideal `𝔭_F = 𝓂[F]` of `𝒪[F]` with the `𝒪[F]`-submodule `𝔄` of `A`.
4. **`𝔓^1` is the Jacobson radical of `𝔄`** (BK93 p. 21, "`End^1_{𝔬_F}(𝓛)` is the Jacobson
   radical of `𝔄`"). For `x ∈ 𝔄`: `x ∈ Ring.jacobson 𝔄` if and only if `x ∈ 𝔓^1`. Here
   `Ring.jacobson 𝔄` is Mathlib's Jacobson radical of the (noncommutative) ring `𝔄`, the
   intersection of its maximal left ideals.
5. **The valuation (1.1.3) is well defined.** For every `x ≠ 0` in `A`, the set
   `{n ∈ ℤ : x ∈ 𝔓^n}` is nonempty and bounded above. BK93 (1.1.3) (p. 22) defines
   `v_𝔄(x) = max {n ∈ ℤ : x ∈ 𝔓^n}` and so uses this fact implicitly. It is included so that
   `LatticeChain.valuation`, which takes the supremum, agrees with BK93's maximum.

## Relation to the task

The task's S1 consists of parts 1–4. Part 5 is the well-definedness of `v_𝔄` from item 5 of
the task's definitions. It is placed here because it is a property of the filtration
`(𝔓^n)` and the definition must not assume it.
