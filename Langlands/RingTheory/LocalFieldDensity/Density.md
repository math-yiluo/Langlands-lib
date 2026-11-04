# Density of rational points of smooth domains over complete normed fields

Author: Worker 712.

This internal helper module proves the following. Let `K` be a complete
nontrivially normed field and let `A` be a smooth `K`-algebra which is a
domain and has at least one `K`-point. Then the `K`-points of `A` separate
the elements of `A`: every nonzero `a : A` has `y a ≠ 0` for some
`y : A →ₐ[K] K`. In geometric terms, which are not formalized here, the
`K`-points are Zariski dense in `Spec A`.

This is a derived result and cites no literature for its proof. The
Markdown of `Langlands.GroupScheme.RationalCenterComparisonStatement` names
a different literature route to rational-point density: unirationality of
reductive groups (Milne, *Algebraic Groups*, Theorem 17.93(b)). This module
does not formalize that argument. It uses the completeness and the
nontrivial norm of `K` instead, through the implicit function theorem of
`Langlands.RingTheory.LocalFieldDensity.ImplicitPoints`. It makes no
assumption on characteristic or perfectness, and it applies to every smooth
domain with a `K`-point, not only to groups. All declarations are in the
namespace `Langlands.RingTheory.LocalFieldDensity`.

## Algebraicity over the free coordinates

For a field `K` and a pre-submersive presentation `P` of a `K`-algebra `S`,
`freeCoordinates P : MvPolynomial (FreeVar P) K →ₐ[K] S` is `aeval` of the
free generators `P.val i`. `freeCoordinates_X` records its value on
variables.

`exists_ne_zero_freeCoordinates_eq_mul`: let `P` be a submersive
presentation with finitely many variables and relations, let `S` be a domain,
and let `freeCoordinates P` be injective. Then for every nonzero `h : S` there
are a nonzero polynomial `c` and some `b : S` with
`freeCoordinates P c = h * b`.

Proof. Write `A₀ = MvPolynomial (FreeVar P) K` and make `S` an
`A₀`-algebra through `φ = freeCoordinates P`.

1. `Ω[S/A₀] = 0`. The module `Ω[S/K]` has the basis `P.basisKaehler`,
   whose elements are the differentials `D (P.val k)` of the free generators.
   The map `KaehlerDifferential.map K A₀ S S : Ω[S/K] → Ω[S/A₀]` sends each of
   them to `D (φ (X k)) = 0`, so this map is zero. It is surjective
   (`KaehlerDifferential.map_surjective`), so `Ω[S/A₀]` is trivial and `S` is
   formally unramified over `A₀`. `S` is of finite type over `A₀` because it
   is of finite type over `K`.
2. Let `L = FractionRing S` and `K₀ = FractionRing A₀`. Since `φ` is
   injective, `A₀ → L` is injective, so `L` is a `K₀`-algebra
   (`FractionRing.liftAlgebra`) compatible with `A₀`. Formal unramifiedness
   passes from `S` to the localization `L` and to the composite `A₀ → L`, and
   then to `K₀ → L` (`FormallyUnramified.of_restrictScalars`). `L` is
   essentially of finite type over `K₀` (`EssFiniteType.of_comp`). Mathlib's
   `Algebra.FormallyUnramified.isSeparable` then shows that `L` is separable,
   in particular algebraic, over `K₀`.
3. By `IsFractionRing.isAlgebraic_iff`, the image of `h` in `L` is algebraic
   over `A₀`. Since `S → L` is injective, `h` itself is algebraic over `A₀`.
   Since `h ≠ 0` lies in the ideal `(h)` of the domain `S`,
   `Ideal.under_ne_bot_of_algebraic_mem` shows that `(h)` has nonzero
   contraction to `A₀`. A nonzero `c` in that contraction satisfies
   `φ c = h * b` for some `b`.

## Density

`exists_algHom_apply_ne_zero`: let `K` be a complete nontrivially normed
field and `A` a smooth `K`-algebra that is a domain. Then for every
`x : A →ₐ[K] K` and every `a ≠ 0` there is `y : A →ₐ[K] K` with `y a ≠ 0`.

Proof. Suppose instead that every `K`-point kills `a`. The kernel of `x` is a
prime ideal. Smoothness gives `f ∉ ker x` such that `S = A_f` is standard
smooth (`Algebra.IsSmoothAt.exists_notMem_isStandardSmooth`). So `S` has a
submersive presentation `P` with finitely many variables and relations.
Since `x f ≠ 0` we have `f ≠ 0`, so `S` is a domain, `A → S` is injective,
and `x` extends to a point `x' : S →ₐ[K] K`. For every point `y` of `S`,
`y (φ c)` is the evaluation of `c` at the free coordinates of `y`, where
`φ = freeCoordinates P`. By `eventually_exists_algHom`, every `t` in some
neighbourhood of the free coordinates of `x'` is the vector of free
coordinates of some point of `S`.

- `φ` is injective: if `φ c = 0`, then `c` vanishes on that neighbourhood,
  so `c = 0` by `eq_zero_of_eventually_eval_eq_zero`.
- The image of `a` in `S` is nonzero, so
  `exists_ne_zero_freeCoordinates_eq_mul` gives `c ≠ 0` and `b` with
  `φ c = a * b` in `S`. Let `t` lie in the neighbourhood and let `y` be a
  point of `S` with free coordinates `t`. Its restriction to `A` is a
  `K`-point of `A`, so `y a = 0`, and therefore `eval t c = y (a * b) = 0`.
  Thus `c` vanishes on a neighbourhood and is zero, a contradiction.
