# Kirillov-model prerequisites for the JPSS integral theory

Author: Worker 11. This file defines two proposition targets. Neither is a
proof, and neither proposition is assumed anywhere.

Both targets concern a complex representation `ρ` of the actual matrix group
`GL_{n+1}(F)` of a p-adic field `F`. The field carries its canonical
local-field topology `F.canonicalTopologicalData.topology`. The additive
character `ψ : F → ℂ` is continuous, nontrivial and unitary. Both statements
cover every positive rank `n + 1`. The field universe `uF` and the
representation-carrier universe `uV` are independent.

## Common notation

Each statement fixes the following conditions on actual matrices with `let`
bindings. None of them is a parameter or a field of a structure.

- `unipotent g`: `g` is upper unitriangular, that is, `g i j = 0` for `j < i`
  and `g i i = 1`. This is the group `N_{n+1}`.
- `θ g = ∏_{i < n} ψ(g_{i,i+1})`. This is the standard character
  `θ_{ψ,r}` of JPSS (1983), printed page 377, with 0-based indices.
- `mirabolic g`: the last row of `g` is `(0, …, 0, 1)`. This is the group
  `P_r` of JPSS (1983), printed page 376, display (4), and the group `P_n` of
  Bernstein--Zelevinsky (1976), 5.1, printed page 44.
- `equivariant ℓ`: the linear functional `ℓ` satisfies
  `ℓ(ρ(g)v) = θ(g) ℓ(v)` for all upper unitriangular `g` and all `v`.
  This is condition (1) of JPSS (1983), Section 2.1, printed page 385.
- `kirillov φ` describes a function on the mirabolic matrices, read only at
  those matrices:
  1. left covariance `φ(uq) = θ(u)φ(q)` for unitriangular `u` and mirabolic `q`;
  2. smoothness: invariance `φ(qk) = φ(q)` for every mirabolic `k` in some
     open subgroup `K` of `GL_{n+1}(F)`;
  3. compact support modulo `N`: there is a compact set `C` of matrices with
     `q = u c`, for some unitriangular `u` and some `c ∈ C`, whenever
     `q` is mirabolic and `φ(q) ≠ 0`.

  This is the space `K_0(ψ)` of JPSS (1983), Section 2.2, printed page 386. It
  is also the space `S(P, Θ)` of the representation `τ°_P = ind(P, U, Θ)` in
  Bernstein--Zelevinsky (1976), 2.21-2.22 (printed page 21) and 5.7 (printed
  page 45).

The following facts justify these encodings. The open subgroups of the
mirabolic group, with its subspace topology, are cofinal with the
intersections `K ∩ P`. If `q = uc` with `q` mirabolic and `u` unitriangular,
then `c` is mirabolic. Because `P` is closed, `C ∩ P` is a compact subset of
`P`. Hence condition 3 says exactly that the support has compact image in
`N \ P`.

## `WhittakerTypeKirillovStatement`

Hypotheses:

- `ρ` is admissible;
- `ρ` is of finite type, that is, finitely generated over the group algebra
  `MonoidAlgebra ℂ GL_{n+1}(F)`;
- `ℓ` is a nonzero equivariant functional, and every equivariant functional
  is a scalar multiple of `ℓ`.

These are exactly the representations of Whittaker type of JPSS (1983),
Section 2.1, printed page 385: admissible of finite type with
`dim V*_θ = 1`. Nonzeroness of the space follows from `ℓ ≠ 0`.

Conclusion: for every `φ` with `kirillov φ` there is a vector `v` with
`ℓ(ρ(q)v) = φ(q)` at every mirabolic `q`. In JPSS notation this says
`K_0(ψ) ⊆ K(π; ψ)`, where `K(π; ψ)` is the space of restrictions to `P_r` of
the functions `W(g) = λ(π(g)v)` of display (3) on printed page 386.

JPSS state this inclusion in Section 2.2, printed page 386, for the
representations of Section 2.1, and attribute it to Gelfand--Kazhdan [G-K].
The Gelfand--Kazhdan paper is not a registered source here. The target
records the JPSS assertion in the JPSS scope; it does not claim that [G-K]
proves this generality.

## `SupercuspidalKirillovStatement`

Hypotheses: `ρ` is irreducible (Mathlib's `Representation.IsIrreducible`,
which includes nonzeroness) and satisfies the published
`GeneralLinear.IsSupercuspidal`. That predicate is admissibility together with
vanishing of the actual Jacquet coinvariants for every proper block parabolic
and every conjugate of its unipotent radical. It agrees with the cuspidal
representations of Bernstein--Zelevinsky (1976), 3.18, printed page 34:
admissible representations all of whose proper standard Jacquet modules
vanish. The coinvariants for a conjugate radical `gNg⁻¹` are isomorphic, via
`ρ(g)`, to those for `N`, so the conjugate clause adds no condition.

Conclusions:

1. Genericity: there is a nonzero equivariant functional. This is the
   non-degeneracy assertion of Bernstein--Zelevinsky (1976), 5.18, printed
   page 50. By 5.7 and 2.30 (printed pages 45 and 24), non-degeneracy means
   that the twisted coinvariant space `E_{U,Θ}` is nonzero. Its dual consists
   exactly of the functionals in `equivariant`. BZ use the character
   `Θ(u) = ψ₀(∑ u_{i,i+1})` (5.5-5.6, printed page 45), which is `θ` above.
2. Kirillov model: for every nonzero equivariant `ℓ`,
   - the restriction `q ↦ ℓ(ρ(q)v)` of every Whittaker function satisfies
     `kirillov`; and
   - every `φ` with `kirillov φ` is such a restriction for exactly one `v`.

   Together these say that `v ↦ (q ↦ ℓ(ρ(q)v))` is a linear bijection from the
   representation space onto `K_0(ψ)`. This is Bernstein--Zelevinsky (1976),
   5.18 (`π|_P ≅ τ°_P` for irreducible cuspidal `π`) and 5.19 (the unique
   realization in `S(P, Θ)` with `P` acting by right translations), printed
   page 50. Uniqueness of the realization uses 5.15(b) there: every
   `P`-homomorphism `τ°_P → τ_P` is proportional to the standard embedding.
   It is also the last sentence of JPSS (1983), Section 2.2, printed page 386:
   for supercuspidal `π`, `K_0(ψ) = K(π; ψ)`.

The target does not assume that every irreducible representation is generic.
It does not use multiplicity one, which is a separate published target,
`Langlands.WhittakerPrerequisitesStatement`.

## Sources

- H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika, *Rankin--Selberg
  Convolutions*, Amer. J. Math. 105 (1983), 367-464; registered source
  `jpss-1983-rankin-selberg`. Retained file
  `C:/Central-Library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`,
  SHA256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
  Printed pages 376, 377, 385 and 386 (PDF pages 11, 12, 20 and 21) were
  read visually.
- I. N. Bernshtein and A. V. Zelevinskii, *Representations of the group
  GL(n,F) where F is a non-Archimedean local field*, Russian Math. Surveys
  31:3 (1976), 1-68; registered source
  `bernstein-zelevinsky-1976-representations-gln`. Retained file
  `C:/Central-Library/Bernstein-Zelevinsky--Representations of the group GL(n,F) where F is a non-archimedean local field (survey)--1976.pdf`,
  SHA256 `72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`.
  Items 2.21-2.22, 2.30, 3.18 and 5.1-5.19 (printed pages 21, 24, 34 and
  44-50) were read. Page 50 was also checked visually.

## Dependencies

The only project import is the published
`Langlands.Representation.Classification.Supercuspidal`, which supplies
`GeneralLinear.IsSupercuspidal` and, through its imports, `IsAdmissible`,
`GeneralLinear`, `PadicField` and the canonical topological data. Everything
else comes from Mathlib.

## Family declaration

`KirillovPrerequisitesStatement` is the conjunction of the two targets, at
the same universes `uF` and `uV`. It adds no hypothesis or conclusion.
