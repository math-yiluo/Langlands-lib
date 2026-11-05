# Integral Chevalley data (`ChevalleyData`)

Author: Worker 1398 (interface agreed with Worker 239).

This module fixes the algebraic input of the split existence construction for a root datum
`P : RootDatum J X Y` with base `b`. The group-theoretic and scheme-theoretic modules use these
data. They are obtained from integral Chevalley data with Lie relations (`ChevalleyLieData`,
Worker 239) by `ChevalleyLieData.toChevalleyData` (module `ToChevalleyData`), which derives the
commutator relations.

* `divExp e s = Σ_{k ≤ n} s^k (e k)` is the truncated exponential of a family of integral
  matrices standing for divided powers `e^k / k!`.
* `sl2Upper`, `sl2Lower`, `sl2Diag`, `sl2Weyl` are the standard elements of `SL₂(R)`.
* `ChevalleyData P b` consists of: a functional `ℓ : X →+ ℤ` positive on the simple roots; a
  weight basis `wt : Fin n → X` whose weights generate `X`; divided-power root operators `e j k`
  for every root `j`, moving weight `μ` to `μ + k • root j`, with `e j 1` nonzero modulo every
  prime; for every simple root `i` a homomorphism `φ i R : SL₂(R) →* GL_n(R)` natural in the
  commutative ring `R`, sending the unipotent upper and lower matrices to the exponentials of
  `i` and `-i` and `diag(t, t⁻¹)` to `diag(t ^ ⟨wt c, i^∨⟩)`; the Weyl element `φ i R sl2Weyl`
  moves weight `μ` to `s_i μ` and conjugates the exponential of a root `j` to that of `s_i j`
  up to a sign of the parameter; and the commutator relations (`commutator`): for roots
  `j, j'` and any `h : X →+ ℤ` positive on both, over every commutative ring `R` and for all
  `s, t ∈ R`, the group commutator `x_j(s) x_j'(t) x_j(-s) x_j'(-t)` equals
  `∏_{(θ, f) ∈ L} x_θ(f)` for some list `L` of pairs (root, parameter in `R`), where every root
  `θ` of `L` satisfies `root θ = a • root j + c • root j'` with `a, c ≥ 1`. This weak form records
  only which roots occur, not the parameters; it is all the later modules use.

Provenance: internal packaging of Chevalley's construction (Steinberg, *Lectures on Chevalley
groups*, §§1–3; Milne, *Algebraic Groups* 2017, §23.h, PDF p.525–527, admissible lattices and
the maps (153)). The data are what the later group-theoretic and scheme-theoretic modules use.
