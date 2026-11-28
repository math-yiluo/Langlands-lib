# Coefficientwise moderate growth on actual rational points: proof

`Langlands.Plancherel.rationalCoefficientModerateGrowth` proves exactly the
proposition `Langlands.Plancherel.RationalCoefficientModerateGrowthStatement.{u, uV}`
of the module `Langlands.Representation.Plancherel.RationalModerateGrowthStatement`,
at independent universes `u` (the field) and `uV` (the representation carrier).
[Statement](RationalModerateGrowthStatement.md)

This is the first assertion of J.-L. Waldspurger, *La formule de Plancherel pour
les groupes p-adiques d'après Harish-Chandra* (2003), Corollary I.4.4 (printed
p.245 / PDF p.11), with the matrix norm of I.1 (printed p.242 / PDF p.8).

## Scope

The theorem has no hypotheses. For every nonarchimedean local field
`F : Type u`, of any characteristic, every connected reductive group scheme `G`
over `Spec F`, with its canonical rational-point topology
`rationalPointTopology F G.X`, every nonempty finite index type `n`, every
matrix representation `ρ : MatrixRepresentation G n` that is a closed subgroup
embedding, every admissible smooth complex representation
`π : SmoothRep.{0, u, uV} ℂ (rationalPoints G)`, every vector `v` and every
`φ : SmoothDual π.representation`, it gives `d : ℕ` and `c : ℝ` with `0 < c`
such that for every rational point `g`

`‖φ (π(g) v)‖ ≤ c * rationalMatrixNorm F ρ g ^ d`.

Both `d` and `c` depend on `v` and `φ`. No finite-length, irreducibility,
unitarity or central-character assumption on `π` is made, and no restriction
on characteristic, residue characteristic, splitness or rank of `G` (rank zero
included). The axioms of the theorem are `propext`, `Classical.choice` and
`Quot.sound`.

## Proof

The Lean term is one application:

```
rationalCoefficientModerateGrowthAssembly
  GroupScheme.standardCocharacter
  BruhatTits.SpecialCompact.jointSpecialCompactBasisExistence
```

Its three declaration-level dependencies are:

- `Langlands.Plancherel.rationalCoefficientModerateGrowthAssembly`
  (module `Langlands.Representation.Plancherel.RationalCoefficientModerateGrowthAssemblyProof`)
  proves `RationalCoefficientModerateGrowthAssemblyStatement.{u, uV}`: the
  standard-cocharacter statement and the joint special-compact/basis existence
  statement together imply `RationalCoefficientModerateGrowthStatement.{u, uV}`.
  [Assembly statement](RationalCoefficientModerateGrowthAssemblyStatement.md),
  [assembly proof](RationalCoefficientModerateGrowthAssemblyProof.md)
- `Langlands.GroupScheme.standardCocharacter`
  (module `Langlands.GroupScheme.Rational.StandardCocharacterProof`) proves
  `GroupScheme.StandardCocharacterStatement.{u}`: for a maximal split torus of a
  connected reductive group over any field, a generic cocharacter `ν` and every
  subset `J` of the simple relative roots, a cocharacter vanishing on `J` and
  positive on the other simple roots exists, and the standard parabolic, Levi
  and unipotent subgroup functors of `J` equal the dynamic subgroups of every
  such cocharacter.
  [Proof](../../GroupScheme/Rational/StandardCocharacterProof.md)
- `Langlands.BruhatTits.SpecialCompact.jointSpecialCompactBasisExistence`
  (module `Langlands.BruhatTits.SpecialCompact.JointBasisProof`) proves
  `BruhatTits.SpecialCompact.JointSpecialCompactBasisExistenceStatement.{u}`:
  for every nonarchimedean local field, connected reductive group, maximal split
  torus and generic cocharacter, one apartment datum `D`, one special vertex `x`
  and one represented torus centralizer with its character comparison satisfy,
  at the common compact subgroup `D.specialCompactSubgroup x`, the special
  compact properties, standard-Levi inheritance, the ambient and Levi Iwasawa
  products, the ambient and Levi Cartan comparisons and the simultaneous
  standard basis (Renard, *Représentations des groupes réductifs p-adiques*,
  V.5.1–V.5.2).
  [Proof](../../BruhatTits/SpecialCompact/JointBasisProof.md)

The universe parameters are passed through unchanged: both structural
theorems are used at the field universe `u`, and the assembly keeps the
carrier universe `uV` independent.

## How the assembly uses the two structural theorems

The proof of `rationalCoefficientModerateGrowthAssembly`, which this theorem
applies, runs as follows for a given `F` and `G`.

1. `exists_maximalSplitTorus_genericCocharacter` chooses a maximal split torus
   `i : S.toGrp ⟶ G` and a generic cocharacter `ν`.
2. The joint structural theorem, applied to `i` and `ν`, gives `D`, `x`, the
   centralizer data `Z`, `j`, `s`, `h`, the special compact properties of
   `K0 = D.specialCompactSubgroup x`, the standard-Levi Cartan compatibility and
   the simultaneous standard basis at `K0`.
   `exists_isFiniteLatticeTransversal` extracts a finite lattice transversal
   from that compatibility.
3. `rationalFiniteSignedCartanCover` (module
   `Langlands.Representation.Plancherel.RationalFiniteSignedCartanCoverProof`)
   uses the standard-cocharacter theorem and these witnesses to give finitely
   many families `gen ε` of linearly independent cocharacters with
   nonnegative pairings against the simple roots, and a finite set `T` of
   rational points, such that every rational point is
   `k₁ * uniformizerPowers i (.ofAdd (∑ a, n a • gen ε a)) * t * k₂` with `k₁, k₂ ∈ K0`,
   `t ∈ T` and natural coefficients `n`; this is a form of the Cartan
   decomposition (Waldspurger I.1 (4)).
4. `rationalFiniteChartModerateGrowth` (module
   `Langlands.Representation.Plancherel.RationalFiniteChartModerateGrowthProof`)
   turns this cover, the simultaneous standard basis at `K0` and the
   compactness of `K0` (the compact clause of the special compact properties)
   into the coefficient bound for every closed embedding, admissible
   representation, vector and smooth functional.

The route thus follows the source's use of the Cartan decomposition. The
bound on each chart and its validity for an arbitrary closed embedding are
proved by `rationalFiniteChartModerateGrowth` and the modules it imports.

## Provenance

The statement formalizes the first assertion of Waldspurger's Corollary I.4.4;
its Markdown gives the source locations. This proof is an internal composition
of the three Library theorems named above.
