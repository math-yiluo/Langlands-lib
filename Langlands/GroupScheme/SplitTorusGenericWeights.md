# Generic integral weights of a split torus representation

Helper module for the proof of `Langlands.GroupScheme.ProjectiveTorusFixedPointDimensionStatement`
(Milne, *Algebraic Groups* (2017), Proposition 20.11). That proof chooses coordinates in which
the torus acts diagonally, together with a cocharacter `z ↦ ν(z)` whose weights separate the
weights of the representation (Milne's "suitably chosen cocharacter"). This module supplies
those two choices on rational points, for a split torus over an arbitrary field.

Notation. `pt` is the base test `Over.mk (𝟙 (Spec k))`; a morphism `pt ⟶ T.toGrp.X` is a
rational point of `T`. For a matrix representation `ρ`, `ρ.rationalMatrix` is the
homomorphism from rational points to `GL n k`, from
`Langlands.GroupScheme.MatrixRepresentationRationalPoints`. The character value
`FlagCore.charValue wt s i = ∏ a, s a ^ wt i a` comes from `Langlands.GroupScheme.FlagCoreLinear`.

Both theorems live in the namespace `Langlands.GroupScheme.SplitTorusGenericWeights`. In both,
`k` is a field, `T` is a commutative group scheme over `Spec k` with `IsSplitTorus T.toGrp`,
the index type `n` is finite with decidable equality, and `ρ : MatrixRepresentation T.toGrp n`.
Neither theorem assumes that `k` is algebraically closed.

## Diagonalization of a split torus

- `exists_splitTorusDiagonal hT ρ`: there are:
  - a finite type `I : Type u`;
  - `P : GL n k` and integral weights `wt : n → I → ℤ`;
  - a map `τ : (I → kˣ) → (pt ⟶ T.toGrp.X)`;

  such that `ρ(τ s) = P · diagonal (charValue wt s) · P⁻¹` for every `s`, and `τ` is
  surjective.

  Proof. This adapts the proof of the Library theorem `FlagCore.exists_torusDiagonal`, with
  the identity in place of a maximal torus. Because `T` is split by hypothesis, the Galois
  splitting premise of that theorem is not needed.
  - `IsSplitTorus` gives a finite type `I` and an isomorphism `e : T.toGrp ≅ splitTorus I`.
  - Restrict `ρ` along `e.inv` to a representation `σ` of the split torus. Then apply the
    Library theorem `GeneralLinear.CocharacterDiagonal.exists_diagonalizingMatrix` with
    `A = k`; mapping `P` along `algebraMap k k` does not change it.
  - Define `τ s` as the composite of three maps: `FlagCore.baseAffineTestIso.hom`, the point
    `(splitTorus.algebraPointsEquiv I k).symm s` of the split torus, and `e.inv`. By
    `FlagCore.rationalMatrix_baseAffineTestIso` and `MatrixRepresentation.affineMatrix_restrict`,
    `ρ.rationalMatrix (τ s)` equals `matrixAt I σ s`, which gives the diagonal formula.
  - Surjectivity: a rational point `g` equals `τ s` for
    `s = splitTorus.algebraPointsEquiv I k (baseAffineTestIso.inv ≫ g ≫ e.hom)`. This uses
    `e.hom ≫ e.inv = 𝟙` and the fact that `baseAffineTestIso` is an isomorphism.

## Generic weights

- `exists_genericWeights hT ρ`: there are `P : GL n k` and `m : n → ℤ` with two properties.
  1. For every `z : kˣ` there is a rational point `t` of `T` with
     `ρ(t) = P · diagonal (fun i => z ^ m i) · P⁻¹`.
  2. For every rational point `t` of `T` there is `χ : n → kˣ` with
     `ρ(t) = P · diagonal χ · P⁻¹` and `χ i = χ l` whenever `m i = m l`.

  So in the coordinates given by `P`, the integral weights `m` are those of a cocharacter of
  `T`. Every rational point of `T` acts by a single scalar on each block `{i | m i = c}`.

  Proof.
  - Take `P`, `wt`, `τ` from `exists_splitTorusDiagonal`.
  - The Library theorem `FlagCore.exists_separating wt` gives `ν : I → ℤ` such that
    `∑ a, ν a * wt i a = ∑ a, ν a * wt l a` implies `wt i = wt l`. Set
    `m i = ∑ a, ν a * wt i a`.
  - For (1), take `t = τ (fun a => z ^ ν a)`. By `FlagCore.charValue_cochar`, the character
    values at this point are `z ^ m i`.
  - For (2), write `t = τ s` using surjectivity and take `χ = charValue wt s`. If
    `m i = m l`, then `wt i = wt l` by the choice of `ν`, so `χ i = χ l`.
