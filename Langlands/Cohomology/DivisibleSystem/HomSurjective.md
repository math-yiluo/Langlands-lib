# Surjectivity of the Hom transitions of ℓ-divisible systems

Author: Worker 61. Built on `Langlands.Cohomology.DivisibleSystem.HomSystem`
(`homTransition`, `homTransition_eq_iff`, `homSystem`, `towerHomEval`,
`homSystemIsLimit`, `cochainTransition`, `cochainTransition_v`,
`homComplexSystem`, `smoothHomComplexSystem`) and on
`Langlands.Cohomology.DivisibleSystem` (`DivisibleSystem`, `powSMul`,
`DivisibleSystem.projection`, `DivisibleSystem.epi_projection`,
`DivisibleSystem.powSMul_eq_zero`, `DivisibleSystem.degree`,
`SmoothRepComplexDivisibleSystem`). From Mathlib it uses
`Functor.IsMittagLeffler` and `Functor.isMittagLeffler_of_surjective`,
`Functor.sections`, `Types.isLimitEquivSections` and
`Types.isLimitEquivSections_symm_apply`, `isLimitOfPreserves` (for the
forgetful functor of a concrete category and for
`HomologicalComplex.eval`), `Projective.factors`, `Cochain.mk` and
`Nat.exists_eq_add_of_le`.

The lemmas on sequential limits are in the namespace `Langlands.Cohomology`;
`PowTorsionProjective` and the lemmas on Hom systems are in
`Langlands.Cohomology.DivisibleSystem`; `isMittagLeffler_smoothHomComplexSystem_eval`
is in `Langlands.Cohomology`.

## Sequential limits of surjections

`F : ℕᵒᵖ ⥤ Type w` is an inverse system of types, and `hF` says that every
map `F (op (k + 1)) ⟶ F (op k)` (the image of `homOfLE (Nat.le_succ k)`) is
surjective.

- `mem_sections_of_map_succ`: a family `s j ∈ F (op j)` with
  `F.map (k + 1 → k) (s (k + 1)) = s k` for all `k` is a section of `F`.
  The proof writes a map `op a ⟶ op b` as the map for `b ≤ b + k`, which is
  the composite of consecutive steps, and inducts on `k`.
- `sequencePreimage hF x k ∈ F (op (n + k))`, for `x ∈ F (op n)`: `x` for
  `k = 0`, and a chosen preimage (`Exists.choose` of `hF (n + k)`) of
  `sequencePreimage hF x k` for `k + 1`.
  `map_sequencePreimage_succ` is the defining property;
  `map_sequencePreimage` says that the map `F (op (n + k)) ⟶ F (op n)` sends
  `sequencePreimage hF x k` to `x` (induction on `k`).
- `sequenceSection hF x j ∈ F (op j)`: the image of
  `sequencePreimage hF x j ∈ F (op (n + j))` under the map for `j ≤ n + j`.
  `map_sequenceSection_succ` says these elements are compatible along
  consecutive steps (both sides are images of
  `sequencePreimage hF x (j + 1)` by functoriality), and
  `sequenceSection_self` says the value at `j = n` is `x`
  (`map_sequencePreimage` with `k = n`).
- `exists_mem_sections_of_surjective_map hF n x`: every `x ∈ F (op n)` is the
  value at `n` of a section of `F`, namely `sequenceSection hF x`.
- `types_surjective_π_app_of_surjective_map hF hc n`: for a limit cone `c`
  of `F`, the projection `c.π.app (op n)` is surjective. The section of the
  previous item gives a point of the limit through
  `Types.isLimitEquivSections`. Mathlib's
  `Types.surjective_π_app_zero_of_surjective_map` is the case `n = 0`.
- `concrete_surjective_π_app_of_surjective_map hc hF n`: the same for an
  inverse system in a concrete category whose forgetful functor preserves
  limits of shape `ℕᵒᵖ`, by applying the previous item to the image of the
  cone under the forgetful functor (Mathlib's
  `Concrete.surjective_π_app_zero_of_surjective_map` is the case `n = 0`).

## Relative projectivity

`C` is a preadditive category and `ℓ m : ℕ`.

- `PowTorsionProjective ℓ m P`: for every epimorphism `p : X ⟶ Y` with
  `powSMul ℓ m X = 0` (multiplication by `ℓ ^ m` on `X` is zero), every
  morphism `P ⟶ Y` factors through `p`. This is projectivity relative to the
  epimorphisms with source killed by `ℓ ^ m`; the target `Y` is then also
  killed by `ℓ ^ m`, but the definition does not use this.
- `powTorsionProjective_of_projective`: a projective object satisfies
  `PowTorsionProjective ℓ m P` for all `ℓ` and `m` (`Projective.factors`).

## Hom systems

`R` is a ring, `C` an `R`-linear abelian category with Hom-universe `v`,
and `T`, `W` are `ℓ`-divisible systems in `C` with levels `T m = T.obj m`.
Recall from HomSystem that for `m' ≤ m`, `homTransition T W h f` is the
morphism `T m' ⟶ W m'` through which `f ≫ W.projection h` factors along the
projection `T.projection h : T m ⟶ T m'`, and that `homSystem R T W` is the
inverse system `m ↦ Hom(T m, W m)` in `ModuleCat.{v} R` with these maps.

- `homTransition_surjective T W h hT`: if `T m` satisfies
  `PowTorsionProjective ℓ m`, then `homTransition T W h` is surjective. For
  `g : T m' ⟶ W m'`, apply `hT` to the projection `W.projection h`, which is
  an epimorphism (`epi_projection`) with source `W m` killed by `ℓ ^ m`
  (`powSMul_eq_zero`), and to `T.projection h ≫ g`. The lift `f` satisfies
  `f ≫ W.projection h = T.projection h ≫ g`, which by
  `homTransition_eq_iff` means `homTransition T W h f = g`. No hypothesis on
  `W` is needed.
- `homSystem_map_surjective R T W hT φ`: if every `T m` satisfies
  `PowTorsionProjective ℓ m`, every map of `homSystem R T W` is surjective.
- `isMittagLeffler_homSystem R T W hT`: under the same hypothesis, the
  inverse system of sets `homSystem R T W ⋙ forget (ModuleCat R)` satisfies
  the Mittag-Leffler condition (`Functor.isMittagLeffler_of_surjective`).
- `towerHomEval_surjective R T W hT n`: under the same hypothesis, every
  morphism `T n ⟶ W n` is the level-`n` component `towerHomEval R T W n` of a
  morphism of inverse systems `T.tower ⟶ W.tower`. HomSystem's
  `homSystemIsLimit` says that the cone with these components is a limit
  cone, so this is `concrete_surjective_π_app_of_surjective_map`.

## Hom complex systems

`T`, `W` are now `ℓ`-divisible systems in `CochainComplex C ℤ`, and
`T.degree p` is the `ℓ`-divisible system of degree-`p` terms. The hypothesis
`hT` is now that every term `(T m).X p` satisfies
`PowTorsionProjective ℓ m`.

- `cochainTransition_surjective T W h hT n`: if every `(T m).X p` satisfies
  `PowTorsionProjective ℓ m`, the transition `cochainTransition T W h` of
  degree-`n` cochains (graded morphisms `T m ⟶ W m` of degree `n`) is
  surjective. A cochain `z'` from `T m'` to `W m'` is reached by the cochain
  whose `(p, q)` component is a chosen preimage of `z'.v p q hpq` under
  `homTransition (T.degree p) (W.degree q) h`, which exists by
  `homTransition_surjective`; `cochainTransition_v` computes the components
  of its image. Here `W.degree q` needs no hypothesis.
- `homComplexSystem_map_f_surjective R T W hT φ n`: if every `(T m).X p`
  satisfies `PowTorsionProjective ℓ m`, the degree-`n` component of every map
  of `homComplexSystem R T W` is surjective.
- `isMittagLeffler_homComplexSystem_eval R T W hT n`: under the same
  hypothesis, for every `n : ℤ` the inverse system of degree-`n` terms
  `homComplexSystem R T W ⋙ HomologicalComplex.eval _ _ n ⋙ forget _`
  satisfies the Mittag-Leffler condition. This is exactly the degreewise
  hypothesis of `DegreewiseInverseLimitCohomologyStatement R` in
  `Langlands.Cohomology.InverseLimit.Statement` for
  `K = homComplexSystem R T W`, with the module universe `v`.
- `homComplexLimit_π_f_surjective R T W hT m n`: under the same hypothesis,
  the degree-`n` component of the limit projection
  `limit.π (homComplexSystem R T W) (op m)` is surjective. Evaluation in
  degree `n` preserves limits, so this is
  `concrete_surjective_π_app_of_surjective_map` applied to the image of
  Mathlib's limit cone.

## Smooth representations

`R : Type u` is a commutative ring, `G : Type v` a topological group, and
`T`, `W` are `ℓ`-divisible systems of `ℤ`-graded cochain complexes of
smooth representations (`SmoothRepComplexDivisibleSystem.{v, u, w} R G ℓ`).

- `isMittagLeffler_smoothHomComplexSystem_eval R G T W hT n`: if every term
  `(T m).X p` satisfies `PowTorsionProjective ℓ m` in the category of smooth
  representations, the degree-`n` terms of `smoothHomComplexSystem R G T W`
  (graded `G`-equivariant `R`-linear maps) satisfy the Mittag-Leffler
  condition. This is `isMittagLeffler_homComplexSystem_eval`, since
  `smoothHomComplexSystem R G T W` is `homComplexSystem R T W` by
  definition.

## Provenance and interpretation

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), proof of Proposition 4.10, printed p.312
(one-based PDF page 14), quoted in full in
`Langlands/Cohomology/DivisibleSystem/HomSystem.md`: "To check the
Mittag-Leffler condition, we first need to study the maps (4.10.3)
T_{m+1}(j, ẽ) → T_m(j, ẽ) as m varies. But we have seen in §2 that the maps
C^j_{m+1}(ẽ)^{H_p} → C^j_m(ẽ)^{H_p} are surjective. Since C^j_m(ẽ)^{H_p} and
Hom(𝒪_m[C_p/H_p]^M, 𝓛_m) are both free 𝒪/ℓ^m𝒪[S(ẽ)/H_p]-modules, it
follows that the maps (4.10.3) are surjective for all m." Here
`T_m(j, ẽ) = Hom_{𝒪/ℓ^m𝒪[S(ẽ)]}(C^j_m(ẽ)^{H_p}, Hom(𝒪_m[C_p/H_p]^M, 𝓛_m))`,
and HomSystem reads the maps (4.10.3) as `homTransition`.

Harris's argument rests on the surjectivity of the projections of the
source and on freeness of source and target. The module isolates the
property of the source that the argument needs, `PowTorsionProjective`, as
an explicit hypothesis on `T`. The projections of `T` and `W` are
epimorphisms for every `ℓ`-divisible system (`epi_projection`, a
consequence of the definition), so no freeness of the target is assumed. The relative
projectivity is weaker than projectivity: in a category of modules over a
group ring `𝒪[Γ]`, a free `𝒪/ℓ^m𝒪[Γ]`-module has it, because a morphism
from it is determined by the images of a basis, which can be lifted along
any surjection from a module killed by `ℓ ^ m`; this remark is not
formalized.

Harris uses the surjectivity of (4.10.3) to check the Mittag-Leffler
condition for the complexes (4.10.2). The module proves the degreewise
Mittag-Leffler condition for `homComplexSystem` in the form required by
`DegreewiseInverseLimitCohomologyStatement`; it does not prove that
statement, which is a separate published statement whose proof is not part
of this module.

The formulation of `PowTorsionProjective`, the sequential-limit lemmas at
arbitrary level `n`, and all the proofs are ours. The cited passage
contains only the surjectivity of (4.10.3) and its justification by
freeness.

## Scope

The module does not identify Harris's modules `T_m(j, ẽ)` or complexes
(4.10.2) with Hom systems of `ℓ`-divisible systems, does not prove that
Harris's modules `C^j_m(ẽ)^{H_p}` are free or satisfy
`PowTorsionProjective`, and does not prove that free modules satisfy it. It
proves nothing about the cohomology of `homComplexLimit` or of the terms of
`homComplexSystem`, the Mittag-Leffler condition for their cohomology
systems, or the comparison with Hom or Ext groups of inverse limits, and it
does not construct the spectral sequences (4.9), (4.10.1) or (4.10.4).

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Dependencies are the modules named above, pinned to Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
