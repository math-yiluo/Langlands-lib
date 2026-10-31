# Reduction of Mumford alternation to a trivialization with equal point restrictions

This module reduces the published target
`Langlands.AbelianScheme.MumfordFiniteWeilAlternationStatement` to a geometric
input about the Mumford family. The input is the proposition
`MumfordKernelPointTrivialization`. The reduction is conditional and is not
itself a proof of the target. Its provenance is internal: it is derived from
the Library's definitions of the finite pairing (`finiteWeilAlongHomPairing`,
`finiteWeilValue`, `dualTorsionCharacter`, `dualKernelCharacter`,
`intrinsicKernelCharacter`, `kernelTranslationUnit`) and of the Mumford map
(`mumfordSchemeMapOfLineBundle`). It is not a step of the source argument
(EGM, Chapter XI, (11.19)-(11.22), theta groups). It replaces the theta-group
commutator by a direct computation of the kernel character.

## Setting and notation

The variables are exactly the inputs of the target statement: the eight
constructor propositions, a quasi-separated base `S`, an abelian scheme `A`
with dual data `hA`, `geometryA`, `MA`, `evaluationA`, and an actual line
bundle `L` with normalization data `B`, `evaluationB`, `M`, `evaluation`.
Write `[n]` for `multiplication A (n : ℤ)` and `Λ` for the published rigidified
Mumford family `mumfordFamilyOfLineBundle preservation A L B evaluationB M evaluation`
on `A ×_S A`. The parameter is the first factor.

- `mumfordKernelPointModule ... n x`: for a test scheme `T` and a point
  `x : T ⟶ A[n]` (a point of `GroupScheme.kernel (groupHom [n])`), this is the
  module on `T ×_S A` obtained by pulling back the carrier of `Λ` along
  `(relativeSpace A.X.hom).map (x ≫ ι)`, i.e. the family `Λ` restricted to the
  parameter `ι ∘ x`. It is definitionally the carrier of
  `(RigidifiedLineBundle.relativePullback ... (x ≫ ι)).obj Λ`.
- `MumfordKernelPointTrivialization ... n x` (a `Prop`): there exists a
  trivialization `α : [n]_T^* (mumfordKernelPointModule ... n x) ≅ O_{T ×_S A}`
  such that `equalCompositeUnitAut p e (e ≫ kernelShear [n] (𝟙 T) x) _ α` is
  the identity. Here `p = (homFamilySpaceMap [n]).app T` and `e` is the unit
  section of `T ×_S A`. The equality proof argument is
  `kernelShear_homFamilySpaceMap`. In words: the restrictions of `α` along the
  sections `t ↦ (t, 0)` and `t ↦ (t, x t)` agree under the canonical identification. This
  identification exists because both sections map under `[n]` to `t ↦ (t, 0)`.

## Main results

- `finiteWeilAlongHomValue_self_eq_one_of_trivialization`: let `lam : A ⟶ DA`
  be a homomorphism whose underlying scheme morphism is the Mumford map
  (`hlam`). For every `n`, every `T` and every `x : T ⟶ A[n]` satisfying
  `MumfordKernelPointTrivialization ... n x`, the value
  `finiteWeilAlongHomValue ... lam n x x` is `1`.
- `mumfordFiniteWeil_diagonal_of_trivialization`: if the input holds for the
  universal point `𝟙 : A[n] ⟶ A[n]`, then
  `prod.lift (𝟙 _) (𝟙 _) ≫ finiteWeilAlongHomPairing ... lam n = 1`. This is
  exactly the target's conclusion; the target's hypothesis `0 < n` is not
  used.

## Proof

Let `y = x ≫ finiteWeilAlongHomTorsionMap lam n`. By the published
`finiteWeilValue_unique` it suffices to show that the evaluation
`Cartier.characterEvaluation (dualTorsionCharacter ... n y) x` is `1`, since
`1 ≫ incl = 1`.

1. `dualTorsionCharacter_eq_dualKernelCharacter` (from
   `FiniteWeilBaseChange`, with `torsion_dualSchemeMap_eq_origin`) rewrites the
   character as `dualKernelCharacter` of the dual point `y ≫ torsionι`.
2. That dual point equals `(x ≫ ι) ≫ mumfordSchemeMapOfLineBundle ...`. This uses
   `finiteWeilAlongHom_torsion_inclusion` and `hlam`.
3. Let `F` be the relative pullback of `Λ` along `x ≫ ι`. Its rigidified class
   equals the class of the dual point family. This holds because
   `dualPointFamily_class` is definitional, and
   `mumfordSchemeMapOfLineBundle_points` identifies the classifying map at
   `(x ≫ ι) ≫ mumfordMap` with the class of `F`. The trivialization `α` from
   the input witnesses `HasTrivialHomPullback [n] T F`. Then
   `dualKernelCharacter_eq_of_family_class` and
   `trivialHomPullbackCharacter_eq` give
   `dualKernelCharacter = intrinsicKernelCharacter [n] α _`.
4. `kernelTranslationUnit_eq_one_of_section` (from
   `Langlands.AbelianScheme.KernelTranslationSectionFormula`) turns the input
   equation into `kernelTranslationUnit [n] α _ (𝟙 T) x = 1`.
   `characterEvaluation_intrinsicKernelCharacter_eq_one` then gives evaluation
   `1` at `x`.

The diagonal statement follows from `finiteWeilAlongHomPairing_points` at
`T = A[n]`, `x = y = 𝟙`.
