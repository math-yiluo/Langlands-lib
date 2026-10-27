# Finiteness of the actual residue-fibre arrow and module: proof

This proof module proves the published statement
`Langlands.Algebra.ResidueFiberFinitenessStatement` from
`Langlands.Algebra.ResidueFiberFinitenessStatement`. It imports that statement and the
published base-change proof `Langlands.Algebra.EssFinitePresentationBaseChangeProof`,
which in turn imports `Langlands.Algebra.EssFinitePresentationTransportProof`. It
changes none of them. It also leaves unchanged the predicate
`Langlands.Algebra.EssFinitePresentation`, the module
`Langlands.Algebra.LocalTowerResidueFiberRings` and everything they import.

The closing theorem is `Langlands.Algebra.residueFiberFiniteness.{u, v, w, z}`. Its
complete type is `Langlands.Algebra.ResidueFiberFinitenessStatement.{u, v, w, z}`. It
keeps the statement's four independent universes and adds no outer parameters or
hypotheses. The final `example` checks this complete type with the unapplied constant
`@residueFiberFiniteness.{u, v, w, z}`.

Unfolded, the theorem says the following. Let `R : Type u`, `S : Type v`, `T : Type w`
be commutative local rings. Suppose there are algebras `R → S`, `S → T`, `R → T` with
`IsScalarTower R S T`, and the maps `R → S` and `S → T` are local. Let `M : Type z` be
an additive commutative group with `R`-, `S`- and `T`-module structures compatible
through the three scalar towers. Put `κ = ResidueField R`, `F = S ⊗[R] κ`,
`G = T ⊗[R] κ` and `N = κ ⊗[R] M`. If `EssFinitePresentation S T` and
`Module.FinitePresentation T M`, then:

- `EssFinitePresentation F G` holds, where `G` is an `F`-algebra by
  `ResidueFiberTensor.upperAlgebra R S κ T`. Its algebra map is the actual arrow
  `ResidueFiberTensor.upperMap R S κ T`, given by `s ⊗ a ↦ algebraMap S T s ⊗ a`.
- `Module.FinitePresentation G N` holds, where `N` is a `G`-module by
  `ResidueFiberTensor.rawModule R T κ M`, given by
  `(t ⊗ a) • (b ⊗ m) = (a * b) ⊗ (t • m)`.

No further hypotheses are used. In particular, the proof does not use essential finite
presentation over `R`, Noetherianity, flatness, nonvanishing, injectivity or any
finiteness of the fibres. The local-ring and local-map hypotheses of the statement are
not used in the proof either. They are only part of the statement's setting.

## Comparison helpers

The module adds one comparison, stated for an arbitrary commutative `R`-algebra `K` in
place of `κ`. It assumes commutative rings `R`, `S`, `K`, `T`, algebras `R → S`,
`R → K`, `R → T`, `S → T` and `IsScalarTower R S T`. No local hypotheses are needed.
The universes of `R`, `S`, `K`, `T` are independent.

- `upperFiberBaseChangeRingEquiv R S K T : (S ⊗[R] K) ⊗[S] T ≃+* T ⊗[R] K` is a ring
  isomorphism. It is the composite of Mathlib's
  `Algebra.TensorProduct.comm S (S ⊗[R] K) T` with Mathlib's
  `Algebra.TensorProduct.cancelBaseChange R S S T K`, which is the map
  `T ⊗[S] (S ⊗[R] K) ≃ₐ[S] T ⊗[R] K`, `t ⊗ (s ⊗ a) ↦ (s • t) ⊗ a`.
  The simp lemmas `upperFiberBaseChangeRingEquiv_tmul` and
  `upperFiberBaseChangeRingEquiv_symm_tmul` record the two formulas

  ```text
  (s ⊗ a) ⊗ t ↦ (algebraMap S T s * t) ⊗ a,      t ⊗ a ↦ (1 ⊗ a) ⊗ t.
  ```

  The forward formula follows by `simp` from `comm_tmul`, `cancelBaseChange_tmul` and
  `Algebra.smul_def`. The inverse formula holds by `rfl`.

- `upperFiberBaseChangeEquiv R S K T` is the same map as an
  `S ⊗[R] K`-algebra equivalence

  ```text
  (S ⊗[R] K) ⊗[S] T ≃ₐ[S ⊗[R] K] T ⊗[R] K.
  ```

  Its type installs `ResidueFiberTensor.upperAlgebra R S K T` by `letI`, exactly as the
  target statement does. So the target is an `S ⊗[R] K`-algebra through `upperMap`. The
  source `(S ⊗[R] K) ⊗[S] T` has Mathlib's left-factor algebra structure,
  `x ↦ x ⊗ 1`. Here `S ⊗[R] K` is an `S`-algebra through its left factor,
  `s ↦ s ⊗ 1`. These are the structures that Mathlib's instance search finds. The
  equivalence is `AlgEquiv.ofRingEquiv` applied to the ring isomorphism above. The
  compatibility to check is

  ```text
  upperFiberBaseChangeRingEquiv R S K T (x ⊗ 1) = upperMap R S K T x
  ```

  for every `x : S ⊗[R] K`. It is proved by induction on `x`. For `x = s ⊗ a` both sides
  are `algebraMap S T s ⊗ a`, by the forward formula with `t = 1` and by
  `upperMap_tmul`. For sums, both sides are additive.
  The simp lemmas `upperFiberBaseChangeEquiv_tmul` and
  `upperFiberBaseChangeEquiv_symm_tmul` repeat the two formulas for the algebra
  equivalence. The inverse lemma also installs `upperAlgebra` by `letI` in its
  statement, because forming `.symm` needs the algebra instance.

## Implemented proof

The proof of `residueFiberFiniteness` introduces the statement's binders and the two
finiteness hypotheses `hT : EssFinitePresentation S T` and
`hM : Module.FinitePresentation T M`. It installs `upperAlgebra R S κ T` and
`rawModule R T κ M` as local instances with `let`. These are the same terms the
statement installs, so the goals are exactly the two conclusions of the statement.
The two halves are proved separately.

**Essential finite presentation of `G` over `F`.** The published
`essFinitePresentation_baseChange`, applied to `B = F` and `hT`, gives
`EssFinitePresentation F (F ⊗[S] T)`. Here `F` is an `S`-algebra through its left
factor and `F ⊗[S] T` has the left-factor `F`-algebra structure. These are the same
instances that appear in the source of `upperFiberBaseChangeEquiv R S κ T`. The
published `essFinitePresentation_of_algEquiv` transports this result along that
equivalence. Since the target of the equivalence is `G` with the `F`-algebra
`upperAlgebra R S κ T`, the result is the first conclusion.

**Finite presentation of `N` over `G`.** Mathlib's instance in
`Mathlib.Algebra.Module.FinitePresentation` gives `Module.FinitePresentation A (A ⊗[R] M)`
from `Module.FinitePresentation R M`. Applied with base ring `T` and `A = G`, it gives
`Module.FinitePresentation G (G ⊗[T] M)`. Here `G` is a `T`-algebra through its left
factor, and `G ⊗[T] M` has its left `G`-module structure. The proof finds this instance
by instance search from `hM`. The published
`ResidueFiberTensor.linearComparison R T κ M : G ⊗[T] M ≃ₗ[G] N` is linear for exactly
the `rawModule R T κ M` action on `N`. It is given by `(t ⊗ a) ⊗ m ↦ a ⊗ (t • m)`.
Mathlib's `Module.FinitePresentation.of_equiv` transports finite presentation along it,
which gives the second conclusion.

The proof uses only the axioms `propext`, `Classical.choice` and `Quot.sound`. It uses
no `sorry`, no new axioms and no native computation.

## Provenance

The statement is a derived internal supporting statement. It isolates the ambient
finiteness used in the second application of Stacks Lemma 10.128.3 (tag **00R6**), to
the fibre system, in the proof of Lemma 10.128.8 (tag **00R7**). The registered source
is `stacks-algebra-flatness-criteria-2026-10-22`, folder SHA-256
`4bc1f2db6141508f6dad2132d4abc7963380cd71497ad20620c0e511b972a949`. The source does not
display this finiteness as a separate lemma or prove it. The proof here is therefore an
independent formal argument. Its essential-finite-presentation half rests on base
change, Stacks Lemma 10.54.3 (tag **0AUF**), through the published
`essFinitePresentation_baseChange`. Its module half rests on base change of finite
presentation in Mathlib.

The route follows the suggestion in the task context: the comparison
`F ⊗[S] T ≃ₐ[F] G` along `upperMap`, the published base-change and transport theorems
for essential finite presentation, and the published `linearComparison` for the module.
That context was written by Worker 254, the statement's author, with routing agreed by
Worker 214 and Worker 336. Worker 788 implemented the Lean proof, the comparison
helpers and this explanation. The proof relies on pinned Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`, specifically
`Mathlib.RingTheory.TensorProduct.Maps` and `Mathlib.Algebra.Module.FinitePresentation`.
