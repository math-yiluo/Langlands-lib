/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.FieldTheory.SeparableExtension
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import WeilConjectures.FieldTheory.MakeSeparablyGenerated
import WeilConjectures.FieldTheory.SeparablyGeneratedSeparable

/-!
# Making a finitely generated field extension separable

Source: Stacks Project, Algebra, Lemma 030R (lemma-make-separable), first assertion
(blueprint: lem-weil-pbc-make-separable).
-/

@[expose] public section

universe u v

namespace Algebra

/-- A finitely generated field extension becomes separable after finite purely inseparable
extensions of the base and of the extension field.
Source: Stacks Project, Algebra, Lemma 030R, first assertion
(blueprint: lem-weil-pbc-make-separable).

Proof outline (the proof is deferred): apply
`lem-weil-pbc-make-separably-generated` to the finitely generated extension.  It supplies
fields `k'` and `K'`, the maps and scalar towers in the displayed square, finite purely
inseparable extensions `k'/k` and `K'/K`, and a separably generated extension `K'/k'`.
Then apply `lem-weil-pbc-separably-generated-separable` to conclude
`Algebra.IsSeparableExtension k' K'`; the two scalar towers identify the two maps from
`k` to `K'`, so the square commutes. -/
theorem exists_finite_purelyInseparable_separable_extension
    (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K]
    (hK : (⊤ : IntermediateField k K).FG) :
    ∃ (k' K' : Type (max u v)) (_ : Field k') (_ : Field K')
      (_ : Algebra k k') (_ : Algebra k K') (_ : Algebra k' K') (_ : Algebra K K')
      (_ : IsScalarTower k k' K') (_ : IsScalarTower k K K')
      (_ : Module.Finite k k') (_ : IsPurelyInseparable k k')
      (_ : Module.Finite K K') (_ : IsPurelyInseparable K K'),
      Algebra.IsSeparableExtension k' K' := by
  obtain ⟨k', hk', akk', K', hK', aKK', akK', hfin, hpi, hFin, hPI, hgen, hcomm⟩ :=
    FieldExtension.exists_finitePurelyInseparable_separablyGenerated k K hK
  let : Field k' := hk'
  let : Field K' := hK'
  let : Algebra k k' := akk'
  let : Algebra K K' := aKK'
  let : Algebra k' K' := akK'
  let : Algebra k K' := ((algebraMap K K').comp (algebraMap k K)).toAlgebra
  have htowerK : IsScalarTower k K K' := IsScalarTower.of_algebraMap_eq' rfl
  have htowerk : IsScalarTower k k' K' :=
    IsScalarTower.of_algebraMap_eq' hcomm.symm
  exact ⟨k', K', hk', hK', akk', inferInstance, akK', aKK', htowerk, htowerK,
    hfin, hpi, hFin, hPI, isSeparableExtension_of_isSeparablyGenerated k' K' hgen⟩

end Algebra
