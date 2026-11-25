/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.Topology.Constructible
import WeilConjectures.AlgebraicGeometry.ConstructibleStratifiedFinite
import WeilConjectures.AlgebraicGeometry.QuasiFiniteLocallyQuasiFinite
import WeilConjectures.AlgebraicGeometry.UnramifiedQuasiFinite

/-!
# Finite étale strata of a separated étale morphism

Source: More on Morphisms, Lemma Tag 07RZ, together with Etale Cohomology, Lemma Tag 03S9
(blueprint: lem-weil-pbc-etale-separated-stratified-finite).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- A quasi-compact separated étale morphism into a quasi-compact quasi-separated scheme is
finite étale after base change to each member of a finite constructible locally closed
stratification of its target.

Source: More on Morphisms, Lemma Tag 07RZ, and Etale Cohomology, Lemma Tag 03S9
(blueprint: lem-weil-pbc-etale-separated-stratified-finite).

Proof:
1. `j` is étale, hence flat, locally of finite presentation and unramified, so locally
   quasi-finite; being quasi-compact it is quasi-finite, and it is separated.
2. Tag 07RZ (`lem-weil-pbc-flat-fp-qf-stratification`) gives closed subsets
   `∅ = Z_{-1} ⊆ Z_0 ⊆ Z_1 ⊆ ⋯` with strata `Y_r = Z_r \ Z_{r-1}` partitioning `X`, such
   that `U ×_X T → T` is finite locally free of degree `r` iff `T → X` lands in `Y_r`, and
   every inclusion `Y_r → X` is quasi-compact.
3. `U` is quasi-compact, so the fibre degrees are bounded by some `n`; hence `Y_r = ∅` for
   `r > n` and `X = Y_0 ⊔ ⋯ ⊔ Y_n`, a finite partition.
4. Each `Y_r` is locally closed, and constructible since its inclusion is quasi-compact in
   the spectral space of the qcqs scheme `X`.
5. Give `Y_r` the reduced closed subscheme structure in the open `X \ Z_{r-1}` and compose
   with the open immersion: an immersion with image `Y_r`.
6. By step 2 the base change of `j` to each stratum is finite locally free, hence finite,
   and étale by base change. -/
theorem exists_etale_separated_stratified_finite {X U : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X]
    (j : U ⟶ X) [Etale j] [IsSeparated j] [QuasiCompact j] :
    ∃ S : Stratification X,
      (∀ i : Fin S.n, Topology.IsConstructible (S.stratum i)) ∧
      (∀ i : Fin S.n,
        IsFinite (pullback.snd j (S.immersion i)) ∧
        Etale (pullback.snd j (S.immersion i))) := by
  let hj : Hom.IsQuasiFinite j :=
    (Hom.isQuasiFinite_iff_isLocallyQuasiFinite_and_quasiCompact j).mpr
      ⟨Hom.isLocallyQuasiFinite_of_unramified j ⟨inferInstance, inferInstance⟩, inferInstance⟩
  obtain ⟨S, hScon, hSfin⟩ := exists_constructible_stratified_finite j hj
  refine ⟨S, hScon, fun i ↦ ⟨hSfin i, inferInstance⟩⟩

end AlgebraicGeometry.Scheme
