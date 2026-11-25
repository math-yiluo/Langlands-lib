/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.Ample
import WeilConjectures.AlgebraicGeometry.Ample.AmpleOnReductionNoetherian
import WeilConjectures.AlgebraicGeometry.AmpleIso
import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.Curve.ExistsAmpleOfReducedDimLEOne
import WeilConjectures.AlgebraicGeometry.Picard.PicardLift
import WeilConjectures.AlgebraicGeometry.ReductionUniversalHomeomorphism

/-! # Ample invertible modules in dimension at most one

Source: Stacks Project, Varieties, Lemma 0A25 and Proposition 09NZ
(blueprint: lem-sc-dim-one-ample-invertible).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- A separated finite-type scheme over a field of topological dimension at most one
has an ample invertible module, including when the scheme is empty.
Source: Stacks Project, Varieties, Lemma 0A25, using Proposition 09NZ
(blueprint: lem-sc-dim-one-ample-invertible).

Proof:
1. A field is Noetherian, and its spectrum is Noetherian. Finite type over this spectrum
makes `X` Noetherian (`lem-weil-pbc-finite-type-over-noetherian`).
2. Separatedness over the affine base gives absolute separatedness
(`lem-sc-separated-over-affine-scheme-separated`).
3. The reduction `Z` is reduced and its closed immersion into `X` is a universal
homeomorphism (`lem-weil-pbc-reduction-universal-homeomorphism`). It is finite
(`lem-weil-pbc-closed-immersion-finite`), so the composite to the field spectrum remains
separated and finite type (`lem-weil-pbc-finite-over-separated-finite-type`). Thus `Z`
is Noetherian and separated; the homeomorphism preserves topological Krull dimension.
4. Apply `lem-sc-reduced-dim-le-one-ample` to obtain an ample invertible module `N` on `Z`.
5. Noetherianity gives minimal closed subsets
(`lem-weil-pbc-noetherian-scheme-closed-subsets-minimal`). Lift `N` to an invertible
module `L` on `X` by `lem-sc-pic-lift-closed-immersion-dim-le-one`. The pullback of `L`
is isomorphic to `N`; this isomorphism matches sections of all tensor powers and their
nonvanishing loci, so the pullback is ample.
6. Apply `lem-sc-ample-on-reduction-noetherian` to the closed immersion, which is a
homeomorphism, to conclude that `L` is ample on `X`.
-/
theorem exists_isAmple_of_dim_le_one {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (hdim : topologicalKrullDim X ≤ 1) :
    ∃ L : X.Modules, ∃ hL : L.IsInvertible, @IsAmple X L hL := by
  have : IsNoetherian X := isNoetherian_of_locallyOfFiniteType f
  have : X.IsSeparated := HasAffineProperty.iff_of_isAffine.mp
    (inferInstance : IsSeparated f)
  let Z := X.nilradical.subscheme
  let i : Z ⟶ X := X.nilradical.subschemeι
  have hred := reduction_isReduced_isClosedImmersion_isSurjective_isUniversalHomeomorphism X
  have : IsReduced Z := hred.1
  have : IsClosedImmersion i := hred.2.1
  have : IsNoetherian Z := isNoetherian_of_locallyOfFiniteType i
  have : Z.IsSeparated := HasAffineProperty.iff_of_isAffine.mp
    (inferInstance : IsSeparated (i ≫ f))
  have hi : IsHomeomorph i.base :=
    isHomeomorph_iff_isEmbedding_surjective.mpr ⟨i.isEmbedding, hred.2.2.1.surj⟩
  have hZdim : topologicalKrullDim Z ≤ 1 := by
    rw [IsHomeomorph.topologicalKrullDim_eq i.base hi]
    exact hdim
  obtain ⟨N, hN, hNamp⟩ := exists_isAmple_of_reduced_dim_le_one Z hZdim
  obtain ⟨L, hL, ⟨e⟩⟩ :=
    exists_isInvertible_tensorPullback_iso_of_isClosedImmersion i hdim N hN
  have : L.IsInvertible := hL
  have : N.IsInvertible := hN
  have : ((tensorPullback i).obj L).IsInvertible :=
    ((invertible_pullback_tensor i).1 L).2
  refine ⟨L, hL, ?_⟩
  apply (isAmple_iff_of_isClosedImmersion_of_isHomeomorph i hi L).mp
  exact (isAmple_iff_of_iso e).mpr hNamp

end AlgebraicGeometry.Scheme.Modules
