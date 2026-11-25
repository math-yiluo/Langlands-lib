/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.SetTheory.Cardinal.ENat
public import WeilConjectures.Mathlib.Topology.KrullDimension
public import WeilConjectures.ZetaSeries
import WeilConjectures.RingTheory.DimensionAtPointLocalRingTrdeg

/-!
# The dimension formula for schemes of finite type over a field

For a scheme `X` of finite type over a field `K` and a point `x` of `X`, the local dimension
of `X` at `x` is the dimension of the stalk plus the transcendence degree of the residue field:
`dim_x X = dim 𝒪_{X,x} + trdeg_K κ(x)` (Stacks Project, Tag 02FX, over a field).

## Main results

- `AlgebraicGeometry.topologicalKrullDimAt_eq_stalk_dimension_add_residue_trdeg`: the dimension
  formula (blueprint `lem-kun-dimension-formula`). It is deduced from the affine case
  `AlgebraicGeometry.topologicalKrullDimAt_eq_ringKrullDim_add_trdeg`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- **The dimension formula** (Stacks Project, Tag 02FX; blueprint `lem-kun-dimension-formula`):
for a finite type `K`-scheme, the local topological dimension at `x` equals the dimension
of its stalk plus the transcendence degree of its residue field. The residue-field algebra
is the canonical one induced by the structure morphism. `Cardinal.toENat` preserves each
finite cardinal and sends infinite cardinals to infinity, embedding the transcendence degree
in the same extended dimension type as the other terms.

Proof:
1. Write `f = X ↘ Spec K`. Choose an affine open neighbourhood `U` of `x` and put
   `R = Γ(X, U)`. By `lem-weil-pbc-lft-affine-pairs`, `R` is a finite type `K`-algebra.
   By `lem-weil-pbc-affine-open-spec-points`, `x` corresponds to a prime `p` of `R`.
2. By `lem-weil-pbc-dimension-at-point-open-subspace`, replacing `X` by `U` leaves its
   dimension at `x` unchanged. The affine homeomorphism identifies this with the dimension
   of `Spec R` at `p`, since it identifies open neighbourhoods and irreducible closed chains.
3. Apply `lem-weil-pbc-dimension-at-point-local-ring-trdeg` to `R` and `p`, obtaining
   `dim_p Spec R = dim R_p + trdeg_K κ(p)`, with finite terms. This applies to reducible
   and nonreduced algebras as well.
4. By `lem-weil-pbc-affine-open-stalk-localization`, `R_p` is isomorphic to the stalk
   at `x` via `r/s ↦ r_x / s_x`. Constants map to their germs, so this is a `K`-linear
   ring isomorphism. It identifies maximal ideals and hence the residue fields over `K`.
   Prime chains and algebraically independent subsets correspond under these isomorphisms,
   preserving ring dimension and transcendence degree. Substitution gives the formula. -/
theorem topologicalKrullDimAt_eq_stalk_dimension_add_residue_trdeg
    {K : Type u} [Field K] (X : Scheme.{u}) [X.Over (Spec (.of K))]
    [LocallyOfFiniteType (X ↘ Spec (.of K))] [QuasiCompact (X ↘ Spec (.of K))] (x : X) :
    topologicalKrullDimAt x = ringKrullDim (X.presheaf.stalk x) +
      (Cardinal.toENat (@Algebra.trdeg K (X.residueField x) _ _
        ((X ↘ Spec (.of K)).residueFieldAlgebraMap x).toAlgebra) : WithBot ℕ∞) := by
  classical
  let f := X ↘ Spec (.of K)
  obtain ⟨U, hU, hx, _⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ (⊤ : X.Opens) from trivial)
  let R := Γ(X, U)
  let φ : K →+* R := (f.appLE ⊤ U (by simp)).hom.comp
    (Scheme.ΓSpecIso (.of K)).inv.hom
  let : Algebra K R := φ.toAlgebra
  have : Algebra.FiniteType K R :=
    (f.finiteType_appLE (isAffineOpen_top _) hU (by simp)).comp
      (RingHom.FiniteType.of_surjective _
        (Scheme.ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv.surjective)
  let p := hU.primeIdealOf ⟨x, hx⟩
  let : Algebra R (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hx⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk x) p.asIdeal :=
    hU.isLocalization_stalk ⟨x, hx⟩
  let e := IsLocalization.algEquiv p.asIdeal.primeCompl
    (Localization.AtPrime p.asIdeal) (X.presheaf.stalk x)
  let er : p.asIdeal.ResidueField ≃+* X.residueField x :=
    IsLocalRing.ResidueField.mapEquiv e.toRingEquiv
  let : Algebra K (X.residueField x) := (f.residueFieldAlgebraMap x).toAlgebra
  have hcanonical : CommRingCat.ofHom (f.residueFieldAlgebraMap x) =
      (Scheme.ΓSpecIso (.of K)).inv ≫ f.appLE ⊤ U (by simp) ≫
        X.presheaf.germ U x hx ≫ X.residue x := by
    change CommRingCat.ofHom (algebraMap (CommRingCat.of K)
        (f.base x).asIdeal.ResidueField) ≫
      (Scheme.Spec.residueFieldIso (.of K) (f.base x)).inv ≫ f.residueFieldMap x = _
    rw [Scheme.Spec.algebraMap_residueFieldIso_inv_assoc, Scheme.residue_residueFieldMap,
      Scheme.Hom.germ_stalkMap_assoc]
    simp only [Scheme.Hom.appLE, Category.assoc, TopCat.Presheaf.germ_res_assoc]
  let ek : p.asIdeal.ResidueField ≃ₐ[K] X.residueField x :=
    AlgEquiv.ofRingEquiv (f := er) fun c ↦ by
      rw [IsScalarTower.algebraMap_apply K R p.asIdeal.ResidueField,
        IsScalarTower.algebraMap_apply R (Localization.AtPrime p.asIdeal),
        IsLocalRing.ResidueField.algebraMap_eq]
      change IsLocalRing.residue _ (e (algebraMap R _ (algebraMap K R c))) = _
      rw [e.commutes]
      exact (ConcreteCategory.congr_hom hcanonical c).symm
  obtain ⟨d, r, hd, hr, ht⟩ := topologicalKrullDimAt_eq_ringKrullDim_add_trdeg
    (k := K) p.asIdeal
  have hdim : ringKrullDim (X.presheaf.stalk x) = (d : WithBot ℕ∞) :=
    (ringKrullDim_eq_of_ringEquiv e.toRingEquiv).symm.trans hd
  have htrdeg : Cardinal.toENat (Algebra.trdeg K (X.residueField x)) = (r : ℕ∞) := by
    rw [← ek.trdeg_eq, hr]
    simp
  have htop : topologicalKrullDimAt (p : Spec (.of R)) = topologicalKrullDimAt x := by
    have hle {A B : Type u} [TopologicalSpace A] [TopologicalSpace B]
        (e : A ≃ₜ B) (a : A) : topologicalKrullDimAt a ≤ topologicalKrullDimAt (e a) := by
      refine le_iInf₂ fun V ha ↦ ?_
      let W : TopologicalSpace.Opens A := ⟨e ⁻¹' V, V.isOpen.preimage e.continuous⟩
      refine (iInf₂_le W ha).trans ?_
      refine Topology.IsInducing.topologicalKrullDim_le
        (f := fun q : W ↦ (⟨e q.1, q.2⟩ : V))
        (.of_comp (g := Subtype.val) (by fun_prop) ?_ ?_)
      · exact continuous_subtype_val
      · exact e.isInducing.comp Topology.IsInducing.subtypeVal
    let e : U ≃ₜ Spec (.of R) := hU.isoSpec.hom.homeomorph
    have he : topologicalKrullDimAt (⟨x, hx⟩ : U) =
        topologicalKrullDimAt (p : Spec (.of R)) :=
      le_antisymm (hle e ⟨x, hx⟩) (by
        have h := hle e.symm (e ⟨x, hx⟩)
        rw [e.symm_apply_apply] at h
        exact h)
    exact he.symm.trans (U.isOpen.topologicalKrullDimAt_eq hx)
  rw [← htop, hdim, htrdeg]
  simpa [Nat.cast_add] using ht

end AlgebraicGeometry
