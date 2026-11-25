/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree

/-! # Degree bound from a finite open cover

Source: literature/stacks-project/morphisms.tex, proof of Lemma Tag 03JA,
lines 15507--15518 (blueprint: lem-weil-pbc-finite-open-cover-degree-sum).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/- The finite open-cover degree estimate is the parenthetical claim in the
proof of Stacks Project Lemma 03JA. -/
/-- A finite open cover by schemes finite over a field makes the whole scheme
finite over that field, with degree bounded by the sum of the piece degrees.
Source: Stacks Project, Morphisms, proof of Lemma Tag 03JA, lines 15507--15518
(blueprint: lem-weil-pbc-finite-open-cover-degree-sum).

Proof:
1. Put `B i = Γ(U i, ⊤)`, with its `k`-algebra structure induced by
   `(U i).ι ≫ t`. By lem-weil-pbc-finite-over-field-affine-finite-dim each piece
   is affine and finite-dimensional. By
   lem-weil-pbc-finite-over-zero-dim-local-discrete-spectrum its spectrum,
   hence the piece itself, is a finite discrete space.
2. The covering makes `T` a finite union of finite sets. Each singleton in `T`
   is open in a covering piece, hence open in `T`; thus `T` is finite discrete.
   When `m = 0`, the covering forces `T` to be empty.
3. By lem-weil-pbc-finite-discrete-scheme-affine, `T` is affine. Give
   `A = Γ(T, ⊤)` the `k`-algebra structure induced by `t` via Spec's global
   sections identification (def-weil-affine-spectrum).
4. Restriction gives a `k`-linear map from `A` to the product of the `B i`:
   functoriality identifies each piece's scalar map with the restriction of
   `t`'s scalar map. This map is injective by the sheaf locality axiom
   (def-pc-scheme). The finite product has dimension the sum of the piece
   dimensions, so `A` is finite-dimensional with dimension at most `∑ i, n i`.
   For the empty cover, sections on the empty scheme form the zero ring.
5. Apply lem-weil-pbc-finite-local-on-target to the single affine open
   `Spec k`: its inverse image `T` is affine and its section algebra `A` is a
   finite `k`-module. Hence `t` is finite (def-weil-finite-integral-morphism),
   with the dimension bound from step 4.
-/
theorem finite_open_cover_degree_sum
    {k : Type u} [Field k] {T : Scheme.{u}}
    (t : T ⟶ Spec (.of k)) (m : ℕ) (U : Fin m → T.Opens)
    (n : Fin m → ℕ)
    (hcover : ⨆ i, U i = ⊤)
    (hfinite : ∀ i : Fin m, IsFinite ((U i).ι ≫ t))
    (hbound : ∀ i : Fin m, ((U i).ι ≫ t).finrankΓ ≤ n i) :
    IsFinite t ∧ t.finrankΓ ≤ ∑ i : Fin m, n i := by
  classical
  let (i : Fin m) : IsFinite ((U i).ι ≫ t) := hfinite i
  let := t.ΓAlgebra
  let (i : Fin m) := ((U i).ι ≫ t).ΓAlgebra
  have hB (i : Fin m) : Module.Finite k Γ(U i, ⊤) := by
    rw [← RingHom.finite_algebraMap]
    change (((Scheme.ΓSpecIso (.of k)).inv ≫ ((U i).ι ≫ t).appTop).hom).Finite
    rw [CommRingCat.hom_comp, RingHom.finite_respectsIso.cancel_left_isIso]
    exact ((U i).ι ≫ t).finite_appTop
  let (i : Fin m) : Module.Finite k Γ(U i, ⊤) := hB i
  have (i : Fin m) : IsAffine (U i).toScheme :=
    isAffine_of_isAffineHom ((U i).ι ≫ t)
  have (i : Fin m) : DiscreteTopology (Spec Γ(U i, ⊤)) :=
    Algebra.QuasiFinite.discreteTopology_primeSpectrum k Γ(U i, ⊤)
  have (i : Fin m) : Finite (Spec Γ(U i, ⊤)) :=
    finite_of_compact_of_discrete
  have hfin (i : Fin m) : Finite (U i) :=
    Finite.of_injective (U i).toScheme.isoSpec.hom.homeomorph
      (U i).toScheme.isoSpec.hom.homeomorph.injective
  let (i : Fin m) : Finite (U i) := hfin i
  have (i : Fin m) : DiscreteTopology (U i) :=
    (U i).toScheme.isoSpec.hom.homeomorph.isEmbedding.discreteTopology
  have hcov : (⋃ i, (U i : Set T)) = Set.univ := by
    simp only [← TopologicalSpace.Opens.coe_iSup, hcover, TopologicalSpace.Opens.coe_top]
  have hTfin : (Set.univ : Set T).Finite := by
    rw [← hcov]
    exact Set.finite_iUnion fun i ↦ hfin i
  let : Finite T := Set.finite_univ_iff.mp hTfin
  let : DiscreteTopology T := discreteTopology_iff_isOpen_singleton.mpr fun x ↦ by
    have hx : x ∈ ⋃ i, (U i : Set T) := hcov.symm ▸ Set.mem_univ x
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    have h := (U i).ι.isOpenEmbedding.isOpenMap {⟨x, hi⟩} (isOpen_discrete _)
    simpa using h
  have : IsAffine T := inferInstance
  let ρ (i : Fin m) : Γ(T, ⊤) →ₐ[k] Γ(U i, ⊤) :=
    { toRingHom := (U i).ι.appTop.hom
      commutes' := fun r ↦ by
        change (U i).ι.appTop.hom
          (((Scheme.ΓSpecIso (.of k)).inv ≫ t.appTop).hom r) =
          (((Scheme.ΓSpecIso (.of k)).inv ≫ ((U i).ι ≫ t).appTop).hom r)
        rw [Scheme.Hom.comp_appTop]
        rfl }
  let f : Γ(T, ⊤) →ₗ[k] (∀ i : Fin m, Γ(U i, ⊤)) :=
    LinearMap.pi fun i ↦ (ρ i).toLinearMap
  have hf : Function.Injective f := by
    intro a b hab
    apply TopCat.Sheaf.eq_of_locally_eq' T.sheaf (fun i ↦ (U i).ι ''ᵁ ⊤) ⊤
      (fun _ ↦ homOfLE le_top)
    · simpa using hcover.ge
    · intro i
      exact congrFun hab i
  have : Module.Finite k Γ(T, ⊤) := Module.Finite.of_injective f hf
  refine ⟨?_, ?_⟩
  · rw [HasAffineProperty.iff_of_isAffine (P := @IsFinite)]
    refine ⟨inferInstance, ?_⟩
    have h : (algebraMap k Γ(T, ⊤)).Finite := RingHom.finite_algebraMap.mpr inferInstance
    change (((Scheme.ΓSpecIso (.of k)).inv ≫ t.appTop).hom).Finite at h
    rwa [CommRingCat.hom_comp, RingHom.finite_respectsIso.cancel_left_isIso] at h
  · change Module.finrank k Γ(T, ⊤) ≤ ∑ i : Fin m, n i
    calc
      _ ≤ Module.finrank k (∀ i : Fin m, Γ(U i, ⊤)) :=
        LinearMap.finrank_le_finrank_of_injective hf
      _ = ∑ i : Fin m, Module.finrank k Γ(U i, ⊤) := Module.finrank_pi_fintype k
      _ ≤ ∑ i : Fin m, n i := Finset.sum_le_sum fun i _ ↦ hbound i

end AlgebraicGeometry
