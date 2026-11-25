/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.ProetaleTopologicalInvariance.AffineModel
public import WeilConjectures.RingTheory.ProEtale.WeaklyEtaleIndEtale

/-!
# Covering by affine models in the small pro-étale site

Let `𝒰` be a basis of affine opens of `S`. Every object `V` of the small pro-étale site of `S` is
covered by affine models `ofAlgebra hU B` with `U ∈ 𝒰` (Zariski-locally), and even by affine
models of ind-étale algebras (Stacks 097Z).

## Main results

- `AlgebraicGeometry.Scheme.ProEt.mem_topology_of_ofAlgebra`: a sieve is covering if its
  pullbacks along all open immersions from affine models over members of `𝒰` are covering.
- `AlgebraicGeometry.Scheme.ProEt.mem_topology_of_indEtale`: a sieve is covering if its pullbacks
  along all morphisms from affine models of ind-étale algebras over members of `𝒰` are covering.
- `AlgebraicGeometry.Scheme.ProEt.mem_topology_of_indEtale_of_mem`: a sieve containing all
  morphisms from affine models of ind-étale algebras over members of `𝒰` is covering.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.ProEt

variable {S : Scheme.{u}} {U : S.Opens} (hU : IsAffineOpen U)

section AffineOpen

variable (V : S.ProEt) {W : V.left.Opens} (hW : IsAffineOpen W) (hWU : W ≤ V.hom ⁻¹ᵁ U)

/-- An affine open `W` of `V : S.ProEt` mapping into the affine open `U` of `S`, viewed as the
affine model of the `Γ(S, U)`-algebra `Γ(V, W)` (via `V.hom.appLE U W`). -/
noncomputable def ofAffineOpen : S.ProEt :=
  letI : Algebra Γ(S, U) Γ(V.left, W) := (V.hom.appLE U W hWU).hom.toAlgebra
  haveI : Algebra.WeaklyEtale Γ(S, U) Γ(V.left, W) :=
    HasRingHomProperty.appLE @WeaklyEtale V.hom inferInstance ⟨U, hU⟩ ⟨W, hW⟩ hWU
  ofAlgebra hU Γ(V.left, W)

/-- The open immersion `ofAffineOpen hU V hW hWU ⟶ V`, given by `hW.fromSpec`. -/
noncomputable def ofAffineOpenHom : ofAffineOpen hU V hW hWU ⟶ V :=
  MorphismProperty.Over.homMk hW.fromSpec
    (IsAffineOpen.SpecMap_appLE_fromSpec V.hom hU hW hWU).symm

@[simp]
lemma ofAffineOpenHom_left : (ofAffineOpenHom hU V hW hWU).left = hW.fromSpec := rfl

end AffineOpen

variable {𝒰 : Set S.Opens} (h𝒰 : TopologicalSpace.Opens.IsBasis 𝒰)
  (h𝒰a : ∀ U ∈ 𝒰, IsAffineOpen U) {O : S.Opens} {V : S.ProEt}

include h𝒰 in
/-- **Zariski reduction.** Let `𝒰` be a basis of affine opens of `S`, and let `V : S.ProEt` lie
over the open `O`. A sieve `T` on `V` is covering as soon as `T.pullback f` is covering for every
open immersion `f : ofAlgebra hU B ⟶ V` from the affine model of a weakly étale
`Γ(S, U)`-algebra `B`, where `U ∈ 𝒰` and `U ≤ O`. -/
theorem mem_topology_of_ofAlgebra (hV : Set.range V.hom.base ⊆ (O : Set S)) (T : Sieve V)
    (hT : ∀ (U : S.Opens) (hU : U ∈ 𝒰), U ≤ O → ∀ (B : Type u) [CommRing B]
      [Algebra Γ(S, U) B] [Algebra.WeaklyEtale Γ(S, U) B] (f : ofAlgebra (h𝒰a U hU) B ⟶ V),
      IsOpenImmersion f.left → T.pullback f ∈ topology S _) :
    T ∈ topology S V := by
  have key (x : V.left) : ∃ (U : S.Opens) (hU : U ∈ 𝒰) (W : V.left.Opens),
      U ≤ O ∧ IsAffineOpen W ∧ x ∈ W ∧ W ≤ V.hom ⁻¹ᵁ U := by
    obtain ⟨U, hU, hxU, hUO⟩ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.mp h𝒰 (hV ⟨x, rfl⟩)
    obtain ⟨W, hW, hxW, hWU⟩ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.mp V.left.isBasis_affineOpens
        (U := V.hom ⁻¹ᵁ U) hxU
    exact ⟨U, hU, W, hUO, hW, hxW, hWU⟩
  choose U hU W hUO hW hxW hWU using key
  let f (x : V.left) := ofAffineOpenHom (h𝒰a _ (hU x)) V (hW x) (hWU x)
  have hR : Sieve.ofArrows _ f ∈ topology S V := by
    rw [mem_topology_iff]
    refine ⟨Presieve.ofArrows _ f, ?_, Sieve.le_generate _⟩
    rw [mem_precoverage_iff, Presieve.map_ofArrows]
    refine zariskiPrecoverage_le_proetalePrecoverage _
      ((Scheme.ofArrows_mem_precoverage_iff _).mpr ⟨fun x ↦ ⟨x, ?_⟩, fun x ↦ ?_⟩)
    · exact (hW x).range_fromSpec.symm ▸ hxW x
    · exact inferInstanceAs (IsOpenImmersion (hW x).fromSpec)
  refine (topology S).transitive hR T fun Z g hg ↦ ?_
  obtain ⟨x, a, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hg
  rw [Sieve.pullback_comp]
  refine (topology S).pullback_stable a ?_
  let : Algebra Γ(S, U x) Γ(V.left, W x) := (V.hom.appLE (U x) (W x) (hWU x)).hom.toAlgebra
  have : Algebra.WeaklyEtale Γ(S, U x) Γ(V.left, W x) :=
    HasRingHomProperty.appLE @WeaklyEtale V.hom inferInstance ⟨U x, h𝒰a _ (hU x)⟩ ⟨W x, hW x⟩
      (hWU x)
  exact hT (U x) (hU x) (hUO x) Γ(V.left, W x) (f x)
    (inferInstanceAs (IsOpenImmersion (hW x).fromSpec))

include h𝒰 in
/-- **Covering by ind-étale affine models** (using Stacks 097Z). Let `𝒰` be a basis of affine
opens of `S`, and let `V : S.ProEt` lie over the open `O`. A sieve `T` on `V` is covering as soon
as `T.pullback f` is covering for every morphism `f : ofAlgebra hU B ⟶ V` from the affine model
of an ind-étale `Γ(S, U)`-algebra `B`, where `U ∈ 𝒰` and `U ≤ O`. -/
theorem mem_topology_of_indEtale (hV : Set.range V.hom.base ⊆ (O : Set S)) (T : Sieve V)
    (hT : ∀ (U : S.Opens) (hU : U ∈ 𝒰), U ≤ O → ∀ (B : Type u) [CommRing B]
      [Algebra Γ(S, U) B] [Algebra.IndEtale Γ(S, U) B] (f : ofAlgebra (h𝒰a U hU) B ⟶ V),
      T.pullback f ∈ topology S _) :
    T ∈ topology S V := by
  refine mem_topology_of_ofAlgebra h𝒰 h𝒰a hV T fun U hU hUO B _ _ _ f _ ↦ ?_
  obtain ⟨B', _, _, _, _, -, h₂, h₃⟩ := Algebra.WeaklyEtale.exists_indEtale Γ(S, U) B
  let g : B →ₐ[Γ(S, U)] B' := IsScalarTower.toAlgHom Γ(S, U) B B'
  have hcov := generate_singleton_ofAlgebraMap_mem_topology (h𝒰a U hU) g
    (RingHom.faithfullyFlat_algebraMap_iff.mpr h₂)
  refine (topology S).transitive hcov _ fun Z k hk ↦ ?_
  obtain ⟨Y, a, _, ⟨⟩, rfl⟩ := hk
  rw [Sieve.pullback_comp, ← Sieve.pullback_comp (S := T)]
  exact (topology S).pullback_stable a (hT U hU hUO B' _)

include h𝒰 in
/-- A sieve on `V : S.ProEt` (lying over the open `O`) containing every morphism
`ofAlgebra hU B ⟶ V` from the affine model of an ind-étale `Γ(S, U)`-algebra `B`, with `U ∈ 𝒰`
and `U ≤ O`, is covering. -/
theorem mem_topology_of_indEtale_of_mem (hV : Set.range V.hom.base ⊆ (O : Set S)) (T : Sieve V)
    (hT : ∀ (U : S.Opens) (hU : U ∈ 𝒰), U ≤ O → ∀ (B : Type u) [CommRing B]
      [Algebra Γ(S, U) B] [Algebra.IndEtale Γ(S, U) B] (f : ofAlgebra (h𝒰a U hU) B ⟶ V), T f) :
    T ∈ topology S V :=
  mem_topology_of_indEtale h𝒰 h𝒰a hV T fun U hU hUO B _ _ _ f ↦ by
    rw [Sieve.pullback_eq_top_of_mem T (hT U hU hUO B f)]
    exact (topology S).top_mem _

end AlgebraicGeometry.Scheme.ProEt
