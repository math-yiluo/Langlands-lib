/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Sieves

/-!
# AffineEtale

Ported from the `proetale` package (`Proetale.Mathlib.AlgebraicGeometry.Sites.AffineEtale`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

namespace AffineEtale

variable (S : Scheme.{u})

noncomputable
abbrev toScheme : S.AffineEtale ⥤ Scheme :=
  AffineEtale.Spec _ ⋙ Etale.forget _ ⋙ Over.forget _

variable {S} in
lemma mem_topology_iff {X : S.AffineEtale} (R : Sieve X) :
    R ∈ topology S X ↔
      Sieve.functorPushforward (toScheme S) R ∈ etaleTopology ((toScheme S).obj X) := by
  rw [Sieve.functorPushforward_comp, Sieve.functorPushforward_comp,
    ← Functor.functorPushforward_mem_iff (J := topology S) (K := S.smallEtaleTopology)
      (G := AffineEtale.Spec S)]
  exact Functor.mem_restrictedTopology_iff (G := MorphismProperty.Over.forget @Etale ⊤ S)
    (K := S.overGrothendieckTopology @Etale)

-- TODO: When the Zariski topology on `CommRingCatᵒᵖ` lands, consider refactoring this.
noncomputable
def zariskiTopology : GrothendieckTopology S.AffineEtale :=
  (Precoverage.comap (toScheme S) zariskiPrecoverage).toGrothendieck

/-- The Zariski topology on the small affine étale site of `S` is coarser than the affine étale
topology, since a Zariski cover consists of open immersions, which are étale. -/
lemma zariskiTopology_le_topology : zariskiTopology S ≤ topology S := by
  rw [zariskiTopology, Precoverage.toGrothendieck_le_iff_le_toPrecoverage]
  intro X R hR
  rw [Precoverage.mem_comap_iff] at hR
  rw [GrothendieckTopology.mem_toPrecoverage_iff, mem_topology_iff,
    ← Sieve.generate_map_eq_functorPushforward]
  -- Open immersions are étale, so a Zariski cover is an étale cover.
  have hle : @IsOpenImmersion ≤ @Etale := fun _ _ _ _ ↦ inferInstance
  exact Precoverage.generate_mem_toGrothendieck (precoverage_mono hle _ hR)

/-- A single surjective (étale) morphism is a cover in the small affine étale site. -/
lemma generate_singleton_mem_topology {X Y : S.AffineEtale} (f : X ⟶ Y)
    (hf : Function.Surjective ((toScheme S).map f).base) :
    Sieve.generate (Presieve.singleton f) ∈ topology S Y := by
  have het : Etale ((toScheme S).map f) :=
    inferInstanceAs <| Etale ((AffineEtale.Spec S).map f).left
  have : Sieve.generate ((Presieve.singleton f).map (toScheme S)) ∈
      grothendieckTopology @Etale ((toScheme S).obj Y) := by
    refine Precoverage.generate_mem_toGrothendieck ?_
    rw [Presieve.map_singleton, singleton_mem_precoverage_iff]
    exact ⟨hf, het⟩
  rw [mem_topology_iff, ← Sieve.generate_map_eq_functorPushforward]
  exact this

/-- **A set of affine étale schemes covers the small étale site.** The category
`S.AffineEtale` of affine schemes `Spec A` étale over `S` is essentially small, and `Spec` from it
to the small étale site of `S` is cover-dense: every object of the small étale site is covered by
affine étale schemes.

(blueprint: `lem-weil-pbc-affine-etale-essentially-small-cover`) -/
theorem essentiallySmall_and_isCoverDense (S : Scheme.{u}) :
    EssentiallySmall.{u} S.AffineEtale ∧
      (AffineEtale.Spec S).IsCoverDense S.smallEtaleTopology :=
  ⟨inferInstance, inferInstance⟩


end AffineEtale

end AlgebraicGeometry.Scheme
