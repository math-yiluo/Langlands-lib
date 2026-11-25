/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleStageSectionCocone
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.AlgebraicGeometry.EtaleSetSectionComparisonEqualOpen
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Filtered.Connected
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Connected
import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # Equality detection for two affine stage sections
Source: Stacks Project, Tags 09YQ and 09XM; Mathlib affine-transition limits.
(blueprint: lem-weil-pbc-affine-section-same-stage-equality). -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- Source: Stacks Project, Tags 09YQ and 09XM; the compact closed-complement
argument in Mathlib `AlgebraicGeometry.exists_map_eq_top`.
(blueprint: lem-weil-pbc-affine-section-same-stage-equality).

Proof: Restrict the limiting diagram to the cofinal category of stages over i₀.
Base change W₀ to each stage and to the limit. Pullbacks commute with connected
limits, so these schemes form a limiting cone. The stages are compact by
quasi-compactness of W₀.hom, and their transitions are affine by base change.
The generic comparison agreement-open theorem gives an open U on the base
change at j such that equality of two comparison images means that the
corresponding scheme map has whole inverse image of U. Apply this at the limit
using hst. Mathlib's `exists_map_eq_top` then gives a single transition into j
with whole inverse image of U. Apply the reverse agreement-open criterion to
that transition. It is the transition in etaleStageSectionDiagram, as required.
Empty base changes are included by the same open-containment argument. -/
theorem etaleAffineSection_sameStageEquality
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    (G : Sheaf (D.obj (op i₀)).smallEtaleTopology (Type (u + 1)))
    (W₀ : (D.obj (op i₀)).Etale) [QuasiCompact W₀.hom] [QuasiSeparated W₀.hom]
    [IsAffine W₀.left]
    (j : Over (op i₀))
    (s t : (etaleStageSectionDiagram D c i₀ G W₀).obj (op j))
    (hst : (etaleStageSectionCocone D c i₀ G W₀).ι.app (op j) s =
      (etaleStageSectionCocone D c i₀ G W₀).ι.app (op j) t) :
    ∃ (k : Over (op i₀)) (a : k ⟶ j),
      (etaleStageSectionDiagram D c i₀ G W₀).map a.op s =
        (etaleStageSectionDiagram D c i₀ G W₀).map a.op t := by
  classical
  let B := Over.forget (op i₀) ⋙ D
  let b := c.whisker (Over.forget (op i₀))
  have hb : IsLimit b :=
    (Functor.Initial.isLimitWhiskerEquiv (Over.forget (op i₀)) c).symm hc
  let : IsConnected (Over (op i₀)) := IsCofiltered.isConnected _
  let E : Over (op i₀) ⥤ Scheme.{u} :=
    { obj := fun j ↦ pullback W₀.hom (D.map j.hom)
      map := fun {j k} a ↦ pullback.map _ _ _ _ (𝟙 W₀.left) (D.map a.left) (𝟙 _)
        (by simp) (by simp only [Category.comp_id, ← D.map_comp, a.w])
      map_id := fun j ↦ by apply pullback.hom_ext <;> simp
      map_comp := fun a a' ↦ by apply pullback.hom_ext <;> simp }
  let e : Cone E :=
    { pt := pullback W₀.hom (c.π.app (op i₀))
      π :=
        { app := fun j ↦ pullback.map _ _ _ _ (𝟙 W₀.left) (c.π.app j.left) (𝟙 _)
            (by simp) (by simp)
          naturality := fun j k a ↦ by
            apply pullback.hom_ext <;> simp [E] } }
  let β : E ⟶ B :=
    { app := fun j ↦ pullback.snd W₀.hom (D.map j.hom)
      naturality := fun j k a ↦ by simp [E, B] }
  have he : IsLimit e :=
    isLimitOfIsPullbackOfIsConnected β e b
      { hom := pullback.snd W₀.hom (c.π.app (op i₀))
        w := fun j ↦ by simp [e, β, b] }
      (fun j ↦ isPullback_pullback_map W₀.hom (c.π.app (op i₀))
        (D.map j.hom) (c.π.app j.left) (c.w j.hom)) hb
  let : ∀ k, CompactSpace (E.obj k) := fun k ↦ by dsimp [E]; infer_instance
  let : ∀ {k l} (a : k ⟶ l), IsAffineHom (E.map a) := fun {k l} a ↦
    MorphismProperty.of_isPullback (P := @IsAffineHom)
      (isPullback_pullback_map W₀.hom (D.map k.hom) (D.map l.hom)
        (D.map a.left) (by rw [← D.map_comp, a.w])).flip inferInstance
  obtain ⟨U, hU⟩ := etaleSetSectionComparison_equal_open (D.map j.hom) G W₀ s t
  have hlimit : e.π.app j ⁻¹ᵁ U = ⊤ :=
    (hU c.pt (c.π.app j.left) (c.π.app (op i₀)) (c.w j.hom)).mp hst
  obtain ⟨k, a, ha⟩ := exists_map_eq_top E e he U hlimit
  refine ⟨k, a, ?_⟩
  exact (hU (D.obj k.left) (D.map a.left) (D.map k.hom)
    ((D.map_comp a.left j.hom).symm.trans
      (congrArg (fun t ↦ D.map t) a.w))).mpr ha

end AlgebraicGeometry
