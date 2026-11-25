/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.Ring.Colimits

import WeilConjectures.AlgebraicGeometry.AffineChartRingColimitGeometric
import WeilConjectures.AlgebraicGeometry.ModuleSectionsPullbackIsoTransport

/-! # Colimit and sections comparisons for a fixed affine chart

Source: Stacks Project, Limits Tag 01ZR, affine case; Modules on Schemes Tag 01I6.
(blueprint: lem-pc-affine-chart-sections-colimit-comparison).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- The rings of the stage charts have the fixed limit chart ring as their colimit,
and changing from the fixed limit chart to an iterated chart transports sections.
There is no finite-presentation assumption and no assertion of a stage module model.
Source: Stacks Project, Limits Tag 01ZR, first proof, affine case, and Modules on
Schemes Tag 01I6, together with pullback pasting.
(blueprint: lem-pc-affine-chart-sections-colimit-comparison).

Proof: Index the stages by the upper tail above i. Form the diagram of the affine
schemes obtained by pulling the fixed chart V.X a back along Spec(R_j) to Spec(R_i).
The maps are the unique maps of pullbacks induced by the transition maps of R;
uniqueness proves their identity and composition laws. Applying global sections
contravariantly gives F. Pullback pasting gives the ring isomorphism e at each
stage to the chart of the pulled-back cover. For any index k a common upper bound
of i and k shows that the upper-tail inclusion is final; its opposite is initial.
Thus the original limit cone restricts to a limit on the upper tail. Lift this
cone to schemes over Spec(R_i), using its cone equations. The base-change functor
Over.pullback is a right adjoint, so preserves limits. Forgetting the over structure
preserves this connected limit: the tail is nonempty and directed. All the resulting
charts are affine: the base maps have affine source
and target. The affine spectrum/global-sections equivalence therefore identifies
the fixed limit chart ring with colimit F, giving q. Pullback pasting also gives
an isomorphism from the iterated limit chart Y to the fixed limit chart Z. Its
global-sections map is s; compatibility with the stage projection gives the stated
ring-map equation: if h : Y -> Z is this isomorphism and r_j : Z -> U.X a is
the stage projection, then h followed by r_j is U.pullbackHom p a. Thus applying
global sections gives precisely colimit.ι F j followed by q.hom and s.hom.
The two maps from these limit charts to the ambient limit scheme commute with h.
Functoriality of module pullback consequently identifies the pullback of the
restriction on Z with the restriction on Y. Since
the chart comparison is an isomorphism, its sections are scalar extension along
s.hom, giving the final module isomorphism. More explicitly, inverse image along h
is reindexing opens, so its sections over top are the original sections over top.
Its ring-sheaf comparison is invertible; extension along the induced ring isomorphism
is transport of the module action. This uses no quasi-coherence. The upper tail
contains i; empty charts, zero rings, zero modules, and equivalent preorder indices
cause no exception. -/
theorem exists_affine_chart_sections_colimit_comparison
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u})
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt]
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    (M : (pullback f (c.π.app (op i))).Modules)
    (V : Xi.OpenCover.{u}) (a : V.I₀) (ha : IsAffine (V.X a)) :
    let W := V.pullback₁ (pullback.fst f (c.π.app (op i)))
    let Z := W.X a
    let N := ModuleCat.of Γ(Z, ⊤) Γ((Scheme.Modules.pullback (W.f a)).obj M, ⊤)
    ∃ F : {j : I // i ≤ j} ⥤ CommRingCat.{u},
      ∃ q : colimit F ≅ Γ(Z, ⊤),
      ∀ j : {j : I // i ≤ j},
        let U : (pullback f (Spec.map (R.map (homOfLE j.property)))).OpenCover.{u} :=
          V.pullback₁ (pullback.fst f (Spec.map (R.map (homOfLE j.property))))
        let p := baseChangeMap f
          (T := Over.mk (Spec.map (R.map (homOfLE j.property))))
          (T' := Over.mk (c.π.app (op i)))
          (Over.homMk (c.π.app (op j.val)) (c.w (homOfLE j.property).op))
        let Y := (U.pullback₁ p).X a
        let P := (Scheme.Modules.pullback ((U.pullback₁ p).f a)).obj M
        ∃ (e : F.obj j ≅ Γ(U.X a, ⊤)) (s : Γ(Z, ⊤) ≅ Γ(Y, ⊤)),
          colimit.ι F j ≫ q.hom ≫ s.hom = e.hom ≫ (U.pullbackHom p a).appTop ∧
          Nonempty ((ModuleCat.extendScalars s.hom.hom).obj N ≅
            ModuleCat.of Γ(Y, ⊤) Γ(P, ⊤)) := by
  classical
  dsimp
  obtain ⟨F, q, hcompare⟩ := exists_affine_chart_ring_colimit_geometric R c hc i f V a ha
  refine ⟨F, q, ?_⟩
  intro j
  obtain ⟨e, h, hg, hmap⟩ := hcompare j
  refine ⟨e, Scheme.Γ.mapIso h.op, hmap, ?_⟩
  exact nonempty_module_sections_pullback_iso_transport h _ _ hg M


end AlgebraicGeometry
