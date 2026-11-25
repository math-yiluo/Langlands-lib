/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.AlgebraicGeometry.TensorPullbackCompositionIso
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.Noetherian.Basic
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackUnit
public import WeilConjectures.AlgebraicGeometry.OpenCoverTensorPullbackComparison
import WeilConjectures.AlgebraicGeometry.FinitePresentationOneChartMapLift
import Mathlib.Data.Finset.Order
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Affine local lifts of fixed-model maps

Source: Stacks Project, Limits, Tag 01ZR, first proof.
(blueprint: lem-pc-fp-local-map-lifts).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Local components of a map lift on a finite affine cover at one stage.
This statement imposes no overlap equations on the lifted components.
Source: Stacks Project, Limits, Tag 01ZR, first proof, affine map lifting;
Algebra, Tag 05N7 (2).
(blueprint: lem-pc-fp-local-map-lifts).

Proof: Choose a finite affine cover of Xj, using quasi-compactness over Spec Rj.
Its inverse images at later stages and at the limit are affine. On a chart,
quasi-coherent sheaves and pullback identify with modules and scalar extension.
The stage coordinate rings have colimit the limit chart ring: they are tensor
products of the fixed chart ring with the stage base rings, and tensor products
commute with this colimit. Apply the map clause of finitePresentation_descent_directedColimit
on each chart, passing through the partial-order quotient of the directed preorder.
There are finitely many charts; choose a common upper bound and pull the local maps
there. Composition comparisons transport their scalar-extension equations to the
displayed recovery equations. The comparison e is explicitly the canonical tensor
pullback composition comparison, so no choice of comparison is needed. No agreement
on overlaps has been imposed. Empty charts have unique maps; an empty cover requires
no lifts and j itself is an upper bound. The zero ring and zero modules cause no
exception. -/
theorem exists_finitePresentation_local_map_lifts
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u})
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt]
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f] :
    (∀ (j : I) (hij : i ≤ j) (Fj Gj : (pullback f (Spec.map (R.map (homOfLE hij)))).Modules),
      Fj.IsFinitePresentation → Fj.IsQuasicoherent →
      Gj.IsFinitePresentation → Gj.IsQuasicoherent →
      ∀ φ : (Scheme.Modules.moduleBaseChange f
            (T := Over.mk (Spec.map (R.map (homOfLE hij))))
            (T' := Over.mk (c.π.app (op i)))
            (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))).obj Fj ⟶
          (Scheme.Modules.moduleBaseChange f
            (T := Over.mk (Spec.map (R.map (homOfLE hij))))
            (T' := Over.mk (c.π.app (op i)))
            (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))).obj Gj,
      ∃ (j' : I) (hjj' : j ≤ j'),
        let A := Scheme.Modules.moduleBaseChange f
            (T := Over.mk (Spec.map (R.map (homOfLE hij))))
            (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjj')))))
            (Over.homMk (Spec.map (R.map (homOfLE hjj')))
              (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))
        let B := Scheme.Modules.moduleBaseChange f
              (T := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjj')))))
              (T' := Over.mk (c.π.app (op i)))
              (Over.homMk (c.π.app (op j')) (c.w (homOfLE (hij.trans hjj')).op))
        ∃ e : Scheme.Modules.moduleBaseChange f
            (T := Over.mk (Spec.map (R.map (homOfLE hij))))
            (T' := Over.mk (c.π.app (op i)))
            (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op)) ≅ A ⋙ B,
          e = Scheme.Modules.tensorPullbackCompositionIso
            (baseChangeMap f
              (T := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjj')))))
              (T' := Over.mk (c.π.app (op i)))
              (Over.homMk (c.π.app (op j')) (c.w (homOfLE (hij.trans hjj')).op)))
            (baseChangeMap f
              (T := Over.mk (Spec.map (R.map (homOfLE hij))))
              (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjj')))))
              (Over.homMk (Spec.map (R.map (homOfLE hjj')))
                (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl)))
            (baseChangeMap f
              (T := Over.mk (Spec.map (R.map (homOfLE hij))))
              (T' := Over.mk (c.π.app (op i)))
              (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op)))
            (by
              rw [← baseChangeMap_comp]
              congr 1
              ext
              simpa using c.w (homOfLE hjj').op) ∧
        ∃ U : (pullback f (Spec.map (R.map (homOfLE (hij.trans hjj'))))).OpenCover.{u},
          Finite U.I₀ ∧ (∀ a, IsAffine (U.X a)) ∧
          let Q := modulesPseudofunctor.toDescentData U.f
          let p := baseChangeMap f
            (T := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjj')))))
            (T' := Over.mk (c.π.app (op i)))
            (Over.homMk (c.π.app (op j')) (c.w (homOfLE (hij.trans hjj')).op))
          let V := U.pullback₁ p
          ∃ r : ∀ a, (Q.obj (A.obj Fj)).obj a ⟶ (Q.obj (A.obj Gj)).obj a,
            ∀ a,
              let t := Scheme.Modules.openCoverTensorPullbackComparison p U a
              t.inv.app (A.obj Fj) ≫ (Scheme.Modules.pullback
                (U.pullbackHom p a)).map (r a) ≫ t.hom.app (A.obj Gj) =
              (Scheme.Modules.pullback (V.f a)).map
                (e.inv.app Fj ≫ φ ≫ e.hom.app Gj)) := by
  classical
  intro j hij Fj Gj hF hFq hG hGq φ
  let Xj := pullback f (Spec.map (R.map (homOfLE hij)))
  let : CompactSpace Xj :=
    QuasiCompact.compactSpace_of_compactSpace
      (pullback.snd f (Spec.map (R.map (homOfLE hij))))
  let Uj : Xj.OpenCover.{u} := Xj.affineCover.finiteSubcover
  have one (a : Uj.I₀) := finitePresentation_one_chart_map_lift_eventually
    R c hc i f j hij Fj Gj hF hFq hG hGq φ Uj a (inferInstance)
  choose stage hstage hlift using one
  let : Nonempty I := ⟨j⟩
  obtain ⟨l, hl⟩ := (insert j (Finset.univ.image stage)).exists_le
  have hjl : j ≤ l := hl j (Finset.mem_insert_self _ _)
  let q := baseChangeMap f
    (T := Over.mk (Spec.map (R.map (homOfLE hij))))
    (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjl)))))
    (Over.homMk (Spec.map (R.map (homOfLE hjl)))
      (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))
  let U : (pullback f (Spec.map
    (R.map (homOfLE (hij.trans hjl))))).OpenCover.{u} := Uj.pullback₁ q
  let e := Scheme.Modules.tensorPullbackCompositionIso
            (baseChangeMap f
              (T := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjl)))))
              (T' := Over.mk (c.π.app (op i)))
              (Over.homMk (c.π.app (op l)) (c.w (homOfLE (hij.trans hjl)).op)))
            (baseChangeMap f
              (T := Over.mk (Spec.map (R.map (homOfLE hij))))
              (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjl)))))
              (Over.homMk (Spec.map (R.map (homOfLE hjl)))
                (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl)))
            (baseChangeMap f
              (T := Over.mk (Spec.map (R.map (homOfLE hij))))
              (T' := Over.mk (c.π.app (op i)))
              (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op)))
            (by
              rw [← baseChangeMap_comp]
              congr 1
              ext
              simpa using c.w (homOfLE hjl).op)
  refine ⟨l, hjl, e, rfl, U, ?_, ?_, ?_⟩
  · exact inferInstanceAs (Finite Uj.I₀)
  · intro a
    let : IsAffineHom (Spec.map (R.map (homOfLE hjl))) := inferInstance
    let : IsAffineHom q := MorphismProperty.of_isPullback
      (isPullback_baseChangeMap f _).flip (inferInstance :
        IsAffineHom (Spec.map (R.map (homOfLE hjl))))
    change IsAffine (pullback q (Uj.f a))
    infer_instance
  · have lifts (a : Uj.I₀) := hlift a l hjl (hl (stage a)
      (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩)))
    choose r hr using lifts
    exact ⟨r, hr⟩

end AlgebraicGeometry
