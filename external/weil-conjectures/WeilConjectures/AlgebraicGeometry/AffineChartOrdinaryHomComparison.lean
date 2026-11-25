/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.AlgebraicGeometry.ChartOrdinaryMapRecovery
public import WeilConjectures.AlgebraicGeometry.AffineChartUpperTailLimitData
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Order.Antisymmetrization
import WeilConjectures.AlgebraicGeometry.AffineChartCanonicalHomNaturality

/-! # Hom comparisons for the explicit affine chart ring diagram

Source: Stacks Project, Tags 01ZR (affine proof), 01I6, 0095 and 0096.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The partial-order quotient of the upper tail, with no selected descent object.
(blueprint: lem-pc-affine-chart-ordinary-hom-comparison)
-/
abbrev OrdinaryChartTail (I : Type u) [Preorder I] (j : I) :=
  Antisymmetrization {k : I // j ≤ k} (· ≤ ·)

/-- A representative in the upper tail; equivalent indices give isomorphic charts.
(blueprint: lem-pc-affine-chart-ordinary-hom-comparison)
-/
noncomputable def ordinaryChartRep {I : Type u} [Preorder I] (j : I) :
    OrdinaryChartTail I j ⥤ {k : I // j ≤ k} :=
  (OrderEmbedding.ofAntisymmetrization (α := {k : I // j ≤ k})).monotone.functor

/-- The starting class in the upper tail.
(blueprint: lem-pc-affine-chart-ordinary-hom-comparison)
-/
def ordinaryChartStart {I : Type u} [Preorder I] (j : I) : OrdinaryChartTail I j :=
  toAntisymmetrization (· ≤ ·) (⟨j, le_rfl⟩ : {k : I // j ≤ k})

/-- Global sections of the explicit pullback diagram, reindexed by the quotient.
(blueprint: lem-pc-affine-chart-ordinary-hom-comparison)
-/
noncomputable def ordinaryChartRings {I : Type u} [Preorder I]
    (R : I ⥤ CommRingCat.{u}) (j : I) {A : Scheme.{u}} (g : A ⟶ Spec (R.obj j)) :
    OrdinaryChartTail I j ⥤ CommRingCat.{u} :=
  ordinaryChartRep j ⋙ (upperTailChartDiagram R j g).rightOp ⋙ Scheme.Γ

/-- Sections of the actual ordinary pullback of M at the starting representative.
(blueprint: lem-pc-affine-chart-ordinary-hom-comparison)
-/
noncomputable def ordinaryChartBaseModule {I : Type u} [Preorder I]
    (R : I ⥤ CommRingCat.{u}) (j : I) {A : Scheme.{u}} (g : A ⟶ Spec (R.obj j))
    (M : A.Modules) : ModuleCat.{u} ((ordinaryChartRings R j g).obj
      (ordinaryChartStart j)) :=
  by
    let k := (ordinaryChartRep j).obj (ordinaryChartStart j)
    let r := Spec.map (R.map (homOfLE k.property))
    change ModuleCat.{u} Γ(pullback r g, ⊤)
    exact ModuleCat.of _ Γ((Scheme.Modules.pullback (pullback.snd r g)).obj M, ⊤)

/-- Ordinary affine Hom sets agree with scalar-extension Hom sets, including the
composition comparison. This asserts comparisons only, not descent of any map.
Source: Stacks Project, Tags 01ZR (affine proof), 01I6, 0095 and 0096.
(blueprint: lem-pc-affine-chart-ordinary-hom-comparison).

Proof: Put A = U.X a and g = U.f a followed by the projection to Spec R(j).
The explicitly defined upperTailChartDiagram consists of the pullbacks of A
along the tail spectra. Each chart is affine, by affine base change. The tail
is nonempty and final, and its partial-order quotient is equivalent to it.
The upperTailChartCone is limiting; applying affine global sections identifies
its vertex ring with the colimit of ordinaryChartRings. Pullback pasting
identifies this vertex with the direct limit chart and identifies each stage
with U pulled back to that stage. The starting representative is equivalent
to j, so its chart is canonically isomorphic to A. Under the affine
quasi-coherent module equivalence the concrete ordinaryChartBaseModule is
therefore the starting module, and its scalar extensions are the sections of
all ordinary pullbacks. Fully faithfulness gives the two Hom equivalences.
For the final assertion, the normalized eP,eQ equal the scalar-extension
composition isomorphisms: both take 1 tensor m to 1 tensor (1 tensor m), and
these elements generate after scalar extension. The algebraic square therefore
transports to the ordinary pullback square. Pulling it back along the canonical
lift from the iterated chart to the direct chart and using its second-projection
equation gives exactly chartOrdinaryMapRecovery. The comparisons are all
universal-property comparisons, so equivalent indices, zero rings, empty affine
charts and zero modules require no extra hypotheses. No finite-presentation
assumption or map-descent conclusion is used in this comparison lemma. -/
theorem affine_chart_ordinary_hom_comparison
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u})
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt]
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    (j : I) (hij : i ≤ j)
    (U : (pullback f (Spec.map (R.map (homOfLE hij)))).OpenCover.{u})
    (a : U.I₀) (ha : IsAffine (U.X a))
    (M N : (U.X a).Modules)
    (hMq : M.IsQuasicoherent)
    (hNq : N.IsQuasicoherent)
    :
    let g := U.f a ≫ pullback.snd f (Spec.map (R.map (homOfLE hij)))
    let F := ordinaryChartRings R j g
    let t := ordinaryChartStart j
    let P := ordinaryChartBaseModule R j g M
    let Q := ordinaryChartBaseModule R j g N
    let r₀ := (colimit.ι F t).hom
    let q₀ := baseChangeMap f
      (T := Over.mk (Spec.map (R.map (homOfLE hij))))
      (T' := Over.mk (c.π.app (op i)))
      (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))
    ∃ α : ((ModuleCat.extendScalars r₀).obj P ⟶
        (ModuleCat.extendScalars r₀).obj Q) ≃
      ((Scheme.Modules.pullback (U.pullbackHom q₀ a)).obj M ⟶
        (Scheme.Modules.pullback (U.pullbackHom q₀ a)).obj N),
      ∀ (x : OrdinaryChartTail I j) (htx : t ≤ x),
        let k := ((ordinaryChartRep j).obj x).val
        let hjk := ((ordinaryChartRep j).obj x).property
        let q := baseChangeMap f
          (T := Over.mk (Spec.map (R.map (homOfLE hij))))
          (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
          (Over.homMk (Spec.map (R.map (homOfLE hjk)))
            (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))
        let p := baseChangeMap f
          (T := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
          (T' := Over.mk (c.π.app (op i)))
          (Over.homMk (c.π.app (op k)) (c.w (homOfLE (hij.trans hjk)).op))
        let q₀ := baseChangeMap f
          (T := Over.mk (Spec.map (R.map (homOfLE hij))))
          (T' := Over.mk (c.π.app (op i)))
          (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))
        let w : p ≫ q = q₀ := by
          rw [← baseChangeMap_comp]
          congr 1
          ext
          simpa using c.w (homOfLE hjk).op
        let r := (F.map (homOfLE htx)).hom
        let r₁ := (colimit.ι F x).hom
        ∃ β : ((ModuleCat.extendScalars r).obj P ⟶
            (ModuleCat.extendScalars r).obj Q) ≃
          ((Scheme.Modules.pullback (U.pullbackHom q a)).obj M ⟶
            (Scheme.Modules.pullback (U.pullbackHom q a)).obj N),
          ∀ (φ : (ModuleCat.extendScalars r₀).obj P ⟶
              (ModuleCat.extendScalars r₀).obj Q)
            (s : (ModuleCat.extendScalars r).obj P ⟶
              (ModuleCat.extendScalars r).obj Q)
            (eP : (ModuleCat.extendScalars r₀).obj P ≅
              (ModuleCat.extendScalars r₁).obj ((ModuleCat.extendScalars r).obj P))
            (eQ : (ModuleCat.extendScalars r₀).obj Q ≅
              (ModuleCat.extendScalars r₁).obj ((ModuleCat.extendScalars r).obj Q)),
            (∀ m : P, eP.hom ((1 : ↑(colimit F)) ⊗ₜ[F.obj t, r₀] m) =
              (1 : ↑(colimit F)) ⊗ₜ[F.obj x, r₁] ((1 : ↑(F.obj x)) ⊗ₜ[F.obj t, r] m)) →
            (∀ n : Q, eQ.hom ((1 : ↑(colimit F)) ⊗ₜ[F.obj t, r₀] n) =
              (1 : ↑(colimit F)) ⊗ₜ[F.obj x, r₁] ((1 : ↑(F.obj x)) ⊗ₜ[F.obj t, r] n)) →
            φ ≫ eQ.hom = eP.hom ≫ (ModuleCat.extendScalars r₁).map s →
            chartOrdinaryMapRecovery q p q₀ w U a M N (α φ) (β s) := by
  classical
  let g := U.f a ≫ pullback.snd f (Spec.map (R.map (homOfLE hij)))
  let F := ordinaryChartRings R j g
  let t := ordinaryChartStart j
  let P := ordinaryChartBaseModule R j g M
  let Q := ordinaryChartBaseModule R j g N
  obtain ⟨α, hα⟩ := affine_chart_canonical_hom_naturality
    R c hc i f j hij U a ha M N hMq hNq
  refine ⟨α, ?_⟩
  intro x htx
  obtain ⟨β, hβ⟩ := hα x htx
  refine ⟨β, ?_⟩
  intro φ s eP eQ hP hQ hs
  have heP : eP = colimitScalarExtensionComp F (homOfLE htx) P := by
    apply Iso.ext
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    exact (hP m).trans (colimitScalarExtensionComp_one_tmul F (homOfLE htx) P m).symm
  have heQ : eQ = colimitScalarExtensionComp F (homOfLE htx) Q := by
    apply Iso.ext
    apply ModuleCat.ExtendScalars.hom_ext
    intro n
    exact (hQ n).trans (colimitScalarExtensionComp_one_tmul F (homOfLE htx) Q n).symm
  have hφ : φ = (colimitScalarExtensionComp F (homOfLE htx) P).hom ≫
      (ModuleCat.extendScalars (colimit.ι F x).hom).map s ≫
      (colimitScalarExtensionComp F (homOfLE htx) Q).inv := by
    calc
      φ = (φ ≫ eQ.hom) ≫ eQ.inv := by simp
      _ = (eP.hom ≫ (ModuleCat.extendScalars (colimit.ι F x).hom).map s) ≫
          eQ.inv := by rw [hs]
      _ = _ := by rw [heP, heQ]; rfl
  rw [hφ]
  exact hβ s

end AlgebraicGeometry
