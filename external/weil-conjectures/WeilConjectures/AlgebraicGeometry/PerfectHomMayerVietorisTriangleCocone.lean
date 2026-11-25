/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Grp.Colimits
public import WeilConjectures.AlgebraicGeometry.PerfectHomLocalComparison
public import WeilConjectures.AlgebraicGeometry.PerfectHomTriangleRow
import WeilConjectures.AlgebraicGeometry.PerfectHomMayerVietorisColumns
import WeilConjectures.AlgebraicGeometry.DerivedMayerVietorisFunctorial

/-! # Coherent Mayer--Vietoris triangle cocones before forming Hom rows

Source: Stacks Project, Tags 09RE and 08BW.
(blueprint: lem-pc-perfect-hom-mayer-vietoris-triangle-cocone).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits Pretriangulated TopologicalSpace
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxSize 2048 in

/-- A geometric cocone of distinguished triangles in D(O_Y), obtained by pushing
stage Mayer--Vietoris triangles to Y. Central Hom identifications are pinned to
canonical pullback transport. The four outer column comparisons are local.
No abelian-group row, zero-composite witness, or short-complex presentation is
supplied by this statement.

Source: Stacks Project, Tags 09RE and 08BW.
(blueprint: lem-pc-perfect-hom-mayer-vietoris-triangle-cocone).

Proof:
1. The maps s and s₀ are qcqs over affine schemes. Thus Y is compact and
   quasi-separated, and X is quasi-separated. The open immersion t is quasi-compact.
   Pulling back U,V gives compact opens covering Y, because t has range U union V.
2. Use perfect_hom_pushPull_cocone to construct the coherent representing cocone
   F,d₀ of quasi-coherent derived objects on Y. Its Hom equivalences are natural in
   every testing object, with transitions pinned to perfectStageMap and legs pinned
   to perfectLimitMap. This construction uses adjunction and Yoneda, not continuity.
3. Apply schemeDerived_mayerVietoris_naturality on the pulled-back cover. Its
   adjunctions, boundary, distinguishedness and prescribed morphism components form
   a PerfectHomMVFamily A. The proved constructors A.diagram and A.cocone give D,d;
   identity, composition and cocone laws follow from equality of the three components.
   Distinguishedness follows objectwise from A.distinguished and quasi-coherence.
4. Compose the representing Hom equivalences with ULift and the zero-shift
   isomorphism. Naturality of shiftFunctorZero transports shifted postcomposition to
   ordinary postcomposition. The two representing equations give the required stage
   and limit formulas, without an additional coherence assumption.
5. Use perfect_hom_mayerVietoris_geometric_columns on this actual family and
   representing cocone. It identifies the four outer column comparisons via open
   adjunction, shifts, filtered set colimits and products. Arbitrary triangle cocones
   are not eligible for this step: both their outer objects and maps must be those
   of the geometric family. No exactness or continuity theorem is used. -/
theorem perfect_hom_mayerVietoris_triangle_cocone
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R)
    (i : I) (X : Scheme.{u}) (s₀ : X ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation s₀] [QuasiCompact s₀] [QuasiSeparated s₀]
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (U V : X.Opens) (hU : IsCompact (U : Set X)) (hV : IsAffineOpen V)
    (Y : Scheme.{u}) (t : Y ⟶ X) [IsOpenImmersion t]
    (ht : t.opensRange = U ⊔ V)
    (s : Y ⟶ Spec (R.obj i)) (hs : s = t ≫ s₀)
    [LocallyOfFinitePresentation s] [QuasiCompact s] [QuasiSeparated s]
    [∀ W : Y.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over W))]
    (P Q : schemeDerivedCategory Y) (hP : Y.IsPerfect P) (hQ : Y.IsPerfect Q)
    : ∃ (D : Set.Ici i ⥤ Triangle (schemeDerivedCategory Y)) (d : Cocone D),
        (∀ j, D.obj j ∈ distTriang (schemeDerivedCategory Y)) ∧
        d.pt ∈ distTriang (schemeDerivedCategory Y) ∧
        ∃ (e : ∀ j : Set.Ici i, ULift.{u} (P ⟶ (D.obj j).obj₁⟦(0 : ℤ)⟧) ≃
          ((derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE j.property))))).obj P ⟶
           (derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE j.property))))).obj Q))
          (b : ULift.{u} (P ⟶ d.pt.obj₁⟦(0 : ℤ)⟧) ≃
          ((derivedPullback (pullback.fst s (Spec.map (c.ι.app i)))).obj P ⟶
           (derivedPullback (pullback.fst s (Spec.map (c.ι.app i)))).obj Q)),
        (∀ (j k : Set.Ici i) (hjk : j ≤ k)
          (f : ULift.{u} (P ⟶ (D.obj j).obj₁⟦(0 : ℤ)⟧)),
          e k ⟨f.down ≫ (D.map (homOfLE hjk)).hom₁⟦(0 : ℤ)⟧'⟩ =
            perfectStageMap R s j.property hjk (e j f)) ∧
        (∀ (j : Set.Ici i) (f : ULift.{u} (P ⟶ (D.obj j).obj₁⟦(0 : ℤ)⟧)),
          b ⟨f.down ≫ (d.ι.app j).hom₁⟦(0 : ℤ)⟧'⟩ =
            perfectLimitMap R c s j.property (e j f)) ∧
        ∀ (r : Fin 5), r.val ≠ 2 →
          PerfectHomLocalMap R c i X s₀ U V
            (colimit.desc ((D ⋙ perfectHomTriangleRowFunctor Y P).flip.obj r)
              ⟨(perfectHomTriangleRow Y P d.pt).obj r,
                (perfectHomTriangleRowCoconeMap Y P D d).app r⟩) := by
  classical
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace s
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated s₀
  have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated s
  have hU' : IsCompact ((t ⁻¹ᵁ U) : Set Y) := t.isCompact_preimage hU
  have hV' : IsCompact ((t ⁻¹ᵁ V) : Set Y) := t.isCompact_preimage hV.isCompact
  have hcover : (t ⁻¹ᵁ U) ⊔ (t ⁻¹ᵁ V) = ⊤ := by
    rw [← Scheme.Hom.preimage_sup, ← ht, Scheme.Hom.preimage_opensRange]
  obtain ⟨F, d₀, ⟨h⟩⟩ := perfect_hom_pushPull_cocone R c s Q hQ
  obtain ⟨adjU, adjV, adjUV, δ, hdist, hnat⟩ :=
    schemeDerived_mayerVietoris_naturality Y (t ⁻¹ᵁ U) (t ⁻¹ᵁ V) hU' hV' hcover
  let A : PerfectHomMVFamily Y (t ⁻¹ᵁ U) (t ⁻¹ᵁ V) :=
    ⟨adjU, adjV, adjUV, δ, hdist, hnat⟩
  let D := A.diagram F h.stageQCoh
  let d := A.cocone F d₀ h.stageQCoh h.limitQCoh
  let z := shiftFunctorZero (schemeDerivedCategory Y) ℤ
  let e (j : Set.Ici i) := Equiv.ulift.trans
    (((z.app (F.obj j)).homToEquiv).trans (h.stageEquiv j P))
  let b := Equiv.ulift.trans ((z.app d₀.pt).homToEquiv.trans (h.limitEquiv P))
  refine ⟨D, d, ?_, ?_, e, b, ?_, ?_, ?_⟩
  · intro j
    exact A.distinguished (F.obj j) (h.stageQCoh j)
  · exact A.distinguished d₀.pt h.limitQCoh
  · intro j k hjk f
    change ULift.{u} (P ⟶ (F.obj j)⟦(0 : ℤ)⟧) at f
    change h.stageEquiv k P
      ((f.down ≫ (A.map (h.stageQCoh j) (h.stageQCoh k)
        (F.map (homOfLE hjk))).hom₁⟦(0 : ℤ)⟧') ≫ z.hom.app (F.obj k)) = _
    rw [A.map_hom₁]
    have hn := z.hom.naturality (F.map (homOfLE hjk))
    dsimp only [CategoryTheory.Functor.id_map] at hn
    have he := congrArg (fun a ↦ f.down ≫ a) hn
    rw [Category.assoc, he, ← Category.assoc]
    exact h.stageMap j k hjk P (f.down ≫ z.hom.app (F.obj j))
  · intro j f
    change ULift.{u} (P ⟶ (F.obj j)⟦(0 : ℤ)⟧) at f
    change h.limitEquiv P
      ((f.down ≫ (A.map (h.stageQCoh j) h.limitQCoh
        (d₀.ι.app j)).hom₁⟦(0 : ℤ)⟧') ≫ z.hom.app d₀.pt) = _
    rw [A.map_hom₁]
    have hn := z.hom.naturality (d₀.ι.app j)
    change (d₀.ι.app j)⟦(0 : ℤ)⟧' ≫ z.hom.app d₀.pt =
      z.hom.app (F.obj j) ≫ d₀.ι.app j at hn
    have he := congrArg (fun a ↦ f.down ≫ a) hn
    rw [Category.assoc, he, ← Category.assoc]
    exact h.limitMap j P (f.down ≫ z.hom.app (F.obj j))
  · exact perfect_hom_mayerVietoris_geometric_columns R c i X s₀ U V hU hV
      Y t ht s hs P Q hP hQ F d₀ h A

end AlgebraicGeometry
