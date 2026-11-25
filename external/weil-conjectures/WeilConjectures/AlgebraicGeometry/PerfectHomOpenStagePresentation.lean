/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectHomPushPullCocone
public import WeilConjectures.AlgebraicGeometry.DerivedMayerVietorisCanonicalData
import WeilConjectures.AlgebraicGeometry.PerfectHomOpenStageData
import WeilConjectures.AlgebraicGeometry.PerfectHomOpenStageMaps

/-! # Local presentations of shifted open Hom systems

Source: Stacks Project, Tags 09RE, 079W, 08FE and 0D5S.
(blueprint: lem-pc-perfect-hom-open-stage-presentation).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace AlgebraicGeometry

/-- Restriction of a representing Hom system to one compact open, before taking
any colimit. This supplies stage and apex equivalences and their transport equations;
it makes no assertion about group colimits, Mayer--Vietoris families or continuity.

Source: Stacks Project, perfect.tex Tag 09RE (open-local Hom comparison),
cohomology.tex Tags 079W, 08FE and 0D5S.
(blueprint: lem-pc-perfect-hom-open-stage-presentation).

Proof:
1. Put B = t inverse-image W and Z = B.toScheme, k = B.ι followed by t,
and s' = B.ι followed by s. Since W lies in the image of t, k has image W.
The source Y is compact (s is quasi-compact with affine target), and X is
quasi-separated (s₀ is quasi-separated with affine target). Thus t is
quasi-compact, B is compact, and its open inclusion is quasi-compact.
The maps s' are locally finitely presented and qcqs by composition. Transport
localized derived categories through the open-site equivalence.
2. Let L be derived restriction to B. Construct P' = (L P)[-n] and Q' = L Q.
For perfectness restrict each bounded finite-free retract model termwise to
smaller opens: restriction preserves the unit, finite sums and retract equations.
Shifting translates the finite bounds and preserves each term's retract. For every j
the natural equivalences
h.stageEquiv identify F_j with Rpi_j* Lpi_j*Q by derived adjunction and Yoneda.
The same construction identifies d.pt with the limit direct image. Their
stageMap and limitMap equations, evaluated at identity morphisms, determine
all representing arrows; stageNatural and limitNatural then identify their action
on every Hom set. No arbitrary representative object is chosen.
3. Restrict these identifications to B using the right-derived comparison for
open restriction and direct image (Tag 08FE). Its underived comparison is the
sectionwise identity, and its derived comparison is pinned by the right-derived
unit. The cartesian open restriction of each pi_j is the base-change projection
for s'. Open adjunction and the direct-image shift comparison identify
Hom(P, Rk_B* L F_j[n]) with Hom(L P[-n], L F_j), and derived adjunction
identifies the latter with Hom(Lpi'_j* P', Lpi'_j* Q'). Compose these
bijections to obtain e_j, and use the same construction at the apex for b.
4. Naturality of the open adjunction, shift comparison and restriction/direct-image
comparison transports h.stageMap and h.limitMap to the two displayed equations.
The pullback composition comparisons used here are the counit-pinned ones defining
perfectStageMap and perfectLimitMap, so these are equalities for the specified
transport maps, not merely existence of some commuting maps. For an empty open all
Hom groups are zero; the same adjunctions and comparisons still apply. -/
theorem perfect_hom_open_stage_presentation
    {I : Type u} [Preorder I]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R)
    (i : I) (X : Scheme.{u}) (s₀ : X ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation s₀] [QuasiCompact s₀] [QuasiSeparated s₀]
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (W : X.Opens) (hW : IsCompact (W : Set X))
    (Y : Scheme.{u}) (t : Y ⟶ X) [IsOpenImmersion t]
    (ht : W ≤ t.opensRange)
    (s : Y ⟶ Spec (R.obj i)) (hs : s = t ≫ s₀)
    [LocallyOfFinitePresentation s] [QuasiCompact s] [QuasiSeparated s]
    [∀ B : Y.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over B))]
    (P Q : schemeDerivedCategory Y) (hP : Y.IsPerfect P) (hQ : Y.IsPerfect Q)
    (F : Set.Ici i ⥤ schemeDerivedCategory Y) (d : Cocone F)
    (h : PerfectHomPushPullData R c s Q F d) (n : ℤ) :
    let H := schemeMVDerivedRestriction Y (t ⁻¹ᵁ W) ⋙
      schemeDerivedDirectImage (t ⁻¹ᵁ W).ι
    ∃ (Z : Scheme.{u}) (k : Z ⟶ X) (_ : IsOpenImmersion k),
      k.opensRange = W ∧
    ∃ (s' : Z ⟶ Spec (R.obj i)), s' = k ≫ s₀ ∧
    ∃ (_ : LocallyOfFinitePresentation s') (_ : QuasiCompact s') (_ : QuasiSeparated s')
      (_ : ∀ T : Z.Opens,
        HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over T)))
      (P' Q' : schemeDerivedCategory Z), Z.IsPerfect P' ∧ Z.IsPerfect Q' ∧
    ∃ (e : ∀ j : Set.Ici i, (P ⟶ (H.obj (F.obj j))⟦n⟧) ≃
        ((derivedPullback (pullback.fst s' (Spec.map (R.map (homOfLE j.property))))).obj P' ⟶
         (derivedPullback (pullback.fst s' (Spec.map (R.map (homOfLE j.property))))).obj Q'))
      (b : (P ⟶ (H.obj d.pt)⟦n⟧) ≃
        ((derivedPullback (pullback.fst s' (Spec.map (c.ι.app i)))).obj P' ⟶
         (derivedPullback (pullback.fst s' (Spec.map (c.ι.app i)))).obj Q')),
      (∀ (j l : Set.Ici i) (hjl : j ≤ l) (f : P ⟶ (H.obj (F.obj j))⟦n⟧),
        e l (f ≫ (H.map (F.map (homOfLE hjl)))⟦n⟧') =
          perfectStageMap R s' j.property hjl (e j f)) ∧
      (∀ (j : Set.Ici i) (f : P ⟶ (H.obj (F.obj j))⟦n⟧),
        b (f ≫ (H.map (d.ι.app j))⟦n⟧') =
          perfectLimitMap R c s' j.property (e j f)) := by
  classical
  dsimp
  let B := t ⁻¹ᵁ W
  have hcomp : QuasiCompact (t ≫ s₀) := hs ▸ inferInstance
  have : QuasiCompact t := QuasiCompact.of_comp t s₀
  have hB : IsCompact (B : Set Y) := t.isCompact_preimage hW
  let : CompactSpace B.toScheme := isCompact_iff_compactSpace.mp hB
  have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated s
  have : QuasiCompact B.ι := inferInstance
  obtain ⟨hcat, hp', hq'⟩ := Scheme.perfect_hom_open_stage_data Y B P Q hP hQ n
  let := hcat
  refine ⟨B.toScheme, B.ι ≫ t, inferInstance, ?_, B.ι ≫ s, ?_,
    inferInstance, inferInstance, inferInstance, hcat,
    ((schemeMVDerivedRestriction Y B).obj P)⟦-n⟧,
    (schemeMVDerivedRestriction Y B).obj Q, hp', hq', ?_⟩
  · rw [Scheme.Hom.opensRange_comp, Scheme.Opens.opensRange_ι,
      Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right.mpr ht]
  · rw [hs, Category.assoc]
  · exact perfect_hom_open_stage_maps R c i X W Y t s P Q F d h n

end AlgebraicGeometry
