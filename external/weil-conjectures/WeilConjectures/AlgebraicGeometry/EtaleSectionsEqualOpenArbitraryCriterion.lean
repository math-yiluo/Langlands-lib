/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.EtaleSectionsEqualOpen
import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageRestriction

/-! # Agreement-open criteria for arbitrary scheme maps
Source: Stacks Project, Tag 09XM, and Tag 03S2.
(blueprint: lem-weil-pbc-etale-sections-equal-open-arbitrary-criterion). -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

private noncomputable def canonicalSection {S T : Scheme.{u}}
    (F : Sheaf S.smallEtaleTopology (Type (u + 1))) (Q : S.Etale)
    (p : T ⟶ Q.left) (w : T ⟶ S) (hw : p ≫ Q.hom = w)
    (x : F.obj.obj (op Q)) :=
  ((Scheme.etaleSetPullback w).obj F).obj.map
    (MorphismProperty.Over.homMk
      (A := Scheme.Etale.mk (𝟙 T))
      (B := (MorphismProperty.Over.pullback @Etale ⊤ w).obj Q)
      (pullback.lift p (𝟙 T) (hw.trans (Category.id_comp w).symm))
      (by simp)).op
    (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (MorphismProperty.Over.pullback @Etale ⊤ w) (Type (u + 1))
      (S.smallGrothendieckTopology @Etale)
      (T.smallGrothendieckTopology @Etale)).unit.app F).hom.app (op Q) x)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem canonicalSection_etale_eq_iff
    (S : Scheme.{u}) (F : Sheaf S.smallEtaleTopology (Type (u + 1)))
    (Q A : S.Etale) (m : A ⟶ Q)
    (w : A.left ⟶ S) (hw : m.left ≫ Q.hom = w) (s t : F.obj.obj (op Q)) :
    canonicalSection F Q m.left w hw s =
        canonicalSection F Q m.left w hw t ↔
      F.obj.map m.op s = F.obj.map m.op t := by
  have hwa : w = A.hom := hw.symm.trans (by simp)
  subst hwa
  let O := Scheme.Etale.mk (𝟙 A.left)
  let β := MorphismProperty.Over.pullback @Etale ⊤ A.hom
  let : β.IsContinuous (S.smallGrothendieckTopology @Etale)
      (A.left.smallGrothendieckTopology @Etale) := Etale.isContinuous_overPullback A.hom
  let H := (Scheme.etaleSetPullback A.hom).obj F
  let η := ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    β (Type (u + 1)) (S.smallGrothendieckTopology @Etale)
    (A.left.smallGrothendieckTopology @Etale)).unit.app F).hom.app (op Q)
  let d : O ⟶ β.obj Q := MorphismProperty.Over.homMk
    (pullback.lift m.left (𝟙 A.left) (hw.trans (Category.id_comp _).symm))
    (by change pullback.lift m.left (𝟙 A.left) _ ≫ pullback.snd Q.hom A.hom = 𝟙 A.left
        simp)
  let M := MorphismProperty.Over.map ⊤ (inferInstance : Etale A.hom)
  let ε := (MorphismProperty.Over.mapPullbackAdj @Etale ⊤ A.hom
    inferInstance trivial).counit.app Q
  let z : M.obj O ≅ A := MorphismProperty.Over.isoMk (Iso.refl A.left)
    (by simp [M, O])
  have hd : M.map d ≫ ε = z.hom ≫ m := by
    apply MorphismProperty.Over.Hom.ext
    simp only [M, d, ε, z, MorphismProperty.Over.mapPullbackAdj_counit_app,
      MorphismProperty.Over.map_map_left,
      MorphismProperty.Comma.comp_hom, MorphismProperty.Over.homMk_hom,
      Comma.comp_left, Over.homMk_left, MorphismProperty.Over.isoMk_hom_left,
      Iso.refl_hom, pullback.lift_fst]
    change m.left = 𝟙 A.left ≫ m.left
    exact (Category.id_comp _).symm
  obtain ⟨ρ, hρ⟩ := etaleSetInverseImageRestriction A.hom
  let χ := (ρ.hom.app F).hom.app (op O)
  let α := F.obj.map z.hom.op
  have hχ : Function.Injective χ := CategoryTheory.injective_of_mono χ
  have hα : Function.Injective α := CategoryTheory.injective_of_mono α
  have hsection (x : F.obj.obj (op Q)) :
      χ (H.obj.map d.op (η x)) = α (F.obj.map m.op x) := by
    have hn := ConcreteCategory.congr_hom ((ρ.hom.app F).hom.naturality d.op) (η x)
    change χ (H.obj.map d.op (η x)) =
      F.obj.map (M.map d).op ((ρ.hom.app F).hom.app (op (β.obj Q)) (η x)) at hn
    have hρx : (ρ.hom.app F).hom.app (op (β.obj Q)) (η x) =
        F.obj.map ε.op x := hρ F Q x
    rw [hρx] at hn
    have hm : F.obj.map ε.op ≫ F.obj.map (M.map d).op =
        F.obj.map m.op ≫ α := by
      rw [← F.obj.map_comp, ← op_comp, hd, op_comp, F.obj.map_comp]
    exact hn.trans (ConcreteCategory.congr_hom hm x)
  have heq : H.obj.map d.op (η s) = H.obj.map d.op (η t) ↔
      F.obj.map m.op s = F.obj.map m.op t := by
    constructor
    · intro h
      apply hα
      rw [← hsection s, ← hsection t, h]
    · intro h
      apply hχ
      rw [hsection s, hsection t, h]
  exact heq

private theorem range_iff_factors {X T : Scheme.{u}} (E : X.Opens) (a : T ⟶ X) :
    Set.range a ⊆ (E : Set X) ↔ ∃ b : T ⟶ E.toScheme, b ≫ E.ι = a := by
  constructor
  · intro h
    exact ⟨IsOpenImmersion.lift E.ι a (by simpa using h),
      IsOpenImmersion.lift_fac _ _ _⟩
  · rintro ⟨b, hb⟩ x ⟨y, rfl⟩
    have hy := congrArg (fun f : T ⟶ X ↦ f y) hb
    rw [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply] at hy
    rw [← hy]
    exact (b y).property

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Source: Stacks Project, Tag 09XM, and Tag 03S2.
(blueprint: lem-weil-pbc-etale-sections-equal-open-arbitrary-criterion).

Proof: Choose the canonical agreement open W with its arbitrary-map criterion.
For an étale test map, the inverse-image restriction isomorphism and unit
naturality identify canonical restriction equality with ordinary restriction
equality. Thus W and E satisfy the same ordinary criterion. Test the open
immersions of E and W to get both inclusions, so E = W. Replace factorization
through this open by range containment using the open-immersion lift.
This works for empty schemes and for identical sections. -/
theorem etaleSections_equal_open_arbitrary_criterion
    (S : Scheme.{u}) (F : Sheaf S.smallEtaleTopology (Type (u + 1)))
    (Q : S.Etale) (s t : F.obj.obj (op Q)) (E : Q.left.Opens)
    (hE : ∀ (A : S.Etale) (m : A ⟶ Q),
      Set.range m.left ⊆ (E : Set Q.left) ↔ F.obj.map m.op s = F.obj.map m.op t) :
    ∀ (T : Scheme.{u}) (a : T ⟶ Q.left),
      let H := (Scheme.etaleSetPullback (a ≫ Q.hom)).obj F
      let δ : Scheme.Etale.mk (𝟙 T) ⟶
          (MorphismProperty.Over.pullback @Etale ⊤ (a ≫ Q.hom)).obj Q :=
        MorphismProperty.Over.homMk
          (pullback.lift a (𝟙 T) (Category.id_comp (a ≫ Q.hom)).symm)
          (pullback.lift_snd _ _ _)
      let η := ((@Functor.sheafPullbackConstruction.sheafAdjunctionContinuous _ _ _ _
        (MorphismProperty.Over.pullback @Etale ⊤ (a ≫ Q.hom)) (Type (u + 1)) _
        (S.smallGrothendieckTopology @Etale)
        (T.smallGrothendieckTopology @Etale)
        (Etale.isContinuous_overPullback (a ≫ Q.hom)) _ _).unit.app F).hom.app (op Q)
      Set.range a ⊆ (E : Set Q.left) ↔ H.obj.map δ.op (η s) = H.obj.map δ.op (η t) := by
  classical
  obtain ⟨W, hW, _⟩ := existsUnique_etaleSections_equal_open S F Q s t
  have hW' (A : S.Etale) (m : A ⟶ Q) :
      Set.range m.left ⊆ (W : Set Q.left) ↔ F.obj.map m.op s = F.obj.map m.op t := by
    have hf := (range_iff_factors W m.left).trans (hW A.left m.left)
    change Set.range m.left ⊆ (W : Set Q.left) ↔
      canonicalSection F Q m.left (m.left ≫ Q.hom) rfl s =
        canonicalSection F Q m.left (m.left ≫ Q.hom) rfl t at hf
    exact hf.trans (canonicalSection_etale_eq_iff S F Q A m (m.left ≫ Q.hom) rfl s t)
  have hle (U W : Q.left.Opens)
      (h : ∀ (A : S.Etale) (m : A ⟶ Q),
        Set.range m.left ⊆ (U : Set Q.left) → Set.range m.left ⊆ (W : Set Q.left)) :
      U ≤ W := by
    let A := Scheme.Etale.mk (U.ι ≫ Q.hom)
    let m : A ⟶ Q := MorphismProperty.Over.homMk U.ι (by dsimp [A])
    have hU : Set.range m.left ⊆ (U : Set Q.left) := by
      change Set.range U.ι ⊆ (U : Set Q.left)
      rw [Scheme.Opens.range_ι]
    have hW := h A m hU
    intro x hx
    exact hW ⟨⟨x, hx⟩, rfl⟩
  have hEW : E = W := le_antisymm
    (hle E W (fun A m h ↦ (hW' A m).mpr ((hE A m).mp h)))
    (hle W E (fun A m h ↦ (hE A m).mpr ((hW' A m).mp h)))
  intro T a
  simpa only [hEW] using (range_iff_factors W a).trans (hW T a)

end AlgebraicGeometry
