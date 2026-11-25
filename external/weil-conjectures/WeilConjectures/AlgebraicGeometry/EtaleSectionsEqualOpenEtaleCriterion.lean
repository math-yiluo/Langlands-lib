/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Etale
import WeilConjectures.AlgebraicGeometry.EtaleSectionsEqualOpen
import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageRestriction

/-! # Agreement opens tested by ordinary étale restriction
Source: Stacks Project, Tag 09XM, and Tag 03S2.
(blueprint: lem-weil-pbc-etale-sections-equal-open-etale-criterion). -/

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

private theorem canonicalSection_eq_iff {S T : Scheme.{u}}
    (F : Sheaf S.smallEtaleTopology (Type (u + 1))) (Q : S.Etale)
    (p : T ⟶ Q.left) (w : T ⟶ S) (hw : p ≫ Q.hom = w)
    (s t : F.obj.obj (op Q)) :
    canonicalSection F Q p (p ≫ Q.hom) rfl s =
        canonicalSection F Q p (p ≫ Q.hom) rfl t ↔
      canonicalSection F Q p w hw s = canonicalSection F Q p w hw t := by
  subst w
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Source: Stacks Project, Tag 09XM (lemma-where-sections-are-equal),
with Tag 03S2 identifying inverse image along an étale map with restriction.
(blueprint: lem-weil-pbc-etale-sections-equal-open-etale-criterion).

Proof: Apply the largest agreement-open theorem to F, Q, s and t. For an étale
object A and m : A → Q, the composite m.left ≫ Q.hom equals A.hom. The inverse
image restriction isomorphism for A.hom identifies canonical pullback along
(m.left,id) with F.map m.op, by unit naturality and the counit formula of the
restriction isomorphism. Its component is injective, so it reflects equality.
Factorization through the open is equivalent to range containment: evaluate a
factorization on points for one implication and use the open immersion lift for
the other. Empty A imposes no condition; equal sections give the top open. -/
theorem exists_etaleSections_equal_open_etale_criterion
    (S : Scheme.{u}) (F : Sheaf S.smallEtaleTopology (Type (u + 1)))
    (Q : S.Etale) (s t : F.obj.obj (op Q)) :
    ∃ E : Q.left.Opens, ∀ (A : S.Etale) (m : A ⟶ Q),
      Set.range m.left ⊆ (E : Set Q.left) ↔ F.obj.map m.op s = F.obj.map m.op t := by
  classical
  obtain ⟨E, hE, _⟩ := existsUnique_etaleSections_equal_open S F Q s t
  refine ⟨E, ?_⟩
  intro A m
  have hw : m.left ≫ Q.hom = A.hom := by simp
  have hf := hE A.left m.left
  change (∃ b : A.left ⟶ E.toScheme, b ≫ E.ι = m.left) ↔
    canonicalSection F Q m.left (m.left ≫ Q.hom) rfl s =
      canonicalSection F Q m.left (m.left ≫ Q.hom) rfl t at hf
  rw [canonicalSection_eq_iff F Q m.left A.hom hw s t] at hf
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
  change (∃ b : A.left ⟶ E.toScheme, b ≫ E.ι = m.left) ↔
    H.obj.map d.op (η s) = H.obj.map d.op (η t) at hf
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
  have hopen : Set.range m.left ⊆ (E : Set Q.left) ↔
      ∃ b : A.left ⟶ E.toScheme, b ≫ E.ι = m.left := by
    constructor
    · intro h
      exact ⟨IsOpenImmersion.lift E.ι m.left (by simpa using h),
        IsOpenImmersion.lift_fac _ _ _⟩
    · rintro ⟨b, hb⟩ x ⟨y, rfl⟩
      have hy := congrArg (fun f : A.left ⟶ Q.left ↦ f y) hb
      rw [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply] at hy
      rw [← hy]
      exact (b y).property
  exact hopen.trans (hf.trans heq)

end AlgebraicGeometry
