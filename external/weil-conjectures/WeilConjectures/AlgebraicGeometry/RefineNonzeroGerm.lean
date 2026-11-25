/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
/-! # RefineNonzeroGerm

Source: blueprint `lem-weil-pbc-lisse-generic-kernel`, first proof step.
(blueprint: lem-weil-pbc-refine-nonzero-germ) -/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
set_option backward.isDefEq.respectTransparency false in
/-- Refinement of a pointed nonzero germ over a locally constant set sheaf.
Source: blueprint `lem-weil-pbc-locally-constant-nonzero-germs`, proof steps 2--4.
A trivialising etale cover and filtered-colimit equality refine the section so
that its germ is nonzero at every geometric point of the refinement.
(blueprint: lem-weil-pbc-refine-nonzero-germ)

Proof:
1. Choose a member of the trivialising etale cover through the marked geometric
   point; surjectivity of the geometric fibre gives a lift to that member.
   Pull back U along this member and restrict a and the zero section.
2. The set-sheaf trivialisation identifies their distinct marked germs with two
   distinct elements m and z of its constant value. Constant-sheaf stalks are
   this value, since sheafification preserves stalks and the pointed
   neighbourhood category is nonempty and connected.
3. Filtered-colimit equality yields pointed refinements on which a is the
   constant section m and zero is the constant section z. Take a common
   refinement V of these two refinements, and let r be its composite to U.
4. The retained marked point proves V is nonempty. At each geometric lift to V,
   the constant-sheaf stalk formula identifies the two restricted germs with
   m and z. They are distinct, so the germ of the restriction of a is nonzero.
   Only a set-sheaf trivialisation is used; addition need not be preserved. -/
theorem refine_section_nonzero_germs (X : Scheme.{u})
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : IsLocallyConstantEtaleSheafOfSets
      ((sheafCompose X.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj F))
    (U : X.Etale) (a : F.obj.obj (op U))
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ X) (v : (pointSmallEtale t).fiber.obj U)
    (ha : (pointSmallEtale t).toPresheafFiber U v F.obj a ≠ 0) :
    ∃ (V : X.Etale) (r : V ⟶ U), Nonempty V.left ∧
      ∀ (Ω' : Type u) [Field Ω'] [IsAlgClosed Ω']
        (t' : Spec (.of Ω') ⟶ X) (v' : (pointSmallEtale t').fiber.obj V),
        (pointSmallEtale t').toPresheafFiber V v' F.obj
          (F.obj.map r.op a) ≠ 0 := by
  classical
  -- Work in a set-sheaf chart; it need not preserve the group structure.
  let G := (sheafCompose X.smallEtaleTopology
    (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj F
  let Φ := pointSmallEtale t
  have : JointlySurjective etalePrecoverage := by
    unfold etalePrecoverage
    infer_instance
  obtain ⟨𝒰, hc⟩ := hF
  obtain ⟨i, x, hx⟩ := 𝒰.exists_eq (t default)
  let Ui := 𝒰.etalePrecoverageToEtale i
  have : Etale (𝒰.f i) := 𝒰.map_prop i
  obtain ⟨l, hl, -⟩ := exists_fac_of_etale_of_isSepClosed (𝒰.f i) t x hx
  have : Etale U.hom := U.prop
  let W₁ : X.Etale := Etale.mk (pullback.fst U.hom (𝒰.f i) ≫ U.hom)
  let g₁ : W₁ ⟶ U := MorphismProperty.Over.homMk (pullback.fst U.hom (𝒰.f i))
  let h₁ : W₁ ⟶ Ui := MorphismProperty.Over.homMk (pullback.snd U.hom (𝒰.f i))
    pullback.condition.symm
  let w₁ : Φ.fiber.obj W₁ := Over.homMk
    (pullback.lift v.left l (v.w.trans hl.symm)) (by
      change pullback.lift v.left l _ ≫
        (pullback.fst U.hom (𝒰.f i) ≫ U.hom) = t
      rw [pullback.lift_fst_assoc]
      exact v.w)
  have hw₁ : Φ.fiber.map g₁ w₁ = v := by
    apply Over.OverMorphism.ext
    change pullback.lift v.left l _ ≫ pullback.fst U.hom (𝒰.f i) = v.left
    exact pullback.lift_fst _ _ _
  have := hc i
  obtain ⟨M, ⟨e₀⟩⟩ := (G.over Ui).mem_essImage_of_isConstant
    (J := X.smallEtaleTopology.over Ui)
  let N := (constantSheaf X.smallEtaleTopology (Type (u + 1))).obj M
  let e : G.over Ui ≅ N.over Ui :=
    e₀.symm ≪≫ constantSheafOverIso X.smallEtaleTopology (Type (u + 1)) Ui M
  let η := toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj M)
  have hnat {W W' : Over Ui} (k : W' ⟶ W) (b : G.obj.obj (op W.left)) :
      e.hom.hom.app (op W') (G.obj.map k.left.op b) =
        N.obj.map k.left.op (e.hom.hom.app (op W) b) :=
    NatTrans.naturality_apply e.hom.hom k.op b
  let W₁' : Over Ui := Over.mk h₁
  let c := e.hom.hom.app (op W₁') (F.obj.map g₁.op a)
  -- First make the section constant, then make the image of zero constant.
  have hsurj := (X.smallEtaleTopology.W_toSheafify
    ((Functor.const X.Etaleᵒᵖ).obj M)).isLocallySurjective
  obtain ⟨W₂, g₂, ⟨m, hm⟩, w₂, hw₂⟩ := Φ.jointly_surjective _
    (Presheaf.imageSieve_mem X.smallEtaleTopology η c) w₁
  let W₂' : Over Ui := Over.mk (g₂ ≫ h₁)
  let zc := e.hom.hom.app (op W₂') (0 : F.obj.obj (op W₂))
  obtain ⟨V, g₃, ⟨z, hz⟩, w₃, hw₃⟩ := Φ.jointly_surjective _
    (Presheaf.imageSieve_mem X.smallEtaleTopology η zc) w₂
  let r := g₃ ≫ g₂ ≫ g₁
  let q := g₃ ≫ g₂ ≫ h₁
  let V' : Over Ui := Over.mk q
  have haV : e.hom.hom.app (op V') (F.obj.map r.op a) = η.app (op V) m := by
    have hr : r = (g₃ ≫ g₂) ≫ g₁ := (Category.assoc _ _ _).symm
    rw [hr, op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
    change e.hom.hom.app (op V') (G.obj.map (g₃ ≫ g₂).op
      (F.obj.map g₁.op a)) = _
    have h := hnat (W := W₁') (W' := V')
      (Over.homMk (g₃ ≫ g₂) (Category.assoc _ _ _)) (F.obj.map g₁.op a)
    change e.hom.hom.app (op V') (G.obj.map (g₃ ≫ g₂).op
      (F.obj.map g₁.op a)) = N.obj.map (g₃ ≫ g₂).op c at h
    rw [h]
    change N.obj.map (g₃ ≫ g₂).op c = _
    rw [op_comp, Functor.map_comp, types_comp_apply]
    erw [← hm]
    exact (NatTrans.naturality_apply η g₃.op m).symm
  have hzV : e.hom.hom.app (op V') (0 : F.obj.obj (op V)) = η.app (op V) z := by
    have h := hnat (W := W₂') (W' := V') (Over.homMk g₃)
      (0 : F.obj.obj (op W₂))
    change e.hom.hom.app (op V') (F.obj.map g₃.op 0) = N.obj.map g₃.op zc at h
    simpa only [map_zero] using h.trans hz.symm
  have hinj : Function.Injective (e.hom.hom.app (op V')) :=
    ((sheafToPresheaf _ _).mapIso e).app (op V') |>.toEquiv.injective
  have hmz : m ≠ z := by
    intro hmz
    have hzero : F.obj.map r.op a = 0 := hinj (by rw [haV, hzV, hmz])
    apply ha
    have h := ConcreteCategory.congr_hom (Φ.toPresheafFiber_w r w₃ F.obj) a
    rw [ConcreteCategory.comp_apply, hzero, map_zero] at h
    have hr : Φ.fiber.map r w₃ = v := by
      dsimp only [r]
      rw [Functor.map_comp, Functor.map_comp]
      change Φ.fiber.map g₁ (Φ.fiber.map g₂ (Φ.fiber.map g₃ w₃)) = v
      rw [hw₃, hw₂]
      exact hw₁
    simpa only [hr] using h.symm
  refine ⟨V, r, ⟨w₃.left (default : Spec (.of Ω))⟩, ?_⟩
  intro Ω' _ _ t' v' hzero
  let Ψ := pointSmallEtale t'
  have : PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  -- Any vanishing germ yields equality on a pointed refinement.
  have heq : Ψ.toPresheafFiber V v' F.obj (F.obj.map r.op a) =
      Ψ.toPresheafFiber V v' F.obj 0 := by simpa only [map_zero] using hzero
  obtain ⟨W, g, w, -, hg⟩ := (Ψ.toPresheafFiber_eq_iff' V v' _ _).1 heq
  have heq' : η.app (op W) m = η.app (op W) z := by
    have haW := hnat (W := V') (W' := Over.mk (g ≫ q)) (Over.homMk g)
      (F.obj.map r.op a)
    have hzW := hnat (W := V') (W' := Over.mk (g ≫ q)) (Over.homMk g)
      (0 : F.obj.obj (op V))
    change e.hom.hom.app (op (Over.mk (g ≫ q))) (F.obj.map g.op (F.obj.map r.op a)) = _ at haW
    change e.hom.hom.app (op (Over.mk (g ≫ q))) (F.obj.map g.op 0) = _ at hzW
    rw [hg] at haW
    rw [haV] at haW
    rw [hzV] at hzW
    have h := haW.symm.trans hzW
    change N.obj.map g.op (η.app (op V) m) = N.obj.map g.op (η.app (op V) z) at h
    exact (NatTrans.naturality_apply η g.op (m : M)).trans
      (h.trans (NatTrans.naturality_apply η g.op (z : M)).symm)
  -- Local injectivity of sheafification detects equality of constant values.
  have hmem := Presheaf.equalizerSieve_mem X.smallEtaleTopology η
    (X := op W) (m : M) (z : M) heq'
  obtain ⟨W', f, hf, w', -⟩ := Ψ.jointly_surjective _ hmem w
  exact hmz hf
end AlgebraicGeometry.Scheme
