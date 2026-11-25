/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.AlgebraicGeometry.ProEtale.SequentialLimit
import Mathlib.CategoryTheory.CofilteredSystem

/-! # Covers mapping to finite etale towers
Source: Stacks Project, Tags 01YW and 0990; finite-stalk adaptation of Tag 09BV.
(blueprint: lem-weil-pbc-finite-etale-tower-cone-cover).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
private theorem seqLimit_lift {S : Scheme.{u}}
    (W : ℕ → S.AffineProEt) (π : ∀ n, W (n + 1) ⟶ W n)
    (T : Scheme.{u}) (a : ∀ n, T ⟶ (W n).left)
    (ha : ∀ n, a (n + 1) ≫ (π n).left = a n) :
    ∃ l : T ⟶ (AffineProEt.seqLimit W π).left,
      ∀ n, l ≫ (AffineProEt.seqLimitπ W π n).left = a n := by
  let c : Cocone (AffineProEt.ringSeq W π) :=
    Cocone.mk Γ(T, ⊤) (NatTrans.ofSequence (fun n ↦ (a n).appTop) (by
      intro n
      rw [AffineProEt.ringSeq_map_succ]
      change (π n).left.appTop ≫ (a (n + 1)).appTop = (a n).appTop ≫ 𝟙 _
      rw [Category.comp_id, ← Scheme.Hom.comp_appTop, ha]))
  refine ⟨T.toSpecΓ ≫ Spec.map (colimit.desc _ c), ?_⟩
  intro n
  change (T.toSpecΓ ≫ Spec.map (colimit.desc _ c)) ≫
    (Spec.map (colimit.ι _ n) ≫ (W n).left.isoSpec.inv) = a n
  rw [Category.assoc, ← Spec.map_comp_assoc, colimit.ι_desc]
  change T.toSpecΓ ≫ Spec.map (a n).appTop ≫ (W n).left.isoSpec.inv = a n
  rw [← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc]
  simp

set_option backward.isDefEq.respectTransparency false in
private theorem seqLimit_surjective {S : Scheme.{u}}
    (W : ℕ → S.AffineProEt) (π : ∀ n, W (n + 1) ⟶ W n)
    (hp : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω]
      (s : Spec (.of Ω) ⟶ S) (n : ℕ),
      Finite (Over.mk s ⟶ Over.mk (W n).hom) ∧
      Nonempty (Over.mk s ⟶ Over.mk (W n).hom)) :
    Surjective (AffineProEt.seqLimit W π).hom := by
  classical
  constructor
  intro y
  let Ω := SeparableClosure (S.residueField y)
  let s : Spec (.of Ω) ⟶ S := Spec.map
    (CommRingCat.ofHom (algebraMap (S.residueField y) Ω)) ≫ S.fromSpecResidueField y
  let D := Functor.ofOpSequence π ⋙
    MorphismProperty.Over.forget _ _ S ⋙ coyoneda.obj (op (Over.mk s))
  have (n : ℕᵒᵖ) : Finite (D.obj n) := (hp Ω s n.unop).1
  have (n : ℕᵒᵖ) : Nonempty (D.obj n) := (hp Ω s n.unop).2
  obtain ⟨a, ha⟩ := nonempty_sections_of_finite_inverse_system D
  have hsucc (n : ℕ) : (a (op (n + 1))).left ≫ (π n).left = (a (op n)).left := by
    have h := ha (homOfLE (Nat.le_succ n)).op
    change a (op (n + 1)) ≫ (MorphismProperty.Over.forget _ _ S).map
      ((Functor.ofOpSequence π).map (homOfLE (Nat.le_succ n)).op) = a (op n) at h
    rw [Functor.ofOpSequence_map_homOfLE_succ] at h
    exact congrArg Over.Hom.left h
  obtain ⟨l, hl⟩ := seqLimit_lift W π _ (fun n ↦ (a (op n)).left) hsucc
  have hw : l ≫ (AffineProEt.seqLimit W π).hom = s := by
    rw [← MorphismProperty.Over.w (AffineProEt.seqLimitπ W π 0), ← Category.assoc, hl]
    exact (a (op 0)).w
  refine ⟨l (default : Spec (.of Ω)), ?_⟩
  change (l ≫ (AffineProEt.seqLimit W π).hom) (default : Spec (.of Ω)) = y
  rw [hw]
  exact S.fromSpecResidueField_apply y _

set_option backward.isDefEq.respectTransparency false in
/-- A finite etale tower with finite nonempty geometric fibers has a compatible
cone whose legs to the base form a pro-etale cover.
Source: Stacks Project, Tags 01YW and 0990; finite-stalk adaptation of Tag 09BV.
(blueprint: lem-weil-pbc-finite-etale-tower-cone-cover).
Proof: Pull the tower back to each affine open of X. Its affine inverse limit is
Spec of the direct limit of the rings, and is weakly etale because the rings are
ind-etale. At a geometric point, finite inverse-system compactness gives compatible
points of all stages, hence a point of the affine limit by its limit property.
Thus the limit is surjective over the affine open and its singleton covers.
Compose these singleton covers with the affine open cover of X. The limit
projections are the required compatible maps. No contractible refinement is asserted. -/
theorem finite_etale_tower_cone_cover
    (X : Scheme.{u}) (P : ℕ → X.Etale) (p : ∀ n : ℕ, P (n + 1) ⟶ P n)
    (hfin : ∀ n : ℕ, IsFinite (P n).hom)
    (hpoints : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω]
      (x : Spec (.of Ω) ⟶ X) (n : ℕ),
      Finite ((pointSmallEtale x).fiber.obj (P n)) ∧
        Nonempty ((pointSmallEtale x).fiber.obj (P n))) :
    ∃ (J : Type u) (U : J → X.ProEt),
      Presieve.ofArrows (fun j ↦ (U j).left) (fun j ↦ (U j).hom) ∈
          proetalePrecoverage X ∧
      ∃ a : ∀ (j : J) (n : ℕ), U j ⟶ (toProEt X).obj (P n),
        ∀ (j : J) (n : ℕ), a j (n + 1) ≫ (toProEt X).map (p n) = a j n := by
  classical
  have (n : ℕ) : IsFinite (P n).hom := hfin n
  let A := X.affineCover
  have (j : A.I₀) : IsAffine (A.X j) := by dsimp [A]; infer_instance
  let W (j : A.I₀) (n : ℕ) : (A.X j).AffineProEt :=
    .ofEtale (pullback.snd (P n).hom (A.f j))
  let π (j : A.I₀) (n : ℕ) : W j (n + 1) ⟶ W j n :=
    MorphismProperty.Over.homMk
      (pullback.map _ _ _ _ (p n).left (𝟙 _) (𝟙 _) (by simp) (by simp)) (by
        change _ ≫ pullback.snd (P n).hom (A.f j) =
          pullback.snd (P (n + 1)).hom (A.f j)
        simp)
  have hp (j : A.I₀) (Ω : Type u) [Field Ω] [IsSepClosed Ω]
      (s : Spec (.of Ω) ⟶ A.X j) (n : ℕ) :
      Finite (Over.mk s ⟶ Over.mk (W j n).hom) ∧
      Nonempty (Over.mk s ⟶ Over.mk (W j n).hom) := by
    let g : (Over.mk s ⟶ Over.mk (W j n).hom) →
        (pointSmallEtale (s ≫ A.f j)).fiber.obj (P n) := fun f ↦
      Over.homMk (f.left ≫ pullback.fst _ _) (by
        change (f.left ≫ pullback.fst (P n).hom (A.f j)) ≫ (P n).hom = s ≫ A.f j
        have hf : f.left ≫ pullback.snd (P n).hom (A.f j) = s := f.w
        rw [Category.assoc, pullback.condition, ← Category.assoc, hf])
    have hg : Function.Injective g := by
      intro f k h
      apply Over.OverMorphism.ext
      apply pullback.hom_ext
      · exact congrArg Over.Hom.left h
      · exact f.w.trans k.w.symm
    have hf := (hpoints Ω (s ≫ A.f j) n).1
    have hn := (hpoints Ω (s ≫ A.f j) n).2
    refine ⟨Finite.of_injective g hg, ?_⟩
    obtain ⟨t⟩ := hn
    exact ⟨Over.homMk (pullback.lift t.left s t.w) (by
      change pullback.lift t.left s t.w ≫ pullback.snd _ _ = s
      simp)⟩
  let L (j : A.I₀) := AffineProEt.seqLimit (W j) (π j)
  have hsurj (j : A.I₀) : Surjective (L j).hom := seqLimit_surjective _ _ (hp j)
  let C : Cover.{u} proetalePrecoverage X := A.weaken
    (zariskiPrecoverage_le_propQCPrecoverage (P := @WeaklyEtale))
  have hqc (j : A.I₀) : QuasiCompact (L j).hom := by
    have ha : IsAffine (L j).left := inferInstance
    have hf : IsAffineHom (L j).hom :=
      @isAffineHom_of_isAffine (L j).left (A.X j) (L j).hom ha inferInstance
    infer_instance
  let D (j : A.I₀) : Cover.{0} proetalePrecoverage (A.X j) :=
    .singleton (L j).hom
      (Hom.singleton_mem_propQCPrecoverage (proAffineEtale_le_weaklyEtale _ (L j).prop))
  let V := C.bind D
  have hwe (i : V.I₀) : WeaklyEtale (V.f i) := Cover.map_prop (Cover.forgetQc V) i
  let U (i : V.I₀) : X.ProEt := ProEt.mk (V.f i)
  let b (i : V.I₀) (n : ℕ) : U i ⟶ (toProEt X).obj (P n) :=
    MorphismProperty.Over.homMk
      ((AffineProEt.seqLimitπ (W i.1) (π i.1) n).left ≫ pullback.fst _ _) (by
        change ((AffineProEt.seqLimitπ (W i.1) (π i.1) n).left ≫
          pullback.fst (P n).hom (A.f i.1)) ≫ (P n).hom = (L i.1).hom ≫ A.f i.1
        rw [Category.assoc, pullback.condition, ← Category.assoc]
        exact congrArg (fun f ↦ f ≫ A.f i.1)
          (MorphismProperty.Over.w (AffineProEt.seqLimitπ (W i.1) (π i.1) n)))
  refine ⟨V.I₀, U, V.mem₀, b, ?_⟩
  intro i n
  apply MorphismProperty.Over.Hom.ext
  change ((AffineProEt.seqLimitπ (W i.1) (π i.1) (n + 1)).left ≫
    pullback.fst _ _) ≫ (p n).left =
      (AffineProEt.seqLimitπ (W i.1) (π i.1) n).left ≫ pullback.fst _ _
  have hh := congrArg (fun f ↦ f.left ≫ pullback.fst (P n).hom (A.f i.1))
    (AffineProEt.seqLimitπ_comp (W := W i.1) (π := π i.1) n)
  change ((AffineProEt.seqLimitπ (W i.1) (π i.1) (n + 1)).left ≫
    (π i.1 n).left) ≫ pullback.fst (P n).hom (A.f i.1) = _ at hh
  change ((AffineProEt.seqLimitπ (W i.1) (π i.1) (n + 1)).left ≫
    pullback.map (P (n + 1)).hom (A.f i.1) (P n).hom (A.f i.1)
      (p n).left (𝟙 _) (𝟙 _) (by simp) (by simp)) ≫ pullback.fst (P n).hom (A.f i.1) = _ at hh
  simpa only [Category.assoc, pullback.map, pullback.lift_fst] using hh

end AlgebraicGeometry.Scheme
