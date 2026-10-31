/-
The lemmas `fg_restrictScalars`, `isNoetherianRing_of_fg` and `specMap_comp` are adapted from
the lemmas `fg_restrictScalars`, `isNoetherianRing_of_fg` and `specMap_val_comp` of the namespace
`NoethModel17` in
`P2M/Sol/S_AlgebraicGeometry_exists_fg_subalgebra_isPullback_smooth_isProper_geometricallyConnected.lean`
of the Anthropic Lean formalization of Fermat's Last Theorem
(commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026 Anthropic, PBC, licensed under
the Apache License, Version 2.0; see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and
`ATTRIBUTION.md`. The rest of this file is not taken from that source.
-/
import Langlands.AlgebraicGeometry.Picard.AbelianSchemeNoetherianModelReductionStatement
import Langlands.AlgebraicGeometry.Picard.FamilyBaseChange

/-! # Noetherian models of an abelian scheme with two rigidified line bundles -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.Picard Langlands.AlgebraicGeometry.NoetherianApproximation
open Langlands.SchemeModule (structureModule)

namespace Langlands.AbelianScheme.NoetherianModelProof

variable {R : CommRingCat.{u}} {A : AbelianScheme (Spec R)}

/-- A tower of finitely generated subalgebras is finitely generated over `ℤ`. -/
theorem fg_restrictScalars (R₁ : Subalgebra ℤ R) (T : Subalgebra ↥R₁ R)
    (h₁ : R₁.FG) (h₂ : T.FG) : (T.restrictScalars ℤ).FG := by
  have i1 : Algebra.FiniteType ℤ ↥R₁ := (Subalgebra.fg_iff_finiteType _).1 h₁
  have i2 : Algebra.FiniteType ↥R₁ ↥T := (Subalgebra.fg_iff_finiteType _).1 h₂
  have i3 : Algebra.FiniteType ℤ ↥T := Algebra.FiniteType.trans i1 i2
  exact (Subalgebra.fg_iff_finiteType (T.restrictScalars ℤ)).2 i3

/-- A finitely generated subring is noetherian. -/
theorem isNoetherianRing_of_fg (R₁ : Subalgebra ℤ R) (h : R₁.FG) : IsNoetherianRing ↥R₁ := by
  have : Algebra.FiniteType ℤ ↥R₁ := (Subalgebra.fg_iff_finiteType _).1 h
  exact Algebra.FiniteType.isNoetherianRing ℤ ↥R₁

/-- The composite of the two base-change maps of a tower of subalgebras. -/
theorem specMap_comp (R₁ : Subalgebra ℤ R) (T : Subalgebra ↥R₁ R) :
    Spec.map (CommRingCat.ofHom (algebraMap ↥R₁ R)) =
      Spec.map (CommRingCat.ofHom (algebraMap ↥T R)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap ↥R₁ ↥T)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

/-- A stage: an abelian scheme over a finitely generated subring of `R` with a pullback
square from `A` that respects the unit sections. -/
structure ModelStage (A : AbelianScheme (Spec R)) where
  T : Subalgebra ℤ R
  fg : T.FG
  B : AbelianScheme (Spec (CommRingCat.of ↥T))
  a : A.X.left ⟶ B.X.left
  isPullback : IsPullback a A.X.hom B.X.hom (Spec.map (CommRingCat.ofHom (algebraMap ↥T R)))
  unit : unitSection A ≫ a = Spec.map (CommRingCat.ofHom (algebraMap ↥T R)) ≫ unitSection B

/-- The comparison map from `A` to the base change of a stage. -/
def ModelStage.stepMap (S : ModelStage A) (T' : Subalgebra ↥S.T R) :
    A.X.left ⟶ pullback S.B.X.hom (Spec.map (CommRingCat.ofHom (algebraMap ↥S.T ↥T'))) :=
  pullback.lift S.a (A.X.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥T' R))) (by
    rw [Category.assoc, ← specMap_comp, S.isPullback.w])

@[reassoc (attr := simp)]
theorem ModelStage.stepMap_fst (S : ModelStage A) (T' : Subalgebra ↥S.T R) :
    S.stepMap T' ≫ pullback.fst _ _ = S.a :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem ModelStage.stepMap_snd (S : ModelStage A) (T' : Subalgebra ↥S.T R) :
    S.stepMap T' ≫ pullback.snd _ _ =
      A.X.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥T' R)) :=
  pullback.lift_snd _ _ _

/-- Base change of a stage to a finitely generated subalgebra over its ring. -/
def ModelStage.step (S : ModelStage A) (T' : Subalgebra ↥S.T R) (hT' : T'.FG) :
    ModelStage A where
  T := T'.restrictScalars ℤ
  fg := fg_restrictScalars S.T T' S.fg hT'
  B := (AbelianScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap ↥S.T ↥T')))).obj S.B
  a := S.stepMap T'
  isPullback := by
    refine IsPullback.of_right (h₁₂ := pullback.fst S.B.X.hom
        (Spec.map (CommRingCat.ofHom (algebraMap ↥S.T ↥T'))))
      (h₂₂ := Spec.map (CommRingCat.ofHom (algebraMap ↥S.T ↥T'))) (v₁₃ := S.B.X.hom)
      ?_ (S.stepMap_snd T') (IsPullback.of_hasPullback _ _)
    have h := S.isPullback
    rw [← S.stepMap_fst T', specMap_comp S.T T'] at h
    exact h
  unit := by
    apply pullback.hom_ext
    · change (unitSection A ≫ S.stepMap T') ≫ pullback.fst _ _ =
        (Spec.map (CommRingCat.ofHom (algebraMap ↥T' R)) ≫
          unitSection ((AbelianScheme.baseChange
            (Spec.map (CommRingCat.ofHom (algebraMap ↥S.T ↥T')))).obj S.B)) ≫ pullback.fst _ _
      rw [Category.assoc, S.stepMap_fst, S.unit, Category.assoc,
        unitSection_baseChange_fst, ← Category.assoc, ← specMap_comp]
    · change (unitSection A ≫ S.stepMap T') ≫ pullback.snd _ _ =
        (Spec.map (CommRingCat.ofHom (algebraMap ↥T' R)) ≫
          unitSection ((AbelianScheme.baseChange
            (Spec.map (CommRingCat.ofHom (algebraMap ↥S.T ↥T')))).obj S.B)) ≫ pullback.snd _ _
      rw [Category.assoc, S.stepMap_snd, ← Category.assoc, unitSection_comp, Category.id_comp,
        Category.assoc]
      exact (Category.comp_id _).symm.trans (congrArg _ (unitSection_comp _).symm)

/-- Successive module pullbacks agree with the pullback along the composite. -/
def pullbackCompEq {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) {h : X ⟶ Z} (w : f ≫ g = h)
    (N : Z.Modules) :
    (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj N) ≅
      (Scheme.Modules.pullback h).obj N :=
  (Scheme.Modules.pullbackComp f g).app N ≪≫ (Scheme.Modules.pullbackCongr w).app N

/-- A locally free rank-one module on a stage whose pullback to `A` is `M`. -/
def Carried (S : ModelStage A) (M : A.X.left.Modules) (N : S.B.X.left.Modules) : Prop :=
  IsLocallyFreeRankOne N ∧ Nonempty ((Scheme.Modules.pullback S.a).obj N ≅ M)

/-- A module on a stage trivialized along the unit section. -/
def Trivialized (S : ModelStage A) (N : S.B.X.left.Modules) : Prop :=
  Nonempty (structureModule (Spec (CommRingCat.of ↥S.T)) ≅
    (Scheme.Modules.pullback (unitSection S.B)).obj N)

/-- The projection from a stepped stage to the stage. -/
abbrev ModelStage.proj (S : ModelStage A) (T' : Subalgebra ↥S.T R) (hT' : T'.FG) :
    (S.step T' hT').B.X.left ⟶ S.B.X.left :=
  pullback.fst S.B.X.hom (Spec.map (CommRingCat.ofHom (algebraMap ↥S.T ↥T')))

theorem Carried.step {S : ModelStage A} {M : A.X.left.Modules} {N : S.B.X.left.Modules}
    (h : Carried S M N) (T' : Subalgebra ↥S.T R) (hT' : T'.FG) :
    Carried (S.step T' hT') M ((Scheme.Modules.pullback (S.proj T' hT')).obj N) := by
  obtain ⟨hN, ⟨e⟩⟩ := h
  exact ⟨hN.pullback _,
    ⟨pullbackCompEq (S.step T' hT').a (S.proj T' hT') (S.stepMap_fst T') N ≪≫ e⟩⟩

theorem Trivialized.step {S : ModelStage A} {N : S.B.X.left.Modules} (h : Trivialized S N)
    (T' : Subalgebra ↥S.T R) (hT' : T'.FG) :
    Trivialized (S.step T' hT') ((Scheme.Modules.pullback (S.proj T' hT')).obj N) := by
  obtain ⟨α⟩ := h
  let g := Spec.map (CommRingCat.ofHom (algebraMap ↥S.T ↥T'))
  exact ⟨(Langlands.Scheme.Modules.pullbackUnitIso g).symm ≪≫
    (Scheme.Modules.pullback g).mapIso α ≪≫ pullbackCompEq g (unitSection S.B) rfl N ≪≫
    (pullbackCompEq (unitSection (S.step T' hT').B) (S.proj T' hT')
      (unitSection_baseChange_fst g S.B) N).symm⟩

/-- A line bundle on `A` comes from one on a stepped stage. -/
theorem exists_step_carried (hLB1 : LineBundleSubalgebraDescentStatement.{u})
    (S : ModelStage A) (M : A.X.left.Modules) (hM : IsLocallyFreeRankOne M) :
    ∃ (T' : Subalgebra ↥S.T R) (hT' : T'.FG) (N : (S.step T' hT').B.X.left.Modules),
      Carried (S.step T' hT') M N := by
  unfold LineBundleSubalgebraDescentStatement at hLB1
  obtain ⟨T', hT', -, N, hN, hc⟩ :=
    hLB1 (A₀ := ↥S.T) (A := R) S.B.X.hom S.a A.X.hom S.isPullback M hM (∅ : Finset R)
  exact ⟨T', hT', N, hN, hc (S.stepMap T') (S.stepMap_fst T') (S.stepMap_snd T')⟩

/-- A carried line bundle becomes trivial along the unit section on a stepped stage. -/
theorem exists_step_trivialized (hLB2 : LineBundleIsoSubalgebraDescentStatement.{u})
    (S : ModelStage A) (M : RigidifiedLineBundle (unitSection A)) {N : S.B.X.left.Modules}
    (h : Carried S M.obj.carrier N) :
    ∃ (T' : Subalgebra ↥S.T R) (hT' : T'.FG),
      Carried (S.step T' hT') M.obj.carrier ((Scheme.Modules.pullback (S.proj T' hT')).obj N) ∧
      Trivialized (S.step T' hT') ((Scheme.Modules.pullback (S.proj T' hT')).obj N) := by
  unfold LineBundleIsoSubalgebraDescentStatement at hLB2
  obtain ⟨hN, ⟨e⟩⟩ := h
  let b := Spec.map (CommRingCat.ofHom (algebraMap ↥S.T R))
  let ε := unitSection S.B
  have hsq : IsPullback b (𝟙 (Spec R)) (𝟙 (Spec (CommRingCat.of ↥S.T))) b :=
    IsPullback.of_vert_isIso ⟨(Category.comp_id _).trans (Category.id_comp _).symm⟩
  have hiso : Nonempty ((Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback ε).obj N) ≅
      (Scheme.Modules.pullback b).obj (structureModule (Spec (CommRingCat.of ↥S.T)))) :=
    ⟨pullbackCompEq b ε rfl N ≪≫ (Scheme.Modules.pullbackCongr S.unit.symm).app N ≪≫
      (pullbackCompEq (unitSection A) S.a rfl N).symm ≪≫
      (Scheme.Modules.pullback (unitSection A)).mapIso e ≪≫
      M.obj.rigidification.symm ≪≫ (Langlands.Scheme.Modules.pullbackUnitIso b).symm⟩
  obtain ⟨T', hT', -, hall⟩ := hLB2 (A₀ := ↥S.T) (A := R) (𝟙 (Spec (CommRingCat.of ↥S.T)))
    ((Scheme.Modules.pullback ε).obj N) (structureModule _) (hN.pullback ε)
    (LineBundle.trivial _).property b (𝟙 _) hsq hiso (∅ : Finset R)
  let g := Spec.map (CommRingCat.ofHom (algebraMap ↥S.T ↥T'))
  have hsq' : IsPullback g (𝟙 (Spec (CommRingCat.of ↥T'))) (𝟙 (Spec (CommRingCat.of ↥S.T))) g :=
    IsPullback.of_vert_isIso ⟨(Category.comp_id _).trans (Category.id_comp _).symm⟩
  obtain ⟨β⟩ := hall g (𝟙 _) hsq'
  refine ⟨T', hT', Carried.step ⟨hN, ⟨e⟩⟩ T' hT', ⟨?_⟩⟩
  exact (Langlands.Scheme.Modules.pullbackUnitIso g).symm ≪≫ β.symm ≪≫
    pullbackCompEq g ε rfl N ≪≫
    (pullbackCompEq (unitSection (S.step T' hT').B) (S.proj T' hT')
      (unitSection_baseChange_fst g S.B) N).symm

/-- The first stage, from a descent of the abelian scheme. -/
def stage₀ (R₀ : Subalgebra ℤ R) (hR₀ : R₀.FG) (A₀ : AbelianScheme (Spec (CommRingCat.of ↥R₀)))
    (e : A ≅ (AbelianScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap ↥R₀ R)))).obj A₀) :
    ModelStage A where
  T := R₀
  fg := hR₀
  B := A₀
  a := AbelianScheme.hom e.hom ≫
    pullback.fst A₀.X.hom (Spec.map (CommRingCat.ofHom (algebraMap ↥R₀ R)))
  isPullback := by
    have : IsIso (AbelianScheme.hom e.hom) :=
      ⟨⟨AbelianScheme.hom e.inv,
        by rw [← AbelianScheme.hom_comp, e.hom_inv_id, AbelianScheme.hom_id],
        by rw [← AbelianScheme.hom_comp, e.inv_hom_id, AbelianScheme.hom_id]⟩⟩
    have h₁ : IsPullback (AbelianScheme.hom e.hom) A.X.hom
        (pullback.snd A₀.X.hom (Spec.map (CommRingCat.ofHom (algebraMap ↥R₀ R)))) (𝟙 _) :=
      IsPullback.of_horiz_isIso
        ⟨by rw [Category.comp_id]; exact Over.w (AbelianScheme.groupHom e.hom).hom.hom⟩
    have h := h₁.paste_horiz (IsPullback.of_hasPullback A₀.X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap ↥R₀ R))))
    rw [Category.id_comp] at h
    exact h
  unit := by
    rw [← Category.assoc, unitSection_hom, unitSection_baseChange_fst]

/-- Assembly: noetherian models from the descent of abelian schemes, line bundles and
isomorphisms of line bundles. -/
theorem noetherianModel_of (hABS : AbelianScheme.SubalgebraDescentStatement.{u})
    (hLB1 : LineBundleSubalgebraDescentStatement.{u})
    (hLB2 : LineBundleIsoSubalgebraDescentStatement.{u}) :
    AbelianSchemeNoetherianModelStatement.{u} := by
  intro R A M₁ M₂
  obtain ⟨R₀, hR₀, A₀, ⟨e⟩⟩ := hABS R A
  let S₀ := stage₀ R₀ hR₀ A₀ e
  obtain ⟨T₁, hT₁, N₁, hN₁⟩ := exists_step_carried hLB1 S₀ M₁.obj.carrier M₁.property
  let S₁ := S₀.step T₁ hT₁
  obtain ⟨T₂, hT₂, N₂, hN₂⟩ := exists_step_carried hLB1 S₁ M₂.obj.carrier M₂.property
  let S₂ := S₁.step T₂ hT₂
  obtain ⟨T₃, hT₃, hc₁, ht₁⟩ := exists_step_trivialized hLB2 S₂ M₁ (hN₁.step T₂ hT₂)
  let S₃ := S₂.step T₃ hT₃
  obtain ⟨T₄, hT₄, hc₂, ht₂⟩ := exists_step_trivialized hLB2 S₃ M₂ (hN₂.step T₃ hT₃)
  let S₄ := S₃.step T₄ hT₄
  obtain ⟨hL₁, ⟨e₁⟩⟩ := hc₁.step T₄ hT₄
  obtain ⟨α₁⟩ := ht₁.step T₄ hT₄
  obtain ⟨hL₂, ⟨e₂⟩⟩ := hc₂
  obtain ⟨α₂⟩ := ht₂
  have hnoeth : IsNoetherianRing ↥S₄.T := isNoetherianRing_of_fg S₄.T S₄.fg
  exact ⟨CommRingCat.of ↥S₄.T, hnoeth, CommRingCat.ofHom (algebraMap ↥S₄.T R), S₄.B, S₄.a,
    RigidifiedLineBundle.ofLineBundle ⟨_, hL₁⟩ α₁, RigidifiedLineBundle.ofLineBundle ⟨_, hL₂⟩ α₂,
    S₄.isPullback, S₄.unit, ⟨ObjectProperty.isoMk _ e₁⟩, ⟨ObjectProperty.isoMk _ e₂⟩⟩

end Langlands.AbelianScheme.NoetherianModelProof

namespace Langlands.AbelianScheme

/-- Descent of abelian schemes, line bundles and isomorphisms of line bundles gives noetherian
models of an abelian scheme with two rigidified line bundles. -/
theorem abelianSchemeNoetherianModelReduction :
    AbelianSchemeNoetherianModelReductionStatement.{u} :=
  fun hABS hLB1 hLB2 => NoetherianModelProof.noetherianModel_of hABS hLB1 hLB2

end Langlands.AbelianScheme
