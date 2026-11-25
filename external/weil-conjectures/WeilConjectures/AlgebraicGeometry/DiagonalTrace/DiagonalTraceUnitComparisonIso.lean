/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTowerTraceCoefficients
import all WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceOrdinaryLimitEpi

/-! # The diagonal completed-unit comparison is invertible -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u a b c v w g va vb vc wa wb wc
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace

open SpTowerClasses

private theorem coefficientCone_lift_isIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] {T : Scheme.{u}}
    [DiagonalTraceLocalizations l T] {c : Chern l E T} {r : Restriction l E T}
    (a : Coefficients l E T c r) :
    IsIso (limit.lift (r.F.obj (coefficient T (Arings l E T)))
      ⟨(diagonalCompletedRestriction l T).obj
        (SheafOfModules.unit (Scheme.purTwistRing T (Scheme.purTwistZlCompletion T l))),
        a.coefficientProjection⟩) := by
  let F := diagonalForget l T
  let G := sheafCompose (Scheme.ProEt.topology T)
    ((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ⋙
      forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})
  let d : Cone (r.F.obj (coefficient T (Arings l E T))) :=
    ⟨_, a.coefficientProjection⟩
  have : F.ReflectsIsomorphisms := by
    dsimp [F, diagonalForget]
    infer_instance
  have : ReflectsLimitsOfShape ℕᵒᵖ F := reflectsLimitsOfShape_of_reflectsIsomorphisms
  have : PreservesLimitsOfShape ℕᵒᵖ
      (G ⋙ sheafToPresheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1}) :=
    inferInstanceAs (PreservesLimitsOfShape ℕᵒᵖ
      (sheafToPresheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1} ⋙
        (Functor.whiskeringRight _ _ _).obj
          ((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ⋙
            forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})))
  have : PreservesLimitsOfShape ℕᵒᵖ G :=
    preservesLimitsOfShape_of_reflects_of_preserves _ (sheafToPresheaf _ _)
  have hc : IsLimit ((Cone.postcompose a.coefficientForget.hom).obj (F.mapCone d)) := by
    apply (isLimitOfPreserves G (limit.isLimit (Scheme.purTwistZlTower T l))).ofIsoLimit
    refine Cone.ext (Iso.refl _) ?_
    intro n
    ext U x
    exact (a.coefficient_projection n.unop U x).symm
  have hd : IsLimit d := isLimitOfReflects F
    ((IsLimit.postcomposeHomEquiv a.coefficientForget (F.mapCone d)) hc)
  exact (IsLimit.nonempty_isLimit_iff_isIso_lift (limit.isLimit _)).mp ⟨hd⟩

private theorem forgetRingAbPreserves (T : Scheme.{u}) :
    (Scheme.ProEt.topology T).PreservesSheafification
      ((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ⋙
        forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1}) := by
  constructor
  intro P Q g hg
  apply ((Scheme.ProEt.topology T).W_iff_isLocallyBijective _).mpr
  have := hg.isLocallyInjective
  have := hg.isLocallySurjective
  constructor
  · exact ⟨fun x y h ↦ Presheaf.equalizerSieve_mem (Scheme.ProEt.topology T) g x y h⟩
  · exact ⟨fun x ↦ Presheaf.imageSieve_mem (Scheme.ProEt.topology T) g x⟩

private theorem coefficientTransitions_epi (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    (n : ℕ) :
    Epi ((sheafCompose (Scheme.ProEt.topology T)
      ((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ⋙
        forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).map
          ((Scheme.purTwistZlTower T l).map (homOfLE (Nat.le_succ n)).op)) := by
  let G := (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ⋙
    forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1}
  let q : CommRingCat.of (ULift.{u + 1} (ZMod (l ^ (n + 2)))) ⟶
      CommRingCat.of (ULift.{u + 1} (ZMod (l ^ (n + 1)))) :=
    CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
      ((ZMod.castHom (pow_dvd_pow l (Nat.le_succ (n + 1)))
        (ZMod (l ^ (n + 1)))).comp ULift.ringEquiv.toRingHom))
  have : Epi (G.map q) := ConcreteCategory.epi_of_surjective _ (by
    intro x
    obtain ⟨z, hz⟩ := ZMod.ringHom_surjective
      (ZMod.castHom (pow_dvd_pow l (Nat.le_succ (n + 1)))
        (ZMod (l ^ (n + 1)))) x.down
    exact ⟨ULift.up z, congrArg ULift.up hz⟩)
  let C := constantSheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1}
  have : C.IsLeftAdjoint := (constantSheafAdj (Scheme.ProEt.topology T)
    AddCommGrpCat.{u + 1} (MorphismProperty.Over.mkIdTerminal _ _)).isLeftAdjoint
  have := C.map_epi (G.map q)
  have := forgetRingAbPreserves T
  let e := constantCommuteCompose (Scheme.ProEt.topology T) G
  have he := e.hom.naturality q
  change (sheafCompose (Scheme.ProEt.topology T) G).map
      ((constantSheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}).map q) ≫
        e.hom.app _ = e.hom.app _ ≫ C.map (G.map q) at he
  have : Epi ((sheafCompose (Scheme.ProEt.topology T) G).map
      ((constantSheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}).map q)) := by
    apply (epi_comp_iff_of_isIso _ (e.hom.app _)).mp
    rw [he]
    infer_instance
  simpa only [Scheme.purTwistZlTower, Scheme.purTwistZlTowerOfUniverses,
    Functor.ofOpSequence_map_homOfLE_succ,
    Scheme.purTwistFiniteTransitionOfUniverses, q, G] using this

private theorem forgottenTower_epi (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    (H : DiagonalSystems l T)
    (ht : ∀ n : ℕ, Epi ((H ⋙ diagonalForget l T).map
      (homOfLE (Nat.le_succ n)).op)) (n : ℕ) :
    Epi (H.map (homOfLE (Nat.le_succ n)).op) :=
  by
    have : (diagonalForget l T).Faithful := by
      unfold diagonalForget
      infer_instance
    exact (diagonalForget l T).epi_of_epi_map (ht n)

private theorem towerTransitions_of_iso
    {C : Type*} [Category C] {H K : ℕᵒᵖ ⥤ C} (e : H ≅ K)
    (ht : ∀ n : ℕ, Epi (K.map (homOfLE (Nat.le_succ n)).op)) (n : ℕ) :
    Epi (H.map (homOfLE (Nat.le_succ n)).op) := by
  have := ht n
  have : Epi (H.map (homOfLE (Nat.le_succ n)).op ≫ e.hom.app (op n)) := by
    rw [e.hom.naturality]
    infer_instance
  exact (epi_comp_iff_of_isIso _ (e.hom.app (op n))).mp this

attribute [local irreducible] diagonalCompletedRestriction
  Coefficients.unitMap exactConeComparison diagonalOrdinaryRlim

/-- The completed coefficient-unit cone induces an invertible derived comparison.

Source: the quotient-tower comparison in the diagonal trace proof, paragraph (1).
(blueprint: new-sfb-diagonal-trace-unit-comparison-iso).

Proof: after forgetting scalars, the projection equations identify the cone with
the additive image of the coefficient-ring limit cone. Scalar forgetting reflects
limits, so its ordinary cone lift is invertible. The transitions are constant
sheaves of surjective quotient maps; scalar forgetting reflects their epimorphy.
Apply the epimorphic-tower comparison and compose the four invertible factors in
the specified coefficient comparison.
-/
theorem diagonalUnitComparison_isIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] {T : Scheme.{u}}
    [DiagonalTraceLocalizations l T] {c : Chern l E T} {r : Restriction l E T}
    (a : Coefficients l E T c r) (L : DiagonalRlim (DiagonalMod l T)) :
    IsIso (a.unitMap l E L) := by
  have hcone := coefficientCone_lift_isIso l E a
  have ht (n : ℕ) : Epi ((r.F.obj (coefficient T (Arings l E T))).map
      (homOfLE (Nat.le_succ n)).op) :=
    forgottenTower_epi l T _
      (towerTransitions_of_iso a.coefficientForget (coefficientTransitions_epi l T)) n
  have hlim := diagonalOrdinaryRlim_isIso_of_epi l T L _ ht
  unfold Coefficients.unitMap
  exact exactConeComparison_isIso _ _ _ _ _ _ hcone hlim

end AlgebraicGeometry.ProEtale.DiagonalTrace
