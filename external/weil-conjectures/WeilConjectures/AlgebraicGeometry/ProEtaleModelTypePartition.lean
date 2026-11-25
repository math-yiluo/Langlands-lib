/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import Mathlib.Algebra.Category.ModuleCat.AB
import all WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModelStalks
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.AlgebraicGeometry.FpqcOpenSubschemeDescent
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafEquivalence

/-! # ProEtaleModelTypePartition

Source: Stacks Project, Tag 099Y, proof of lemma-compare-locally-constant.
-/

@[expose] public section
universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.Scheme

private noncomputable def sliceModelIso
    {X : Scheme.{u}} (Λ : Type (u + 1)) [CommRing Λ]
    (F : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ))
    (U : X.ProEt) (M : ModuleCat.{u + 1} Λ)
    (e : (AlgebraicGeometry.ProEtale.upperStar (ModuleCat.{u + 1} Λ) U.hom).obj F ≅
      (constantSheaf (ProEt.topology U.left) (ModuleCat.{u + 1} Λ)).obj M) :
    F.over U ≅ (constantSheaf ((ProEt.topology X).over U) (ModuleCat.{u + 1} Λ)).obj M := by
  have : (ProEt.sliceEquiv X U).inverse.IsDenseSubsite
      (ProEt.topology U.left) ((ProEt.topology X).over U) := ProEt.sliceDense X U
  let S := (ProEt.sliceEquiv X U).sheafCongr
    ((ProEt.topology X).over U) (ProEt.topology U.left) (ModuleCat.{u + 1} Λ)
  let r : S.functor.obj (F.over U) ≅
      (AlgebraicGeometry.ProEtale.localizationRestriction
        (ModuleCat.{u + 1} Λ) U.hom U.prop).obj F :=
    ObjectProperty.isoMk _ (NatIso.ofComponents (fun _ ↦ Iso.refl _))
  let c := ((ProEt.sliceEquiv X U).constantSheafSheafCongrIso
    ((ProEt.topology X).over U) (ProEt.topology U.left)
    (ModuleCat.{u + 1} Λ) (Over.mkIdTerminal (X := U))).app M
  exact S.functor.preimageIso (r ≪≫
    ((AlgebraicGeometry.ProEtale.upperStarIsoLocalizationRestriction
      (ModuleCat.{u + 1} Λ) U.hom U.prop).app F).symm ≪≫ e ≪≫ c.symm)

private theorem model_iso_on_overlap
    {X : Scheme.{u}} (Λ : Type (u + 1)) [CommRing Λ]
    (F : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ))
    (U V : X.ProEt) (M N : ModuleCat.{u + 1} Λ)
    (eM : (AlgebraicGeometry.ProEtale.upperStar (ModuleCat.{u + 1} Λ) U.hom).obj F ≅
      (constantSheaf (ProEt.topology U.left) (ModuleCat.{u + 1} Λ)).obj M)
    (eN : (AlgebraicGeometry.ProEtale.upperStar (ModuleCat.{u + 1} Λ) V.hom).obj F ≅
      (constantSheaf (ProEt.topology V.left) (ModuleCat.{u + 1} Λ)).obj N)
    (z : (pullback U.hom V.hom : Scheme.{u})) : Nonempty (M ≅ N) := by
  let Ω := AlgebraicClosure ((pullback U.hom V.hom).residueField z)
  let y : Spec (.of Ω) ⟶ pullback U.hom V.hom := (SpecToEquivOfField Ω _).2
    ⟨z, CommRingCat.ofHom (algebraMap ((pullback U.hom V.hom).residueField z) Ω)⟩
  let x := y ≫ pullback.fst U.hom V.hom ≫ U.hom
  let Φ := AlgebraicGeometry.ProEtale.geometricPoint x
  let zM : Φ.fiber.obj U := ⟨Over.homMk (y ≫ pullback.fst U.hom V.hom) rfl⟩
  let zN : Φ.fiber.obj V := ⟨Over.homMk (y ≫ pullback.snd U.hom V.hom)
    (by change (y ≫ pullback.snd U.hom V.hom) ≫ V.hom =
          y ≫ pullback.fst U.hom V.hom ≫ U.hom
        rw [Category.assoc, ← pullback.condition])⟩
  let sM := AlgebraicGeometry.ProEtale.sheafFiberOverIso Φ zM Λ F
  let sN := AlgebraicGeometry.ProEtale.sheafFiberOverIso Φ zN Λ F
  exact ⟨((Φ.over zM).sheafFiberConstantSheafIso M).symm ≪≫
    ((Φ.over zM).sheafFiber.mapIso (sliceModelIso Λ F U M eM)).symm ≪≫
    sM ≪≫ sN.symm ≪≫
    (Φ.over zN).sheafFiber.mapIso (sliceModelIso Λ F V N eN) ≪≫
    (Φ.over zN).sheafFiberConstantSheafIso N⟩

/-- The loci of the isomorphism types of constant pro-etale local models are open.
Source: Stacks Project, Tag 099Y, proof of lemma-compare-locally-constant.
At a geometric point of a double overlap, both models identify with the same fiber,
so they are isomorphic. For each fixed model, select the whole space on cover members
of that type and the empty open on other members. These opens agree on overlaps and
descend by fpqc open descent. Joint surjectivity proves that the descended opens cover.
(auxiliary; not a blueprint node) -/
theorem proEtale_model_type_opens
    {X : Scheme.{u}} (Λ : Type (u + 1)) [CommRing Λ]
    (F : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ))
    {I : Type (u + 1)} (W : I → Scheme.{u}) (g : ∀ i, W i ⟶ X)
    (hg : Presieve.ofArrows W g ∈ Scheme.proetalePrecoverage X)
    (M : I → ModuleCat.{u + 1} Λ)
    (e : ∀ i, (AlgebraicGeometry.ProEtale.upperStar (ModuleCat.{u + 1} Λ) (g i)).obj F ≅
      (constantSheaf (ProEt.topology (W i)) (ModuleCat.{u + 1} Λ)).obj (M i)) :
    ∃ O : I → X.Opens,
      (∀ i j (y : W j), g j y ∈ O i ↔ Nonempty (M j ≅ M i)) ∧
      (⋃ i, (O i : Set X)) = Set.univ := by
  classical
  have hweak := hg.2
  rw [Scheme.ofArrows_mem_precoverage_iff] at hweak
  have (i : I) : WeaklyEtale (g i) := hweak.2 i
  let U (i : I) : X.ProEt := ProEt.mk (g i)
  have hfpqc : Presieve.ofArrows W g ∈ fpqcPrecoverage X :=
    proetalePrecoverage_le_fpqcPrecoverage _ hg
  have compat (i j k : I) :
      pullback.fst (g j) (g k) ⁻¹ᵁ
        (if Nonempty (M j ≅ M i) then ⊤ else ⊥) =
      pullback.snd (g j) (g k) ⁻¹ᵁ
        (if Nonempty (M k ≅ M i) then ⊤ else ⊥) := by
    ext z
    obtain ⟨a⟩ := model_iso_on_overlap Λ F (U j) (U k) (M j) (M k) (e j) (e k) z
    have ht : Nonempty (M j ≅ M i) ↔ Nonempty (M k ≅ M i) :=
      ⟨fun ⟨b⟩ ↦ ⟨a.symm ≪≫ b⟩, fun ⟨b⟩ ↦ ⟨a ≪≫ b⟩⟩
    by_cases hk : Nonempty (M k ≅ M i) <;> simp [ht, hk]
  choose O hO using fun i ↦
    (AlgebraicGeometry.openSubscheme_existsUnique_of_fpqc g hfpqc
      (fun j ↦ if Nonempty (M j ≅ M i) then ⊤ else ⊥) (compat i)).exists
  have hO' (i j : I) (y : W j) : g j y ∈ O i ↔ Nonempty (M j ≅ M i) := by
    change y ∈ g j ⁻¹ᵁ O i ↔ _
    rw [hO i j]
    split_ifs <;> simp_all
  refine ⟨O, hO', ?_⟩
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨i, y, rfl⟩ := hweak.1 x
  refine Set.mem_iUnion.mpr ⟨i, ?_⟩
  exact (hO' i i y).2 ⟨Iso.refl _⟩

end AlgebraicGeometry.Scheme
