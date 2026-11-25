/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy

/-! # A normalized derived adjunction from a resolving class
Source: Stacks Project, Tags 06XN, 0FND and 09T5.
-/
@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
universe uA vA uB vB wA wB
-- A full, essentially surjective functor is initial: every comma object maps
-- to a fixed lift of the target, giving a zigzag between any two objects.
private theorem initial_of_full_essSurj
    {A B : Type*} [Category A] [Category B] (F : A ⥤ B) [F.Full] [F.EssSurj] :
    F.Initial := by
  classical
  constructor
  intro Y
  let e := F.objObjPreimageIso Y
  let Z : CostructuredArrow F Y := CostructuredArrow.mk e.hom
  have lift (X : CostructuredArrow F Y) : Nonempty (X ⟶ Z) := by
    refine ⟨CostructuredArrow.homMk (F.preimage (X.hom ≫ e.inv)) ?_⟩
    simp [Z, e]
  let : Nonempty (CostructuredArrow F Y) := ⟨Z⟩
  apply zigzag_isConnected
  intro X X'
  exact (Zigzag.of_hom (lift X).some).trans (Zigzag.of_inv (lift X').some)

-- The induced functor on structured arrows is also full and essentially
-- surjective, so restricting the defining limit cone preserves its limit.
private noncomputable def pointwise_precomp_full
    {A C D H : Type*} [Category A] [Category C] [Category D] [Category H]
    (P : A ⥤ C) [P.Full] [P.EssSurj] (Q : C ⥤ D) (F : C ⥤ H) (L : D ⥤ H)
    (α : Q ⋙ L ⟶ F)
    (h : (Functor.RightExtension.mk L α).IsPointwiseRightKanExtension) :
    (Functor.RightExtension.mk L
      ((Functor.associator P Q L).hom ≫ Functor.whiskerLeft P α)).IsPointwiseRightKanExtension := by
  intro Y
  let p := StructuredArrow.pre Y P Q
  let : p.Initial := initial_of_full_essSurj p
  apply Limits.IsLimit.ofIsoLimit ((Functor.Initial.isLimitWhiskerEquiv p _).symm (h Y))
  refine Limits.Cone.ext (Iso.refl _) ?_
  intro X
  dsimp [Functor.RightExtension.coneAt, Functor.RightExtension.mk, p]
  simp

-- Transport the defining limit cone through an equivalence of structured
-- arrow categories and the prescribed isomorphism of diagram functors.
private noncomputable def pointwise_change_iso
    {C D H : Type*} [Category C] [Category D] [Category H]
    {Q Q' : C ⥤ D} {F F' : C ⥤ H} (L : D ⥤ H)
    (i : Q ≅ Q') (j : F ≅ F') (α : Q ⋙ L ⟶ F)
    (h : (Functor.RightExtension.mk L α).IsPointwiseRightKanExtension) :
    (Functor.RightExtension.mk L
      (Functor.whiskerRight i.inv L ≫ α ≫ j.hom)).IsPointwiseRightKanExtension := by
  intro Y
  let Φ : StructuredArrow Y Q' ≌ StructuredArrow Y Q := Comma.mapRightIso _ i.symm
  let k : Φ.functor ⋙ StructuredArrow.proj Y Q ⋙ F ≅
      StructuredArrow.proj Y Q' ⋙ F' :=
    NatIso.ofComponents (fun X ↦ j.app X.right) (by
      intro X X' f
      exact j.hom.naturality f.right)
  apply Limits.IsLimit.ofIsoLimit
    ((Limits.IsLimit.postcomposeHomEquiv k _).symm ((h Y).whiskerEquivalence Φ))
  refine Limits.Cone.ext (Iso.refl _) ?_
  intro X
  dsimp [Functor.RightExtension.coneAt, Functor.RightExtension.mk, Φ, k]
  simp [Category.assoc]

private theorem inverted_indDiagram
    {D : Type*} [Category* D] {H : Type*} [Category* H]
    (W : MorphismProperty D) [W.HasLeftCalculusOfFractions]
    (U : D ⥤ H) (hU : W.IsInvertedBy U) (X : D) :
    IsEssentiallyConstantIndDiagram
      (MorphismProperty.Under.forget W ⊤ X ⋙ Under.forget X ⋙ U) (U.obj X) := by
  classical
  let I := W.Under ⊤ X
  let V := MorphismProperty.Under.forget W ⊤ X ⋙ Under.forget X ⋙ U
  have hI : IsFiltered I := by
    refine {
      nonempty := ⟨MorphismProperty.Under.mk ⊤ (𝟙 X) (W.id_mem X)⟩
      cocone_objs := ?_
      cocone_maps := ?_ }
    · intro s t
      obtain ⟨ψ, hψ⟩ :=
        (MorphismProperty.RightFraction.mk s.hom s.prop t.hom).exists_leftFraction
      let k : I := MorphismProperty.Under.mk ⊤ (t.hom ≫ ψ.s)
        (W.comp_mem _ _ t.prop ψ.hs)
      exact ⟨k, MorphismProperty.Under.homMk ψ.f hψ.symm,
        MorphismProperty.Under.homMk ψ.s, trivial⟩
    · intro s t f g
      obtain ⟨Y, a, ha, heq⟩ := MorphismProperty.HasLeftCalculusOfFractions.ext
        f.right g.right s.hom s.prop (f.w.symm.trans g.w)
      let k : I := MorphismProperty.Under.mk ⊤ (t.hom ≫ a)
        (W.comp_mem _ _ t.prop ha)
      refine ⟨k, MorphismProperty.Under.homMk a, ?_⟩
      exact MorphismProperty.Under.Hom.ext heq
  have hi (j : I) : IsIso (U.map j.hom) := hU _ j.prop
  let p : V ⟶ (Functor.const I).obj (U.obj X) :=
    { app := fun j ↦ inv (U.map j.hom)
      naturality := by
        intro s t f
        change U.map f.right ≫ inv (U.map t.hom) = inv (U.map s.hom) ≫ 𝟙 _
        apply (cancel_epi (U.map s.hom)).1
        rw [← Category.assoc, ← U.map_comp, MorphismProperty.Under.w f]
        simp }
  let j₀ : I := MorphismProperty.Under.mk ⊤ (𝟙 X) (W.id_mem X)
  refine ⟨hI, p, j₀, 𝟙 _, ?_, ?_⟩
  · change 𝟙 _ ≫ inv (U.map (𝟙 X)) = 𝟙 _
    simp
  · intro j
    refine ⟨j, MorphismProperty.Under.homMk j.hom (by simp [j₀]), 𝟙 j, ?_⟩
    change U.map (𝟙 j.right) = inv (U.map j.hom) ≫ 𝟙 _ ≫ U.map j.hom
    simp

namespace CategoryTheory.Adjunction
variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]

/-- Resolve the left source, derive the adjunction against an exact right adjoint,
and retain the cochain representative-transpose equation.
Source: Stacks 06XN, 0FND, 09T5
(auxiliary; not a blueprint node).
Proof: use the resolving class to form the everywhere-defined left derived functor
on homotopy categories. Exactness of the right adjoint makes its denominator systems
constant. The canonical derived-adjunction theorem gives the Hom bijection and its
strict transpose. Precompose the universal comparison with the full essentially
surjective homotopy quotient; its structured-arrow functor is initial, so the
pointwise right Kan property and the comparison on resolutions are preserved.
The quotient-to-derived isomorphisms convert the Hom formula to cochain complexes. -/
theorem exists_leftDerived_adjunction
    (E : A ⥤ B) (R : B ⥤ A) [E.Additive] [R.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R] (a : E ⊣ R)
    (P : CochainComplex A ℤ → Prop)
    (hres : ∀ X : CochainComplex A ℤ, ∃ (Y : CochainComplex A ℤ) (s : Y ⟶ X),
      P Y ∧ QuasiIso s)
    (hpres : ∀ {X Y : CochainComplex A ℤ} (f : X ⟶ Y), P X → P Y → QuasiIso f →
      QuasiIso ((E.mapHomologicalComplex (.up ℤ)).map f)) :
    (E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q).HasPointwiseLeftDerivedFunctor
      (HomologicalComplex.quasiIso A (.up ℤ)) ∧
    ∃ (L : DerivedCategory A ⥤ DerivedCategory B)
      (ε : DerivedCategory.Q ⋙ L ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q),
      L.IsLeftDerivedFunctor ε (HomologicalComplex.quasiIso A (.up ℤ)) ∧
      (∀ X, P X → IsIso (ε.app X)) ∧
      ∃ d : L ⊣ R.mapDerivedCategory, ∀ X K
        (f : (E.mapHomologicalComplex (.up ℤ)).obj X ⟶ K),
        d.homEquiv (DerivedCategory.Q.obj X) (DerivedCategory.Q.obj K)
          (ε.app X ≫ DerivedCategory.Q.map f) =
        DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).homEquiv X K f) ≫
          R.mapDerivedCategoryFactors.inv.app K := by
  classical
  let WA := HomotopyCategory.quasiIso A (.up ℤ)
  let WB := HomotopyCategory.quasiIso B (.up ℤ)
  let F := E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh (C := B)
  let Q : Set (HomotopyCategory A (.up ℤ)) := fun X ↦
    ∃ Y : CochainComplex A ℤ, P Y ∧ (HomotopyCategory.quotient A (.up ℤ)).obj Y = X
  have hres' : ∀ X : HomotopyCategory A (.up ℤ),
      ∃ (Y : HomotopyCategory A (.up ℤ)) (s : Y ⟶ X), Y ∈ Q ∧ WA s := by
    intro X
    obtain ⟨X, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    obtain ⟨Y, s, hY, hs⟩ := hres X
    exact ⟨_, (HomotopyCategory.quotient A (.up ℤ)).map s, ⟨Y, hY, rfl⟩,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff s).2 hs⟩
  have hinv : ∀ X Y (s : X ⟶ Y), X ∈ Q → Y ∈ Q → WA s → IsIso (F.map s) := by
    rintro X Y s ⟨X, hX, rfl⟩ ⟨Y, hY, rfl⟩ hs
    obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient A (.up ℤ)).map_surjective s
    have hf := hpres f hX hY ((HomotopyCategory.quotient_map_mem_quasiIso_iff f).1 hs)
    exact Localization.inverts DerivedCategory.Qh WB _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 hf)
  obtain ⟨hpw, L, α, huniv, _, hcomp⟩ :=
    Functor.leftDerived_from_resolvingClass A (DerivedCategory B) F Q hres' hinv
  obtain ⟨_, _, _, _, htwo, _, _, _, _⟩ :=
    HomotopyCategory.quasiIso_saturated_triangulated A
  let : WA.HasTwoOutOfThreeProperty := htwo
  have hL : ∀ X, ∃ Y, IsEssentiallyConstantProDiagram
      (MorphismProperty.Over.forget WA ⊤ X ⋙ Over.forget X ⋙ F) Y := by
    intro X
    obtain ⟨Y, _, hY, _⟩ := Functor.resolvingClass_essentialConstancy WA F Q hres' hinv X
    exact ⟨Y, hY⟩
  let U := R.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh (C := A)
  have hU : WB.IsInvertedBy U := by
    intro X Y f hf
    have : IsIso (DerivedCategory.Qh.map f) := Localization.inverts DerivedCategory.Qh WB f hf
    exact (NatIso.isIso_map_iff R.mapDerivedCategoryFactorsh f).1 (by
      change IsIso (R.mapDerivedCategory.map (DerivedCategory.Qh.map f))
      infer_instance)
  obtain ⟨hleftB, _, _, _, _, _, _, _, _⟩ :=
    HomotopyCategory.quasiIso_saturated_triangulated B
  let : WB.HasLeftCalculusOfFractions := hleftB
  have hR : ∀ K, ∃ X, IsEssentiallyConstantIndDiagram
      (MorphismProperty.Under.forget WB ⊤ K ⋙ Under.forget K ⋙ U) X := by
    intro K
    exact ⟨U.obj K, inverted_indDiagram WB U hU K⟩
  have hRF := Functor.isRightDerivedFunctor_of_inverts WB
    R.mapDerivedCategory R.mapDerivedCategoryFactorsh
  obtain ⟨d, hd⟩ := exists_derived_adjunction_compatibility
    R E a hR hL R.mapDerivedCategory L R.mapDerivedCategoryFactorsh.inv α hRF huniv
  let : F.HasPointwiseLeftDerivedFunctor WA := hpw
  let : L.IsLeftDerivedFunctor α WA := huniv
  let q := HomotopyCategory.quotient A (.up ℤ)
  let β := (Functor.associator q DerivedCategory.Qh L).hom ≫ Functor.whiskerLeft q α
  have hβ := pointwise_precomp_full q DerivedCategory.Qh F L α
    (Functor.isPointwiseRightKanExtensionOfHasPointwiseLeftDerivedFunctor L α WA)
  let i := DerivedCategory.quotientCompQhIso A
  let j : q ⋙ F ≅ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (E.mapHomotopyCategoryFactors (.up ℤ)) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso B)
  let ε := Functor.whiskerRight i.inv L ≫ β ≫ j.hom
  have hε := pointwise_change_iso L i j β hβ
  refine ⟨?_, L, ε, ⟨hε.isRightKanExtension⟩, ?_, d, ?_⟩
  · intro X
    exact (Functor.hasPointwiseLeftDerivedFunctorAt_iff _ DerivedCategory.Q _ X).2
      ((hε _).hasPointwiseRightKanExtensionAt)
  · intro X hX
    have := hcomp (q.obj X) ⟨X, hX, rfl⟩
    dsimp [ε, β]
    infer_instance
  · intro X K f
    have hα : ε.app X = L.map (i.inv.app X) ≫ α.app (q.obj X) ≫
        (DerivedCategory.quotientCompQhIso B).hom.app
          ((E.mapHomologicalComplex (.up ℤ)).obj X) := by
      dsimp [ε, β, j, q]
      simp only [Functor.mapHomotopyCategoryFactors_hom_app, Category.id_comp]
      change L.map (i.inv.app X) ≫ α.app (q.obj X) ≫ 𝟙 _ ≫
        DerivedCategory.Qh.map (𝟙 _) ≫
          (DerivedCategory.quotientCompQhIso B).hom.app
            ((E.mapHomologicalComplex (.up ℤ)).obj X) = _
      simp only [Functor.map_id, Category.id_comp]
      erw [Category.id_comp]
    have hfac' : R.mapDerivedCategoryFactorsh.inv.app
        ((HomotopyCategory.quotient B (.up ℤ)).obj K) ≫
          R.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso B).hom.app K) =
        i.hom.app ((R.mapHomologicalComplex (.up ℤ)).obj K) ≫
          R.mapDerivedCategoryFactors.inv.app K := by
      apply (cancel_epi (R.mapDerivedCategoryFactorsh.hom.app
        ((HomotopyCategory.quotient B (.up ℤ)).obj K))).1
      rw [Iso.hom_inv_id_app_assoc, R.mapDerivedCategoryFactorsh_hom_app]
      simp [i, Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_inv]
    have hequiv : (a.mapHomotopyCategory (.up ℤ)).homEquiv
        (q.obj X) ((HomotopyCategory.quotient B (.up ℤ)).obj K)
        ((HomotopyCategory.quotient B (.up ℤ)).map f) =
        q.map ((a.mapHomologicalComplex (.up ℤ)).homEquiv X K f) := by
      rw [Adjunction.homEquiv_unit, Adjunction.mapHomotopyCategory_unit_app_quotient]
      change q.map _ ≫ q.map _ = q.map _
      rw [← q.map_comp]
      rfl
    have hh := hd (q.obj X) ((HomotopyCategory.quotient B (.up ℤ)).obj K)
      ((HomotopyCategory.quotient B (.up ℤ)).map f)
    rw [hequiv] at hh
    rw [hα]
    simp only [Category.assoc]
    rw [← DerivedCategory.quotientCompQhIso_hom_naturality f,
      ← Category.assoc (α.app (q.obj X)), d.homEquiv_naturality_left,
      d.homEquiv_naturality_right]
    dsimp only [q, Functor.comp_obj] at hh ⊢
    rw [hh]
    simp only [Category.assoc, hfac', i, Iso.inv_hom_id_app_assoc,
      ← DerivedCategory.quotientCompQhIso_inv_naturality_assoc]
end CategoryTheory.Adjunction
