/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffineGlobalHomBaseChangeMap
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
import WeilConjectures.AlgebraicGeometry.PerfectRHomTensorComparison
import WeilConjectures.AlgebraicGeometry.PerfectImpliesQCoh
import WeilConjectures.AlgebraicGeometry.CanonicalPullbackTensorMonoidalRealization
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence
import WeilConjectures.AlgebraicGeometry.DerivedInternalHomAdjunction

/-! # Invertibility of the evaluation-defined perfect internal-Hom pullback map

Source: Stacks Project, cohomology.tex, Tags 08I3 and 0FPC.
(blueprint: lem-pc-perfect-internal-hom-pullback-isIso).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.MonoidalCategory Opposite TopologicalSpace
namespace AlgebraicGeometry

private theorem monoidal_rigid_counit
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D) [F.Monoidal] (M N K : C) [ExactPairing M N] :
    Functor.LaxMonoidal.μ F (K ⊗ N) M ≫
        F.map ((tensorRightAdjunction M N).counit.app K) =
      (Functor.OplaxMonoidal.δ F K N ▷ F.obj M) ≫
        (letI := ExactPairing.map F M N
         (tensorRightAdjunction (F.obj M) (F.obj N)).counit.app (F.obj K)) := by
  let := ExactPairing.map F M N
  rw [tensorRightAdjunction_counit_app, tensorRightAdjunction_counit_app]
  change _ = _ ≫ (α_ _ _ _).hom ≫
    F.obj K ◁ (Functor.LaxMonoidal.μ F N M ≫ F.map (ExactPairing.evaluation M N) ≫
      Functor.OplaxMonoidal.η F) ≫ (ρ_ _).hom
  simp only [Functor.map_comp, Functor.Monoidal.map_associator,
    Functor.Monoidal.map_whiskerLeft,
    whiskerLeft_comp, Category.assoc, Functor.Monoidal.μ_δ_assoc]
  rw [Functor.Monoidal.map_rightUnitor F K]
  simp only [Functor.Monoidal.μ_δ_assoc]

private theorem monoidal_adjunct_isIso
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D) [F.Monoidal] (M N K : C) [ExactPairing M N]
    (H : C ⥤ C) (J : D ⥤ D) (b : tensorRight M ⊣ H)
    (c : tensorRight (F.obj M) ⊣ J) :
    IsIso (c.homEquiv (F.obj (H.obj K)) (F.obj K)
      (Functor.LaxMonoidal.μ F (H.obj K) M ≫ F.map (b.counit.app K))) := by
  let := ExactPairing.map F M N
  let s := (tensorRightAdjunction M N).rightAdjointUniq b
  let s' := (tensorRightAdjunction (F.obj M) (F.obj N)).rightAdjointUniq c
  let q := c.homEquiv (F.obj (H.obj K)) (F.obj K)
    (Functor.LaxMonoidal.μ F (H.obj K) M ≫ F.map (b.counit.app K))
  have h : F.map (s.hom.app K) ≫ q =
      Functor.OplaxMonoidal.δ F K N ≫ s'.hom.app (F.obj K) := by
    apply (c.homEquiv _ _).symm.injective
    rw [c.homEquiv_naturality_left_symm, c.homEquiv_naturality_left_symm]
    dsimp only [q]
    rw [Equiv.symm_apply_apply]
    change F.map (s.hom.app K) ▷ F.obj M ≫ _ =
      Functor.OplaxMonoidal.δ F K N ▷ F.obj M ≫ _
    rw [Functor.LaxMonoidal.μ_natural_left_assoc, ← F.map_comp]
    dsimp only [s, s']
    have hs := Adjunction.rightAdjointUniq_hom_app_counit
      (tensorRightAdjunction M N) b K
    change s.hom.app K ▷ M ≫ b.counit.app K = _ at hs
    rw [hs]
    have hs' := Adjunction.homEquiv_symm_rightAdjointUniq_hom_app
      (tensorRightAdjunction (F.obj M) (F.obj N)) c (F.obj K)
    change (c.homEquiv (F.obj K ⊗ F.obj N) (F.obj K)).symm
      (s'.hom.app (F.obj K)) = _ at hs'
    rw [hs']
    exact monoidal_rigid_counit F M N K
  have : IsIso (F.map (s.hom.app K) ≫ q) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_left (F.map (s.hom.app K)) q

/-- Use only the dual and pairing from the full perfect comparison package. -/
private theorem perfect_exactPairing_exists
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (M : schemeDerivedCategory X) (hM : Scheme.IsPerfect X M) :
    ∃ D : schemeDerivedCategory X, Nonempty (ExactPairing M D) := by
  have ha := scheme_derivedInternalHom_adjunction X
  let adj := ha.choose
  let adj' := ha.choose_spec.choose_spec.choose
  have hadj := ha.choose_spec.choose_spec.choose_spec.1
  have hadj' := ha.choose_spec.choose_spec.choose_spec.2.2.2
  let P : schemeDerivedQCohCategory X :=
    ⟨M, schemeDerivedQCohProperty_of_isPerfect X M hM⟩
  have hp := perfect_rhom_tensor_comparison X P P hM adj hadj adj' hadj'
  exact ⟨hp.choose.obj, ⟨hp.choose_spec.choose_spec.choose_spec.2.2.choose_spec.2.2.2
    |>.choose_spec.2.2.choose_spec.2.2.1.choose⟩⟩

/-- Convert the tensor comparison to the tensorator before specializing to derived categories. -/
private theorem monoidal_adjunct_isIso_of_tensorIso
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D) (M K : C)
    (hM : ∃ N : C, Nonempty (ExactPairing M N))
    (t : tensor C ⋙ F ≅ F.prod F ⋙ tensor D)
    (ht : ∃ m : F.CoreMonoidal, ∀ A B : C, (m.μIso A B).inv = t.hom.app (A, B))
    (H : C ⥤ C) (J : D ⥤ D) (b : tensorRight M ⊣ H)
    (c : tensorRight (F.obj M) ⊣ J) :
    IsIso (c.homEquiv (F.obj (H.obj K)) (F.obj K)
      (t.inv.app (H.obj K, M) ≫ F.map (b.counit.app K))) := by
  obtain ⟨N, ⟨p⟩⟩ := hM
  let := p
  obtain ⟨m, hm⟩ := ht
  let := m.toMonoidal
  have htensor (A B : C) : t.inv.app (A, B) = Functor.LaxMonoidal.μ F A B := by
    have he : (m.μIso A B).symm = t.app (A, B) := Iso.ext (hm A B)
    exact (congrArg Iso.inv he).symm
  rw [htensor]
  exact monoidal_adjunct_isIso F M N K H J b c

/-- Pullback of internal Hom from a perfect source commutes with internal Hom.
This asserts invertibility of the evaluation-defined map, for the fixed normalized
tensor-Hom adjunctions and a canonical pullback tensor comparison, rather than
existence of an unrelated isomorphism between the two objects.

Source: Stacks Project, cohomology.tex, Remark 08I3 and Example 0FPC.
(blueprint: lem-pc-perfect-internal-hom-pullback-isIso).

Proof: Equip M with quasi-coherent cohomology using PerfectImpliesQCoh, and
apply perfect_rhom_tensor_comparison with both inputs M to obtain an exact pairing
of M with its perfect dual D. Realize the supplied canonical tensor comparison by
canonicalPullbackTensor_monoidal_realization; its inverse is the monoidal tensorator.
The upstream counit formula and two proved private helpers perform the remaining
categorical calculation.
The rigid tensor adjunction has counit associator followed by evaluation and the
right unitor. A monoidal functor carries this counit to the transported pairing's
counit after precomposition by its inverse tensorator. Uniqueness of right adjoints
identifies both internal-Hom functors with tensoring by the respective duals.
Naturality of the target adjunction and compatibility of these counits show that
precomposing the displayed mate by the pulled-back source identification gives
inverse tensorator followed by the target identification. All these maps are
invertible, so cancellation proves the displayed mate invertible. This argument
uses arbitrary adjunctions and arbitrary K, hence applies to the fixed normalized
adjunctions without any quasi-coherence or boundedness assumption on K. -/
theorem perfect_internalHom_pullback_isIso
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (A : Type u) [Ring A], HasDerivedCategory.{w} (ModuleCat.{u} A)]
    {T X : Scheme.{u}} (g : T ⟶ X)
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (M K : schemeDerivedCategory X) (hM : Scheme.IsPerfect X M)
    (t : tensor (schemeDerivedCategory X) ⋙ derivedPullback g ≅
      (derivedPullback g).prod (derivedPullback g) ⋙ tensor (schemeDerivedCategory T))
    (ht : IsCanonicalPullbackTensorComparison g (fun E K => t.hom.app (E, K))) :
    IsIso
      ((canonicalTensorHomAdjunction T ((derivedPullback g).obj M)).homEquiv
        ((derivedPullback g).obj
          ((derivedInternalHom (Opens.grothendieckTopology X)
            X.toRingedSpace.sheaf).obj (op M, K))) ((derivedPullback g).obj K)
        (t.inv.app
            ((derivedInternalHom (Opens.grothendieckTopology X)
              X.toRingedSpace.sheaf).obj (op M, K), M) ≫
          (derivedPullback g).map ((canonicalTensorHomAdjunction X M).counit.app K))) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
  exact (by
    exact monoidal_adjunct_isIso_of_tensorIso (derivedPullback g) M K
      (perfect_exactPairing_exists X M hM) t
      (canonicalPullbackTensor_monoidal_realization g (fun A B ↦ t.hom.app (A, B)) ht)
      _ _ (canonicalTensorHomAdjunction X M)
      (canonicalTensorHomAdjunction T ((derivedPullback g).obj M)))

end AlgebraicGeometry
