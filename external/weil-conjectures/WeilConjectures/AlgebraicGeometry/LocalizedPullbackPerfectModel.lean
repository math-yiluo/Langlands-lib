/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
import WeilConjectures.AlgebraicGeometry.FlatComplexDerivedPullback
import WeilConjectures.AlgebraicGeometry.DerivedPullbackOpenRestrictionUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Computing derived pullback on a local strictly perfect model

Source: Stacks Project, Tags 09UA, 08DW and 06YJ.
(blueprint: lem-pc-localized-pullback-perfect-model).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Ordinary pullback between the localized module sites, constructed by transporting
scheme-module pullback across the open-site equivalences.
Source: Stacks Project, Tags 0095 and 08DW
(blueprint: lem-pc-localized-pullback-perfect-model). -/
noncomputable def Scheme.Modules.localizedPullback {T X : Scheme.{u}} (g : T ⟶ X)
    (U : X.Opens) :
    SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U) ⥤
      SheafOfModules.{u} ((moduleRings T.toRingedSpace).over (g ⁻¹ᵁ U)) :=
  (Scheme.Modules.overEquiv U).functor ⋙
    Scheme.Modules.pullback (g.resLE U (g ⁻¹ᵁ U) le_rfl) ⋙
      (Scheme.Modules.overEquiv (g ⁻¹ᵁ U)).inverse

instance {T X : Scheme.{u}} (g : T ⟶ X) (U : X.Opens) :
    (Scheme.Modules.localizedPullback g U).Additive := by
  have : (Scheme.Modules.overEquiv U).functor.Additive :=
    Functor.additive_of_preserves_binary_products _
  have : (Scheme.Modules.overEquiv (g ⁻¹ᵁ U)).inverse.Additive :=
    Functor.additive_of_preserves_binary_products _
  unfold Scheme.Modules.localizedPullback
  infer_instance

/-- A finite-free retract is flat by flatness of coproducts and retracts. -/
private theorem flat_retract (Y : Scheme.{u})
    (M : SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (m : ℕ)
    (i : M ⟶ SheafOfModules.free (R := moduleRings Y.toRingedSpace) (ULift.{u} (Fin m)))
    (r : SheafOfModules.free (R := moduleRings Y.toRingedSpace) (ULift.{u} (Fin m)) ⟶ M)
    (h : i ≫ r = 𝟙 M) : SheafOfModules.IsFlat M := by
  let := SheafOfModules.monoidalCategory Y.sheaf
  let := SheafOfModules.symmetricCategory Y.sheaf
  obtain ⟨⟨mp⟩, ⟨mc⟩, _⟩ := SheafOfModules.tensorClosed Y.sheaf
  let := mp
  let := mc
  have := SheafOfModules.isGrothendieckAbelian (moduleRings Y.toRingedSpace)
  have hf : ObjectProperty.flat
      (SheafOfModules.free (R := moduleRings Y.toRingedSpace) (ULift.{u} (Fin m))) :=
    ObjectProperty.flat_coproduct _ (fun _ ↦ ObjectProperty.prop_unit _)
  exact (ObjectProperty.flat_of_retract ⟨i, r, h⟩ hf).2

/-- Identify the tensor pullback and module pullback by uniqueness of left adjoints. -/
private theorem ordinaryPullback_Q_iso {T X : Scheme.{u}} (g : T ⟶ X)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings T.toRingedSpace))]
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hb : ∃ b : ℤ, ∀ n : ℤ, b < n → IsZero (P.X n))
    (hf : ∀ n : ℤ, SheafOfModules.IsFlat (P.X n)) :
    Nonempty ((derivedPullback g).obj (DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj
        (((Scheme.Modules.pullback g).mapHomologicalComplex (.up ℤ)).obj P)) := by
  obtain ⟨F, hF, hm, ha, ε, hd, e, he⟩ := flatComplexDerivedPullback g P hb hf
  have hEq : F = Scheme.Modules.tensorPullback g :=
    CategoryTheory.Functor.ext hF (fun _ _ a ↦ hm a)
  subst F
  have : (Scheme.Modules.tensorPullback g).Additive := ha
  obtain ⟨adj⟩ := Scheme.Modules.nonempty_tensorPullbackAdjunction g
  let η := adj.leftAdjointUniq (Scheme.Modules.pullbackPushforwardAdjunction g)
  exact ⟨(derivedPullback g).mapIso ((DerivedCategory.quotientCompQhIso _).app P).symm ≪≫
    e.symm ≪≫
    DerivedCategory.Qh.mapIso
      (((Scheme.Modules.tensorPullback g).mapHomotopyCategoryFactors (.up ℤ)).app P) ≪≫
    (DerivedCategory.quotientCompQhIso _).app _ ≪≫
    DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex η (.up ℤ)).app P)⟩

/-- A specified local strictly perfect model computes derived pullback on its inverse-image
open. This only identifies the derived object; preservation of strict perfectness of the
ordinary pulled complex is a separate, elementary argument.
Source: Stacks Project, Tag 09UA, the alternative proof via Tag 09U7;
Tag 08DW (restriction comparison), and Tags 06YD and 06YJ (flat computation).
(blueprint: lem-pc-localized-pullback-perfect-model).

Proof: put V = g inverse-image U and transport K through Modules.overEquiv U to a
complex on U.toScheme. This equivalence identifies the unit sheaves and preserves
coproducts, zero objects and retract equations, so the transported terms are finite
projective, hence flat, and the complex is bounded above. Apply
flatComplexDerivedPullback to the restricted morphism V.toScheme -> U.toScheme:
the derived pullback is represented by its ordinary termwise tensor pullback.
The tensor formula and Mathlib's module pullback are both left adjoint to the same
pushforward, so uniqueness of left adjoints identifies these ordinary pullbacks.
The restriction comparison of derivedPullback_openRestriction_iso_universes identifies
the restriction of Lg* E with the derived pullback of E restricted to U. Map the given
isomorphism e through this latter functor, then compose with the flat computation.
Finally transport back along Modules.overEquiv V and the canonical localization
factorization isomorphisms. Full faithfulness of the induced equivalence of derived
categories reflects the resulting isomorphism to the localized site. The localization
on open subschemes can be chosen standard independently of w, as in the universe-aware
restriction comparison. The zero complex and empty opens require no exceptions. -/
theorem localizedPullback_perfectModel_iso {T X : Scheme.{u}} (g : T ⟶ X)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings T.toRingedSpace))]
    [∀ V : T.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings T.toRingedSpace).over V))]
    (U : X.Opens) (E : schemeDerivedCategory X)
    (K : CochainComplex (SheafOfModules.{u}
      ((moduleRings X.toRingedSpace).over U)) ℤ)
    (hK : Scheme.IsStrictlyPerfect X U K)
    (e : (SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj E ≅ DerivedCategory.Q.obj K) :
    Nonempty ((SheafOfModules.overFunctor.{u}
      (moduleRings T.toRingedSpace) (g ⁻¹ᵁ U)).mapDerivedCategory.obj
        ((derivedPullback g).obj E) ≅
      DerivedCategory.Q.obj
        (((Scheme.Modules.localizedPullback g U).mapHomologicalComplex (.up ℤ)).obj K)) := by
  let V := g ⁻¹ᵁ U
  let f := g.resLE U V le_rfl
  -- Reuse sheafification on the localized sites throughout the comparisons below.
  have hsX : HasSheafify ((Opens.grothendieckTopology X).over U)
      AddCommGrpCat.{u} := inferInstance
  have : HasWeakSheafify ((Opens.grothendieckTopology X).over U)
      AddCommGrpCat.{u} := hsX.isRightAdjoint
  have : ((Opens.grothendieckTopology X).over U).WEqualsLocallyBijective
      AddCommGrpCat.{u} := inferInstance
  have hsT : HasSheafify ((Opens.grothendieckTopology T).over V)
      AddCommGrpCat.{u} := inferInstance
  have : HasWeakSheafify ((Opens.grothendieckTopology T).over V)
      AddCommGrpCat.{u} := hsT.isRightAdjoint
  have : ((Opens.grothendieckTopology T).over V).WEqualsLocallyBijective
      AddCommGrpCat.{u} := inferInstance
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))
  let A : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U) ⥤
      SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace) :=
    (Scheme.Modules.overEquiv U).functor
  let C : SheafOfModules.{u} ((moduleRings T.toRingedSpace).over V) ⥤
      SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace) :=
    (Scheme.Modules.overEquiv V).functor
  let B : SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace) ⥤
      SheafOfModules.{u} ((moduleRings T.toRingedSpace).over V) :=
    (Scheme.Modules.overEquiv V).inverse
  let RX := SheafOfModules.overFunctor.{u} (moduleRings T.toRingedSpace) V
  let RY := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U
  let F := Scheme.Modules.localizedPullback g U
  have : A.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_isLeftAdjoint A
  have : A.Additive := Functor.additive_of_preserves_binary_products _
  have : B.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_isLeftAdjoint B
  have : B.Additive := Functor.additive_of_preserves_binary_products _
  have : C.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_isLeftAdjoint C
  have : C.Additive := Functor.additive_of_preserves_binary_products _
  have : (Scheme.Modules.pullback f).Additive := Scheme.Modules.instAdditivePullback f
  have : (A ⋙ Scheme.Modules.pullback f).Additive := inferInstance
  have : PreservesFiniteLimits (RX ⋙ C) := comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits (RX ⋙ C) := comp_preservesFiniteColimits _ _
  have : PreservesFiniteLimits (RY ⋙ A) := comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits (RY ⋙ A) := comp_preservesFiniteColimits _ _
  let P := (A.mapHomologicalComplex (.up ℤ)).obj K
  obtain ⟨⟨a, b, hb⟩, hp⟩ := hK
  have hPbounded : ∃ b : ℤ, ∀ n : ℤ, b < n → IsZero (P.X n) :=
    ⟨b, fun n hn ↦ A.map_isZero (hb n (Or.inr hn))⟩
  have hPflat : ∀ n : ℤ, SheafOfModules.IsFlat (P.X n) := by
    intro n
    obtain ⟨m, i, r, hir⟩ := hp n
    let ei : A.obj (SheafOfModules.free
        (R := (moduleRings X.toRingedSpace).over U) (ULift.{u} (Fin m))) ≅
        SheafOfModules.free (R := moduleRings U.toScheme.toRingedSpace)
          (ULift.{u} (Fin m)) :=
      (asIso (sigmaComparison A (fun _ : ULift.{u} (Fin m) ↦
        SheafOfModules.unit ((moduleRings X.toRingedSpace).over U)))).symm ≪≫
      Sigma.mapIso (fun _ ↦ U.sheafOfModulesEquivOverUnit (moduleRings X.toRingedSpace))
    apply flat_retract U.toScheme (P.X n) m (A.map i ≫ ei.hom) (ei.inv ≫ A.map r)
    change (A.map i ≫ ei.hom) ≫ ei.inv ≫ A.map r = 𝟙 (A.obj (K.X n))
    simp only [Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp, hir]
    exact A.map_id _
  obtain ⟨θ⟩ := derivedPullback_openRestriction_iso_universes g V U le_rfl
  obtain ⟨q⟩ := ordinaryPullback_Q_iso f P hPbounded hPflat
  let eP : A.mapDerivedCategory.obj (RY.mapDerivedCategory.obj E) ≅
      DerivedCategory.Q.obj P :=
    A.mapDerivedCategory.mapIso e ≪≫ A.mapDerivedCategoryFactors.app K
  let left : C.mapDerivedCategory.obj
      (RX.mapDerivedCategory.obj ((derivedPullback g).obj E)) ≅
      DerivedCategory.Q.obj
        (((Scheme.Modules.pullback f).mapHomologicalComplex (.up ℤ)).obj P) :=
    (Functor.mapDerivedCategoryCompIso RX C).app _ ≪≫ θ.app E ≪≫
      (derivedPullback f).mapIso (((Functor.mapDerivedCategoryCompIso RY A).app E).symm ≪≫ eP) ≪≫ q
  let δ : F ⋙ C ≅ A ⋙ Scheme.Modules.pullback f :=
    Functor.associator A (Scheme.Modules.pullback f ⋙ B) C ≪≫
      Functor.isoWhiskerLeft A (Functor.associator (Scheme.Modules.pullback f) B C) ≪≫
      Functor.isoWhiskerLeft A
        (Functor.isoWhiskerLeft (Scheme.Modules.pullback f)
          (Scheme.Modules.overEquiv V).counitIso) ≪≫
      Functor.isoWhiskerLeft A (Functor.rightUnitor (Scheme.Modules.pullback f))
  let FK := (F.mapHomologicalComplex (.up ℤ)).obj K
  let right : C.mapDerivedCategory.obj (DerivedCategory.Q.obj FK) ≅
      DerivedCategory.Q.obj
        (((Scheme.Modules.pullback f).mapHomologicalComplex (.up ℤ)).obj P) :=
    C.mapDerivedCategoryFactors.app FK ≪≫ DerivedCategory.Q.mapIso
      (((Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ C)) (.up ℤ)).app K).symm ≪≫
        (NatIso.mapHomologicalComplex δ (.up ℤ)).app K ≪≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl (A ⋙ Scheme.Modules.pullback f))
          (.up ℤ)).app K)
  exact ⟨C.mapDerivedCategory.preimageIso (left ≪≫ right.symm)⟩

end AlgebraicGeometry
