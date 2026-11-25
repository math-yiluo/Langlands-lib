/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ExtensionTensorComparison
public import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatAllIndependentCoefficients
public import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.FlatScalarRestrictionKFlat
public import WeilConjectures.Algebra.Homology.KFlatFixedTensorTriangulated
public import WeilConjectures.Algebra.Homology.KFlatResolution
public import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import WeilConjectures.AlgebraicGeometry.CoefficientRingedSequenceSite
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionCompletedFinitePull
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionInverseImageExists
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionKoszulReflector
public import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
public import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.CategoryTheory.FlatScalarKoszulTowerComparison
public import WeilConjectures.CategoryTheory.NatTransFromResolvingClass
public import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
public import WeilConjectures.SecSmoothPurity.CochainTensorCoherenceData
import all WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatAllIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule
import WeilConjectures.Algebra.Homology.AcyclicKFlatTensor
import WeilConjectures.Algebra.Homology.ChangeOfRingsTensorCancellationIndependentCoefficients
import WeilConjectures.CategoryTheory.DerivedCategory.KFlatAcyclic
import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitudeResidueIdeal
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import Mathlib.Algebra.Module.Torsion.Basic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle

/-! # Tensor vanishing for nilpotent quotient coefficients

Source: Stacks Project, more-algebra.tex, Tag 0G1T, proof of
lemma-derived-vanishing-mod-I, finite ideal-power filtration.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory Opposite

namespace CategoryTheory
namespace NilpotentCoefficientProof

-- The tip's high-priority `hasSheafify_of_essentiallySmall` (Hom-types in a successor universe)
-- fails hard on the universe constraint for these small sites; Mathlib's instance applies.
attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall

variable {C : Type u} [SmallCategory C] {T : GrothendieckTopology C}

private abbrev Mod (R : Sheaf T CommRingCat.{u}) := ConstantCompletion.Mod R
private abbrev Γ (R : Sheaf T CommRingCat.{u}) :=
  RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat RingCat)

private structure DescendedAction {A B M : Type u}
    [CommRing A] [CommRing B] [AddCommGroup M] [Module A M] (f : A →+* B) where
  action : Module B M
  equation : let := action; ∀ (a : A) (m : M), f a • m = a • m

@[irreducible] private def descendedAction {A B M : Type u}
    [CommRing A] [CommRing B] [AddCommGroup M] [Module A M]
    (f : A →+* B) (hf : Function.Surjective f)
    (hM : Module.IsTorsionBySet A M (RingHom.ker f)) : DescendedAction (M := M) f := by
  let := hM.module
  refine ⟨Module.compHom M (f.quotientKerEquivOfSurjective hf).symm.toRingHom, ?_⟩
  dsimp only
  intro a m
  change (f.quotientKerEquivOfSurjective hf).symm (f a) • m = a • m
  rw [RingHom.quotientKerEquivOfSurjective_symm_apply]
  rfl

private theorem exists_quotient_module
    {R S : Sheaf T CommRingCat.{u}} (q : R ⟶ S)
    (hq : ∀ U : C, Function.Surjective (q.hom.app (op U))) (N : Mod R)
    (hN : ∀ U : Cᵒᵖ, ∀ a ∈ RingHom.ker (q.hom.app U).hom,
      ∀ x : N.val.obj U, a • x = 0) :
    ∃ M : Mod S, Nonempty ((ConstantCompletion.res q).obj M ≅ N) := by
  let d (U : Cᵒᵖ) := descendedAction (q.hom.app U).hom (hq U.unop)
    (fun {x} {a} ↦ hN U a.val a.property x)
  let action (U : Cᵒᵖ) : Module (S.obj.obj U) (N.val.obj U) := (d U).action
  let resMap {U V : Cᵒᵖ} (f : U ⟶ V) : N.val.obj U → N.val.obj V :=
    fun x ↦ N.val.map f x
  have linear {U V : Cᵒᵖ} (f : U ⟶ V) (s : S.obj.obj U) (x : N.val.obj U) :
      resMap f (s • x) = S.obj.map f s • resMap f x := by
    obtain ⟨a, rfl⟩ := hq U.unop s
    have he : S.obj.map f (q.hom.app U a) = q.hom.app V (R.obj.map f a) :=
      ConcreteCategory.congr_hom (q.hom.naturality f).symm a
    calc
      resMap f (q.hom.app U a • x) = resMap f (a • x) :=
        congrArg (resMap f) ((d U).equation a x)
      _ = R.obj.map f a • resMap f x := N.val.map_smul f a x
      _ = q.hom.app V (R.obj.map f a) • resMap f x :=
        ((d V).equation (R.obj.map f a) (resMap f x)).symm
      _ = S.obj.map f (q.hom.app U a) • resMap f x :=
        congrArg (fun s : S.obj.obj V ↦ s • resMap f x) he.symm
  let P : PresheafOfModules.{u} (S.obj ⋙ forget₂ CommRingCat RingCat) :=
    { obj U := ModuleCat.of (S.obj.obj U) (N.val.obj U)
      map {U V} f := ModuleCat.ofHom
        (X := ModuleCat.of (S.obj.obj U) (N.val.obj U))
        (Y := (ModuleCat.restrictScalars (S.obj.map f).hom).obj
          (ModuleCat.of (S.obj.obj V) (N.val.obj V)))
        { toFun := resMap f
          map_add' := map_add (N.val.map f).hom
          map_smul' := linear f }
      map_id U := by ext x; exact ConcreteCategory.congr_hom (N.val.map_id U) x
      map_comp f g := by ext x; exact N.val.map_comp_apply f g x }
  let M : Mod S := ⟨P, N.isSheaf⟩
  let f : (ConstantCompletion.res q).obj M ⟶ N :=
    { val :=
        { app U := ModuleCat.ofHom
            (X := ((ConstantCompletion.res q).obj M).val.obj U) (Y := N.val.obj U)
            { toFun := fun x ↦ x
              map_add' := fun _ _ ↦ rfl
              map_smul' := fun a x ↦ (d U).equation a x }
          naturality := by intro U V g; ext x; rfl } }
  have : IsIso ((SheafOfModules.toSheaf _).map f) := by
    change IsIso (𝟙 ((SheafOfModules.toSheaf _).obj N))
    infer_instance
  have : IsIso f := isIso_of_reflects_iso f (SheafOfModules.toSheaf _)
  exact ⟨M, ⟨asIso f⟩⟩

private theorem tensor_restricted_acyclic
    {R S : Sheaf T CommRingCat.{u}} (q : R ⟶ S)
    (P : ringedSiteComplex R) (hP : P.IsKFlatTensor)
    (hE : (((ConstantCompletion.change q).mapHomologicalComplex (.up ℤ)).obj P).Acyclic)
    (M : Mod S) :
    (((ringedKoszulTensor R).obj P).obj ((HomologicalComplex.single _ (.up ℤ) 0).obj
      ((ConstantCompletion.res q).obj M))).Acyclic := by
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.monoidalCategory S
  let := SheafOfModules.symmetricCategory R
  let E := ConstantCompletion.change q
  let U := ConstantCompletion.res q
  let EP := (E.mapHomologicalComplex (.up ℤ)).obj P
  have hK := SheafOfModules.changeOfRings_isKFlat_independentCoefficients q P E
    (fun _ ↦ rfl) (fun g ↦ by simp only [eqToHom_refl, Category.id_comp, Category.comp_id]; rfl)
    ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).2 hP)
  have hac := SheafOfModules.tensor_acyclic_of_isKFlat EP
    ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat EP).1 hK) hE
    ((HomologicalComplex.single _ (.up ℤ) 0).obj M)
  have hleft : (((tensorLeft M).mapHomologicalComplex (.up ℤ)).obj EP).Acyclic :=
    hac.of_iso (CochainComplex.mapBifunctorSingle₁Iso (curriedTensor _) M EP)
  have hU := SheafOfModules.restrictScalars_exact_kflat
    ((sheafCompose T (forget₂ CommRingCat RingCat)).map q)
  have : PreservesFiniteLimits U := hU.1
  have : PreservesFiniteColimits U := hU.2
  obtain ⟨e, he⟩ :=
    SheafOfModules.exists_changeOfRings_tensorCancellation_independentCoefficients q
  let c : E ⋙ tensorLeft M ⋙ U ≅ tensorLeft (U.obj M) :=
    NatIso.ofComponents (e M) (by
      intro X Y g
      have hh := he (𝟙 M) g
      change U.map ((𝟙 M) ⊗ₘ E.map g) ≫ (e M Y).hom =
        (e M X).hom ≫ (U.map (𝟙 M) ⊗ₘ g) at hh
      rw [U.map_id, id_tensorHom, id_tensorHom] at hh
      exact hh)
  let t := (Functor.mapHomologicalComplexCompIso c (.up ℤ)).app P
  have hleftR : (((tensorLeft (U.obj M)).mapHomologicalComplex (.up ℤ)).obj P).Acyclic := by
    have hres : ((U.mapHomologicalComplex (.up ℤ)).obj
        (((tensorLeft M).mapHomologicalComplex (.up ℤ)).obj EP)).Acyclic :=
      fun i ↦ (hleft i).map U
    exact hres.of_iso t
  let br := (NatIso.mapHomologicalComplex
    (BraidedCategory.tensorLeftIsoTensorRight (U.obj M)) (.up ℤ)).app P
  exact (hleftR.of_iso br).of_iso
    (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _) (U.obj M) P).symm

end NilpotentCoefficientProof

/-- If ordinary extension of a flat-term K-flat complex is acyclic, its tensor with
any module killed by a power of the sectionwise quotient kernel is acyclic.

Source: Stacks Project, more-algebra.tex, Tag 0G1T, proof of
lemma-derived-vanishing-mod-I; Modules on Sites, Tags 03DD and 05V4.
(auxiliary; not a blueprint node).

Proof: global sections act on all morphisms of module sheaves. The finitely generated
ideal of these global scalars has a finite image/cokernel filtration on a module killed
by its m-th power. Each factor is killed by every generator, hence by the sectionwise
kernel. Such a factor has the unique quotient-ring action: lift a scalar along q;
annihilation of the kernel makes this independent of the lift. These actions commute
with restrictions and give an S-module sheaf with the original underlying sheaf.
Scalar extension of P is K-flat and acyclic. Its tensor with any S-module is acyclic;
restriction of scalars and balanced tensor cancellation give vanishing for each factor.
Fixed tensor with P descends to an exact functor on the derived category. Apply it to
the short-exact single-module triangles of the filtration and induct. At exponent zero,
the module itself is zero. Evaluation of global scalars carries their ideal powers into
the corresponding sectionwise ideal powers, so the stated annihilation implies the
annihilation used in the induction. No noetherian or boundedness assumption is used. -/
theorem tensor_acyclic_of_nilpotent_coefficient
    {C : Type u} [SmallCategory C] {T : GrothendieckTopology C}
    {R S : Sheaf T CommRingCat.{u}} (q : R ⟶ S) (r : ℕ)
    (b : Fin r → (R.obj ⋙ forget CommRingCat).sections)
    (hq : ∀ U : C, Function.Surjective (q.hom.app (op U)))
    (hker : ∀ U : C, RingHom.ker (q.hom.app (op U)).hom =
      Ideal.span (Set.range (fun i ↦ (b i).val (op U))))
    (P : ringedSiteComplex R) (hP : P.IsKFlatTensor)
    (hflat : ∀ i : ℤ, SheafOfModules.IsFlat (P.X i))
    (hE : (((ConstantCompletion.change q).mapHomologicalComplex (.up ℤ)).obj P).Acyclic)
    (N : ConstantCompletion.Mod R) (m : ℕ)
    (hN : ∀ U : Cᵒᵖ, ∀ a ∈
      (Ideal.span (Set.range (fun j : Fin r ↦ (b j).val U))) ^ m,
      ∀ x : N.val.obj U, a • x = 0) :
    (((ringedKoszulTensor R).obj P).obj
      ((HomologicalComplex.single _ (.up ℤ) 0).obj N)).Acyclic := by
  let A := ConstantCompletion.Mod R
  let G := NilpotentCoefficientProof.Γ R
  let : CommRing G := (RingCat.sectionsSubring
    (R.obj ⋙ forget₂ CommRingCat RingCat)).toCommRing
  let : Linear G A := SheafOfModules.homLinear R.obj _
  let v : Fin r → G := b
  let := HasDerivedCategory.standard A
  have hPf : ∀ i : ℤ, SheafOfModules.IsFlatOnSite (J := T) (R := R) (P.X i) := by
    intro i
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso R (P.X i)).symm (hflat i)
  obtain ⟨s, hs⟩ := SheafOfModules.KFlatFixedTensor.kFlat_fixed_tensor_triangulated R
  let := s
  obtain ⟨_, _, htri, ⟨c, _, _⟩, _⟩ := hs P
    ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).2 hP) hPf
  let F := (SheafOfModules.KFlatFixedTensor.derivedTensor R).obj (DerivedCategory.Q.obj P)
  let : F.CommShift ℤ := s.commShiftObj _
  have : F.IsTriangulated := htri.1
  have key : ∀ (e : ℕ) (M : A),
      (∀ a ∈ Ideal.span (Set.range v) ^ e, a • 𝟙 M = 0) →
      IsZero (F.obj ((DerivedCategory.singleFunctor A 0).obj M)) := by
    intro e
    induction e with
    | zero =>
      intro M hM
      have hz : IsZero M := (IsZero.iff_id_eq_zero M).2 (by
        simpa only [one_smul] using hM 1 (by simp))
      exact F.map_isZero ((DerivedCategory.singleFunctor A 0).map_isZero hz)
    | succ e ih =>
      intro M hM
      obtain ⟨D, hD, rfl, h₁, h₃⟩ :=
        exists_shortExact_of_smul_eq_zero_of_mem_pow_succ v hM
      have hann : ∀ U : Cᵒᵖ, ∀ a ∈ RingHom.ker (q.hom.app U).hom,
          ∀ x : D.X₃.val.obj U, a • x = 0 := by
        intro U a ha
        rw [hker U.unop] at ha
        have hg (j : Fin r) (x : D.X₃.val.obj U) : (b j).val U • x = 0 := by
          have hh := h₃ (v j) (Ideal.subset_span ⟨j, rfl⟩)
          exact congrArg (fun f : D.X₃ ⟶ D.X₃ ↦ f.val.app U x) hh
        induction ha using Submodule.span_induction with
        | mem a ha => obtain ⟨j, rfl⟩ := ha; exact hg j
        | zero => intro x; exact zero_smul _ _
        | add a z ha hz iha ihz => intro x; rw [add_smul, iha, ihz, add_zero]
        | smul a z hz ihz => intro x; rw [smul_eq_mul, mul_smul, ihz, smul_zero]
      obtain ⟨M₃, ⟨e₃⟩⟩ := NilpotentCoefficientProof.exists_quotient_module q hq D.X₃ hann
      have hac := NilpotentCoefficientProof.tensor_restricted_acyclic q P hP hE M₃
      have hz := (DerivedCategory.isZero_Q_obj_iff _).2 hac
      have hz' : IsZero (F.obj ((DerivedCategory.singleFunctor A 0).obj D.X₃)) :=
        (hz.of_iso (c.app _).symm).of_iso
          (F.mapIso ((DerivedCategory.singleFunctor A 0).mapIso e₃)).symm
      exact (F.mapTriangle.obj hD.singleTriangle).isZero₂_of_isZero₁₃
        (F.map_distinguished _ hD.singleTriangle_distinguished) (ih _ h₁) hz'
  have hglob : ∀ a ∈ Ideal.span (Set.range v) ^ m, a • 𝟙 N = 0 := by
    intro a ha
    ext U x
    change a.val U • x = 0
    let ev : G →+* R.obj.obj U := (Pi.evalRingHom _ U).comp
      (RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat RingCat)).subtype
    have he : Ideal.map ev (Ideal.span (Set.range v)) ≤
        Ideal.span (Set.range (fun j : Fin r ↦ (b j).val U)) := by
      rw [Ideal.map_span]
      apply Ideal.span_mono
      rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
      exact ⟨j, rfl⟩
    have hm := Ideal.mem_map_of_mem ev ha
    rw [Ideal.map_pow] at hm
    exact hN U _ ((pow_le_pow_left' he m) hm) x
  exact (DerivedCategory.isZero_Q_obj_iff _).1 ((key m N hglob).of_iso (c.app _))

end CategoryTheory
