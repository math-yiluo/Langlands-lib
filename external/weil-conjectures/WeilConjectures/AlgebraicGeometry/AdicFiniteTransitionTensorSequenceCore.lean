/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicFiniteReductionData
public import WeilConjectures.AlgebraicGeometry.CoefficientTorFlatModel
import WeilConjectures.Algebra.Homology.ChangeOfRingsTensorCancellationIndependentCoefficients
import WeilConjectures.AlgebraicGeometry.AdicFiniteStrictReductionSuccessor
import WeilConjectures.AlgebraicGeometry.AdicFiniteTransitionKernelTensor
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionCore
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionInverseImage
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle

/-! # The transition-sequence construction after choosing a residue model

The short exact sequence is the kernel sequence of the actual strict reduction map.
Its normalization, residue balancing and representative independence are proved here;
only the ordinary flat-tensor kernel identification is delegated to its own module.
Source: Stacks Project, proetale.tex, Tag 09C2, proof of (1), and Tags 06YS and 06YY.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.ConstantCompletion
open MonoidalCategory
namespace AlgebraicGeometry.Scheme

attribute [local irreducible] HasDerivedCategory.standard DerivedCategory.Q
  derivedExtension adicFiniteTransition adicFiniteStrictReductionLevel
  adicFiniteUnderlying adicFiniteStrictReductionEvaluationIso

private theorem constant_surjective {C : Type w} [SmallCategory C]
    (T : GrothendieckTopology C) {B D : CommRingCat.{w}} (f : B ⟶ D)
    (hf : Function.Surjective f) (U : Cᵒᵖ) :
    Function.Surjective (((constantSheaf T CommRingCat.{w}).map f).hom.app U) := by
  classical
  let e := constantCommuteCompose T (CategoryTheory.forget CommRingCat.{w})
  let s := (constantSheaf T (Type w)).map (TypeCat.ofHom (Function.surjInv hf))
  have hs : s ≫ (constantSheaf T (Type w)).map ((CategoryTheory.forget _).map f) = 𝟙 _ := by
    rw [← Functor.map_comp]
    trans (constantSheaf T (Type w)).map (𝟙 ((CategoryTheory.forget CommRingCat.{w}).obj D))
    · congr 1
      ext x
      exact Function.surjInv_eq hf x
    exact (constantSheaf T (Type w)).map_id _
  let r := e.hom.app D ≫ s ≫ e.inv.app B
  have hr : r ≫ (sheafCompose T (CategoryTheory.forget CommRingCat.{w})).map
      ((constantSheaf T CommRingCat.{w}).map f) = 𝟙 _ := by
    dsimp only [r]
    rw [Category.assoc, Category.assoc]
    change e.hom.app D ≫ s ≫ e.inv.app B ≫
      (constantSheaf T CommRingCat.{w} ⋙
        sheafCompose T (CategoryTheory.forget CommRingCat.{w})).map f = _
    rw [← e.inv.naturality f]
    change e.hom.app D ≫ s ≫
      (constantSheaf T (Type w)).map ((CategoryTheory.forget _).map f) ≫ e.inv.app D = _
    rw [← Category.assoc s, hs, Category.id_comp, e.hom_inv_id_app D]
  intro x
  exact ⟨r.hom.app U x, congrArg (fun h ↦ h.hom.app U x) hr⟩

private theorem reductionStep_epi {C : Type w} [SmallCategory C]
    (T : GrothendieckTopology C) (A : Type w) [CommRing A] (J : Ideal A) (n : ℕ)
    (M : Mod (constant T A)) : Epi ((reductionStep T A J false n).app M) := by
  constructor
  intro Z a b hab
  apply restrictedTensor_hom_ext (quotient T A J n) M Z a b
  intro U s m
  have hq : Function.Surjective (Ideal.Quotient.factorPow J
      (Nat.add_le_add_right (Nat.le_succ n) 1)) := by
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨Ideal.Quotient.mk _ x, rfl⟩
  obtain ⟨t, ht⟩ := constant_surjective T (CommRingCat.ofHom
    (Ideal.Quotient.factorPow J (Nat.add_le_add_right (Nat.le_succ n) 1))) hq U s
  have h := congrArg (fun f ↦ f.val.app U
    (tensorSection (quotient T A J (n + 1)) M U t m)) hab
  have hstep := (reductionStep_existsUnique T A J false n).exists.choose_spec M U t m
  change ((reductionStep T A J false n).app M).val.app U
      (tensorSection (quotient T A J (n + 1)) M U t m) =
    tensorSection (quotient T A J n) M U ((transition T A J n).hom.app U t) m at hstep
  change (transition T A J n).hom.app U t = s at ht
  change a.val.app U (((reductionStep T A J false n).app M).val.app U _) =
    b.val.app U (((reductionStep T A J false n).app M).val.app U _) at h
  rw [hstep, ht] at h
  exact h

private theorem transitionKernel_homology
    {C : Type w} [SmallCategory C] (T : GrothendieckTopology C)
    (A : Type w) [CommRing A] (J : Ideal A)
    (K : Cx (constant T A)) (hflat : ∀ q : ℤ, SheafOfModules.IsFlat (K.X q))
    (n : ℕ) (q : ℤ) :
    Nonempty ((kernel ((reductionComplex T A J false K).asFunctor.map
        (homOfLE (Nat.le_succ n)).op)).homology q ≅
      (res (quotient T A J 0)).obj
        (coefficientModelTensorTest _
          (((change (quotient T A J 0)).mapHomologicalComplex (.up ℤ)).obj K)
          (adicFiniteCoefficientKernelSheaf T A J n) q)) := by
  let R := constant T A
  let R₀ := constant T (adicFiniteCoeff J 0)
  let f := quotient T A J 0
  let E := change f
  let U := res f
  let M := adicFiniteCoefficientKernelSheaf T A J n
  let K₀ := (E.mapHomologicalComplex (.up ℤ)).obj K
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.monoidalCategory R₀
  let := SheafOfModules.symmetricCategory R₀
  obtain ⟨e, he⟩ :=
    SheafOfModules.exists_changeOfRings_tensorCancellation_independentCoefficients f
  let c : E ⋙ MonoidalCategory.tensorLeft M ⋙ U ≅
      MonoidalCategory.tensorLeft (U.obj M) :=
    NatIso.ofComponents (e M) (by
      intro X Y g
      have hh := he (𝟙 M) g
      change U.map ((𝟙 M) ⊗ₘ E.map g) ≫ (e M Y).hom =
        (e M X).hom ≫ (U.map (𝟙 M) ⊗ₘ g) at hh
      rw [U.map_id, MonoidalCategory.id_tensorHom,
        MonoidalCategory.id_tensorHom] at hh
      exact hh)
  let W := ((MonoidalCategory.tensorLeft M).mapHomologicalComplex (.up ℤ)).obj K₀
  let cK : (U.mapHomologicalComplex (.up ℤ)).obj W ≅
      ((MonoidalCategory.tensorLeft (U.obj M)).mapHomologicalComplex (.up ℤ)).obj K :=
    (Functor.mapHomologicalComplexCompIso c (.up ℤ)).app K
  let B := ((ringedKoszulTensor R₀).obj K₀).obj
    ((HomologicalComplex.single (Mod R₀) (.up ℤ) 0).obj M)
  let b : B ≅ W :=
    CochainComplex.mapBifunctorSingle₂Iso (MonoidalCategory.curriedTensor _) M K₀ ≪≫
      (NatIso.mapHomologicalComplex
        (BraidedCategory.tensorLeftIsoTensorRight M).symm (.up ℤ)).app K₀
  obtain ⟨ek⟩ := adicFiniteTransitionKernel_tensor T A J K hflat n
  let ec := ek ≪≫ cK.symm ≪≫ (U.mapHomologicalComplex (.up ℤ)).mapIso b.symm
  have := (siteRestrictScalars_exact f).1
  have := (siteRestrictScalars_exact f).2
  exact ⟨(HomologicalComplex.homologyFunctor (Mod R) (.up ℤ) q).mapIso ec ≪≫
    (B.sc q).mapHomologyIso U⟩

/--
The remaining coefficient-kernel part of the normalized adic transition construction.

Source: Stacks Project, proetale.tex, Tag 09C2, proof of (1), using the coefficient
sequence and K-flat computations of Tags 06YS and 06YY.
(auxiliary; not a blueprint node).

Proof: Choose a flat-term K-flat representative K of N. The strict reduction successor
is epic: every coefficient section lifts through the constant quotient factor (a set
section of the surjective ring map gives a section after constant sheafification),
and the reductionStep tensor formula and tensor extensionality prove cancellation.
Its canonical kernel sequence S is therefore short exact. The existing strict-level
comparison and normalized successor square give the two endpoint isomorphisms and
identify the localized second arrow with adicFiniteTransition. The coefficient
module M is explicitly constructed from the kernel of A/J^(n+2) -> A/J^(n+1);
a proved annihilation statement gives its A/J action. Apply the ordinary flat-tensor
kernel identification to S.X1. Scalar tensor cancellation, the single-factor total
tensor comparison and exact restriction on homology identify its homology with the
tensor test of the residue reduction of K and M. Finally that residue reduction is
K-flat and represents the same derived object as P; coefficientModelTensorTest_iso
transports the tensor homology to the supplied P. All constructions include zero
and unit ideals and the empty site. -/
theorem adicFiniteTransition_tensor_sequence_core
    (X : Scheme.{u}) (A : Type (max v (u + 1))) [CommRing A] (J : Ideal A)
    (N : adicFiniteAmbient.{u, v} X A) (n : ℕ)
    (P : Cx (constant (coefficientProEtaleModelTopology.{u, v} X)
      (adicFiniteCoeff J 0)))
    (_hP : P.IsKFlatIndependentCoefficients)
    (_eP : Nonempty ((Q _).obj P ≅ adicFiniteReduction.{u, v} X J N 0)) :
    ∃ (M : Mod (constant (coefficientProEtaleModelTopology.{u, v} X)
        (adicFiniteCoeff J 0)))
      (S : ShortComplex (Cx (constant (coefficientProEtaleModelTopology.{u, v} X) A))),
      S.ShortExact ∧
      ∃ (e₂ : (Q _).obj S.X₂ ≅ adicFiniteUnderlying.{u, v} X J N (n + 1))
        (e₃ : (Q _).obj S.X₃ ≅ adicFiniteUnderlying.{u, v} X J N n),
        (Q _).map S.g ≫ e₃.hom = e₂.hom ≫ adicFiniteTransition.{u, v} X J N n ∧
        ∀ q : ℤ, Nonempty (S.X₁.homology q ≅
          (res (quotient (coefficientProEtaleModelTopology.{u, v} X) A J 0)).obj
            (coefficientModelTensorTest _ P M q)) := by
  let T := coefficientProEtaleModelTopology.{u, v} X
  let R := constant T A
  let R₀ := constant T (adicFiniteCoeff J 0)
  let f := quotient T A J 0
  obtain ⟨K, hK, hflat, ⟨eK⟩⟩ := exists_coefficientModelFlatKFlatRepresentative R N
  have hk : K.IsKFlatTensor :=
    (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat K).mp hK
  let K₀ : Cx R₀ := ((change f).mapHomologicalComplex (.up ℤ)).obj K
  have hk₀ : K₀.IsKFlatIndependentCoefficients :=
    (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat K₀).mpr
      (change_flat_kFlat f K hk hflat).1
  have hc : IsIso ((extendComparison f).app K) := (derivedExtension f).computation K hk
  let e₀ : (Q R₀).obj K₀ ≅ adicFiniteReduction X J N 0 :=
    (asIso ((extendComparison f).app K)).symm ≪≫ (extend f).mapIso eK
  obtain ⟨eP⟩ := _eP
  let M := adicFiniteCoefficientKernelSheaf T A J n
  let U := (reductionComplex T A J false K).asFunctor
  let g := U.map (homOfLE (Nat.le_succ n)).op
  have hg : Epi g := by
    apply HomologicalComplex.epi_of_epi_f
    intro i
    change Epi (((Functor.ofOpSequence (reductionStep T A J false)).map
      (homOfLE (Nat.le_succ n)).op).app (K.X i))
    rw [Functor.ofOpSequence_map_homOfLE_succ]
    exact reductionStep_epi T A J n (K.X i)
  let S := ShortComplex.kernelSequence g
  have hs : S.ShortExact := by
    change (ShortComplex.kernelSequence g).ShortExact
    exact { exact := ShortComplex.kernelSequence_exact g
            mono_f := by change Mono (kernel.ι g); infer_instance
            epi_g := by change Epi g; exact hg }
  have hnorm := adicFiniteStrictReduction_successor.{u, v} X A J K hk hflat N eK n
  let e₂ := (adicFiniteStrictReductionLevel.{u, v} X A J K hk N eK (n + 1)).symm
  let e₃ := (adicFiniteStrictReductionLevel.{u, v} X A J K hk N eK n).symm
  refine ⟨M, S, hs, e₂, e₃, ?_, ?_⟩
  · simpa only [Functor.comp_map, S, ShortComplex.kernelSequence, e₂, e₃,
      Iso.symm_hom, g, U] using hnorm
  · intro q
    obtain ⟨ek⟩ := transitionKernel_homology T A J K hflat n q
    obtain ⟨ep⟩ := coefficientModelTensorTest_iso R₀ K₀ P hk₀ _hP
      (e₀ ≪≫ eP.symm) M q
    exact ⟨ek ≪≫ (res f).mapIso ep⟩

end AlgebraicGeometry.Scheme
