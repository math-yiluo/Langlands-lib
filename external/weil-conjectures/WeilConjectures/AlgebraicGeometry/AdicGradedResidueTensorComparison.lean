/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicCoefficientFiltration
public import WeilConjectures.AlgebraicGeometry.CoefficientConstructibleConstantTensor
import WeilConjectures.Algebra.Homology.ChangeOfRingsTensorCancellationIndependentCoefficients
import WeilConjectures.Algebra.Homology.RingedKFlatSingleTensorComparison
public import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Finiteness.Basic

/-! # The residue module underlying an adic graded layer

Source: Stacks Project, Tag 09BR, second displayed isomorphism.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
universe u v w
open CategoryTheory CategoryTheory.ConstantCompletion
namespace AlgebraicGeometry.Scheme

/-- The kernel of the residue quotient annihilates the consecutive-power kernel.
Source: Stacks Tag 09BR
(auxiliary; not a blueprint node).
Proof: lift both factors to A. They lie in J and J^(n+1), so their product lies
in J^(n+2) and vanishes in the larger quotient. -/
theorem adicFiniteGradedModule_torsion {A : Type w} [CommRing A]
    (J : Ideal A) (n : ℕ) :
    Module.IsTorsionBySet (adicFiniteCoeff J (n + 1))
      (RingHom.ker (adicFiniteFactor J (Nat.le_succ n)))
      (RingHom.ker (adicFiniteFactor J (Nat.zero_le (n + 1)))) := by
  intro x b
  apply Subtype.ext
  change (b : adicFiniteCoeff J (n + 1)) * x = 0
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (b : adicFiniteCoeff J (n + 1))
  obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective
    (x : adicFiniteCoeff J (n + 1))
  have ha' : a ∈ J ^ 1 := Ideal.Quotient.eq_zero_iff_mem.mp (by
    change adicFiniteFactor J (Nat.zero_le (n + 1))
      (Ideal.Quotient.mk (J ^ (n + 1 + 1)) a) = 0
    rw [ha]
    exact b.property)
  have hc' : c ∈ J ^ (n + 1) := Ideal.Quotient.eq_zero_iff_mem.mp (by
    change adicFiniteFactor J (Nat.le_succ n)
      (Ideal.Quotient.mk (J ^ (n + 1 + 1)) c) = 0
    rw [hc]
    exact x.property)
  rw [← ha, ← hc, ← map_mul]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  simpa only [← pow_add, Nat.add_comm 1 (n + 1)] using Ideal.mul_mem_mul ha' hc'

/-- The same kernel, with its action descended through the surjective residue map.
This is a construction from the annihilation proof, with no choice of a module witness.
Source: Stacks Tag 09BR
(auxiliary; not a blueprint node). -/
def adicFiniteResidueGradedModule {A : Type w} [CommRing A] (J : Ideal A) (n : ℕ) :
    ModuleCat.{w} (adicFiniteCoeff J 0) :=
  let r := adicFiniteFactor J (Nat.zero_le (n + 1))
  let L := RingHom.ker (adicFiniteFactor J (Nat.le_succ n))
  letI := (adicFiniteGradedModule_torsion J n).module
  letI := Module.compHom L
    (r.quotientKerEquivOfSurjective
      (Ideal.Quotient.factor_surjective
        (Ideal.pow_le_pow_right (Nat.add_le_add_right (Nat.zero_le (n + 1)) 1)))).symm.toRingHom
  ModuleCat.of _ L

/-- The descended residue action agrees with the original larger-quotient action.
Source: Stacks Tag 09BR
(auxiliary; not a blueprint node).
Proof: the inverse kernel-quotient equivalence sends r(b) to the class of b;
the quotient-module action on that class is the original action of b. -/
theorem adicFiniteResidueGradedModule_smul {A : Type w} [CommRing A]
    (J : Ideal A) (n : ℕ) (b : adicFiniteCoeff J (n + 1))
    (x : RingHom.ker (adicFiniteFactor J (Nat.le_succ n))) :
    adicFiniteFactor J (Nat.zero_le (n + 1)) b •
      (show adicFiniteResidueGradedModule J n from x) = b • x := by
  let := (adicFiniteGradedModule_torsion J n).module
  change ((adicFiniteFactor J (Nat.zero_le (n + 1))).quotientKerEquivOfSurjective
    (Ideal.Quotient.factor_surjective
        (Ideal.pow_le_pow_right (Nat.add_le_add_right (Nat.zero_le (n + 1)) 1)))).symm
      (adicFiniteFactor J (Nat.zero_le (n + 1)) b) • x = b • x
  rw [RingHom.quotientKerEquivOfSurjective_symm_apply]
  rfl

/-- Restricting the constructed residue module gives exactly the original kernel module.
Source: Stacks Tag 09BR
(auxiliary; not a blueprint node). -/
def adicFiniteResidueGradedModule_restrictIso {A : Type w} [CommRing A]
    (J : Ideal A) (n : ℕ) :
    adicFiniteGradedModule J n ≅
      (ModuleCat.restrictScalars (adicFiniteFactor J (Nat.zero_le (n + 1)))).obj
        (adicFiniteResidueGradedModule J n) := by
  refine ModuleCat.isoMk (Iso.refl _) ?_
  intro b
  ext x
  exact adicFiniteResidueGradedModule_smul J n b x

/-- Noetherianity makes the constructed residue module finite.
Source: Stacks Tag 09BR
(auxiliary; not a blueprint node).
Proof: the kernel is an ideal in the Noetherian larger quotient, so it is finite
over that quotient. The identity semilinear map, with scalar map the residue
surjection, carries its finite generating set to generators over the residue ring. -/
theorem adicFiniteResidueGradedModule_finite {A : Type w} [CommRing A]
    [IsNoetherianRing A] (J : Ideal A) (n : ℕ) :
    Module.Finite (adicFiniteCoeff J 0) (adicFiniteResidueGradedModule J n) := by
  let B := adicFiniteCoeff J (n + 1)
  let L := RingHom.ker (adicFiniteFactor J (Nat.le_succ n))
  let r := adicFiniteFactor J (Nat.zero_le (n + 1))
  let f : L →ₛₗ[r] adicFiniteResidueGradedModule J n :=
    { toFun := id
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun b x ↦ (adicFiniteResidueGradedModule_smul J n b x).symm }
  exact Module.Finite.of_surjective f Function.surjective_id

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local instance] SheafOfModules.monoidalCategory
  SheafOfModules.symmetricCategory SheafOfModules.isMonoidal_W_independentCoefficients
attribute [local irreducible] HasDerivedCategory.standard
  SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory
  derivedExtension

-- Cancellation, as a natural isomorphism in the complex to be resolved.
private theorem gradedCancellation {E : Type w} [SmallCategory E]
    {T : GrothendieckTopology E} {R S : Sheaf T CommRingCat.{w}}
    (φ : R ⟶ S) (M : Mod S) :
    Nonempty ((SheafOfModules.KFlatFixedTensor.ordinaryTensor R).flip.obj ((res φ).obj M) ≅
      change φ ⋙ (SheafOfModules.KFlatFixedTensor.ordinaryTensor S).flip.obj M ⋙ res φ) := by
  obtain ⟨e, he⟩ :=
    SheafOfModules.exists_changeOfRings_tensorCancellation_independentCoefficients φ
  let c : change φ ⋙ MonoidalCategory.tensorLeft M ⋙ res φ ≅
      MonoidalCategory.tensorLeft ((res φ).obj M) :=
    NatIso.ofComponents (fun N ↦ e M N) (by
      intro N N' g
      have h := he (𝟙 M) g
      change (res φ).map (MonoidalCategory.tensorHom (𝟙 M) ((change φ).map g)) ≫ _ =
        _ ≫ MonoidalCategory.tensorHom ((res φ).map (𝟙 M)) g at h
      have hid : (res φ).map (𝟙 M) = 𝟙 ((res φ).obj M) := (res φ).map_id M
      rw [hid, MonoidalCategory.id_tensorHom, MonoidalCategory.id_tensorHom] at h
      exact h)
  exact ⟨(BraidedCategory.tensorLeftIsoTensorRight ((res φ).obj M)).symm ≪≫
    c.symm ≪≫ Functor.isoWhiskerLeft (change φ)
      (Functor.isoWhiskerRight (BraidedCategory.tensorLeftIsoTensorRight M) (res φ))⟩

-- Only the first tensor factor is resolved; the module in degree zero is arbitrary.
private theorem gradedSingleProjection {E : Type w} [SmallCategory E]
    {T : GrothendieckTopology E} {R S : Sheaf T CommRingCat.{w}}
    (φ : R ⟶ S) (N : D R) (M : Mod S) :
    let := HasDerivedCategory.standard (Mod R)
    let := HasDerivedCategory.standard (Mod S)
    Nonempty (((SheafOfModules.KFlatFixedTensor.derivedTensor R).obj N).obj
        ((Q R).obj ((HomologicalComplex.single (Mod R) (.up ℤ) 0).obj ((res φ).obj M))) ≅
      (dres φ).obj (((SheafOfModules.KFlatFixedTensor.derivedTensor S).obj
        ((extend φ).obj N)).obj
          ((Q S).obj ((HomologicalComplex.single (Mod S) (.up ℤ) 0).obj M)))) := by
  let := HasDerivedCategory.standard (Mod R)
  let := HasDerivedCategory.standard (Mod S)
  let G := (Q R).objPreimage N
  obtain ⟨P, q, hP, _, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients G
  have := hq
  let e : (Q R).obj P ≅ N := asIso ((Q R).map q) ≪≫ (Q R).objObjPreimageIso N
  let P' := ((change φ).mapHomologicalComplex (.up ℤ)).obj P
  have hP' : CochainComplex.IsKFlatIndependentCoefficients P' := by
    apply SheafOfModules.changeOfRings_isKFlat_independentCoefficients φ P (change φ)
      (fun _ ↦ rfl) ?_ hP
    intro M M' f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  have : IsIso ((extendComparison φ).app P) :=
    (derivedExtension φ).computation P
      ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).mp hP)
  let d : (Q S).obj P' ≅ (extend φ).obj N :=
    (asIso ((extendComparison φ).app P)).symm ≪≫ (extend φ).mapIso e
  obtain ⟨cR, _⟩ := SheafOfModules.ringed_kFlat_single_tensor_comparison R
  obtain ⟨cS, _⟩ := SheafOfModules.ringed_kFlat_single_tensor_comparison S
  obtain ⟨o⟩ := gradedCancellation φ M
  let tS := (SheafOfModules.KFlatFixedTensor.ordinaryTensor S).flip.obj M
  let tR := (SheafOfModules.KFlatFixedTensor.ordinaryTensor R).flip.obj ((res φ).obj M)
  let b : (tR.mapHomologicalComplex (.up ℤ)).obj P ≅
      ((res φ).mapHomologicalComplex (.up ℤ)).obj
        ((tS.mapHomologicalComplex (.up ℤ)).obj P') :=
    HomologicalComplex.Hom.isoOfComponents (fun i ↦ o.app (P.X i))
      (fun i j _ ↦ (o.hom.naturality (P.d i j)).symm)
  let FR := SheafOfModules.KFlatFixedTensor.derivedTensor R
  let FS := SheafOfModules.KFlatFixedTensor.derivedTensor S
  exact ⟨(FR.mapIso e.symm).app _ ≪≫ cR P hP ((res φ).obj M) ≪≫
    (Q R).mapIso b ≪≫
    (resFactors φ).app ((tS.mapHomologicalComplex (.up ℤ)).obj P') ≪≫
    (dres φ).mapIso ((cS P' hP' M).symm ≪≫ (FS.mapIso d).app _)⟩

section ConstantRestriction
variable {E : Type w} [SmallCategory E] (T : GrothendieckTopology E)
  {B C : Type w} [CommRing B] [CommRing C]

@[instance_reducible, no_expose]
private def gradedSectionModule (S : Sheaf T CommRingCat.{w}) (M : Mod S) (U : Eᵒᵖ) :
    Module (S.obj.obj U) (M.val.obj U) := (M.val.obj U).isModule

attribute [local instance 10000] gradedSectionModule

-- The constant-module unit, with its scalar action precomposed by the ring map.
private def gradedConstantSeed (p : B →+* C) (M : ModuleCat.{w} C) :
    (siteConstantModulePresheafGeneral (C := E) B).obj
        ((ModuleCat.restrictScalars p).obj M) ⟶
      (PresheafOfModules.restrictScalars (realizationRingUnit T B)).obj
        ((res (adicFiniteConstantMap p T)).obj
          ((commutativeSiteConstantModuleFunctor T C).obj M)).val := by
  let := (realizationRingUnit_locallyBijective T C).1
  let := (realizationRingUnit_locallyBijective T C).2
  let η := (PresheafOfModules.sheafificationAdjunction
    (realizationRingUnit T C)).unit.app
      ((siteConstantModulePresheafGeneral (C := E) C).obj M)
  let P := (siteConstantModulePresheafGeneral (C := E) B).obj
    ((ModuleCat.restrictScalars p).obj M)
  let H := ((res (adicFiniteConstantMap p T)).obj
    ((commutativeSiteConstantModuleFunctor T C).obj M)).val
  exact
    { app U := ModuleCat.ofHom (X := P.obj U)
        (Y := ((PresheafOfModules.restrictScalars (realizationRingUnit T B)).obj H).obj U)
        { toFun := η.app U
          map_add' := map_add _
          map_smul' := by
            intro b m
            change B at b
            change M at m
            change η.app U (p b • m) =
              (adicFiniteConstantMap p T).hom.app U
                ((realizationRingUnit T B).app U b) •
                (show ((commutativeSiteConstantModuleFunctor T C).obj M).val.obj U from
                  η.app U m)
            have h := toSheafify_naturality T
              ((Functor.const Eᵒᵖ).map (CommRingCat.ofHom p))
            have hb := ConcreteCategory.congr_hom (congr_app h U) b
            change (realizationRingUnit T C).app U (p b) =
              (adicFiniteConstantMap p T).hom.app U
                ((realizationRingUnit T B).app U b) at hb
            rw [← hb]
            exact (η.app U).hom.map_smul (p b) m }
      naturality := by
        intro U V f
        ext m
        exact ConcreteCategory.congr_hom (η.naturality f) m }

private theorem gradedConstantSeed_locallyBijective (p : B →+* C) (M : ModuleCat.{w} C) :
    Presheaf.IsLocallyInjective T ((PresheafOfModules.toPresheaf _).map
        (gradedConstantSeed T p M)) ∧
      Presheaf.IsLocallySurjective T ((PresheafOfModules.toPresheaf _).map
        (gradedConstantSeed T p M)) := by
  let P := (siteConstantModulePresheafGeneral (C := E) C).obj M
  constructor
  · constructor
    intro U x y h
    exact Presheaf.equalizerSieve_mem T (toSheafify T P.presheaf) x y h
  · constructor
    intro U s
    exact Presheaf.imageSieve_mem T (toSheafify T P.presheaf) s

attribute [local irreducible] gradedConstantSeed

@[no_expose]
private def gradedConstantHom (p : B →+* C) (M : ModuleCat.{w} C) :
    (commutativeSiteConstantModuleFunctor T B).obj
        ((ModuleCat.restrictScalars p).obj M) ⟶
      (res (adicFiniteConstantMap p T)).obj
        ((commutativeSiteConstantModuleFunctor T C).obj M) :=
  letI := (realizationRingUnit_locallyBijective T B).1
  letI := (realizationRingUnit_locallyBijective T B).2
  (PresheafOfModules.sheafificationHomEquiv (realizationRingUnit T B)).symm
    (gradedConstantSeed T p M)

private theorem gradedConstantHom_isIso (p : B →+* C) (M : ModuleCat.{w} C) :
    IsIso (gradedConstantHom T p M) := by
  let := (realizationRingUnit_locallyBijective T B).1
  let := (realizationRingUnit_locallyBijective T B).2
  let P := (siteConstantModulePresheafGeneral (C := E) B).obj
    ((ModuleCat.restrictScalars p).obj M)
  let F := SheafOfModules.toSheaf (siteModuleRings (constant T B))
  let g := (PresheafOfModules.toPresheaf _).map (gradedConstantSeed T p M)
  let h := F.map (gradedConstantHom T p M)
  have he : toSheafify T P.presheaf ≫ h.hom = g := by
    have he := congrArg ((PresheafOfModules.toPresheaf _).map)
      ((PresheafOfModules.sheafificationHomEquiv (realizationRingUnit T B)
        (P := P) (F := (res (adicFiniteConstantMap p T)).obj
          ((commutativeSiteConstantModuleFunctor T C).obj M))).apply_symm_apply
        (gradedConstantSeed T p M))
    rw [PresheafOfModules.toPresheaf_map_sheafificationHomEquiv_def] at he
    exact he
  have hg₁ : Presheaf.IsLocallyInjective T g :=
    (gradedConstantSeed_locallyBijective T p M).1
  have hg₂ : Presheaf.IsLocallySurjective T g :=
    (gradedConstantSeed_locallyBijective T p M).2
  have hi : Presheaf.IsLocallyInjective T (toSheafify T P.presheaf ≫ h.hom) :=
    he.symm ▸ hg₁
  have hs : Presheaf.IsLocallySurjective T (toSheafify T P.presheaf ≫ h.hom) :=
    he.symm ▸ hg₂
  have : Presheaf.IsLocallyInjective T h.hom :=
    (Presheaf.comp_isLocallyInjective_iff T (toSheafify T P.presheaf) h.hom).mp hi
  have : Presheaf.IsLocallySurjective T h.hom :=
    (Presheaf.comp_isLocallySurjective_iff T (toSheafify T P.presheaf) h.hom).mp hs
  have : IsIso h := (Sheaf.isLocallyBijective_iff_isIso h).mp
    ⟨inferInstance, inferInstance⟩
  exact isIso_of_reflects_iso (gradedConstantHom T p M) F

attribute [local irreducible] gradedConstantHom

@[no_expose]
private def gradedConstantIso (p : B →+* C) (M : ModuleCat.{w} C) :
    (commutativeSiteConstantModuleFunctor T B).obj
        ((ModuleCat.restrictScalars p).obj M) ≅
      (res (adicFiniteConstantMap p T)).obj
        ((commutativeSiteConstantModuleFunctor T C).obj M) :=
  letI := gradedConstantHom_isIso T p M
  asIso (gradedConstantHom T p M)
end ConstantRestriction

attribute [local irreducible] gradedConstantIso

/-- The actual graded layer is the restriction of one tensor over the residue ring.
This comparison has no constructibility or cohomological boundedness assumption.

Source: Stacks Project, proetale.tex, Tag 09BR,
lemma-compare-truncations-constructible, second displayed isomorphism;
Cohomology on Sites, Tags 06YY and 06YU, derived change of rings and tensor.
(auxiliary; not a blueprint node).

Proof: write B=A/J^(n+2), C=A/J and I=ker(B -> A/J^(n+1)). The preceding
annihilation calculation equips I with exactly the constructed C-action.
Its restriction is the original B-module via the identity on elements.
Take a termwise-flat K-flat representative P of N. The actual extension of P
to B is still K-flat. Tensor it with a K-flat resolution of the constant I.
Tensor cancellation computes the resulting object by P tensor_A I, with its
B-action retained. The same calculation over C computes the tensor of the
residue extension of P and the constant C-module I by the same complex.
The balancing maps send (p tensor b) tensor i to p tensor bi and their inverses
send p tensor i to (p tensor 1) tensor i. These respect the scalar actions,
restrictions and total differentials. Exact scalar restriction and the selected
K-flat computation isomorphisms give the displayed comparison. The argument
also applies to J=0, J=top, the zero ring and the empty scheme. -/
theorem adicFiniteGradedLayer_residueTensor (X : Scheme.{u})
    {A : Type (max v (u + 1))} [CommRing A] (J : Ideal A)
    (N : adicFiniteAmbient.{u, v} X A) (n : ℕ) :
    Nonempty (adicFiniteGradedLayer.{u, v} X J N n ≅
      (dres (adicFiniteConstantMap (adicFiniteFactor J (Nat.zero_le (n + 1)))
        (coefficientProEtaleModelTopology.{u, v} X))).obj
          (coefficientConstantTensor.{u, v} X (adicFiniteCoeff J 0)
            (adicFiniteReduction.{u, v} X J N 0) (adicFiniteResidueGradedModule J n))) := by
  let T := coefficientProEtaleModelTopology.{u, v} X
  let B := adicFiniteCoeff J (n + 1)
  let C := adicFiniteCoeff J 0
  let R := constant T B
  let S := constant T C
  let r := adicFiniteFactor J (Nat.zero_le (n + 1))
  let φ := adicFiniteConstantMap r T
  let := HasDerivedCategory.standard (Mod R)
  let := HasDerivedCategory.standard (Mod S)
  let M := (commutativeSiteConstantModuleFunctor T C).obj
    (adicFiniteResidueGradedModule J n)
  let eM : (commutativeSiteConstantModuleFunctor T B).obj (adicFiniteGradedModule J n) ≅
      (res φ).obj M :=
    (commutativeSiteConstantModuleFunctor T B).mapIso
      (adicFiniteResidueGradedModule_restrictIso J n) ≪≫
        gradedConstantIso T r (adicFiniteResidueGradedModule J n)
  obtain ⟨e⟩ := gradedSingleProjection φ (adicFiniteReduction.{u, v} X J N (n + 1)) M
  let F := SheafOfModules.KFlatFixedTensor.derivedTensor R
  let G := SheafOfModules.KFlatFixedTensor.derivedTensor S
  exact ⟨(F.obj (adicFiniteReduction.{u, v} X J N (n + 1))).mapIso
    ((Q R).mapIso ((HomologicalComplex.single (Mod R) (.up ℤ) 0).mapIso eM)) ≪≫ e ≪≫
      (dres φ).mapIso ((G.mapIso
        (adicFiniteRho.{u, v} X J N (Nat.zero_le (n + 1)))).app _)⟩

end AlgebraicGeometry.Scheme
