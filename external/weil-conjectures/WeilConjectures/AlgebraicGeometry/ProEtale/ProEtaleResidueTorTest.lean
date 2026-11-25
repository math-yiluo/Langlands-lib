/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitude
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleResidueModuleTensorHomology
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

/-!
# The residue test on the small pro-etale site
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Scheme

namespace ResidueTensor

open MonoidalCategory

section

variable {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u + 1})

set_option hygiene false in
local notation "𝒜" => SheafOfModules.{u + 1}
  ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)

private local instance : HasSheafify J AddCommGrpCat.{u + 1} := inferInstance
private local instance : J.WEqualsLocallyBijective AddCommGrpCat.{u + 1} := inferInstance

private local instance :
    letI := SheafOfModules.monoidalCategory R
    MonoidalPreadditive 𝒜 :=
  SheafOfModules.tensorPreadditive.{u + 1, u, u + 1} R

set_option synthInstance.maxSize 2048 in
set_option maxRecDepth 2048 in
private theorem tensor_right_quasiIso
    {E E' P : CochainComplex 𝒜 ℤ} (f : E ⟶ E') (hf : QuasiIso f)
    (hP : P.IsAcyclicTensorKFlat) :
    letI := SheafOfModules.monoidalCategory R
    QuasiIso (HomologicalComplex.mapBifunctorMap f (𝟙 P) (curriedTensor _) (.up ℤ)) := by
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.tensorPreadditive.{u + 1, u, u + 1} R
  have hc := (CochainComplex.mappingCone.quasiIso_iff_acyclic f).1 hf
  have ht := hP (CochainComplex.mappingCone f) hc
  apply (CochainComplex.mappingCone.quasiIso_iff_acyclic _).2
  intro i
  exact (ht i).of_iso (CochainComplex.mapBifunctorMappingCone₁Iso f P (curriedTensor _))

set_option synthInstance.maxSize 2048 in
set_option maxRecDepth 2048 in
private theorem tensor_left_quasiIso
    {P E E' : CochainComplex 𝒜 ℤ} (f : E ⟶ E') (hf : QuasiIso f)
    (hP : P.IsAcyclicTensorKFlat) :
    letI := SheafOfModules.monoidalCategory R
    QuasiIso (HomologicalComplex.mapBifunctorMap (𝟙 P) f (curriedTensor _) (.up ℤ)) := by
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let := SheafOfModules.tensorPreadditive.{u + 1, u, u + 1} R
  have hc := (CochainComplex.mappingCone.quasiIso_iff_acyclic f).1 hf
  have ht := hP (CochainComplex.mappingCone f) hc
  let F := curriedTensor 𝒜
  let e : (((F.mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj
      (CochainComplex.mappingCone f)).obj P) ≅
      (((F.flip.mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj
      (CochainComplex.mappingCone f)).obj P) :=
    HomologicalComplex.Hom.isoOfComponents
      (fun p ↦ HomologicalComplex.Hom.isoOfComponents
        (fun q ↦ β_ ((CochainComplex.mappingCone f).X p) (P.X q)) (by
          intro q q' hqq'
          exact (BraidedCategory.braiding_naturality_right
            ((CochainComplex.mappingCone f).X p) (P.d q q')).symm)) (by
        intro p p' hpp'
        ext q : 1
        exact (BraidedCategory.braiding_naturality_left
          ((CochainComplex.mappingCone f).d p p') (P.X q)).symm)
  have ht' : (CochainComplex.mapBifunctor P (CochainComplex.mappingCone f) F).Acyclic := by
    intro i
    exact (ht i).of_iso (HomologicalComplex₂.total.mapIso e (.up ℤ) ≪≫
      HomologicalComplex.mapBifunctorFlipIso P (CochainComplex.mappingCone f) F (.up ℤ))
  apply (CochainComplex.mappingCone.quasiIso_iff_acyclic _).2
  intro i
  exact (ht' i).of_iso (CochainComplex.mapBifunctorMappingCone₂Iso P f F)

set_option synthInstance.maxSize 2048 in
set_option maxRecDepth 2048 in
private theorem tensor_homology_iso
    [HasDerivedCategory 𝒜] (P Q N : CochainComplex 𝒜 ℤ)
    (hP : P.IsAcyclicTensorKFlat) (hQ : Q.IsAcyclicTensorKFlat)
    (e : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj Q) (i : ℤ) :
    letI := SheafOfModules.monoidalCategory R
    Nonempty ((CochainComplex.mapBifunctor P N (curriedTensor _)).homology i ≅
      (CochainComplex.mapBifunctor Q N (curriedTensor _)).homology i) := by
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.tensorPreadditive.{u + 1, u, u + 1} R
  obtain ⟨S, s, hS, _, hs, _⟩ := CochainComplex.exists_isKFlatResolutionIndependentCoefficients N
  have hS : S.IsAcyclicTensorKFlat := hS
  let G := (curriedTensor 𝒜).map₂CochainComplex.flip.obj S
  let H := G ⋙ HomologicalComplex.homologyFunctor 𝒜 (.up ℤ) i
  let W := HomologicalComplex.quasiIso 𝒜 (.up ℤ)
  have hH : W.IsInvertedBy H := by
    intro X Y f hf
    have : QuasiIso (G.map f) := tensor_right_quasiIso R f hf hS
    exact inferInstanceAs (IsIso (HomologicalComplex.homologyMap (G.map f) i))
  let L := Localization.lift H hH (DerivedCategory.Q : _ ⥤ DerivedCategory 𝒜)
  let fac := Localization.fac H hH (DerivedCategory.Q : _ ⥤ DerivedCategory 𝒜)
  let ep : H.obj P ≅ H.obj Q := (fac.app P).symm ≪≫ L.mapIso e ≪≫ fac.app Q
  have htP := tensor_left_quasiIso R s hs hP
  have htQ := tensor_left_quasiIso R s hs hQ
  exact ⟨(asIso (HomologicalComplex.homologyMap
      (HomologicalComplex.mapBifunctorMap (𝟙 P) s (curriedTensor _) (.up ℤ)) i)).symm ≪≫
    ep ≪≫ asIso (HomologicalComplex.homologyMap
      (HomologicalComplex.mapBifunctorMap (𝟙 Q) s (curriedTensor _) (.up ℤ)) i)⟩

set_option synthInstance.maxSize 2048 in
set_option maxRecDepth 2048 in
private theorem tensor_homology_extension
    (P : CochainComplex 𝒜 ℤ)
    (hflat : ∀ i : ℤ, exactFunctor _ _
      (@MonoidalCategory.tensorRight _ _ (SheafOfModules.monoidalCategory R) (P.X i)))
    (S : ShortComplex 𝒜) (hS : S.ShortExact) (i : ℤ) :
    letI := SheafOfModules.monoidalCategory R
    IsZero ((((tensorRight S.X₁).mapHomologicalComplex (.up ℤ)).obj P).homology i) →
    IsZero ((((tensorRight S.X₃).mapHomologicalComplex (.up ℤ)).obj P).homology i) →
    IsZero ((((tensorRight S.X₂).mapHomologicalComplex (.up ℤ)).obj P).homology i) := by
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let := SheafOfModules.tensorPreadditive.{u + 1, u, u + 1} R
  let F : 𝒜 ⥤ CochainComplex 𝒜 ℤ :=
    { obj := fun M ↦ ((tensorRight M).mapHomologicalComplex (.up ℤ)).obj P
      map := fun f ↦ (((curriedTensor 𝒜).flip.map f).mapHomologicalComplex (.up ℤ)).app P
      map_id := by intro M; ext j; simp
      map_comp := by intro M N L f g; ext j; simp }
  have : F.PreservesZeroMorphisms := by
    constructor
    intro M N
    apply HomologicalComplex.Hom.ext
    funext j
    change P.X j ◁ (0 : M ⟶ N) = 0
    simp
  have ht : (S.map F).ShortExact := by
    apply HomologicalComplex.shortExact_iff_degreewise_shortExact _ |>.2
    intro j
    have hleft : exactFunctor _ _ (tensorLeft (P.X j)) :=
      (exactFunctor _ _).prop_of_iso
        (BraidedCategory.tensorLeftIsoTensorRight (P.X j)).symm (hflat j)
    have : PreservesFiniteLimits (tensorLeft (P.X j)) := hleft.1
    have : PreservesFiniteColimits (tensorLeft (P.X j)) := hleft.2
    exact hS.map_of_exact (tensorLeft (P.X j))
  intro h₁ h₃
  exact (ht.homology_exact₂ i).isZero_X₂ (h₁.eq_of_src _ _) (h₃.eq_of_tgt _ _)

set_option synthInstance.maxSize 2048 in
set_option maxRecDepth 2048 in
private theorem termwise_tensor_homology_iso
    [HasDerivedCategory 𝒜] (P Q : CochainComplex 𝒜 ℤ) (M : 𝒜)
    (hP : P.IsAcyclicTensorKFlat) (hQ : Q.IsAcyclicTensorKFlat)
    (e : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj Q) (i : ℤ) :
    letI := SheafOfModules.monoidalCategory R
    Nonempty ((((tensorRight M).mapHomologicalComplex (.up ℤ)).obj P).homology i ≅
      (((tensorRight M).mapHomologicalComplex (.up ℤ)).obj Q).homology i) := by
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.tensorPreadditive.{u + 1, u, u + 1} R
  obtain ⟨e'⟩ := tensor_homology_iso R P Q
    ((HomologicalComplex.single _ (.up ℤ) 0).obj M) hP hQ e i
  exact ⟨((HomologicalComplex.homologyFunctor _ (.up ℤ) i).mapIso
      (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _) M P)).symm ≪≫ e' ≪≫
    (HomologicalComplex.homologyFunctor _ (.up ℤ) i).mapIso
      (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _) M Q)⟩

end

section Nilpotent

variable {𝒞 : Type u} [Category.{v} 𝒞] [Abelian 𝒞]

omit [Abelian 𝒞] in
private lemma natural_power_comm (η : 𝟭 𝒞 ⟶ 𝟭 𝒞) {X Y : 𝒞} (f : X ⟶ Y) (n : ℕ) :
    ((End.of (η.app X)) ^ n).asHom ≫ f = f ≫ ((End.of (η.app Y)) ^ n).asHom := by
  induction n with
  | zero => simp [End.one_asHom]
  | succ n ih =>
    simp only [pow_succ, End.mul_asHom]
    rw [Category.assoc, ih, ← Category.assoc,
      show η.app X ≫ f = f ≫ η.app Y from (η.naturality f).symm, Category.assoc]

private theorem property_of_nilpotent
    (η : 𝟭 𝒞 ⟶ 𝟭 𝒞) (W : 𝒞 → Prop)
    (hzero : ∀ X, IsZero X → W X)
    (hext : ∀ S : ShortComplex 𝒞, S.ShortExact → W S.X₁ → W S.X₃ → W S.X₂)
    (hkilled : ∀ X, η.app X = 0 → W X)
    (n : ℕ) (X : 𝒞) (hn : ((End.of (η.app X)) ^ n) = 0) : W X := by
  induction n generalizing X with
  | zero =>
    apply hzero X
    exact (IsZero.iff_id_eq_zero X).2 (congrArg End.asHom hn)
  | succ n ih =>
    let f := η.app X
    let I := image f
    let i : I ⟶ X := image.ι f
    let q := cokernel.π i
    have hI : ((End.of (η.app I)) ^ n) = 0 := by
      apply End.ext
      apply (cancel_epi (factorThruImage f)).1
      apply (cancel_mono i).1
      rw [End.zero_asHom, comp_zero, zero_comp, Category.assoc, natural_power_comm η i n,
        ← Category.assoc]
      change (factorThruImage f ≫ image.ι f) ≫ _ = 0
      rw [image.fac]
      simpa only [pow_succ, End.mul_asHom, End.zero_asHom] using congrArg End.asHom hn
    have hQ : η.app (cokernel i) = 0 := by
      apply (cancel_epi q).1
      rw [comp_zero, show q ≫ η.app (cokernel i) = f ≫ q from η.naturality q]
      change f ≫ cokernel.π i = 0
      rw [← image.fac f, Category.assoc]
      rw [cokernel.condition, comp_zero]
    exact hext (ShortComplex.mk i q (cokernel.condition i))
      { exact := ShortComplex.exact_cokernel i } (ih I hI) (hkilled _ hQ)

end Nilpotent

end ResidueTensor

namespace ResidueTensor

private noncomputable def constantSections (T : Scheme.{u}) (A : Type u) [CommRing A] :
    A →+* RingCat.sectionsSubring
      ((proEtaleConstantRing T A).obj ⋙ forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) where
  toFun a :=
    ⟨fun U ↦ (toSheafify (ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} A)))).app U
          (ULift.up a), by
      intro U V f
      exact congrArg (fun h ↦ h (ULift.up a))
        ((toSheafify (ProEt.topology T)
          ((Functor.const T.ProEtᵒᵖ).obj
            (CommRingCat.of (ULift.{u + 1, u} A)))).naturality f).symm⟩
  map_one' := by ext U; exact map_one _
  map_mul' a b := by ext U; exact map_mul _ _ _
  map_zero' := by ext U; exact map_zero _
  map_add' a b := by ext U; exact map_add _ _ _

private noncomputable def scalarEnd (T : Scheme.{u}) (A : Type u) [CommRing A]
    (M : proEtaleRingModules T (proEtaleConstantRing T A)) : A →+* End M where
  toFun a := .of ⟨PresheafOfModules.sectionsSMul M.val (constantSections T A a)⟩
  map_one' := by
    apply End.ext
    apply SheafOfModules.hom_ext
    change PresheafOfModules.sectionsSMul M.val (constantSections T A 1) = _
    rw [(constantSections T A).map_one]
    exact congrArg End.asHom (PresheafOfModules.sectionsSMulHom M.val).map_one
  map_mul' a b := by
    apply End.ext
    apply SheafOfModules.hom_ext
    change PresheafOfModules.sectionsSMul M.val (constantSections T A (a * b)) = _
    rw [(constantSections T A).map_mul]
    exact congrArg End.asHom ((PresheafOfModules.sectionsSMulHom M.val).map_mul _ _)
  map_zero' := by
    apply End.ext
    apply SheafOfModules.hom_ext
    change PresheafOfModules.sectionsSMul M.val (constantSections T A 0) = _
    rw [(constantSections T A).map_zero]
    exact congrArg End.asHom (PresheafOfModules.sectionsSMulHom M.val).map_zero
  map_add' a b := by
    apply End.ext
    apply SheafOfModules.hom_ext
    change PresheafOfModules.sectionsSMul M.val (constantSections T A (a + b)) = _
    rw [(constantSections T A).map_add]
    exact congrArg End.asHom ((PresheafOfModules.sectionsSMulHom M.val).map_add _ _)

private noncomputable def scalarNatTrans (T : Scheme.{u}) (A : Type u) [CommRing A]
    (a : A) : 𝟭 (proEtaleRingModules T (proEtaleConstantRing T A)) ⟶ 𝟭 _ where
  app M := (scalarEnd T A M a).asHom
  naturality {M N} f := by
    apply SheafOfModules.hom_ext
    exact PresheafOfModules.sectionsSMul_naturality f.val (constantSections T A a)

private theorem scalarNatTrans_nilpotent (T : Scheme.{u}) (A : Type u) [CommRing A]
    (a : A) (n : ℕ) (hn : a ^ n = 0)
    (M : proEtaleRingModules T (proEtaleConstantRing T A)) :
    (End.of ((scalarNatTrans T A a).app M)) ^ n = 0 := by
  change (scalarEnd T A M a) ^ n = 0
  rw [← map_pow, hn, map_zero]

private theorem uniformizer_nilpotent
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) :
    (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E n)
      (Padic.coefficientExtensionUniformizer l E)) ^ n = 0 := by
  rw [← map_pow]
  apply Ideal.Quotient.eq_zero_iff_mem.2
  rw [Padic.coefficientExtensionIdeal, Ideal.span_singleton_pow]
  exact Ideal.subset_span (Set.mem_singleton _)

private theorem residue_isMaximal
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n) :
    (Ideal.span
      {Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E n)
        (Padic.coefficientExtensionUniformizer l E)}).IsMaximal := by
  have h := (Padic.coefficientExtensionIntegers_dvr l E).choose_spec
  have hmax : (Padic.coefficientExtensionMaximalIdeal l E).IsMaximal := h.2.2.2.2.1
  have hgen : Ideal.span {Padic.coefficientExtensionUniformizer l E} =
      Padic.coefficientExtensionMaximalIdeal l E := h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have : (Ideal.span {Padic.coefficientExtensionUniformizer l E}).IsMaximal := hgen ▸ hmax
  let φ := Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E n)
  have hm := Ideal.IsMaximal.map_of_surjective_of_ker_le (f := φ)
    (m := Ideal.span {Padic.coefficientExtensionUniformizer l E})
    Ideal.Quotient.mk_surjective (by
      rw [Ideal.mk_ker]
      exact Ideal.pow_le_self (by omega))
  simpa only [Ideal.map_span, Set.image_singleton] using hm

set_option synthInstance.maxSize 2048 in
private noncomputable def derivedTensor_module_homology_iso
    (T : Scheme.{u}) (A : Type u) [CommRing A]
    (K P : CochainComplex (proEtaleRingModules T (proEtaleConstantRing T A)) ℤ)
    (f : P ⟶ K) (hf : QuasiIso f) (hP : P.IsAcyclicTensorKFlat)
    (M : proEtaleRingModules T (proEtaleConstantRing T A)) (i : ℤ) :
    letI := SheafOfModules.monoidalCategory (proEtaleConstantRing T A)
    (DerivedCategory.homologyFunctor _ i).obj
        (derivedTensor T A K ((HomologicalComplex.single _ (.up ℤ) 0).obj M) P f hf hP) ≅
      (((tensorRight M).mapHomologicalComplex (.up ℤ)).obj P).homology i := by
  let := SheafOfModules.monoidalCategory (proEtaleConstantRing T A)
  let := SheafOfModules.tensorPreadditive.{u + 1, u, u + 1} (proEtaleConstantRing T A)
  exact (DerivedCategory.homologyFunctorFactors _ i).app _ ≪≫
    (HomologicalComplex.homologyFunctor _ (.up ℤ) i).mapIso
      (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _) M P)

end ResidueTensor

set_option synthInstance.maxSize 2048 in
set_option maxRecDepth 2048 in
/-- Tor amplitude over `A = A_{E,n}` is detected by derived tensor with `A/(ϖ_E)`.
The quotient ideal is generated by the image of the recorded uniformizer in `A`;
`Ideal.Quotient.mk` is the canonical coefficient map. `K` is an arbitrary cochain
representative, and `f: P ⟶ K` is any K-flat resolution used by `derivedTensorRing`.
-/
theorem proEtale_torAmplitude_iff_residue_tensor
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n) (T : Scheme.{u})
    [∀ x : T, Invertible (l : T.residueField x)]
    (K P : CochainComplex (proEtaleRingModules T
      (proEtaleConstantRing T (Padic.coefficientExtensionRing l E n))) ℤ)
    (f : P ⟶ K) (hf : QuasiIso f)
    (hP : CochainComplex.IsAcyclicTensorKFlat.{u + 1, u}
      (R := proEtaleConstantRing T (Padic.coefficientExtensionRing l E n)) P)
    (_hK : intrinsicFiniteTorsionConstructible l E n hn T (DerivedCategory.Q.obj K))
    (a b : ℤ) (_hab : a ≤ b) :
    HasProEtaleTorAmplitude T (Padic.coefficientExtensionRing l E n)
      (DerivedCategory.Q.obj K) a b ↔
      ∀ i : ℤ, (i < a ∨ b < i) →
        IsZero ((DerivedCategory.homologyFunctor (proEtaleRingModules T
          (proEtaleConstantRing T (Padic.coefficientExtensionRing l E n))) i).obj
            (derivedTensorRing T (Padic.coefficientExtensionRing l E n)
              (Padic.coefficientExtensionRing l E n ⧸ Ideal.span
                {Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E n)
                  (Padic.coefficientExtensionUniformizer l E)})
              (Ideal.Quotient.mk _) K P f hf hP)) := by
  constructor
  · intro h
    exact h.2 K P ⟨Iso.refl _⟩ f hf hP _
  · intro h
    let A := Padic.coefficientExtensionRing l E n
    let R := proEtaleConstantRing T A
    let 𝒜 := proEtaleRingModules T R
    let := SheafOfModules.monoidalCategory R
    let := SheafOfModules.tensorPreadditive.{u + 1, u, u + 1} R
    let r : A := Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E n)
      (Padic.coefficientExtensionUniformizer l E)
    let B := A ⧸ Ideal.span {r}
    let RB := proEtaleConstantRing T B
    let SB := (sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RB
    let α : ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) ⟶ SB :=
      (sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      ((constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (RingHom.ulift (Ideal.Quotient.mk (Ideal.span {r})))))
    let N : 𝒜 := (SheafOfModules.restrictScalars.{u + 1} α).obj (SheafOfModules.unit SB)
    obtain ⟨Q, g, hQ, hflat, hg, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients K
    have hQ : Q.IsAcyclicTensorKFlat := hQ
    have := hf
    have := hg
    let ePQ : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj Q :=
      asIso (DerivedCategory.Q.map f) ≪≫ (asIso (DerivedCategory.Q.map g)).symm
    have hres (i : ℤ) (hi : i < a ∨ b < i) :
        IsZero ((((tensorRight N).mapHomologicalComplex (.up ℤ)).obj Q).homology i) := by
      have hz := h i hi
      have hzP := hz.of_iso
        (ResidueTensor.derivedTensor_module_homology_iso T A K P f hf hP N i).symm
      obtain ⟨e⟩ := ResidueTensor.termwise_tensor_homology_iso R P Q N hP hQ ePQ i
      exact hzP.of_iso e.symm
    have hall (M : 𝒜) (i : ℤ) (hi : i < a ∨ b < i) :
        IsZero ((((tensorRight M).mapHomologicalComplex (.up ℤ)).obj Q).homology i) := by
      apply ResidueTensor.property_of_nilpotent (ResidueTensor.scalarNatTrans T A r)
        (fun M ↦ IsZero ((((tensorRight M).mapHomologicalComplex (.up ℤ)).obj Q).homology i))
        ?_ ?_ ?_ n M
        (ResidueTensor.scalarNatTrans_nilpotent T A r n
          (ResidueTensor.uniformizer_nilpotent l E n) M)
      · intro M hM
        apply HomologicalComplex.ExactAt.isZero_homology
        apply HomologicalComplex.ExactAt.of_isZero
        exact (tensorLeft (Q.X i)).map_isZero hM
      · intro S hS h₁ h₃
        exact ResidueTensor.tensor_homology_extension R Q hflat S hS i h₁ h₃
      · intro M hM
        apply proEtale_residue_module_tensor_homology T A r
          (ResidueTensor.residue_isMaximal l E n hn) Q M ?_ i (hres i hi)
        intro U x
        exact congrArg (fun z ↦ z.val.app U x) hM
    refine ⟨_hab, ?_⟩
    intro L P' e f' hf' hP' M i hi
    obtain ⟨e⟩ := e
    have := hf'
    let eQP' : DerivedCategory.Q.obj Q ≅ DerivedCategory.Q.obj P' :=
      asIso (DerivedCategory.Q.map g) ≪≫ e.symm ≪≫
        (asIso (DerivedCategory.Q.map f')).symm
    obtain ⟨c⟩ := ResidueTensor.termwise_tensor_homology_iso R Q P' M hQ hP' eQP' i
    exact ((hall M i hi).of_iso c.symm).of_iso
      (ResidueTensor.derivedTensor_module_homology_iso T A L P' f' hf' hP' M i)

end AlgebraicGeometry.Scheme
