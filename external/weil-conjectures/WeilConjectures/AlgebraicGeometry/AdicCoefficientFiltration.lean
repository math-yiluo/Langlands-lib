/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicFiniteReductionData
public import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
import WeilConjectures.Algebra.Homology.RingedKFlatSingleTensorComparison
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionInverseImage
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # The graded coefficient filtration triangle

Source: Stacks Project, Tag 09BR, lemma-compare-truncations-constructible.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.ConstantCompletion
namespace AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

/-- The actual kernel of the successive quotient, as a module over the larger quotient.
It is canonically J^(n+1)/J^(n+2), with no choice of a presentation or generators.
Source: Stacks Tag 09BR (auxiliary; not a blueprint node). -/
def adicFiniteGradedModule {A : Type w} [CommRing A] (J : Ideal A) (n : ℕ) :
    ModuleCat.{w} (adicFiniteCoeff J (n + 1)) :=
  ModuleCat.of _ (RingHom.ker (adicFiniteFactor J (Nat.le_succ n)))

/-- The constant graded module placed in degree zero in the standard localization.
Source: Stacks Tags 09BR and 093J
(auxiliary; not a blueprint node). -/
def adicFiniteGradedSingle (X : Scheme.{u})
    {A : Type (max v (u + 1))} [CommRing A] (J : Ideal A) (n : ℕ) :
    adicFiniteAmbient.{u, v} X (adicFiniteCoeff J (n + 1)) :=
  let T := coefficientProEtaleModelTopology.{u, v} X
  let R := constant T (adicFiniteCoeff J (n + 1))
  (Q R).obj ((HomologicalComplex.single (Mod R) (.up ℤ) 0).obj
    ((commutativeSiteConstantModuleFunctor T (adicFiniteCoeff J (n + 1))).obj
      (adicFiniteGradedModule J n)))

/-- The derived tensor with the actual graded coefficient module. The K-flat tensor is
computed over the larger quotient, so the layer retains that quotient's scalar action.
Source: Stacks Tag 09BR (auxiliary; not a blueprint node). -/
def adicFiniteGradedLayer (X : Scheme.{u})
    {A : Type (max v (u + 1))} [CommRing A] (J : Ideal A)
    (N : adicFiniteAmbient.{u, v} X A) (n : ℕ) :
    adicFiniteAmbient.{u, v} X (adicFiniteCoeff J (n + 1)) :=
  let R := constant (coefficientProEtaleModelTopology.{u, v} X)
    (adicFiniteCoeff J (n + 1))
  letI := HasDerivedCategory.standard (Mod R)
  ((SheafOfModules.KFlatFixedTensor.derivedTensor R).obj
    (adicFiniteReduction.{u, v} X J N (n + 1))).obj
      (adicFiniteGradedSingle.{u, v} X J n)

/-- The lower reduction, retaining the larger quotient's scalar action.
Source: Stacks Tag 09BR (auxiliary; not a blueprint node). -/
def adicFiniteRestrictedReduction (X : Scheme.{u})
    {A : Type (max v (u + 1))} [CommRing A] (J : Ideal A)
    (N : adicFiniteAmbient.{u, v} X A) (n : ℕ) :
    adicFiniteAmbient.{u, v} X (adicFiniteCoeff J (n + 1)) :=
  (dres (adicFiniteConstantMap (adicFiniteFactor J (Nat.le_succ n))
    (coefficientProEtaleModelTopology.{u, v} X))).obj
      (adicFiniteReduction.{u, v} X J N n)

private theorem monoidalUnit_eq {E : Type w} [SmallCategory E]
    {T : GrothendieckTopology E} (R : Sheaf T CommRingCat.{w}) :
    @MonoidalCategory.tensorUnit (Mod R) _
      (SheafOfModules.monoidalCategory R).toMonoidalCategoryStruct =
      SheafOfModules.unit (siteModuleRings R) := rfl

attribute [local instance] SheafOfModules.monoidalCategory
  SheafOfModules.symmetricCategory SheafOfModules.isMonoidal_W_independentCoefficients
attribute [local instance] HasDerivedCategory.standard
attribute [local irreducible] HasDerivedCategory.standard
  SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory

section ConstantScalars
set_option backward.defeqAttrib.useBackward true

variable {E : Type w} [SmallCategory E] (T : GrothendieckTopology E)
    {B C : Type w} [CommRing B] [CommRing C]

-- The coefficient sheafification unit is linear for the induced constant-ring map.
private def constantScalarSeed (p : B →+* C) :
    (siteConstantModulePresheafGeneral (C := E) B).obj
        ((ModuleCat.restrictScalars p).obj (ModuleCat.of C C)) ⟶
      (PresheafOfModules.restrictScalars (realizationRingUnit T B)).obj
        ((res (adicFiniteConstantMap p T)).obj
          (SheafOfModules.unit (siteModuleRings (constant T C)))).val where
  app U := ModuleCat.ofHom
    (X := ((siteConstantModulePresheafGeneral (C := E) B).obj
      ((ModuleCat.restrictScalars p).obj (ModuleCat.of C C))).obj U)
    (Y := ((PresheafOfModules.restrictScalars (realizationRingUnit T B)).obj
      ((res (adicFiniteConstantMap p T)).obj
        (SheafOfModules.unit (siteModuleRings (constant T C)))).val).obj U)
    { toFun := (toSheafify T ((Functor.const Eᵒᵖ).obj (CommRingCat.of C))).app U
      map_add' := map_add _
      map_smul' := by
        intro b c
        change B at b
        change C at c
        change (toSheafify T ((Functor.const Eᵒᵖ).obj (CommRingCat.of C))).app U
            (p b * c) = _
        rw [map_mul]
        congr 1
        have h := toSheafify_naturality T
          ((Functor.const Eᵒᵖ).map (CommRingCat.ofHom p))
        exact ConcreteCategory.congr_hom (congr_app h U) b }
  naturality := by
    intro U V f
    ext c
    exact (ConcreteCategory.congr_hom
      ((toSheafify T ((Functor.const Eᵒᵖ).obj (CommRingCat.of C))).naturality f) c)

private theorem constantScalarSeed_locallyBijective (p : B →+* C) :
    Presheaf.IsLocallyInjective T
        ((PresheafOfModules.toPresheaf _).map (constantScalarSeed T p)) ∧
      Presheaf.IsLocallySurjective T
        ((PresheafOfModules.toPresheaf _).map (constantScalarSeed T p)) := by
  constructor
  · constructor
    intro U x y h
    exact Presheaf.equalizerSieve_mem T
      (toSheafify T ((Functor.const Eᵒᵖ).obj (CommRingCat.of C))) x y h
  · constructor
    intro U s
    exact Presheaf.imageSieve_mem T
      (toSheafify T ((Functor.const Eᵒᵖ).obj (CommRingCat.of C))) s

attribute [local irreducible] constantScalarSeed

private def constantScalarComparison (p : B →+* C) :
    (commutativeSiteConstantModuleFunctor T B).obj
        ((ModuleCat.restrictScalars p).obj (ModuleCat.of C C)) ⟶
      (res (adicFiniteConstantMap p T)).obj
        (SheafOfModules.unit (siteModuleRings (constant T C))) :=
  letI := (realizationRingUnit_locallyBijective T B).1
  letI := (realizationRingUnit_locallyBijective T B).2
  (PresheafOfModules.sheafificationHomEquiv (realizationRingUnit T B)).symm
    (constantScalarSeed T p)

-- Both units are locally bijective; the sheafification adjunction gives the comparison.
private theorem constantScalarComparison_isIso (p : B →+* C) :
    IsIso (constantScalarComparison T p) := by
  have := (realizationRingUnit_locallyBijective T B).1
  have := (realizationRingUnit_locallyBijective T B).2
  let P := (siteConstantModulePresheafGeneral (C := E) B).obj
    ((ModuleCat.restrictScalars p).obj (ModuleCat.of C C))
  let F := SheafOfModules.toSheaf (siteModuleRings (constant T B))
  let g := (PresheafOfModules.toPresheaf _).map (constantScalarSeed T p)
  let h := F.map (constantScalarComparison T p)
  have he : toSheafify T P.presheaf ≫ h.hom = g := by
    have he := congrArg ((PresheafOfModules.toPresheaf _).map)
      ((PresheafOfModules.sheafificationHomEquiv (realizationRingUnit T B)
        (P := P) (F := (res (adicFiniteConstantMap p T)).obj
          (SheafOfModules.unit (siteModuleRings (constant T C))))).apply_symm_apply
        (constantScalarSeed T p))
    rw [PresheafOfModules.toPresheaf_map_sheafificationHomEquiv_def] at he
    exact he
  have hg₁ : Presheaf.IsLocallyInjective T g :=
    (constantScalarSeed_locallyBijective T p).1
  have hg₂ : Presheaf.IsLocallySurjective T g :=
    (constantScalarSeed_locallyBijective T p).2
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
  exact isIso_of_reflects_iso (constantScalarComparison T p) F

attribute [local irreducible] constantScalarComparison

end ConstantScalars

private def constantUnitIso {E : Type w} [SmallCategory E]
    (T : GrothendieckTopology E) (B : Type w) [CommRing B] :
    (commutativeSiteConstantModuleFunctor T B).obj (ModuleCat.of B B) ≅
      SheafOfModules.unit (siteModuleRings (constant T B)) := by
  have := constantScalarComparison_isIso T (RingHom.id B)
  refine (commutativeSiteConstantModuleFunctor T B).mapIso
    ((ModuleCat.restrictScalarsId B).symm.app (ModuleCat.of B B)) ≪≫
      asIso (constantScalarComparison T (RingHom.id B)) ≪≫ ?_
  unfold adicFiniteConstantMap
  rw [show CommRingCat.ofHom (RingHom.id B) = 𝟙 (CommRingCat.of B) from rfl,
    CategoryTheory.Functor.map_id]
  apply (SheafOfModules.fullyFaithfulForget _).preimageIso
  refine PresheafOfModules.isoMk (fun U ↦
    ModuleCat.restrictScalarsId'App _ rfl _) ?_
  intro U V f
  ext
  rfl

-- Compute on a K-flat representative, then use the ordinary restricted tensor comparison.
private theorem tensorWithCoefficient_iso
    {E : Type w} [SmallCategory E] {T : GrothendieckTopology E}
    {R S : Sheaf T CommRingCat.{w}} (φ : R ⟶ S) (M : ConstantCompletion.D R)
    (V : Mod R) (v : V ≅ (res φ).obj (SheafOfModules.unit (siteModuleRings S))) :
    let := HasDerivedCategory.standard (Mod R)
    Nonempty (((SheafOfModules.KFlatFixedTensor.derivedTensor R).obj M).obj
      ((Q R).obj ((HomologicalComplex.single (Mod R) (.up ℤ) 0).obj V)) ≅
        (dres φ).obj ((extend φ).obj M)) := by
  let := HasDerivedCategory.standard (Mod R)
  let := HasDerivedCategory.standard (Mod S)
  let G := (Q R).objPreimage M
  obtain ⟨P, q, hP, _, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients G
  have := hq
  let e : (Q R).obj P ≅ M := asIso ((Q R).map q) ≪≫ (Q R).objObjPreimageIso M
  let F := SheafOfModules.KFlatFixedTensor.derivedTensor R
  let U := (res φ).obj (SheafOfModules.unit (siteModuleRings S))
  let single := HomologicalComplex.single (Mod R) (.up ℤ) 0
  obtain ⟨c, _⟩ := SheafOfModules.ringed_kFlat_single_tensor_comparison R
  let o := (BraidedCategory.tensorLeftIsoTensorRight U).symm ≪≫ extensionTensorIso φ
  let b := (NatIso.mapHomologicalComplex o (.up ℤ)).app P
  have hP' := (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).mp hP
  have : IsIso ((extendComparison φ).app P) := (derivedExtension φ).computation P hP'
  exact ⟨(F.mapIso e.symm).app _ ≪≫
    (F.obj ((Q R).obj P)).mapIso ((Q R).mapIso (single.mapIso v)) ≪≫
    c P hP U ≪≫ (Q R).mapIso b ≪≫
    (resFactors φ).app (((change φ).mapHomologicalComplex (.up ℤ)).obj P) ≪≫
    (dres φ).mapIso ((asIso ((extendComparison φ).app P)).symm ≪≫
      (extend φ).mapIso e)⟩

private theorem tensorWithUnit_iso
    {E : Type w} [SmallCategory E] {T : GrothendieckTopology E}
    (R : Sheaf T CommRingCat.{w}) (M : ConstantCompletion.D R) :
    let := HasDerivedCategory.standard (Mod R)
    Nonempty (((SheafOfModules.KFlatFixedTensor.derivedTensor R).obj M).obj
      ((Q R).obj ((HomologicalComplex.single (Mod R) (.up ℤ) 0).obj
        (SheafOfModules.unit (siteModuleRings R)))) ≅ M) := by
  let := HasDerivedCategory.standard (Mod R)
  let G := (Q R).objPreimage M
  obtain ⟨P, q, hP, _, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients G
  have := hq
  let e : (Q R).obj P ≅ M := asIso ((Q R).map q) ≪≫ (Q R).objObjPreimageIso M
  let F := SheafOfModules.KFlatFixedTensor.derivedTensor R
  obtain ⟨c, _⟩ := SheafOfModules.ringed_kFlat_single_tensor_comparison R
  let o := (MonoidalCategory.tensoringRight (Mod R)).mapIso
    (eqToIso (monoidalUnit_eq R).symm) ≪≫ MonoidalCategory.rightUnitorNatIso (Mod R)
  exact ⟨(F.mapIso e.symm).app _ ≪≫ c P hP _ ≪≫
    (Q R).mapIso ((NatIso.mapHomologicalComplex o (.up ℤ)).app P) ≪≫ e⟩

private def coefficientSequence {B C : Type w} [CommRing B] [CommRing C]
    (p : B →+* C) : ShortComplex (ModuleCat.{w} B) :=
  let V := (ModuleCat.restrictScalars p).obj (ModuleCat.of C C)
  letI : Module B C := Module.compHom C p
  let q : ModuleCat.of B B ⟶ V := ModuleCat.ofHom
    { toFun := p
      map_add' := p.map_add
      map_smul' := p.map_mul }
  ShortComplex.mk (ModuleCat.ofHom (RingHom.ker p).subtype) q (by
    ext x
    exact x.property)

private theorem coefficientSequence_shortExact {B C : Type w} [CommRing B] [CommRing C]
    (p : B →+* C) (hp : Function.Surjective p) :
    (coefficientSequence p).ShortExact := by
  have : Mono (coefficientSequence p).f :=
    (ModuleCat.mono_iff_injective _).mpr Subtype.val_injective
  have : Epi (coefficientSequence p).g :=
    (ModuleCat.epi_iff_surjective _).mpr hp
  refine ⟨?_⟩
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  intro x hx
  exact ⟨⟨x, hx⟩, rfl⟩

-- Exactness for a resolving representative transfers along its isomorphism to M.
private theorem fixedTensor_triangulated
    {E : Type w} [SmallCategory E] {T : GrothendieckTopology E}
    (R : Sheaf T CommRingCat.{w}) (M : ConstantCompletion.D R) :
    let := HasDerivedCategory.standard (Mod R)
    ∃ _s : (SheafOfModules.KFlatFixedTensor.derivedTensor R).CommShift₂Int,
      ((SheafOfModules.KFlatFixedTensor.derivedTensor R).obj M).IsTriangulated := by
  let := HasDerivedCategory.standard (Mod R)
  obtain ⟨s, hs⟩ := SheafOfModules.KFlatFixedTensor.kFlat_fixed_tensor_triangulated R
  let := s
  let G := (DerivedCategory.Q (C := Mod R)).objPreimage M
  let e := (DerivedCategory.Q (C := Mod R)).objObjPreimageIso M
  obtain ⟨P, q, hP, hf, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients G
  have := hq
  have hf' (i : ℤ) : SheafOfModules.IsFlatOnSite.{w, w, w, w} (J := T) (R := R) (P.X i) := by
    change exactFunctor (Mod R) (Mod R) (SheafOfModules.siteSheafTensorRight (A := R) _)
    exact (exactFunctor (Mod R) (Mod R)).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso.{w, w, w} (J := T) R (P.X i)).symm (hf i)
  have htri := (hs P hP hf').2.2.1.1
  have := htri
  let d : DerivedCategory.Q.obj P ≅ M :=
    asIso (DerivedCategory.Q.map q) ≪≫ e
  have : NatTrans.CommShift
      ((SheafOfModules.KFlatFixedTensor.derivedTensor R).mapIso d).hom ℤ := by
    change NatTrans.CommShift
      ((SheafOfModules.KFlatFixedTensor.derivedTensor R).map d.hom) ℤ
    infer_instance
  exact ⟨s, Functor.isTriangulated_of_iso
    ((SheafOfModules.KFlatFixedTensor.derivedTensor R).mapIso d)⟩

private theorem triangle_transport
    {V : Type*} [Category V] [HasZeroObject V] [HasShift V ℤ]
    [Preadditive V] [∀ n : ℤ, (shiftFunctor V n).Additive] [Pretriangulated V]
    (t : Pretriangulated.Triangle V) (ht : t ∈ distTriang V)
    {L M N : V} (e₁ : L ≅ t.obj₁) (e₂ : M ≅ t.obj₂) (e₃ : N ≅ t.obj₃) :
    ∃ (f : L ⟶ M) (g : M ⟶ N) (δ : N ⟶ L⟦(1 : ℤ)⟧),
      Pretriangulated.Triangle.mk f g δ ∈ distTriang V := by
  let f := e₁.hom ≫ t.mor₁ ≫ e₂.inv
  let g := e₂.hom ≫ t.mor₂ ≫ e₃.inv
  let δ := e₃.hom ≫ t.mor₃ ≫ (shiftFunctor V (1 : ℤ)).map e₁.inv
  refine ⟨f, g, δ, Pretriangulated.isomorphic_distinguished _ ht _ ?_⟩
  refine Pretriangulated.Triangle.isoMk _ _ e₁ e₂ e₃ ?_ ?_ ?_
  · simp [f]
  · simp [g]
  · simp [δ, ← CategoryTheory.Functor.map_comp]

/-- The graded filtration gives a distinguished triangle with the two actual reductions.
This assertion has no constructibility or boundedness hypothesis or conclusion.

Source: Stacks Project, proetale.tex, Tag 09BR,
lemma-compare-truncations-constructible, first displayed triangle.
(auxiliary; not a blueprint node).

Proof: Set B=A/J^(n+2), C=A/J^(n+1), and I=ker(B -> C). The quotient map is
surjective, so 0 -> I -> B -> C -> 0 is short exact. Exact constant realization
and degree-zero embedding give its standard distinguished triangle over the constant
B-ring. Tensor this triangle with the actual reduction N tensor_A^L B, using the
triangulated K-flat tensor. The first term is the displayed graded layer by its
construction. The unit comparison identifies the middle term with N tensor_A^L B.
Balancing identifies the last term with the restriction of N tensor_A^L C; its
comparison is the canonical composition comparison adicFiniteRho. Transport the
triangle along these isomorphisms. Surjectivity and exactness still apply to zero
quotients, J=0, J=top, and the empty scheme; no flatness of C over B is used. -/
theorem adicFiniteGradedLayer_triangle (X : Scheme.{u})
    {A : Type (max v (u + 1))} [CommRing A] (J : Ideal A)
    (N : adicFiniteAmbient.{u, v} X A) (n : ℕ) :
    ∃ (f : adicFiniteGradedLayer.{u, v} X J N n ⟶
        adicFiniteReduction.{u, v} X J N (n + 1))
      (g : adicFiniteReduction.{u, v} X J N (n + 1) ⟶
        adicFiniteRestrictedReduction.{u, v} X J N n)
      (δ : adicFiniteRestrictedReduction.{u, v} X J N n ⟶
        (adicFiniteGradedLayer.{u, v} X J N n)⟦(1 : ℤ)⟧),
      Pretriangulated.Triangle.mk f g δ ∈ distTriang _ := by
  let T := coefficientProEtaleModelTopology.{u, v} X
  let B := adicFiniteCoeff J (n + 1)
  let C := adicFiniteCoeff J n
  let p : B →+* C := adicFiniteFactor J (Nat.le_succ n)
  let R := constant T B
  let M := adicFiniteReduction.{u, v} X J N (n + 1)
  let := HasDerivedCategory.standard (Mod R)
  let c := commutativeSiteConstantModuleFunctor T B
  let S := (coefficientSequence p).map c
  have hp : Function.Surjective p := Ideal.Quotient.factor_surjective
    (Ideal.pow_le_pow_right (Nat.add_le_add_right (Nat.le_succ n) 1))
  have hS : S.ShortExact := (coefficientSequence_shortExact p hp).map_of_exact c
  obtain ⟨s, hF⟩ := fixedTensor_triangulated R M
  let := s
  let F := (SheafOfModules.KFlatFixedTensor.derivedTensor R).obj M
  have : F.IsTriangulated := hF
  let t := F.mapTriangle.obj hS.singleTriangle
  have ht : t ∈ distTriang _ := F.map_distinguished _ hS.singleTriangle_distinguished
  let e₁ : adicFiniteGradedLayer.{u, v} X J N n ≅ t.obj₁ :=
    (F.mapIso ((DerivedCategory.singleFunctorIsoCompQ (Mod R) 0).app S.X₁)).symm
  obtain ⟨unitIso⟩ := tensorWithUnit_iso R M
  let e₂ : M ≅ t.obj₂ :=
    (F.mapIso ((DerivedCategory.singleFunctorIsoCompQ (Mod R) 0).app S.X₂) ≪≫
      F.mapIso ((Q R).mapIso
        ((HomologicalComplex.single (Mod R) (.up ℤ) 0).mapIso (constantUnitIso T B))) ≪≫
      unitIso).symm
  have := constantScalarComparison_isIso T p
  obtain ⟨scalarIso⟩ := tensorWithCoefficient_iso (adicFiniteConstantMap p T) M
    (c.obj ((ModuleCat.restrictScalars p).obj (ModuleCat.of C C)))
    (asIso (constantScalarComparison T p))
  let e₃ : adicFiniteRestrictedReduction.{u, v} X J N n ≅ t.obj₃ :=
    (F.mapIso ((DerivedCategory.singleFunctorIsoCompQ (Mod R) 0).app S.X₃) ≪≫
      scalarIso ≪≫ (dres (adicFiniteConstantMap p T)).mapIso
        (adicFiniteRho.{u, v} X J N (Nat.le_succ n))).symm
  exact triangle_transport t ht e₁ e₂ e₃

end AlgebraicGeometry.Scheme
