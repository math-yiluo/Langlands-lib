/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.Additive
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf

/-! # RingedToposAcyclicKFlatPullback

Source: Stacks Project, Tag 0G7E (lemma-pullback-K-flat), acyclic case.
(auxiliary; not a blueprint node). -/

@[expose] public section
universe uC vC uD vD w
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits MonoidalCategory
open scoped ZeroObject
namespace SheafOfModules

private local instance {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{w}) (I : Type w) :
    HasColimitsOfShape (Discrete I) (PresheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R).obj) :=
  PresheafOfModules.hasColimitsOfShape
    ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R).obj (Discrete I)


section Tensor

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
  {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{w})

set_option hygiene false in
local notation "𝒜" => SheafOfModules.{w}
  ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)

private noncomputable def tensor_symmetry
    (K L : CochainComplex 𝒜 ℤ) :
    letI := isMonoidal_W_independentCoefficients R
    letI := monoidalCategory R
    letI := preservesZeroMorphisms_curriedTensor_independentCoefficients R
    letI := preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
    CochainComplex.mapBifunctor K L (curriedTensor _) ≅
      CochainComplex.mapBifunctor L K (curriedTensor _) := by
  let := isMonoidal_W_independentCoefficients R
  let := monoidalCategory R
  let := preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let := preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  let := symmetricCategory R
  let T := curriedTensor 𝒜
  let A := ((T.mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj K).obj L
  let B := ((T.flip.mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj K).obj L
  let e : A ≅ B := HomologicalComplex.Hom.isoOfComponents
    (fun p ↦ HomologicalComplex.Hom.isoOfComponents
      (fun q ↦ β_ (K.X p) (L.X q)) (by
        intro q q' hq
        exact (BraidedCategory.braiding_naturality_right (K.X p) (L.d q q')).symm))
    (by
      intro p p' hp
      ext q : 1
      exact (BraidedCategory.braiding_naturality_left (K.d p p') (L.X q)).symm)
  exact (HomologicalComplex₂.total.mapIso e (.up ℤ)) ≪≫
    HomologicalComplex.mapBifunctorFlipIso L K T (.up ℤ)

-- The resolution-and-cone proof of Tags 06Y0 and 06YT works at independent universes.
private theorem tensor_acyclic
    (K : CochainComplex 𝒜 ℤ) (hK : K.IsKFlatIndependentCoefficients)
    (hA : K.Acyclic) (F : CochainComplex 𝒜 ℤ) :
    letI := isMonoidal_W_independentCoefficients R
    letI := monoidalCategory R
    letI := preservesZeroMorphisms_curriedTensor_independentCoefficients R
    letI := preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
    (CochainComplex.mapBifunctor F K (curriedTensor _)).Acyclic := by
  let := isMonoidal_W_independentCoefficients R
  let := monoidalCategory R
  let := preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let := preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  let := tensorPreadditive R
  obtain ⟨P, r, hP, _, hr, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients F
  have hcone : (CochainComplex.mappingCone r).Acyclic :=
    (CochainComplex.mappingCone.quasiIso_iff_acyclic r).1 hr
  have hc := hK (CochainComplex.mappingCone r) hcone
  let g := HomologicalComplex.mapBifunctorMap r (𝟙 K) (curriedTensor _) (.up ℤ)
  have : QuasiIso g := by
    apply (CochainComplex.mappingCone.quasiIso_iff_acyclic g).2
    exact fun i ↦ (hc i).of_iso
      (CochainComplex.mapBifunctorMappingCone₁Iso r K (curriedTensor _))
  have hp : (CochainComplex.mapBifunctor P K (curriedTensor _)).Acyclic :=
    fun i ↦ (hP K hA i).of_iso (tensor_symmetry R K P)
  intro i
  exact (quasiIsoAt_iff_exactAt g i (hp i)).1 inferInstance

end Tensor

private theorem flat_iff_tensorLeft_preservesFiniteLimits
    {A : Type*} [Category A] [MonoidalCategory A] [BraidedCategory A]
    [∀ X : A, PreservesColimitsOfSize.{0, 0} (tensorLeft X)] (X : A) :
    ObjectProperty.flat X ↔ PreservesFiniteLimits (tensorLeft X) := by
  refine ⟨fun h ↦ h.1.1, fun h ↦ ⟨⟨h,
    (inferInstance : PreservesFiniteColimits (tensorLeft X))⟩, ?_, ?_⟩⟩
  · exact preservesFiniteLimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight X)
  · exact preservesFiniteColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight X)

-- The Tor diagram chase of FlatModel.flat_opcycles_of_exactAt uses only right exactness
-- of tensor, supplied here directly by colimit preservation instead of closedness.
private theorem flat_opcycles_of_tensor_exactAt
    {A : Type*} [Category A] [Abelian A] [MonoidalCategory A] [BraidedCategory A]
    [MonoidalPreadditive A]
    [∀ X : A, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
    (P : CochainComplex A ℤ) (a : ℤ)
    (h₁ : ObjectProperty.flat (P.X (a - 1))) (h₂ : ObjectProperty.flat (P.X a))
    (hP : ∀ F : A, (((tensorRight F).mapHomologicalComplex (.up ℤ)).obj P).ExactAt (a - 1)) :
    ObjectProperty.flat (P.opcycles a) := by
  have := h₁.tensorLeft.preservesFiniteLimits
  have := h₂.tensorLeft.preservesFiniteLimits
  rw [flat_iff_tensorLeft_preservesFiniteLimits,
    Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono]
  intro S hS
  refine ⟨hS.exact.map_of_epi_of_preservesCokernel _ hS.epi_g inferInstance, ?_⟩
  have := hS.mono_f
  have := hS.epi_g
  dsimp
  set d := P.d (a - 1) a
  set d' := P.d (a - 1 - 1) (a - 1)
  set p := P.pOpcycles a
  have hdp : d ≫ p = 0 := P.d_pOpcycles _ _
  have (F : A) : PreservesColimitsOfSize.{0, 0} (tensorRight F) :=
    preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight F)
  -- the cokernel sequence `P^{a-1} ⟶ P^a ⟶ C ⟶ 0`, tensored with any object, stays exact
  have hcok (F : A) : (ShortComplex.mk (d ▷ F) (p ▷ F)
      (by rw [← comp_whiskerRight, hdp, MonoidalPreadditive.zero_whiskerRight])).Exact := by
    have h : (ShortComplex.mk d p hdp).Exact :=
      ShortComplex.exact_of_g_is_cokernel _ (P.opcyclesIsCokernel _ _ (by simp))
    exact h.map_of_epi_of_preservesCokernel (tensorRight F) (by dsimp; infer_instance)
      inferInstance
  have hpe (F : A) : Epi (p ▷ F) := (tensorRight F).map_epi p
  have hge (X : A) : Epi (X ◁ S.g) := (tensorLeft X).map_epi S.g
  refine Preadditive.mono_of_cancel_zero _ (fun {T} x hx ↦ ?_)
  -- lift `x` to `P^a ⊗ S.X₁`
  obtain ⟨T₁, π₁, _, y, hy⟩ := surjective_up_to_refinements_of_epi (p ▷ S.X₁) x
  -- its image in `P^a ⊗ S.X₂` dies in `C ⊗ S.X₂`, so it comes from `P^{a-1} ⊗ S.X₂`
  obtain ⟨T₂, π₂, _, z, hz⟩ :=
      (hcok S.X₂).exact_up_to_refinements (y ≫ P.X a ◁ S.f) (by
    dsimp
    rw [Category.assoc, whisker_exchange, ← Category.assoc, ← hy, Category.assoc,
      hx, comp_zero])
  -- the image of `z` in `P^{a-1} ⊗ S.X₃` is a cycle, hence a boundary
  have hex := (HomologicalComplex.exactAt_iff' _ (a - 1 - 1) (a - 1) a (by simp)
    (by simp)).1 (hP S.X₃)
  obtain ⟨T₃, π₃, _, w, hw⟩ := hex.exact_up_to_refinements (z ≫ P.X (a - 1) ◁ S.g) (by
    change (z ≫ P.X (a - 1) ◁ S.g) ≫ d ▷ S.X₃ = 0
    dsimp at hz
    rw [Category.assoc, whisker_exchange, ← Category.assoc, ← hz, Category.assoc,
      Category.assoc, ← MonoidalCategory.whiskerLeft_comp, S.zero,
      MonoidalPreadditive.whiskerLeft_zero, comp_zero, comp_zero])
  let w₀ : T₃ ⟶ P.X (a - 1 - 1) ⊗ S.X₃ := w
  have hw₂ : π₃ ≫ z ≫ P.X (a - 1) ◁ S.g = w₀ ≫ d' ▷ S.X₃ := hw
  obtain ⟨T₄, π₄, _, w', hw'⟩ :=
    surjective_up_to_refinements_of_epi (P.X (a - 1 - 1) ◁ S.g) w₀
  dsimp at hz
  -- correcting `z` by a boundary, it comes from `P^{a-1} ⊗ S.X₁`
  have hz' : (π₄ ≫ π₃ ≫ z - w' ≫ d' ▷ S.X₂) ≫ P.X (a - 1) ◁ S.g = 0 := by
    rw [Preadditive.sub_comp, Category.assoc, Category.assoc, hw₂, Category.assoc,
      ← whisker_exchange, ← reassoc_of% hw', sub_self]
  have hex₁ : (S.map (tensorLeft (P.X (a - 1)))).Exact := hS.exact.map _
  have : Mono (S.map (tensorLeft (P.X (a - 1)))).f :=
    (tensorLeft (P.X (a - 1))).map_mono S.f
  have : Mono (P.X a ◁ S.f) := (tensorLeft (P.X a)).map_mono S.f
  let v : T₄ ⟶ P.X (a - 1) ⊗ S.X₁ := hex₁.lift _ hz'
  have hv : v ≫ P.X (a - 1) ◁ S.f = π₄ ≫ π₃ ≫ z - w' ≫ d' ▷ S.X₂ :=
    hex₁.lift_f _ hz'
  have hvy : v ≫ d ▷ S.X₁ = π₄ ≫ π₃ ≫ π₂ ≫ y := by
    rw [← cancel_mono (P.X a ◁ S.f)]
    simp only [Category.assoc]
    rw [← whisker_exchange, reassoc_of% hv,
      Preadditive.sub_comp, Category.assoc, Category.assoc, ← hz, Category.assoc,
      ← comp_whiskerRight, P.d_comp_d, MonoidalPreadditive.zero_whiskerRight, comp_zero,
      sub_zero]
  rw [← cancel_epi (π₄ ≫ π₃ ≫ π₂ ≫ π₁), comp_zero]
  simp only [Category.assoc]
  rw [hy, ← reassoc_of% hvy, ← comp_whiskerRight, hdp,
    MonoidalPreadditive.zero_whiskerRight, comp_zero]

section Cycles

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
  {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{w})

set_option hygiene false in
local notation "𝒜" => SheafOfModules.{w}
  ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)

private theorem flat_cycles
    (A : CochainComplex 𝒜 ℤ) (hA : A.Acyclic)
    (hK : A.IsKFlatIndependentCoefficients)
    (hflat : ∀ i : ℤ, IsFlatOnSite (J := J) (R := R) (A.X i)) (n : ℤ) :
    IsFlatOnSite (J := J) (R := R) (A.cycles n) := by
  let := isMonoidal_W_independentCoefficients R
  let := monoidalCategory R
  let := symmetricCategory R
  let := tensorPreadditive R
  have (M : 𝒜) : PreservesColimitsOfSize.{0, 0} (tensorLeft M) := by
    have := tensorLeft_preservesColimits_independentCoefficients R M
    exact preservesColimitsOfSize_shrink (tensorLeft M)
  have hop : ObjectProperty.flat (A.opcycles (n - 1)) := by
    apply flat_opcycles_of_tensor_exactAt A (n - 1)
      (flat_to_cat R _ (hflat _)) (flat_to_cat R _ (hflat _))
    intro N
    let e₁ := CochainComplex.mapBifunctorSingle₁Iso (curriedTensor _) N A
    let e₂ := (NatIso.mapHomologicalComplex
      (BraidedCategory.tensorLeftIsoTensorRight N) (.up ℤ)).app A
    exact (tensor_acyclic R A hK hA
      ((CochainComplex.singleFunctor _ 0).obj N) ((n - 1) - 1)).of_iso (e₁ ≪≫ e₂)
  -- Exactness in the two adjacent degrees makes the induced differential an isomorphism.
  have hm : Mono (A.fromOpcycles (n - 1) n) := by
    have hm' : Mono (A.fromOpcycles (n - 1) ((ComplexShape.up ℤ).next (n - 1))) := by
      have hf : A.fromOpcycles (n - 1) ((ComplexShape.up ℤ).next (n - 1)) =
          (A.sc (n - 1)).fromOpcycles := by
        apply (cancel_epi (A.pOpcycles (n - 1))).1
        rw [A.p_fromOpcycles]
        exact (A.sc (n - 1)).p_fromOpcycles.symm
      rw [hf]
      exact (hA (n - 1)).mono_fromOpcycles
    have hn : (ComplexShape.up ℤ).next (n - 1) = n := by simp
    exact Eq.mp (congrArg (fun j : ℤ ↦ Mono (A.fromOpcycles (n - 1) j)) hn) hm'
  have he : Epi (A.toCycles (n - 1) n) := by
    have he' : Epi (A.toCycles ((ComplexShape.up ℤ).prev n) n) := by
      have hf : A.toCycles ((ComplexShape.up ℤ).prev n) n = (A.sc n).toCycles := by
        apply (cancel_mono (A.iCycles n)).1
        rw [A.toCycles_i]
        exact (A.sc n).toCycles_i.symm
      rw [hf]
      exact (hA n).epi_toCycles
    have hn : (ComplexShape.up ℤ).prev n = n - 1 := by simp
    exact hn ▸ he'
  have : Mono (A.opcyclesToCycles (n - 1) n) :=
    mono_of_mono_fac (A.opcyclesToCycles_iCycles (n - 1) n)
  have : Epi (A.opcyclesToCycles (n - 1) n) :=
    epi_of_epi_fac (A.pOpcycles_opcyclesToCycles (n - 1) n)
  have : IsIso (A.opcyclesToCycles (n - 1) n) := isIso_of_mono_of_epi _
  have hc : ObjectProperty.flat (A.cycles n) :=
    ObjectProperty.prop_of_iso _ (asIso (A.opcyclesToCycles (n - 1) n)) hop
  exact (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso R (A.cycles n)).symm hc.2

end Cycles

section InverseImage

private def sheafUliftIso
    {C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)
    (A : Type uD) [Category.{vD} A] (U : A ⥤ Type w)
    [J.HasSheafCompose U] [J.HasSheafCompose (U ⋙ uliftFunctor.{w, w})] :
    sheafCompose J (U ⋙ uliftFunctor.{w, w}) ≅ sheafCompose J U :=
  NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _
    (NatIso.ofComponents (fun X ↦ uliftTrivial (U.obj (M.obj.obj X)))
      (by intros; rfl))) (by intros; rfl)

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
  {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
  {R : Sheaf JC CommRingCat.{w}} {RI : Sheaf JD CommRingCat.{w}}
  {L : Sheaf JC (Type w) ⥤ Sheaf JD (Type w)}

set_option backward.isDefEq.respectTransparency false in
private noncomputable def inverseImageOfUniverses (I : AlgebraicInverseImage L R RI) :
    AlgebraicInverseImageOfUniverses.{uC, vC, uD, vD, w, w} L R RI := by
  let eR := sheafUliftIso JC CommRingCat.{w} (CategoryTheory.forget CommRingCat.{w})
  let eS := sheafUliftIso JD CommRingCat.{w} (CategoryTheory.forget CommRingCat.{w})
  let eM := isoWhiskerLeft (toSheaf ((sheafCompose JC
    (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) <|
    sheafUliftIso JC AddCommGrpCat.{w} (CategoryTheory.forget AddCommGrpCat.{w})
  let eN := isoWhiskerLeft (toSheaf ((sheafCompose JD
    (forget₂ CommRingCat.{w} RingCat.{w})).obj RI)) <|
    sheafUliftIso JD AddCommGrpCat.{w} (CategoryTheory.forget AddCommGrpCat.{w})
  let er := L.mapIso (eR.app R) ≪≫ I.ringUnderlying ≪≫ (eS.app RI).symm
  let em := isoWhiskerLeft I.modules eN ≪≫ I.moduleUnderlying ≪≫
    isoWhiskerRight eM.symm L
  refine
    { ringUnderlying := er
      ringAdd := ?_
      ringMul := ?_
      ringZero := ?_
      ringOne := ?_
      modules := I.modules
      moduleUnderlying := em
      moduleAdd := ?_
      moduleZero := ?_
      moduleSMul := ?_ }
  · intro T a b t h V x
    have hr := I.ringAdd T (a ≫ (eR.app R).hom) (b ≫ (eR.app R).hom)
      (t ≫ (eR.app R).hom) h V x
    simpa [er, eS, sheafUliftIso, uliftTrivial, Functor.map_comp] using hr
  · intro T a b t h V x
    have hr := I.ringMul T (a ≫ (eR.app R).hom) (b ≫ (eR.app R).hom)
      (t ≫ (eR.app R).hom) h V x
    simpa [er, eS, sheafUliftIso, uliftTrivial, Functor.map_comp] using hr
  · intro T a h V x
    have hr := I.ringZero T (a ≫ (eR.app R).hom) h V x
    simpa [er, eS, sheafUliftIso, uliftTrivial, Functor.map_comp] using hr
  · intro T a h V x
    have hr := I.ringOne T (a ≫ (eR.app R).hom) h V x
    simpa [er, eS, sheafUliftIso, uliftTrivial, Functor.map_comp] using hr
  · intro M T a b t h V x
    have hr := I.moduleAdd M T (a ≫ (eM.app M).hom) (b ≫ (eM.app M).hom)
      (t ≫ (eM.app M).hom) h V x
    simpa [em, eN, sheafUliftIso, uliftTrivial, Functor.map_comp] using hr
  · intro M T a h V x
    have hr := I.moduleZero M T (a ≫ (eM.app M).hom) h V x
    simpa [em, eN, sheafUliftIso, uliftTrivial, Functor.map_comp] using hr
  · intro M T a b t h V x
    have hr := I.moduleSMul M T (a ≫ (eR.app R).hom) (b ≫ (eM.app M).hom)
      (t ≫ (eM.app M).hom) h V x
    simpa [er, em, eS, eN, sheafUliftIso, uliftTrivial, Functor.map_comp] using hr

end InverseImage

/-- The acyclic case of K-flat pullback along a morphism of ringed topoi.
Source: Stacks Project, Cohomology on Sites, Tag 0G7E, the acyclic-case paragraph,
using Tag 0G7C for flatness of cycles.
(auxiliary; not a blueprint node).

Proof: because P is acyclic, K-flat, and flat in every degree, its cycles are flat
by the acyclic K-flat cycles criterion. Its good truncation at n therefore has flat
terms: the old terms below n, the flat cycle sheaf in degree n, and zero above n.
Flat pullback makes the terms of its image flat; additivity sends zero to zero, so
the image remains bounded above. Every such image is K-flat by the bounded-above
flat criterion. The integer-indexed good truncations have degreewise colimit P,
since in every degree they are eventually equal to P. The filtered-colimit
preservation theorem for the specified module pullback implies that uStar preserves
this colimit, including all transition maps and differentials. Filtered-colimit
closure of K-flatness now proves that the
image of P is K-flat. No exactness of uStar on arbitrary short exact sequences is used. -/
theorem isKFlat_ringedToposPullback_of_acyclic
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    {R : Sheaf JC CommRingCat.{w}} {S RI : Sheaf JD CommRingCat.{w}}
    (uInv : Sheaf JC (Type (w)) ⥤ Sheaf JD (Type (w)))
    (uPush : Sheaf JD (Type (w)) ⥤ Sheaf JC (Type (w)))
    (adj : uInv ⊣ uPush) [PreservesFiniteLimits uInv]
    (I : AlgebraicInverseImage uInv R RI) (c : RI ⟶ S)
    (uStar : SheafOfModules.{w} ((sheafCompose JC
      (forget₂ CommRingCat.{w} RingCat.{w})).obj R) ⥤
      SheafOfModules.{w} ((sheafCompose JD
        (forget₂ CommRingCat.{w} RingCat.{w})).obj S))
    (hobj : ∀ M : SheafOfModules.{w} ((sheafCompose JC
      (forget₂ CommRingCat.{w} RingCat.{w})).obj R),
      uStar.obj M = changeOfRings c (I.modules.obj M))
    (hmap : ∀ {M N : SheafOfModules.{w} ((sheafCompose JC
      (forget₂ CommRingCat.{w} RingCat.{w})).obj R)} (a : M ⟶ N),
      uStar.map a = eqToHom (hobj M) ≫
        changeOfRingsHom c (I.modules.obj M) (I.modules.map a) ≫ eqToHom (hobj N).symm)
    [uStar.Additive]
    (P : CochainComplex (SheafOfModules.{w} ((sheafCompose JC
      (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) ℤ)
    (hacyclic : P.Acyclic) (hP : P.IsKFlatIndependentCoefficients)
    (hflat : ∀ n : ℤ, IsFlatOnSite (J := JC) (R := R) (P.X n)) :
    CochainComplex.IsKFlatIndependentCoefficients
      ((uStar.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) := by
  let 𝒜 := SheafOfModules.{w}
    ((sheafCompose JC (forget₂ CommRingCat.{w} RingCat.{w})).obj R)
  let ℬ := SheafOfModules.{w}
    ((sheafCompose JD (forget₂ CommRingCat.{w} RingCat.{w})).obj S)
  let := isMonoidal_W_independentCoefficients R
  let := monoidalCategory R
  let := symmetricCategory R
  let := tensorPreadditive R
  let := isMonoidal_W_independentCoefficients S
  let := monoidalCategory S
  let := symmetricCategory S
  let := tensorPreadditive S
  have (M : ℬ) : PreservesColimitsOfSize.{0, 0} (tensorLeft M) := by
    have := tensorLeft_preservesColimits_independentCoefficients S M
    exact preservesColimitsOfSize_shrink (tensorLeft M)
  have (M : ℬ) : PreservesColimitsOfSize.{0, 0} (tensorRight M) :=
    preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight M)
  have : ∀ X₁ X₂ : GradedObject ℤ ℬ, GradedObject.HasTensor X₁ X₂ := by infer_instance
  have : ∀ X₁ X₂ X₃ : GradedObject ℤ ℬ,
      GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃ := by infer_instance
  have : ∀ X₁ X₂ X₃ : GradedObject ℤ ℬ,
      GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃ := by infer_instance
  have : ∀ X₁ X₂ X₃ X₄ : GradedObject ℤ ℬ,
      GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄ := by infer_instance
  have : AB5OfSize.{w, w} AddCommGrpCat.{w} := inferInstance
  have : AB5OfSize.{0, 0} AddCommGrpCat.{w} := AB5OfSize_shrink _
  have : HasExactColimitsOfShape ℤ ℬ :=
    HasExactColimitsOfShape.domain_of_functor ℤ (toSheaf _)
  have htrunc (n i : ℤ) : ObjectProperty.flat ((P.truncLE n).X i) := by
    by_cases hi : i < n
    · exact ObjectProperty.prop_of_iso _ (P.truncLEXIso n i hi).symm
        (flat_to_cat R _ (hflat i))
    · by_cases hin : i = n
      · subst i
        exact ObjectProperty.prop_of_iso _ (P.truncLEXIsoCycles n).symm
          (flat_to_cat R _ (flat_cycles R P hacyclic hP hflat n))
      · exact ObjectProperty.flat_of_isZero
          ((P.truncLE n).isZero_of_isStrictlyLE n i (by omega))
  have hpull (M : 𝒜) (hM : ObjectProperty.flat M) :
      ObjectProperty.flat (uStar.obj M) := by
    have hM' : IsFlatOnSite (J := JC) (R := R) M :=
      (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso R M).symm hM.2
    apply flat_to_cat S
    rw [hobj M]
    exact isFlat_ringedToposPullback.{uC, vC, uD, vD, w, w} uInv uPush adj
      (inverseImageOfUniverses I) c M hM'
  have : PreservesColimitsOfShape (AsSmall.{w} ℤ) uStar :=
    preservesFilteredColimits_ringedToposPullback uInv uPush adj I c uStar hobj hmap _
  have : PreservesColimitsOfShape ℤ uStar :=
    preservesColimitsOfShape_of_equiv (show ℤ ≌ AsSmall.{w} ℤ from AsSmall.equiv).symm uStar
  let F := uStar.mapHomologicalComplex (ComplexShape.up ℤ)
  have : PreservesColimitsOfShape ℤ F := by infer_instance
  have hk : (HomologicalComplex.quasiIso ℬ (.up ℤ)).kFlat (F.obj P) := by
    apply ObjectProperty.prop_of_isColimit _
      (isColimitOfPreserves F P.isColimitFiltrationLECocone)
    intro n
    have : CochainComplex.IsStrictlyLE (F.obj (P.truncLE n)) n := by
      rw [CochainComplex.isStrictlyLE_iff]
      intro i hi
      exact uStar.map_isZero ((P.truncLE n).isZero_of_isStrictlyLE n i hi)
    exact CochainComplex.kFlat_of_isStrictlyLE_of_flat (F.obj (P.truncLE n)) n
      (fun i ↦ hpull _ (htrunc n i))
  intro Z hZ
  let T := MonoidalCategory.tensorRight (F.obj P)
  have hz : QuasiIso (0 : (0 : CochainComplex ℬ ℤ) ⟶ Z) := by
    rw [quasiIso_iff]
    intro i
    exact (quasiIsoAt_iff_exactAt _ i
      ((HomologicalComplex.acyclic_of_isZero _ (isZero_zero _)) i)).2 (hZ i)
  have hmap : QuasiIso (T.map (0 : (0 : CochainComplex ℬ ℤ) ⟶ Z)) := hk.2 _ hz
  have htzero : (T.obj (0 : CochainComplex ℬ ℤ)).Acyclic :=
    HomologicalComplex.acyclic_of_isZero _ (T.map_isZero (isZero_zero _))
  exact fun i ↦ (exactAt_iff_of_quasiIsoAt
    (T.map (0 : (0 : CochainComplex ℬ ℤ) ⟶ Z)) i).1 (htzero i)

end SheafOfModules
