/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.RingComplexCechData
import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.AlgebraicGeometry.RingComplexGodementCech
import WeilConjectures.AlgebraicGeometry.RingComplexOrderedScalarIso
public import Mathlib.RingTheory.Flat.Localization

/-! # Element-power torsion in ordered localization-model cohomology -/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private abbrev point : (Discrete PUnit.{u + 1})ᵒᵖ := op ⟨PUnit.unit⟩

private noncomputable abbrev pointEval (A : CommRingCat.{u}) :
    RingSiteModules A ⥤ ModuleCat.{u} A :=
  SheafOfModules.evaluation _ point

private noncomputable def pointUnitIso (A : CommRingCat.{u}) (M : RingSiteModules A) :
    M ≅ (ringComplexConstant A).obj ((pointEval A).obj M) where
  hom := ringComplexPointLift _ _ LinearMap.id
  inv := ringComplexPointLift _ _ LinearMap.id
  hom_inv_id := by apply ringComplex_point_hom_ext; rfl
  inv_hom_id := by apply ringComplex_point_hom_ext; rfl

private noncomputable def pointEquivalence (A : CommRingCat.{u}) :
    RingSiteModules A ≌ ModuleCat.{u} A where
  functor := pointEval A
  inverse := ringComplexConstant A
  unitIso := NatIso.ofComponents (pointUnitIso A) (by
    intro M N f
    apply ringComplex_point_hom_ext
    rfl)
  counitIso := Iso.refl _

private noncomputable local instance pointEval_isEquivalence (A : CommRingCat.{u}) :
    (pointEval A).IsEquivalence := (pointEquivalence A).isEquivalence_functor

private local instance pointEval_additive (A : CommRingCat.{u}) :
    (pointEval A).Additive where
  map_add := by intros; rfl

private theorem point_isZero {A : CommRingCat.{u}} (M : RingSiteModules A)
    (h : Subsingleton (M.val.obj point)) : IsZero M := by
  rw [IsZero.iff_id_eq_zero]
  apply ringComplex_point_hom_ext
  ext x
  exact h.elim _ _

private theorem acyclic_two_term {D : Type*} [Category D] [Abelian D]
    (K : CochainComplex D ℤ)
    (hzero : ∀ n : ℤ, n ≠ 0 → n ≠ 1 → IsZero (K.X n))
    [IsIso (K.d 0 1)] : K.Acyclic := by
  intro n
  by_cases hn : n = 0
  · subst n
    rw [HomologicalComplex.exactAt_iff' K (i := -1) (j := 0) (k := 1)
      (by simp) (by simp)]
    apply (ShortComplex.exact_iff_mono _
      ((hzero (-1) (by omega) (by omega)).eq_zero_of_src _)).2
    change Mono (K.d 0 1)
    infer_instance
  · by_cases hn' : n = 1
    · subst n
      rw [HomologicalComplex.exactAt_iff' K (i := 0) (j := 1) (k := 2)
        (by simp) (by simp)]
      apply (ShortComplex.exact_iff_epi _
        ((hzero 2 (by omega) (by omega)).eq_zero_of_tgt _)).2
      change Epi (K.d 0 1)
      infer_instance
    · exact HomologicalComplex.ExactAt.of_isZero (hzero n hn hn')

-- Compare the unit ideal with the singleton list (1), rather than constructing
-- a contraction for every ordered list separately.
private theorem unitIdeal_godement_zero (A : CommRingCat.{u})
    [HasDerivedCategory.{w} (RingSiteModules A)] :
    IsZero (DerivedCategory.Q.obj (ringComplexGodement A ⊤)) := by
  classical
  let f : Fin 1 → A := fun _ ↦ 1
  have hf : Ideal.span (Set.range f) = ⊤ := by
    apply Ideal.eq_top_of_isUnit_mem _ _ isUnit_one
    exact Ideal.subset_span ⟨0, rfl⟩
  obtain ⟨C, a, e₀, e, l, hneg, hd₀, hd, ha, α, hα⟩ :=
    ringComplex_godement_cech A ⟨⊤, Module.Finite.fg_top⟩ 1 f hf
  let t₀ : Fin 1 ↪o Fin 1 := (OrderIso.refl _).toOrderEmbedding
  have ht (t : Fin 1 ↪o Fin 1) : t = t₀ := by
    apply DFunLike.ext
    intro i
    exact Subsingleton.elim _ _
  let g : A := ∏ i, f (t₀ i)
  let b : A ≃ₐ[A] Localization.Away g :=
    IsLocalization.atUnit A _ g (by simp [g, f])
  have hd₀' (x : (C.X 0).val.obj point) :
      e 0 ((C.d 0 1).val.app point x) t₀ = b (e₀ x) := by
    exact (hd₀ x t₀).trans (b.commutes (e₀ x)).symm
  have hbij : Function.Bijective ((C.d 0 1).val.app point) := by
    constructor
    · intro x y h
      apply e₀.injective
      apply b.injective
      exact (hd₀' x).symm.trans ((congrArg (fun z ↦ e 0 z t₀) h).trans (hd₀' y))
    · intro z
      refine ⟨e₀.symm (b.symm (e 0 z t₀)), ?_⟩
      apply (e 0).injective
      funext t
      rw [ht t, hd₀', LinearEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
  have : IsIso ((pointEval A).map (C.d 0 1)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  have : IsIso (C.d 0 1) := isIso_of_reflects_iso _ (pointEval A)
  have hC : C.Acyclic := acyclic_two_term C (by
    intro n hn₀ hn₁
    by_cases hn : n < 0
    · exact hneg n hn
    · obtain ⟨q, rfl⟩ : ∃ q : ℕ, n = (q : ℤ) + 1 :=
        ⟨(n - 1).toNat, by omega⟩
      have he : IsEmpty (Fin (q + 1) ↪o Fin 1) := ⟨fun t ↦ by
        have hc := Fintype.card_le_of_injective t t.injective
        simp only [Fintype.card_fin] at hc
        omega⟩
      let := he
      exact point_isZero _ (e q).injective.subsingleton)
  have hz : IsZero (DerivedCategory.Q.obj C) := by
    apply (DerivedCategory.isZero_iff _).2
    intro i
    exact (hC i).isZero_homology.of_iso ((DerivedCategory.homologyFunctorFactors _ i).app C)
  exact hz.of_iso α.symm

-- The sheafification unit on the bottom topology commutes with each differential.
private noncomputable def extensionEvaluationIso {A B : CommRingCat.{u}}
    (φ : A →+* B) (C : CochainComplex (RingSiteModules A) ℤ) :
    (((pointEval A ⋙ ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj C) ≅
      (((pointEval B).mapHomologicalComplex (.up ℤ)).obj
        (ringComplexExtensionComplex φ C)) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ ringComplexExtensionSections φ (C.X n)) (by
      intro n m hnm
      apply ModuleCat.ExtendScalars.hom_ext
      intro x
      exact ringComplexExtension_map_one_tmul φ (C.d n m) x)

private theorem power_torsion_of_localization_zero (A : CommRingCat.{u}) (s : A)
    (B : Type u) [CommRing B] [Algebra A B] [IsLocalization (Submonoid.powers s) B]
    (M : ModuleCat.{u} A)
    (hM : IsZero ((ModuleCat.extendScalars (algebraMap A B)).obj M)) (x : M) :
    ∃ k : ℕ, s ^ k • x = 0 := by
  let φ := algebraMap A B
  have halg : φ.toAlgebra = inferInstanceAs (Algebra A B) :=
    Algebra.algebra_ext _ _ fun _ ↦ rfl
  have hloc : IsLocalization (Submonoid.powers s) B := inferInstance
  let : Algebra A B := φ.toAlgebra
  let : IsLocalization (Submonoid.powers s) B := by
    change @IsLocalization A _ (Submonoid.powers s) B _ φ.toAlgebra
    rw [halg]
    exact hloc
  let : IsLocalizedModule (Submonoid.powers s) (TensorProduct.mk A B M 1) :=
    IsLocalization.tensorProduct_isLocalizedModule (Submonoid.powers s) B
  have hz : (TensorProduct.mk A B M 1) x = 0 :=
    (ModuleCat.isZero_iff_subsingleton.mp hM).elim _ _
  obtain ⟨t, ht⟩ := (IsLocalizedModule.eq_zero_iff (Submonoid.powers s)
    (TensorProduct.mk A B M 1)).mp hz
  obtain ⟨k, hk⟩ := t.property
  exact ⟨k, by simpa only [Submonoid.smul_def, ← hk] using ht⟩

/-- Every cohomology class of an ordered localization model is killed by some power
of each element of the defining ideal. No coefficient module or derived Hom occurs.
Source: Stacks Project, dualizing.tex, Tag 0A6R, lemma-local-cohomology-adjoint,
and the finite localization calculation in its proof.
(auxiliary; not a blueprint node)

Proof: choose a finite generating list of I and append s, retaining the same span.
Apply hT to that list. Invert s in every term of its ordered localization complex.
A coordinate whose index contains the appended index is identified with the same
localization as the coordinate obtained by deleting that index. Insert or delete
this final index, with the alternating sign of its position, to define a degree
minus one homotopy. The two homotopy composites cancel in pairs on all other
coordinates and give the identity on the remaining coordinate, also in degree
zero. Thus the localized complex is contractible. Localization is exact, so it
commutes with cohomology. The model isomorphism transports this vanishing to T.
The module-localization zero criterion says precisely that each original class
is annihilated by some power of s. Evaluation at the unique object is exact and
identifies the calculation with ordinary modules. Zero and nilpotent s, the zero
ring, repeated generators, and the empty initial generating list are included.
-/
theorem ringComplex_cech_cohomology_power_torsion
    (A : CommRingCat.{u}) [HasDerivedCategory.{w} (RingSiteModules A)]
    (I : {I : Ideal A // I.FG})
    (T : CochainComplex (RingSiteModules A) ℤ) (εT : T ⟶ ringComplexSingle A)
    (hT : RingComplexHasCechModel A I.val T εT)
    (s : A) (hs : s ∈ I.val) :
    ∀ (i : ℤ) (x : (T.homology i).val.obj (op ⟨PUnit.unit⟩)),
      ∃ k : ℕ, s ^ k • x = 0 := by
  classical
  let B : CommRingCat.{u} := CommRingCat.of (Localization.Away s)
  let φ : A →+* B := algebraMap A (Localization.Away s)
  let : HasDerivedCategory.{u + 1} (RingSiteModules B) :=
    HasDerivedCategory.standard _
  obtain ⟨r, f, hf⟩ := Submodule.fg_iff_exists_fin_generating_family.mp I.property
  obtain ⟨C, a, e₀, e, l, hneg, hd₀, hd, ha, α, hα⟩ := hT r f hf
  have hI : I.val.map φ = ⊤ := by
    apply Ideal.eq_top_of_isUnit_mem _ _
      (IsLocalization.Away.algebraMap_isUnit s (S := Localization.Away s))
    exact Ideal.mem_map_of_mem φ hs
  have hf' : Ideal.span (Set.range f) = I.val := hf
  have hfB : Ideal.span (Set.range (φ ∘ f)) = (⊤ : Ideal B) := by
    rw [Set.range_comp, ← Ideal.map_span, hf', hI]
  obtain ⟨D, b, e₀', e', l', hneg', hd₀', hd', ha', β, hβ⟩ :=
    ringComplex_godement_cech B ⟨⊤, Module.Finite.fg_top⟩ r (φ ∘ f) hfB
  obtain ⟨γ, hγ⟩ := ringComplex_ordered_scalar_iso A B φ r f
    C a e₀ e l hneg hd₀ hd ha D b e₀' e' l' hneg' hd₀' hd' ha'
  have hD : IsZero (DerivedCategory.Q.obj D) :=
    (unitIdeal_godement_zero B).of_iso β
  have hDacyclic : D.Acyclic := by
    intro i
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact ((DerivedCategory.homologyFunctor _ i).map_isZero hD).of_iso
      ((DerivedCategory.homologyFunctorFactors _ i).app D).symm
  let L := ModuleCat.extendScalars φ
  let : PreservesFiniteLimits L :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat
      (RingHom.flat_algebraMap_iff.mpr
        (IsLocalization.flat (Localization.Away s) (Submonoid.powers s)))
  let : L.IsLeftAdjoint := (ModuleCat.extendRestrictScalarsAdj φ).isLeftAdjoint
  let : L.Additive := (ModuleCat.extendRestrictScalarsAdj φ).left_adjoint_additive
  let E := pointEval A ⋙ L
  have : (pointEval A).IsEquivalence := pointEval_isEquivalence A
  have : (pointEval B).IsEquivalence := pointEval_isEquivalence B
  have : (pointEval B).Additive := pointEval_additive B
  have : PreservesFiniteLimits (pointEval A) := inferInstance
  have : PreservesFiniteColimits (pointEval A) := inferInstance
  have : PreservesFiniteLimits (pointEval B) := inferInstance
  have : PreservesFiniteColimits (pointEval B) := inferInstance
  have : PreservesFiniteLimits E := comp_preservesFiniteLimits (pointEval A) L
  have : PreservesFiniteColimits E := comp_preservesFiniteColimits (pointEval A) L
  let δ := extensionEvaluationIso φ C ≪≫
    ((pointEval B).mapHomologicalComplex (.up ℤ)).mapIso γ
  have hEC : ((E.mapHomologicalComplex (.up ℤ)).obj C).Acyclic := by
    intro i
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    have hz : IsZero ((((pointEval B).mapHomologicalComplex (.up ℤ)).obj D).homology i) :=
      ((pointEval B).map_isZero (hDacyclic i).isZero_homology).of_iso
        (((pointEval B).mapHomologicalComplexHomologyIso (.up ℤ) i).app D)
    exact hz.of_iso ((HomologicalComplex.homologyFunctor _ _ i).mapIso δ)
  intro i x
  let η : C.homology i ≅ T.homology i :=
    ((DerivedCategory.homologyFunctorFactors _ i).app C).symm ≪≫
      (DerivedCategory.homologyFunctor _ i).mapIso α ≪≫
        (DerivedCategory.homologyFunctorFactors _ i).app T
  have hHC : IsZero (E.obj (C.homology i)) :=
    (hEC i).isZero_homology.of_iso ((E.mapHomologicalComplexHomologyIso (.up ℤ) i).app C).symm
  have hHT : IsZero (E.obj (T.homology i)) := hHC.of_iso (E.mapIso η).symm
  exact power_torsion_of_localization_zero A s (Localization.Away s)
    ((pointEval A).obj (T.homology i)) hHT x

end AlgebraicGeometry
