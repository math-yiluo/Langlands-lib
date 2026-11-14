import Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeqCreation
import Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeqSlantDual
import Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeqAxisSlant

/-! # Bottom-degree classes for creation and shuffle slant -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeq

open Langlands.Cohomology Cech Cech.KunnethDetection DerivedSections
open Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof
open Langlands.AlgebraicGeometry.Picard.FieldTwoAxisH1Injectivity

section ZeroClasses

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (π : X ⟶ Spec R)
  {ι : Type u} [Fintype ι] (U : ι → X.Opens) (M : X.Modules)

lemma subtype_comp_d_zero :
    ModuleCat.ofHom (LinearMap.ker (dCochain π U M 0)).subtype ≫
      (cochainComplex π U M).d 0 1 = 0 := by
  rw [cochainComplex_d]
  ext z
  exact z.2

/-- A closed zero-cochain as a cycle of the actual ordered complex. -/
def cyclesOfKerZero :
    ModuleCat.of R (LinearMap.ker (dCochain π U M 0)) ⟶
      (cochainComplex π U M).cycles 0 :=
  (cochainComplex π U M).liftCycles
    (ModuleCat.ofHom (LinearMap.ker (dCochain π U M 0)).subtype) 1 (by simp)
    (subtype_comp_d_zero π U M)

lemma cyclesOfKerZero_i (z : LinearMap.ker (dCochain π U M 0)) :
    (cochainComplex π U M).iCycles 0 (cyclesOfKerZero π U M z) = z.1 := by
  rw [← ConcreteCategory.comp_apply, cyclesOfKerZero, HomologicalComplex.liftCycles_i]
  rfl

/-- The homology class of a closed zero-cochain. -/
def classMapZero :
    LinearMap.ker (dCochain π U M 0) →ₗ[R] (cochainComplex π U M).homology 0 :=
  (cyclesOfKerZero π U M ≫ (cochainComplex π U M).homologyπ 0).hom

lemma classMapZero_apply (z : LinearMap.ker (dCochain π U M 0)) :
    classMapZero π U M z =
      (cochainComplex π U M).homologyπ 0 (cyclesOfKerZero π U M z) := rfl

variable [IsSeparated π] (hUtop : ⨆ i, U i = ⊤) (hUa : ∀ i, IsAffineOpen (U i))

/-- A degree-zero cocycle class in actual right-derived cohomology. -/
def canonicalClassZero :
    LinearMap.ker (dCochain π U (unitModule X) 0) →ₗ[R]
      (relativeCohomology π 0).obj (unitModule X) :=
  (cohomologyEquiv π U hUtop hUa 0).toLinearMap.comp (classMapZero π U (unitModule X))

end ZeroClasses

section Unit

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (π : X ⟶ Spec R)
  {ι : Type u} [Fintype ι] (U : ι → X.Opens)

/-- The constant unit zero-cocycle. -/
def oneZeroCocycle : LinearMap.ker (dCochain π U (unitModule X) 0) :=
  ⟨Cech.one X.presheaf U, by
    rw [LinearMap.mem_ker]
    rw [dCochain_unit]
    exact Cech.d_one⟩

omit [Fintype ι] in
lemma cup_oneZeroCocycle (z : cochain π U (unitModule X) 1) :
    cup π U z (oneZeroCocycle π U).1 = z := by
  funext τ
  change cup₁ X.presheaf U z (Cech.one X.presheaf U) τ = z τ
  rw [cup₁_apply, face_one', mul_one]
  have he : edge (0 : Fin 1) = id := by
    funext i
    fin_cases i <;> rfl
  rw [he, face_id]

/-- The class of the unit zero-cocycle. -/
def unitH : (cochainComplex π U (unitModule X)).homology 0 :=
  classMapZero π U (unitModule X) (oneZeroCocycle π U)

lemma creationByCocycle_unitH
    (z : LinearMap.ker (dCochain π U (unitModule X) 1)) :
    creationByCocycle π U z 0 (unitH π U) = classMap π U (unitModule X) 0 z := by
  rw [unitH, classMapZero_apply, classMap_apply, ← ConcreteCategory.comp_apply,
    creationByCocycle, Cech.creationHomologyMap_homologyπ, ConcreteCategory.comp_apply]
  congr 1
  apply (ModuleCat.mono_iff_injective
    ((cochainComplex π U (unitModule X)).iCycles 1)).1 inferInstance
  have h := congrArg (fun f => f (cyclesOfKerZero π U (unitModule X) (oneZeroCocycle π U)))
    (Cech.creationCyclesMap_i _ _ (creationCochainMap π U z)
      (creationCochainMap_anticomm π U z) 0)
  simp only [ConcreteCategory.comp_apply] at h ⊢
  refine h.trans ?_
  change creationCochainMap π U z 0
      ((cochainComplex π U (unitModule X)).iCycles 0
        (cyclesOfKerZero π U (unitModule X) (oneZeroCocycle π U))) =
    (cochainComplex π U (unitModule X)).iCycles 1 (cyclesOfKer π U (unitModule X) 0 z)
  rw [cyclesOfKerZero_i, cyclesOfKer_i]
  exact cup_oneZeroCocycle π U z.1

lemma creationH_unitH (x : (cochainComplex π U (unitModule X)).homology 1) :
    creationH π U 0 x (unitH π U) = x := by
  obtain ⟨z, rfl⟩ := classMap_surjective π U (unitModule X) 0 x
  rw [creationH_classMap]
  exact creationByCocycle_unitH π U z

variable [IsSeparated π] (hUtop : ⨆ i, U i = ⊤) (hUa : ∀ i, IsAffineOpen (U i))

/-- The actual degree-zero class represented by the unit cocycle on the fixed cover. -/
def unitCanonical : (relativeCohomology π 0).obj (unitModule X) :=
  cohomologyEquiv π U hUtop hUa 0 (unitH π U)

lemma creationCanonical_unitCanonical
    (x : (relativeCohomology π 1).obj (unitModule X)) :
    creationCanonical π U hUtop hUa 0 x (unitCanonical π U hUtop hUa) = x := by
  rw [creationCanonical_apply]
  simp only [unitCanonical, LinearEquiv.symm_apply_apply, creationH_unitH,
    LinearEquiv.apply_symm_apply]

end Unit

section SlantBottom

variable {R : CommRingCat.{u}} {X Y P : Scheme.{u}}
  {πX : X ⟶ Spec R} {πY : Y ⟶ Spec R} {πP : P ⟶ Spec R}
  {p₁ : P ⟶ X} {p₂ : P ⟶ Y} (hP : IsPullback p₁ p₂ πX πY)
  [∀ W : X.Opens, Algebra R Γ(X, W)]
  (halgX : ∀ W : X.Opens, algebraMap R Γ(X, W) = (secHom πX W).hom)
  [∀ W : Y.Opens, Algebra R Γ(Y, W)]
  (halgY : ∀ W : Y.Opens, algebraMap R Γ(Y, W) = (secHom πY W).hom)
  [∀ W : P.Opens, Algebra R Γ(P, W)]
  (halgP : ∀ W : P.Opens, algebraMap R Γ(P, W) = (secHom πP W).hom)
  (hπ : p₁ ≫ πX = πP)
  {ι κ : Type u} [Fintype ι] [Fintype κ] (U : ι → X.Opens) (V : κ → Y.Opens)
  (hU : ∀ σ : Fin 2 → ι, IsAffineOpen (inter U σ))
  (hV : ∀ (m : ℕ) (τ : Fin (m + 1) → κ), IsAffineOpen (inter V τ))
  (l : (∀ σ : Fin 2 → ι, Γ(X, inter U σ)) →ₗ[R] R)
  (hl : ∀ y : C (ab X.presheaf) U 0, l (Cech.d (ab X.presheaf) U 0 y) = 0)

include hl in
lemma slantCochainMap_mem_ker_zero
    (b : LinearMap.ker (dCochain πP (prodCover p₁ p₂ U V) (unitModule P) 1)) :
    slantCochainMap hP halgX halgY halgP hπ U V hU hV l 0 b.1 ∈
      LinearMap.ker (dCochain πY V (unitModule Y) 0) := by
  rw [LinearMap.mem_ker]
  have h := congrArg
    (fun f => f b.1)
    (slantCochainMap_anticomm hP halgX halgY halgP hπ U V hU hV l hl 0)
  rw [cochainComplex_d, cochainComplex_d] at h
  change slantCochainMap hP halgX halgY halgP hπ U V hU hV l 1
      (dCochain πP (prodCover p₁ p₂ U V) (unitModule P) 1 b.1) =
    -dCochain πY V (unitModule Y) 0
      (slantCochainMap hP halgX halgY halgP hπ U V hU hV l 0 b.1) at h
  rw [b.2, map_zero] at h
  exact neg_eq_zero.mp h.symm

/-- Slant of a one-cocycle is represented by its degree-zero shuffle slant. -/
lemma slantH_classMap_bottom
    (b : LinearMap.ker (dCochain πP (prodCover p₁ p₂ U V) (unitModule P) 1)) :
    slantH hP halgX halgY halgP hπ U V hU hV l hl 0
        (classMap πP (prodCover p₁ p₂ U V) (unitModule P) 0 b) =
      classMapZero πY V (unitModule Y)
        ⟨slantCochainMap hP halgX halgY halgP hπ U V hU hV l 0 b.1,
          slantCochainMap_mem_ker_zero hP halgX halgY halgP hπ U V hU hV l hl b⟩ := by
  rw [classMap_apply, classMapZero_apply, ← ConcreteCategory.comp_apply,
    slantH, slantHomologyMap_homologyπ, ConcreteCategory.comp_apply]
  congr 1
  apply (ModuleCat.mono_iff_injective
    ((cochainComplex πY V (unitModule Y)).iCycles 0)).1 inferInstance
  have h := congrArg (fun f =>
    f (cyclesOfKer πP (prodCover p₁ p₂ U V) (unitModule P) 0 b))
    (slantCyclesMap_i _ _
      (slantCochainMap hP halgX halgY halgP hπ U V hU hV l)
      (slantCochainMap_anticomm hP halgX halgY halgP hπ U V hU hV l hl)
      (slantCochainMap_bottom hP halgX halgY halgP hπ U V hU hV l hl) 0)
  simp only [ConcreteCategory.comp_apply] at h ⊢
  refine h.trans ?_
  change slantCochainMap hP halgX halgY halgP hπ U V hU hV l 0
      ((cochainComplex πP (prodCover p₁ p₂ U V) (unitModule P)).iCycles 1
        (cyclesOfKer πP (prodCover p₁ p₂ U V) (unitModule P) 0 b)) =
    (cochainComplex πY V (unitModule Y)).iCycles 0
      (cyclesOfKerZero πY V (unitModule Y) _)
  rw [cyclesOfKer_i, cyclesOfKerZero_i]

variable [IsSeparated πY] [IsSeparated πP]
  (hVtop : ⨆ j, V j = ⊤) (hVa : ∀ j, IsAffineOpen (V j))
  (hUVtop : ⨆ j, prodCover p₁ p₂ U V j = ⊤)
  (hUVa : ∀ j, IsAffineOpen (prodCover p₁ p₂ U V j))

lemma slantCanonical_canonicalClass_bottom
    (b : LinearMap.ker (dCochain πP (prodCover p₁ p₂ U V) (unitModule P) 1)) :
    slantCanonical hP halgX halgY halgP hπ U V hU hV l hl hVtop hVa hUVtop hUVa 0
        (canonicalClass πP (prodCover p₁ p₂ U V) hUVtop hUVa 0 b) =
      canonicalClassZero πY V hVtop hVa
        ⟨slantCochainMap hP halgX halgY halgP hπ U V hU hV l 0 b.1,
          slantCochainMap_mem_ker_zero hP halgX halgY halgP hπ U V hU hV l hl b⟩ := by
  simp only [canonicalClass, canonicalClassZero, LinearMap.comp_apply,
    LinearEquiv.coe_coe, slantCanonical_apply, LinearEquiv.symm_apply_apply]
  rw [slantH_classMap_bottom]

end SlantBottom

end Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeq

namespace Langlands.Cohomology.Cech.KunnethDetection

open Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof
open Langlands.AlgebraicGeometry.Picard.FieldTwoAxisH1Injectivity

variable {R : CommRingCat.{u}} {X Y P : Scheme.{u}} {πX : X ⟶ Spec R} {πY : Y ⟶ Spec R}
  {p₁ : P ⟶ X} {p₂ : P ⟶ Y} (hP : IsPullback p₁ p₂ πX πY)
  [∀ W : X.Opens, Algebra R Γ(X, W)]
  (halgX : ∀ W : X.Opens, algebraMap R Γ(X, W) = (secHom πX W).hom)
  [∀ W : Y.Opens, Algebra R Γ(Y, W)]
  (halgY : ∀ W : Y.Opens, algebraMap R Γ(Y, W) = (secHom πY W).hom)
  {ι κ : Type u} [Finite ι] (U : ι → X.Opens) (V : κ → Y.Opens)
  (hU : ∀ σ : Fin 2 → ι, IsAffineOpen (inter U σ))
  (hV : ∀ (m : ℕ) (τ : Fin (m + 1) → κ), IsAffineOpen (inter V τ))
  (l : (∀ σ : Fin 2 → ι, Γ(X, inter U σ)) →ₗ[R] R)

/-- Bottom-degree slant of a first-axis one-cochain is its functional times one. -/
lemma L_bottom_pull_left (z : C (ab X.presheaf) U 1) :
    L hP halgX halgY U V hU hV l 0
      (pull p₁ U (prodCover p₁ p₂ U V) Prod.fst (fun _ => inf_le_left) 1 z) =
      fun b => l z • (1 : Γ(Y, inter V b)) := by
  funext b
  rw [L_apply]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, pow_zero, one_smul, add_zero]
  rw [ev]
  trans slant hP halgX halgY U hU l (inter V b) (hV 0 b) (fun σ =>
    (p₁.appLE (inter U σ) (prodOpen p₁ p₂ (inter U σ) (inter V b)) inf_le_left).hom (z σ) *
      (p₂.appLE (inter V b) (prodOpen p₁ p₂ (inter U σ) (inter V b)) inf_le_right).hom 1)
  · congr 1
    funext σ
    rw [map_one, mul_one]
    have hf : res (P := ab P.presheaf)
        (le_inter_prodCover U V σ b (step 1) (degen 0))
        (pull p₁ U (prodCover p₁ p₂ U V) Prod.fst (fun _ => inf_le_left) 1 z
          (fun j => (σ ((step 1) j), b ((degen 0) j)))) =
        (p₁.appLE (inter U σ) (prodOpen p₁ p₂ (inter U σ) (inter V b)) inf_le_left).hom
          (face z σ (step 1)) := by
      rw [pull_apply, res_appLE, face, appLE_res]
      rfl
    rw [hf]
    have hs : (step 1 : Fin 2 → Fin 2) = id := by
      funext j
      fin_cases j <;> rfl
    rw [hs, face_id]
  · exact slant_mul hP halgX halgY U hU l (inter V b) (hV 0 b) z 1

/-- Bottom-degree slant kills a second-axis one-cocycle. -/
lemma L_bottom_pull_right (y : C (ab Y.presheaf) V 1)
    (hy : d (ab Y.presheaf) V 1 y = 0) :
    L hP halgX halgY U V hU hV l 0
      (pull p₂ V (prodCover p₁ p₂ U V) Prod.snd (fun _ => inf_le_right) 1 y) = 0 := by
  funext b
  rw [L_apply]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, pow_zero, one_smul, add_zero]
  apply ev_pull_right_zero hP halgX halgY U V hU hV l
  have hd : (degen 0 : Fin 2 → Fin 1) = fun _ => 0 := by
    funext j
    fin_cases j <;> rfl
  rw [hd, face]
  change res _ (y (fun _ => b 0)) = 0
  rw [cocycle_apply_const hy, map_zero]

end Langlands.Cohomology.Cech.KunnethDetection

namespace Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeq

open Langlands.Cohomology Cech Cech.KunnethDetection DerivedSections
open Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof
open Langlands.AlgebraicGeometry.Picard.FieldTwoAxisH1Injectivity

variable {K : Type u} [Field K] {X Y P : Over (Spec (CommRingCat.of K))}
  (p₁ : P ⟶ X) (p₂ : P ⟶ Y)
  (hP : IsPullback p₁.left p₂.left X.hom Y.hom)
  [IsSeparated X.hom] [IsSeparated Y.hom] [IsSeparated P.hom]
  [∀ W : X.left.Opens, Algebra (CommRingCat.of K) Γ(X.left, W)]
  (halgX : ∀ W : X.left.Opens,
    algebraMap (CommRingCat.of K) Γ(X.left, W) = (secHom X.hom W).hom)
  [∀ W : Y.left.Opens, Algebra (CommRingCat.of K) Γ(Y.left, W)]
  (halgY : ∀ W : Y.left.Opens,
    algebraMap (CommRingCat.of K) Γ(Y.left, W) = (secHom Y.hom W).hom)
  [∀ W : P.left.Opens, Algebra (CommRingCat.of K) Γ(P.left, W)]
  (halgP : ∀ W : P.left.Opens,
    algebraMap (CommRingCat.of K) Γ(P.left, W) = (secHom P.hom W).hom)
  {ι κ : Type u} [Fintype ι] [Fintype κ] (U : ι → X.left.Opens) (V : κ → Y.left.Opens)
  (hUtop : ⨆ i, U i = ⊤) (hUa : ∀ i, IsAffineOpen (U i))
  (hU : ∀ σ : Fin 2 → ι, IsAffineOpen (inter U σ))
  (hV : ∀ (m : ℕ) (τ : Fin (m + 1) → κ), IsAffineOpen (inter V τ))
  (hVtop : ⨆ j, V j = ⊤) (hVa : ∀ j, IsAffineOpen (V j))
  (hUVtop : ⨆ j, prodCover p₁.left p₂.left U V j = ⊤)
  (hUVa : ∀ j, IsAffineOpen (prodCover p₁.left p₂.left U V j))

/-- Bottom slant of a first-axis H1 class evaluates the dual times the actual unit. -/
lemma slantByH1Dual_bottom_pull_left
    (ell : (relativeCohomology X.hom 1).obj (unitModule X.left) →ₗ[K] K)
    (x : (relativeCohomology X.hom 1).obj (unitModule X.left)) :
    slantByH1Dual hP halgX halgY halgP p₁.w U V hUtop hUa hU hV hVtop hVa hUVtop hUVa ell 0
      (unitCohomologyPullbackLinear p₁ 1 x) = ell x • unitCanonical Y.hom V hVtop hVa := by
  obtain ⟨z, rfl⟩ := canonicalClass_surjective X.hom U hUtop hUa 0 x
  dsimp only [unitCohomologyPullbackLinear]
  rw [pull_canonicalClass p₁ U (prodCover p₁.left p₂.left U V) Prod.fst
      (fun _ => inf_le_left) hUtop hUVtop hUa hUVa]
  unfold slantByH1Dual
  rw [slantCanonical_canonicalClass_bottom]
  change canonicalClassZero Y.hom V hVtop hVa _ =
    ell (canonicalClass X.hom U hUtop hUa 0 z) •
      canonicalClassZero Y.hom V hVtop hVa (oneZeroCocycle Y.hom V)
  rw [← map_smul]
  apply congrArg (canonicalClassZero Y.hom V hVtop hVa)
  apply Subtype.ext
  apply (cochainSecEquiv Y.hom V halgY 0).injective
  simp only [Submodule.coe_smul]
  rw [map_smul]
  change L hP halgX halgY U V hU hV
      (h1DualCochainFunctional X.hom U hUtop hUa halgX ell) 0
      ((unitCochainMap p₁ U (prodCover p₁.left p₂.left U V) Prod.fst
        (fun _ => inf_le_left)).f 1 z.1) = _
  rw [unitCochainMap_eq_pull, L_bottom_pull_left]
  have hdual := h1DualCochainFunctional_cocycle X.hom U hUtop hUa halgX ell z
  change h1DualCochainFunctional X.hom U hUtop hUa halgX ell
    (z.1 : C (ab X.left.presheaf) U 1) = _ at hdual
  rw [hdual]
  funext b
  rfl

/-- Bottom slant of a second-axis H1 class vanishes. -/
lemma slantByH1Dual_bottom_pull_right
    (ell : (relativeCohomology X.hom 1).obj (unitModule X.left) →ₗ[K] K)
    (y : (relativeCohomology Y.hom 1).obj (unitModule Y.left)) :
    slantByH1Dual hP halgX halgY halgP p₁.w U V hUtop hUa hU hV hVtop hVa hUVtop hUVa ell 0
      (unitCohomologyPullbackLinear p₂ 1 y) = 0 := by
  obtain ⟨z, rfl⟩ := canonicalClass_surjective Y.hom V hVtop hVa 0 y
  dsimp only [unitCohomologyPullbackLinear]
  rw [pull_canonicalClass p₂ V (prodCover p₁.left p₂.left U V) Prod.snd
      (fun _ => inf_le_right) hVtop hUVtop hVa hUVa]
  unfold slantByH1Dual
  rw [slantCanonical_canonicalClass_bottom]
  have hzero : slantCochainMap hP halgX halgY halgP p₁.w U V hU hV
      (h1DualCochainFunctional X.hom U hUtop hUa halgX ell) 0
      ((unitCochainMap p₂ V (prodCover p₁.left p₂.left U V) Prod.snd
        (fun _ => inf_le_right)).f 1 z.1) = 0 := by
    apply (cochainSecEquiv Y.hom V halgY 0).injective
    rw [map_zero]
    change L hP halgX halgY U V hU hV
      (h1DualCochainFunctional X.hom U hUtop hUa halgX ell) 0
      ((unitCochainMap p₂ V (prodCover p₁.left p₂.left U V) Prod.snd
        (fun _ => inf_le_right)).f 1 z.1) = 0
    rw [unitCochainMap_eq_pull]
    apply L_bottom_pull_right
    rw [← dCochain_unit Y.hom V 1 z.1]
    exact z.2
  rw [show (⟨_, _⟩ : LinearMap.ker (dCochain Y.hom V (unitModule Y.left) 0)) = 0 from
    Subtype.ext hzero, map_zero]

end Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeq
