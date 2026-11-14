import Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeqCup
import Langlands.AlgebraicGeometry.CechCreationClass
import Mathlib.Algebra.Homology.ShortComplex.Linear

/-! # All-degree creation on actual structure-sheaf cohomology -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeq

open Langlands.Cohomology

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (π : X ⟶ Spec R)
  {ι : Type u} [Fintype ι] (U : ι → X.Opens)

/-- Cup creation as a morphism between the scalar-linear cochain objects. -/
def creationCochainMap (z : cochain π U (unitModule X) 1) (n : ℕ) :
    (cochainComplex π U (unitModule X)).X n ⟶
      (cochainComplex π U (unitModule X)).X (n + 1) :=
  ModuleCat.ofHom (cupL π U n z)

lemma creationCochainMap_anticomm
    (z : LinearMap.ker (dCochain π U (unitModule X) 1)) (n : ℕ) :
    (cochainComplex π U (unitModule X)).d n (n + 1) ≫ creationCochainMap π U z (n + 1) =
      -(creationCochainMap π U z n ≫
        (cochainComplex π U (unitModule X)).d (n + 1) (n + 2)) := by
  change (cochainComplex π U (unitModule X)).d n (n + 1) ≫ creationCochainMap π U z (n + 1) =
    -(creationCochainMap π U z n ≫
      (cochainComplex π U (unitModule X)).d (n + 1) ((n + 1) + 1))
  rw [cochainComplex_d, cochainComplex_d]
  ext b
  change cup π U z (dCochain π U (unitModule X) n b) =
    -dCochain π U (unitModule X) (n + 1) (cup π U z b)
  rw [dCochain_cup π U z.2, neg_neg]

/-- A one-cocycle creates scalar-linear maps on ordered Cech homology in every degree. -/
def creationByCocycle (z : LinearMap.ker (dCochain π U (unitModule X) 1)) (n : ℕ) :
    (cochainComplex π U (unitModule X)).homology n ⟶
      (cochainComplex π U (unitModule X)).homology (n + 1) :=
  Cech.creationHomologyMap _ _ (creationCochainMap π U z)
    (creationCochainMap_anticomm π U z) n

lemma creationByCocycle_π_ι (z : LinearMap.ker (dCochain π U (unitModule X) 1)) (n : ℕ) :
    (cochainComplex π U (unitModule X)).homologyπ n ≫ creationByCocycle π U z n ≫
        (cochainComplex π U (unitModule X)).homologyι (n + 1) =
      (cochainComplex π U (unitModule X)).iCycles n ≫ creationCochainMap π U z n ≫
        (cochainComplex π U (unitModule X)).pOpcycles (n + 1) := by
  change ((cochainComplex π U (unitModule X)).sc n).homologyπ ≫
      ShortComplex.homologyMap (Cech.creationShortComplexMap _ _
        (creationCochainMap π U z) (creationCochainMap_anticomm π U z) n) ≫
      ((cochainComplex π U (unitModule X)).sc (n + 1)).homologyι = _
  rw [ShortComplex.π_homologyMap_ι, Cech.creationShortComplexMap_τ₂]
  rfl

/-- Cup creation is linear in its creating one-cocycle, on homology. -/
def creationByCocycleL (n : ℕ) :
    LinearMap.ker (dCochain π U (unitModule X) 1) →ₗ[R]
      ((cochainComplex π U (unitModule X)).homology n →ₗ[R]
        (cochainComplex π U (unitModule X)).homology (n + 1)) where
  toFun z := (creationByCocycle π U z n).hom
  map_add' z w := by
    have h : creationByCocycle π U (z + w) n =
        creationByCocycle π U z n + creationByCocycle π U w n := by
      apply (cancel_epi ((cochainComplex π U (unitModule X)).homologyπ n)).mp
      apply (cancel_mono ((cochainComplex π U (unitModule X)).homologyι (n + 1))).mp
      simp only [Preadditive.comp_add, Preadditive.add_comp, Category.assoc,
        creationByCocycle_π_ι]
      have hc : creationCochainMap π U (z + w) n =
          creationCochainMap π U z n + creationCochainMap π U w n := by
        ext b
        exact cup_add_left π U z w b
      simp only [Submodule.coe_add, hc, Preadditive.comp_add, Preadditive.add_comp]
    exact congrArg ModuleCat.Hom.hom h
  map_smul' r z := by
    have h : creationByCocycle π U (r • z) n = r • creationByCocycle π U z n := by
      apply (cancel_epi ((cochainComplex π U (unitModule X)).homologyπ n)).mp
      apply (cancel_mono ((cochainComplex π U (unitModule X)).homologyι (n + 1))).mp
      simp only [Linear.comp_smul, Linear.smul_comp, Category.assoc, creationByCocycle_π_ι]
      have hc : creationCochainMap π U (r • z) n = r • creationCochainMap π U z n := by
        ext b
        exact cup_smul_left π U r z b
      simp only [Submodule.coe_smul, hc, Linear.comp_smul, Linear.smul_comp]
    exact congrArg ModuleCat.Hom.hom h

/-- Multiplication by a zero-cochain, with the actual structure-morphism scalars. -/
def cupZeroCochainMap (h : cochain π U (unitModule X) 0) (n : ℕ) :
    (cochainComplex π U (unitModule X)).X n ⟶
      (cochainComplex π U (unitModule X)).X n :=
  ModuleCat.ofHom
    { toFun := Cech.cup₀ X.presheaf U h
      map_add' := fun b b' => by
        funext τ
        simp only [Cech.cup₀_apply, Pi.add_apply, mul_add]
      map_smul' := fun r b => by
        funext τ
        change Cech.face (P := Cech.ab X.presheaf) (U := U)
            (h : Cech.C (Cech.ab X.presheaf) U 0) τ (fun _ => 0) *
            (algC π (Cech.inter U τ) r *
              (show (Cech.ab X.presheaf).obj (op (Cech.inter U τ)) from b τ)) =
          algC π (Cech.inter U τ) r *
            (Cech.face (P := Cech.ab X.presheaf) (U := U)
                (h : Cech.C (Cech.ab X.presheaf) U 0) τ (fun _ => 0) *
              (show (Cech.ab X.presheaf).obj (op (Cech.inter U τ)) from b τ))
        exact mul_left_comm _ _ _ }

/-- The scalar-linear creation map is unchanged by a coboundary in its creator. -/
lemma creationByCocycle_eq_of_sub_eq_d
    (z z' : LinearMap.ker (dCochain π U (unitModule X) 1))
    (h : cochain π U (unitModule X) 0)
    (hh : (z : cochain π U (unitModule X) 1) - z' = dCochain π U (unitModule X) 0 h)
    (n : ℕ) :
    creationByCocycle π U z n = creationByCocycle π U z' n := by
  apply Cech.creationHomologyMap_eq_of_homotopy
    (h := cupZeroCochainMap π U h)
  intro m
  change creationCochainMap π U z m =
    cupZeroCochainMap π U h m ≫ (cochainComplex π U (unitModule X)).d m (m + 1) -
      (cochainComplex π U (unitModule X)).d m (m + 1) ≫ cupZeroCochainMap π U h (m + 1) +
        creationCochainMap π U z' m
  rw [cochainComplex_d]
  ext b
  change cup π U (z : cochain π U (unitModule X) 1) b =
    dCochain π U (unitModule X) m
        (show cochain π U (unitModule X) m from Cech.cup₀ X.presheaf U h b) -
      (show cochain π U (unitModule X) (m + 1) from
        Cech.cup₀ X.presheaf U h (dCochain π U (unitModule X) m b)) +
      cup π U (z' : cochain π U (unitModule X) 1) b
  have hh' : (show Cech.C (Cech.ab X.presheaf) U 1 from
      (z : cochain π U (unitModule X) 1)) -
      (show Cech.C (Cech.ab X.presheaf) U 1 from
        (z' : cochain π U (unitModule X) 1)) =
      Cech.d (Cech.ab X.presheaf) U 0 h := by
    rw [← dCochain_unit]; exact hh
  have he : Cech.cup₁ X.presheaf U (z : cochain π U (unitModule X) 1) b =
      Cech.d (Cech.ab X.presheaf) U m (Cech.cup₀ X.presheaf U h b) -
        Cech.cup₀ X.presheaf U h (Cech.d (Cech.ab X.presheaf) U m b) +
        Cech.cup₁ X.presheaf U (z' : cochain π U (unitModule X) 1) b := by
    rw [Cech.d_cup₀, add_sub_cancel_right, ← Cech.cup₁_add_left, ← hh', sub_add_cancel]
  rw [← dCochain_unit π U m b, ← dCochain_unit π U m
    (show cochain π U (unitModule X) m from Cech.cup₀ X.presheaf U h b)] at he
  exact he

lemma creationByCocycleL_eq_zero
    (z : LinearMap.ker (dCochain π U (unitModule X) 1))
    (hz : classMap π U (unitModule X) 0 z = 0) (n : ℕ) :
    creationByCocycleL π U n z = 0 := by
  obtain ⟨h, hh⟩ := (classMap_eq_zero_iff π U _ 0 z).1 hz
  have he := creationByCocycle_eq_of_sub_eq_d π U z 0 h (by simpa using hh.symm) n
  calc
    creationByCocycleL π U n z = creationByCocycleL π U n 0 :=
      congrArg ModuleCat.Hom.hom he
    _ = 0 := map_zero _

/-- Creation by an ordered Čech cohomology class, in every degree. -/
def creationH (n : ℕ) :
    (cochainComplex π U (unitModule X)).homology 1 →ₗ[R]
      ((cochainComplex π U (unitModule X)).homology n →ₗ[R]
        (cochainComplex π U (unitModule X)).homology (n + 1)) :=
  let e := (classMap π U (unitModule X) 0).quotKerEquivOfSurjective
    (classMap_surjective π U (unitModule X) 0)
  ((LinearMap.ker (classMap π U (unitModule X) 0)).liftQ
    (creationByCocycleL π U n) (fun z hz => creationByCocycleL_eq_zero π U z hz n)).comp
      e.symm.toLinearMap

lemma creationH_classMap (z : LinearMap.ker (dCochain π U (unitModule X) 1)) (n : ℕ) :
    creationH π U n (classMap π U (unitModule X) 0 z) = (creationByCocycle π U z n).hom := by
  simp only [creationH, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.quotKerEquivOfSurjective_symm_apply]
  rfl

omit [Fintype ι] in
lemma creation_cup_mem_ker
    (z : LinearMap.ker (dCochain π U (unitModule X) 1)) (n : ℕ)
    (b : LinearMap.ker (dCochain π U (unitModule X) (n + 1))) :
    cup π U z b ∈ LinearMap.ker (dCochain π U (unitModule X) (n + 2)) := by
  rw [LinearMap.mem_ker]
  change dCochain π U (unitModule X) ((n + 1) + 1) (cup π U z b) = 0
  rw [dCochain_cup π U z.2, b.2]
  exact neg_eq_zero.mpr (Cech.cup₁_zero_right (R := X.presheaf) (U := U) _)

/-- Creation sends the class of a cocycle to the class of its cup product. -/
lemma creationByCocycle_classMap
    (z : LinearMap.ker (dCochain π U (unitModule X) 1)) (n : ℕ)
    (b : LinearMap.ker (dCochain π U (unitModule X) (n + 1))) :
    creationByCocycle π U z (n + 1) (classMap π U (unitModule X) n b) =
      classMap π U (unitModule X) (n + 1)
        ⟨cup π U z b, creation_cup_mem_ker π U z n b⟩ := by
  rw [classMap_apply, classMap_apply, ← ConcreteCategory.comp_apply,
    creationByCocycle, Cech.creationHomologyMap_homologyπ, ConcreteCategory.comp_apply]
  congr 1
  apply (ModuleCat.mono_iff_injective
    ((cochainComplex π U (unitModule X)).iCycles ((n + 1) + 1))).1 inferInstance
  have h := congrArg (fun f => f (cyclesOfKer π U (unitModule X) n b))
    (Cech.creationCyclesMap_i _ _ (creationCochainMap π U z)
      (creationCochainMap_anticomm π U z) (n + 1))
  simp only [ConcreteCategory.comp_apply] at h ⊢
  refine h.trans ?_
  change creationCochainMap π U z (n + 1)
      ((cochainComplex π U (unitModule X)).iCycles (n + 1)
        (cyclesOfKer π U (unitModule X) n b)) =
    (cochainComplex π U (unitModule X)).iCycles ((n + 1) + 1)
      (cyclesOfKer π U (unitModule X) (n + 1)
        ⟨cup π U z b, creation_cup_mem_ker π U z n b⟩)
  rw [cyclesOfKer_i, cyclesOfKer_i]
  rfl

lemma creationH_classMap_classMap
    (z : LinearMap.ker (dCochain π U (unitModule X) 1)) (n : ℕ)
    (b : LinearMap.ker (dCochain π U (unitModule X) (n + 1))) :
    creationH π U (n + 1) (classMap π U (unitModule X) 0 z)
        (classMap π U (unitModule X) n b) =
      classMap π U (unitModule X) (n + 1)
        ⟨cup π U z b, creation_cup_mem_ker π U z n b⟩ := by
  rw [creationH_classMap]
  exact creationByCocycle_classMap π U z n b

/-- In degree one, creation agrees with the previously defined cup product. -/
lemma creationH_one : creationH π U 1 = cupH π U := by
  ext x y
  obtain ⟨z, rfl⟩ := classMap_surjective π U (unitModule X) 0 x
  obtain ⟨w, rfl⟩ := classMap_surjective π U (unitModule X) 0 y
  rw [creationH_classMap_classMap, cupH_classMap]
  rfl

section Canonical

open DerivedSections

variable [IsSeparated π] (hU : ⨆ i, U i = ⊤) (hUa : ∀ i, IsAffineOpen (U i))

/-- Creation by an actual structure-sheaf `H¹` class on actual cohomology. -/
def creationCanonical (n : ℕ) :
    (relativeCohomology π 1).obj (unitModule X) →ₗ[R]
      (relativeCohomology π n).obj (unitModule X) →ₗ[R]
        (relativeCohomology π (n + 1)).obj (unitModule X) :=
  ((creationH π U n).compl₁₂ (cohomologyEquiv π U hU hUa 1).symm.toLinearMap
    (cohomologyEquiv π U hU hUa n).symm.toLinearMap).compr₂
      (cohomologyEquiv π U hU hUa (n + 1)).toLinearMap

lemma creationCanonical_apply (n : ℕ)
    (x : (relativeCohomology π 1).obj (unitModule X))
    (y : (relativeCohomology π n).obj (unitModule X)) :
    creationCanonical π U hU hUa n x y =
      cohomologyEquiv π U hU hUa (n + 1)
        (creationH π U n ((cohomologyEquiv π U hU hUa 1).symm x)
          ((cohomologyEquiv π U hU hUa n).symm y)) := rfl

/-- The canonical creation operator is computed by cup product on cocycles. -/
lemma creationCanonical_canonicalClass
    (z : LinearMap.ker (dCochain π U (unitModule X) 1)) (n : ℕ)
    (b : LinearMap.ker (dCochain π U (unitModule X) (n + 1))) :
    creationCanonical π U hU hUa (n + 1)
        (canonicalClass π U hU hUa 0 z) (canonicalClass π U hU hUa n b) =
      canonicalClass π U hU hUa (n + 1)
        ⟨cup π U z b, creation_cup_mem_ker π U z n b⟩ := by
  simp only [canonicalClass, LinearMap.comp_apply, LinearEquiv.coe_coe,
    creationCanonical_apply, LinearEquiv.symm_apply_apply]
  rw [creationH_classMap_classMap]

lemma creationCanonical_one :
    creationCanonical π U hU hUa 1 = cupCanonical π U hU hUa := by
  unfold creationCanonical cupCanonical
  rw [creationH_one]

end Canonical

end Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeq
