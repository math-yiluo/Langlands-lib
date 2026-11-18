import Langlands.GroupScheme.Cohomology.FlatKernelCochains
import Langlands.GroupScheme.HomScheme.DefectReduction
import Langlands.GroupScheme.HomScheme.GenericReduction
import Langlands.GroupScheme.HomScheme.ReducedAffineLift
import Langlands.GroupScheme.Products

/-! # Reconstructing actual regular kernel corrections -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped TensorProduct CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.HomScheme

open Cohomology Lie.NonaffineKernel Langlands.AlgebraicGeometry.SmoothLifting

variable {R : CommRingCat.{u}} (H : GroupScheme (Spec R)) [IsAffineHom H.X.hom]
variable (G : GroupScheme (Spec R))

theorem genericPoint_eq_coordinateIso : genericPoint H = (Lie.coordinateIso H).hom := by
  change (algSpec R).map
    (CommAlgCat.ofHom (AlgHom.id R (Lie.coordinateAlgebra H))).op ≫ _ = _
  rw [show CommAlgCat.ofHom (AlgHom.id R (Lie.coordinateAlgebra H)) = 𝟙 _ from rfl,
    op_id, CategoryTheory.Functor.map_id, Category.id_comp]

/-- An actual point of the target over the affine source coordinate algebra
is exactly a regular map from that source to the target. -/
def schemeMapFromPoint (x : G.affinePoints (Lie.coordinateAlgebra H)) : H.X ⟶ G.X :=
  (Lie.coordinateIso H).inv ≫ x

theorem schemeMapFromPoint_generic (x : G.affinePoints (Lie.coordinateAlgebra H)) :
    genericPoint H ≫ schemeMapFromPoint H G x = x := by
  rw [genericPoint_eq_coordinateIso, schemeMapFromPoint, Iso.hom_inv_id_assoc]

theorem schemeMapFromPoint_value (x : G.affinePoints (Lie.coordinateAlgebra H))
    (A : CommAlgCat.{u} R) (h : H.affinePoints A) :
    h ≫ schemeMapFromPoint H G x = G.affinePointMap (pointSpecialization H h) x := by
  have he : H.affinePointMap (pointSpecialization H h) (Lie.coordinateIso H).hom = h := by
    rw [← genericPoint_eq_coordinateIso]
    exact genericPoint_specialize H h
  conv_lhs => rw [← he]
  simp only [schemeMapFromPoint, affinePointMap_apply, Category.assoc, Iso.hom_inv_id_assoc]

/-- Regard a point on the base coefficient algebra as a section over the
identity of the base scheme. -/
def basePointOfAffine (x : Lie.AffinePoints G R) : Over.mk (𝟙 (Spec R)) ⟶ G.X :=
  Over.homMk x.left (by
    have hx := x.w
    change x.left ≫ G.X.hom = Spec.map (𝟙 R) at hx
    change x.left ≫ G.X.hom = 𝟙 (Spec R)
    rw [Spec.map_id] at hx
    exact hx)

theorem constantPoint_basePointOfAffine (x : Lie.AffinePoints G R)
    (A : CommAlgCat.{u} R) :
    G.constantPoint (basePointOfAffine G x) ((algSpec R).obj (op A)) =
      Lie.affineMap G (Algebra.ofId R A) x := by
  apply Over.OverMorphism.ext
  rfl

theorem basePointOfAffine_reduction (I : Ideal R) (x : Lie.AffinePoints G R)
    (hx : reduction G I x = 1) :
    G.constantPoint (basePointOfAffine G x) (Over.mk (Spec.algebraMap R (R ⧸ I))) = 1 := by
  apply Over.OverMorphism.ext
  exact congrArg Over.Hom.left hx

/-- A regular defect correction identity for a flat affine source is detected
on flat affine tests, then holds on arbitrary test schemes. -/
theorem isDefectCorrection_of_flat [Flat H.X.hom] (s b : H.X ⟶ G.X)
    (hb : ∀ (A : CommAlgCat.{u} R) [Module.Flat R A] (h k : H.affinePoints A),
      ((h ≫ s) * (k ≫ s) * ((h * k) ≫ s)⁻¹) * ((h * k) ≫ b) =
        (h ≫ s) * (k ≫ b) * (h ≫ s)⁻¹ * (h ≫ b)) :
    IsDefectCorrection s b := by
  let HH : GroupScheme (Spec R) := H ⊗ H
  let : IsAffineHom HH.X.hom := by
    change IsAffineHom (pullback.fst H.X.hom H.X.hom ≫ H.X.hom)
    let : IsAffineHom (pullback.fst H.X.hom H.X.hom) :=
      MorphismProperty.pullback_fst _ _ (inferInstance : IsAffineHom H.X.hom)
    infer_instance
  let : Flat HH.X.hom := by
    change Flat (pullback.fst H.X.hom H.X.hom ≫ H.X.hom)
    infer_instance
  let L : H.X ⊗ H.X ⟶ G.X :=
    multiplicationDefect s * ((fst H.X H.X * snd H.X H.X) ≫ b)
  let K : H.X ⊗ H.X ⟶ G.X :=
    (fst H.X H.X ≫ s) * (snd H.X H.X ≫ b) *
      (fst H.X H.X ≫ s)⁻¹ * (fst H.X H.X ≫ b)
  have hLK : L = K := by
    apply (cancel_epi (Lie.coordinateIso HH).hom).mp
    let e := (Lie.coordinateIso HH).hom
    have he : lift (e ≫ fst H.X H.X) (e ≫ snd H.X H.X) = e :=
      lift_comp_fst_snd e
    have ht := hb (Lie.coordinateAlgebra HH) (e ≫ fst H.X H.X) (e ≫ snd H.X H.X)
    change e ≫ L = e ≫ K
    rw [← he]
    simpa only [L, K, multiplicationDefect, MonObj.comp_mul, GrpObj.comp_inv,
      ← Category.assoc, lift_fst, lift_snd] using ht
  intro T h k
  rw [multiplicationDefect_value]
  have he := congrArg (fun z => lift h k ≫ z) hLK
  simpa only [L, K, multiplicationDefect, MonObj.comp_mul, GrpObj.comp_inv,
    ← Category.assoc, lift_fst, lift_snd] using he

variable [Flat H.X.hom] (I : Ideal R) [Fact (SqZero I)] [Smooth G.X.hom]

/-- Reconstruct the regular kernel-valued correction from the generic
coefficient value of an actual natural one-cochain. -/
def cochainKernelMap (b : OneCochain (Additive (Lie.NonaffineKernel.kernel G I)) H) :
    H.X ⟶ G.X :=
  schemeMapFromPoint H G
    ((flatKernelEquiv G I (Lie.coordinateAlgebra H)).symm
      (b.value (Lie.coordinateAlgebra H) (genericPoint H))).toMul.val

theorem cochainKernelMap_flat
    (b : OneCochain (Additive (Lie.NonaffineKernel.kernel G I)) H)
    (A : CommAlgCat.{u} R) [Module.Flat R A] (h : H.affinePoints A) :
    h ≫ cochainKernelMap H G I b =
      ((flatKernelEquiv G I A).symm (b.value A h)).toMul.val := by
  rw [cochainKernelMap, schemeMapFromPoint_value]
  have he := flatComparison_symm_naturality G I (pointSpecialization H h)
    (b.value (Lie.coordinateAlgebra H) (genericPoint H))
  rw [b.naturality, genericPoint_specialize] at he
  exact congrArg (fun x : Additive (Lie.NonaffineKernel.kernel G (I.map (algebraMap R A))) =>
    x.toMul.val) he

/-- The reconstructed regular map becomes the identity after actual scheme
base change to the quotient ring. -/
theorem cochainKernelMap_baseChange
    (b : OneCochain (Additive (Lie.NonaffineKernel.kernel G I)) H) :
    (Over.pullback (Spec.algebraMap R (R ⧸ I))).map (cochainKernelMap H G I b) =
      (1 : (Over.pullback (Spec.algebraMap R (R ⧸ I))).obj H.X ⟶
        ((baseChange (Spec.algebraMap R (R ⧸ I))).obj G).X) := by
  apply baseChange_eq_one_of_generic_reduction I
  change reduction G (I.map (algebraMap R (Lie.coordinateAlgebra H)))
    (genericPoint H ≫ cochainKernelMap H G I b) = 1
  rw [cochainKernelMap, schemeMapFromPoint_generic]
  exact ((flatKernelEquiv G I (Lie.coordinateAlgebra H)).symm
    (b.value (Lie.coordinateAlgebra H) (genericPoint H))).toMul.property

variable (s : H.X ⟶ G.X)
variable (s₀ : ∀ A : CommAlgCat.{u} R,
  H.affinePoints A →* Lie.AffinePoints G (A ⧸ I.map (algebraMap R A)))
variable (hs : ∀ (A : CommAlgCat.{u} R) (h : H.affinePoints A),
  reduction G (I.map (algebraMap R A)) (h ≫ s) = s₀ A h)

/-- A regular additive defect primitive gives an actual regular kernel
correction on all test schemes. -/
theorem cochainKernelMap_isDefectCorrection
    (b : OneCochain (Additive (Lie.NonaffineKernel.kernel G I)) H)
    (hb : ∀ (A : CommAlgCat.{u} R) (h k : H.affinePoints A),
      (regularDefectCochain H G I s s₀ hs).value A h k + b.value A (h * k) =
        (regularKernelRepresentation H G I s s₀ hs).action A h (b.value A k) + b.value A h) :
    IsDefectCorrection s (cochainKernelMap H G I b) := by
  apply isDefectCorrection_of_flat H G
  intro A hA h k
  rw [cochainKernelMap_flat, cochainKernelMap_flat, cochainKernelMap_flat]
  have he := congrArg (flatKernelEquiv G I A).symm (hb A h k)
  simp only [map_add, regularDefectCochain_flat, regularKernelRepresentation_action,
    flatConjugationAction, MonoidHom.coe_mk, OneHom.coe_mk, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply] at he
  have hv := congrArg (fun x : Additive
    (Lie.NonaffineKernel.kernel G (I.map (algebraMap R A))) => x.toMul.val) he
  simpa only [toMul_add, Subgroup.coe_mul, liftDefectPoint, kernelDefect_val,
    kernelConjugationAut_val] using hv

/-- Low-degree vanishing turns any actual scheme-map lift into a
homomorphism lift, for a flat affine source and an arbitrary smooth target. -/
theorem exists_homLift_of_schemeLift
    (f₀ : (baseChange (Spec.algebraMap R (R ⧸ I))).obj H ⟶
      (baseChange (Spec.algebraMap R (R ⧸ I))).obj G)
    (s : H.X ⟶ G.X)
    (hs : (Over.pullback (Spec.algebraMap R (R ⧸ I))).map s = f₀.hom.hom)
    (hH : HasVanishingLowDegreeCohomology
      ((baseChange (Spec.algebraMap R (R ⧸ I))).obj H)) :
    ∃ f : H ⟶ G, (baseChange (Spec.algebraMap R (R ⧸ I))).map f = f₀ := by
  let s₀ := reducedAffineHom I f₀
  have hs₀ := fun A h => reducedAffineHom_of_lift I f₀ A s hs h
  obtain ⟨b, hb⟩ := regularDefectCochain_isCoboundary H G I s s₀ hs₀ hH
  have hcor := cochainKernelMap_isDefectCorrection H G I s s₀ hs₀ b hb
  exact ⟨correctedHom s (cochainKernelMap H G I b) hcor,
    correctedHom_baseChange_eq _ s (cochainKernelMap H G I b) hcor f₀ hs
      (cochainKernelMap_baseChange H G I b)⟩

/-- A regular difference primitive gives actual conjugacy by a base point
that is the identity over the quotient base. -/
theorem exists_kernelConjugator_of_cohomology
    (f f' : H ⟶ G)
    (hf : (baseChange (Spec.algebraMap R (R ⧸ I))).map f =
      (baseChange (Spec.algebraMap R (R ⧸ I))).map f')
    (hH : HasVanishingLowDegreeCohomology
      ((baseChange (Spec.algebraMap R (R ⧸ I))).obj H)) :
    ∃ g : Over.mk (𝟙 (Spec R)) ⟶ G.X,
      G.constantPoint g (Over.mk (Spec.algebraMap R (R ⧸ I))) = 1 ∧
        f' = f ≫ (G.innerIso g).hom := by
  let f₀ := (baseChange (Spec.algebraMap R (R ⧸ I))).map f
  have hf' : (Over.pullback (Spec.algebraMap R (R ⧸ I))).map f'.hom.hom = f₀.hom.hom :=
    congrArg (fun z => z.hom.hom) hf.symm
  have hp : ∀ (A : CommAlgCat.{u} R) (h : H.affinePoints A),
      reduction G (I.map (algebraMap R A)) (h ≫ f.hom.hom) =
        reduction G (I.map (algebraMap R A)) (h ≫ f'.hom.hom) := by
    intro A h
    rw [reducedAffineHom_of_lift I f₀ A f.hom.hom rfl h,
      reducedAffineHom_of_lift I f₀ A f'.hom.hom hf' h]
  obtain ⟨m, hm⟩ := regularDifferenceCochain_isCoboundary H G I f f' hp hH
  let g := basePointOfAffine G m.toMul.val⁻¹
  refine ⟨g, ?_, ?_⟩
  · apply basePointOfAffine_reduction
    rw [map_inv, m.toMul.property, inv_one]
  · have hprim (A : CommAlgCat.{u} R) [Module.Flat R A] (h : H.affinePoints A) :
        kernelDifference G (I.map (algebraMap R A))
          (H.affinePointsTarget f A) (H.affinePointsTarget f' A) (hp A) h =
        kernelConjugationAut G (I.map (algebraMap R A)) (H.affinePointsTarget f A h)
          (kernelBcMap G I A m) - kernelBcMap G I A m := by
      have he := congrArg (flatKernelEquiv G I A).symm (hm A h)
      simp only [map_sub, regularDifferenceCochain_flat, homKernelRepresentation_action,
        flatConjugationAction, MonoidHom.coe_mk, OneHom.coe_mk, LinearEquiv.trans_apply,
        LinearEquiv.symm_apply_apply, flatKernelEquiv_symm_tmul, one_smul] at he
      erw [H.affinePointsTarget_apply f A h]
      exact he
    let A := Lie.coordinateAlgebra H
    have hc := kernelDifference_conjugacy G (I.map (algebraMap R A))
      (H.affinePointsTarget f A) (H.affinePointsTarget f' A) (hp A)
      (kernelBcMap G I A m) (hprim A) (genericPoint H)
    have hg : G.constantPoint g ((algSpec R).obj (op A)) =
        (kernelBcMap G I A m).toMul.val⁻¹ := by
      rw [constantPoint_basePointOfAffine, map_inv]
      rfl
    apply Grp.hom_ext
    apply (cancel_epi (Lie.coordinateIso H).hom).mp
    rw [← genericPoint_eq_coordinateIso H]
    change genericPoint H ≫ f'.hom.hom =
      (genericPoint H ≫ f.hom.hom) ≫ (G.innerIso g).hom.hom.hom
    rw [comp_innerIso_hom, hg, inv_inv]
    erw [H.affinePointsTarget_apply f' A (genericPoint H),
      H.affinePointsTarget_apply f A (genericPoint H)] at hc
    exact hc

end Langlands.GroupScheme.HomScheme
