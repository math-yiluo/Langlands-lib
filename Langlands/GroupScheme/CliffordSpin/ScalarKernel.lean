import Langlands.GroupScheme.CliffordSpin.GeometricPoints
import Langlands.GroupScheme.CorepresentedAffineComparison
import Langlands.GroupScheme.Multiplicative
import Langlands.GroupScheme.CentralIsogeny.Basic

/-! # The full scalar kernel of the Clifford lift projection -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry Matrix
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.CliffordSpin

open CliffordAlgebra Quaternionic Langlands.QuadraticForm
open Langlands.LinearAlgebra.OrthogonalCocycleDescent

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 900000
set_option synthInstance.maxHeartbeats 100000

variable {F : Type u} [Field F] [Invertible (2 : F)] {n : ℕ}
  (Q : QuadraticForm F (Fin n → F))

local notation "Rbase" => CommRingCat.of F
local notation "b" => Pi.basisFun F (Fin n)

/-- Scalar square roots of unity in the tensor-unit and matrix coordinates. -/
def scalarPair (A : Type u) [CommRing A] [Algebra F A] :
    rootsOfUnity 2 A →* coefficientSubgroup Q b A :=
  (coefficientLiftEquiv Q A).symm.toMonoidHom.comp (CliffordSpinLift.scalar (Q.baseChange A))

@[simp] theorem scalarPair_val (A : Type u) [CommRing A] [Algebra F A] (t : rootsOfUnity 2 A) :
    (scalarPair Q A t).val = (Units.map (algebraMap A (A ⊗[F] CliffordAlgebra Q)) (t : Aˣ), 1) := by
  apply Prod.ext
  · apply Units.ext
    change toBaseChange A Q (algebraMap A (CliffordAlgebra (Q.baseChange A)) (t : Aˣ)) = _
    exact AlgHom.commutes _ _
  · exact map_one (matrixAction b A).symm

/-- Scalar pairs commute with every map of coefficient algebras. -/
theorem scalarPair_map {A A' : CommAlgCat.{u} Rbase} (f : A ⟶ A') (t : rootsOfUnity 2 A) :
    (ambientFunctor (n := n) Q).map f (scalarPair Q A t).val =
      (scalarPair Q A' (restrictRootsOfUnity f.hom.toRingHom 2 t)).val := by
  rw [scalarPair_val, scalarPair_val]
  apply Prod.ext
  · apply Units.ext
    change tensorMap Q f.hom (algebraMap A (A ⊗[F] CliffordAlgebra Q) (t.val : A)) =
      algebraMap A' (A' ⊗[F] CliffordAlgebra Q) (f.hom (t.val : A))
    simp [Algebra.TensorProduct.algebraMap_apply]
  · exact map_one (Matrix.GeneralLinearGroup.map f.hom.toRingHom)

/-- The scalar pair embedding is injective over every coefficient algebra. -/
theorem scalarPair_injective (A : Type u) [CommRing A] [Algebra F A] :
    Function.Injective (scalarPair Q A) := by
  intro t r h
  have ht := congrArg (fun x : coefficientSubgroup Q b A => (x.val.1 : A ⊗[F] CliffordAlgebra Q)) h
  simp only [scalarPair_val, Units.coe_map] at ht
  have hi : Function.Injective (algebraMap A (A ⊗[F] CliffordAlgebra Q)) :=
    Algebra.TensorProduct.includeLeft_injective (R := F) (S := F) (algebraMap F (CliffordAlgebra Q)).injective
  exact Subtype.ext (Units.ext (hi ht))

variable [CharZero F] [NeZero n]
  (q : (FirstKindInvolution.scalar F).QuadraticForms (Fin n))

local notation "τ" => FirstKindInvolution.scalar F
local notation "SO" => FirstKindInvolution.normOneIsometryGroup τ q
local notation "Qq" => Matrix.toQuadraticForm' (FirstKindInvolution.polar τ q)
local notation "P" => groupScheme Qq b
local notation "π" => projection q
local notation "μ₂" => CommGroupScheme.toGrp (mu (Spec Rbase) 2)

private abbrev sections (T : Over (Spec Rbase)) : CommAlgCat.{u} Rbase :=
  ((algΓ Rbase).obj T).unop

omit [NeZero n] in
/-- The equation for a trivial vector action characterizes the scalar pairs on all
commutative coefficient algebras. -/
theorem exists_scalarPair_eq (hq : (τ).IsNondegenerateQuadratic q)
    (A : Type u) [CommRing A] [Algebra F A] (x : coefficientSubgroup Qq b A) (hx : x.val.2 = 1) :
    ∃ t : rootsOfUnity 2 A, scalarPair Qq A t = x := by
  let qA := (Qq).baseChange A
  let : Invertible (2 : A) := (Invertible.map (algebraMap F A) 2).copy 2 (map_ofNat _ _).symm
  have hQ : (Qq).polarBilin.Nondegenerate := polar_nondegenerate_of_symmetric_unit
    (OrthogonalMatrix.scalar_polar_transpose q) hq
  have hs : (Qq).polarBilin.IsSymm := ⟨fun v w => QuadraticMap.polar_comm Qq v w⟩
  obtain ⟨c, hc⟩ := LinearMap.BilinForm.exists_orthogonal_basis hs
  have hu (i : Fin (Module.finrank F (Fin n → F))) : IsUnit (qA (c.baseChange A i)) := by
    have h := LinearMap.BilinForm.iIsOrtho.not_isOrtho_basis_self_of_nondegenerate
      (B := (Qq).polarBilin) (v := c) hc hQ i
    have h' : (Qq) (c i) ≠ 0 := by
      change QuadraticMap.polar Qq (c i) (c i) ≠ 0 at h
      rw [QuadraticMap.polar_self] at h
      exact fun hz => h (by rw [hz, smul_zero])
    have he : qA (c.baseChange A i) = algebraMap F A ((Qq) (c i)) := by
      simp [qA, QuadraticForm.baseChange_tmul, Algebra.smul_def]
    rw [he]
    exact (isUnit_iff_ne_zero.mpr h').map (algebraMap F A)
  have ho (i j : Fin (Module.finrank F (Fin n → F))) (hij : i ≠ j) :
      QuadraticMap.polar qA (c.baseChange A i) (c.baseChange A j) = 0 := by
    change qA.polarBilin (c.baseChange A i) (c.baseChange A j) = 0
    dsimp only [qA]
    rw [QuadraticForm.polarBilin_baseChange, Module.Basis.baseChange_apply,
      Module.Basis.baseChange_apply, LinearMap.BilinForm.baseChange_tmul]
    rw [show (Qq).polarBilin (c i) (c j) = 0 from hc hij, zero_smul]
  let y := coefficientLiftEquiv Qq A x
  have hy : CliffordSpinLift.vectorAction qA y = 1 := by
    rw [show CliffordSpinLift.vectorAction qA y = matrixAction b A x.val.2 from rfl, hx, map_one]
  obtain ⟨t, ht⟩ := CliffordSpinLift.exists_scalar_of_vectorAction_eq_one qA (c.baseChange A) hu ho y hy
  exact ⟨t, (coefficientLiftEquiv Qq A).injective (by
    change coefficientLiftEquiv Qq A ((coefficientLiftEquiv Qq A).symm (CliffordSpinLift.scalar qA t)) = y
    rw [MulEquiv.apply_symm_apply, ht])⟩

/-- Points on a relative test scheme are pairs over its relative global sections. -/
def pointsPairEquiv (T : Over (Spec Rbase)) : (T ⟶ (P).X) ≃* coefficientSubgroup Qq b (sections T) :=
  Corepresented.pointsEquiv (Corepresented.cutFunctor (isCutOutBy Qq b))
    (Corepresented.cutCorepresentableBy (isCutOutBy Qq b)) T

private abbrev pairCorep := Corepresented.cutCorepresentableBy (isCutOutBy Qq b)

omit [CharZero F] [NeZero n] in
private theorem pullback_affinePair (T : Over (Spec Rbase)) (z : coefficientSubgroup Qq b (sections T)) :
    (algΓAlgSpecAdjunction Rbase).unit.app T ≫ (affinePairEquiv Qq b (sections T)).symm z =
      (pointsPairEquiv q T).symm z := by
  let d := pairCorep q
  obtain ⟨f, rfl⟩ := d.homEquiv.surjective z
  have ha : (affinePairEquiv Qq b (sections T)).symm (d.homEquiv f) = (algSpec Rbase).map f.op := by
    apply (affinePairEquiv Qq b (sections T)).injective
    rw [MulEquiv.apply_symm_apply]
    exact (Corepresented.affinePointsEquiv_map _ d _ f).symm
  rw [ha]
  apply (pointsPairEquiv q T).injective
  rw [MulEquiv.apply_symm_apply]
  change Corepresented.pointsEquiv _ d T ((algΓAlgSpecAdjunction Rbase).homEquiv T _ f.op) = _
  rw [Corepresented.pointsEquiv_apply, Equiv.symm_apply_apply]
  rfl

omit [Invertible (2 : F)] [CharZero F] in
private theorem precomp_unit_injective (T Y : Over (Spec Rbase)) [IsAffine Y.left] :
    Function.Injective (fun x : (algSpec Rbase).obj ((algΓ Rbase).obj T) ⟶ Y =>
      (algΓAlgSpecAdjunction Rbase).unit.app T ≫ x) := by
  obtain ⟨A, ⟨e⟩⟩ : ∃ A : (CommAlgCat.{u} Rbase)ᵒᵖ, Nonempty ((algSpec Rbase).obj A ≅ Y) := by
    have h : (algSpec Rbase).essImage Y := essImage_algSpec.mpr inferInstance
    exact ⟨h.witness, ⟨h.getIso⟩⟩
  intro x y h
  change (algΓAlgSpecAdjunction Rbase).unit.app T ≫ x =
    (algΓAlgSpecAdjunction Rbase).unit.app T ≫ y at h
  apply (cancel_mono e.inv).mp
  let f := algSpec.fullyFaithful.preimage (x ≫ e.inv)
  let g := algSpec.fullyFaithful.preimage (y ≫ e.inv)
  have hf : (algSpec Rbase).map f = x ≫ e.inv := algSpec.fullyFaithful.map_preimage _
  have hg : (algSpec Rbase).map g = y ≫ e.inv := algSpec.fullyFaithful.map_preimage _
  rw [← hf, ← hg]
  congr 1
  apply ((algΓAlgSpecAdjunction Rbase).homEquiv T A).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, hf, hg, ← Category.assoc,
    ← Category.assoc, h]

local instance kernel_isAffine_scalarNormOne : IsAffine (SO).X.left := by
  let p := FirstKindInvolution.normOneIsometryAmbientι τ q
  let : IsClosedImmersion p.hom.hom.left := FirstKindInvolution.isClosedSubgroup_normOneIsometryAmbientι τ q
  exact isAffine_of_isAffineHom p.hom.hom.left

/-- On arbitrary tests the point is in the kernel precisely when its matrix entry is one. -/
theorem projection_eq_one_iff (T : Over (Spec Rbase)) (x : T ⟶ (P).X) :
    x ≫ (π).hom.hom = 1 ↔ (pointsPairEquiv q T x).val.2 = 1 := by
  let A := sections T
  let u := (algΓAlgSpecAdjunction Rbase).unit.app T
  let z := pointsPairEquiv q T x
  let y := (affinePairEquiv Qq b A).symm z
  have hy : u ≫ y = x := (pullback_affinePair q T z).trans ((pointsPairEquiv q T).symm_apply_apply x)
  have h₁ : x ≫ (π).hom.hom = 1 ↔ y ≫ (π).hom.hom = 1 := by
    rw [← hy, Category.assoc, ← MonObj.comp_one u]
    exact (precomp_unit_injective (F := F) T (SO).X).eq_iff
  rw [h₁, ← (actionMatrix_injective q A).eq_iff, actionMatrix_projection, map_one]
  exact Iff.of_eq (congrArg (fun p : coefficientSubgroup Qq b A => p.val.2 = 1)
    ((affinePairEquiv Qq b A).apply_symm_apply z))

private def scalarKernelPoints (T : Over (Spec Rbase)) :
    rootsOfUnity 2 (sections T) →* (T ⟶ (kernel (π)).X) :=
  let f := (pointsPairEquiv q T).symm.toMonoidHom.comp (scalarPair Qq (sections T))
  (kernelPointsEquiv (π) T).symm.toMonoidHom.comp
    (f.codRestrict _ (fun t => (projection_eq_one_iff q T (f t)).mpr (by
      change (pointsPairEquiv q T ((pointsPairEquiv q T).symm (scalarPair Qq (sections T) t))).val.2 = 1
      rw [MulEquiv.apply_symm_apply, scalarPair_val])))

/-- The comparison of kernel sections with scalar square roots of unity. -/
theorem pair_scalarKernelPoints (T : Over (Spec Rbase)) (t : rootsOfUnity 2 (sections T)) :
    pointsPairEquiv q T (scalarKernelPoints q T t ≫ (kernelι (π)).hom.hom) = scalarPair Qq (sections T) t := by
  have h := congrArg Subtype.val ((kernelPointsEquiv (π) T).apply_symm_apply
    ⟨(pointsPairEquiv q T).symm (scalarPair Qq (sections T) t),
      (projection_eq_one_iff q T _).mpr (by rw [MulEquiv.apply_symm_apply, scalarPair_val])⟩)
  change scalarKernelPoints q T t ≫ (kernelι (π)).hom.hom = _ at h
  rw [h, MulEquiv.apply_symm_apply]

private theorem scalarKernelPoints_bijective (hq : (τ).IsNondegenerateQuadratic q) (T : Over (Spec Rbase)) :
    Function.Bijective (scalarKernelPoints q T) := by
  constructor
  · intro a c h
    apply scalarPair_injective Qq (sections T)
    rw [← pair_scalarKernelPoints q T a, ← pair_scalarKernelPoints q T c, h]
  · intro x
    let y := x ≫ (kernelι (π)).hom.hom
    have hy : y ≫ (π).hom.hom = 1 := (kernelPointsEquiv (π) T x).property
    obtain ⟨t, ht⟩ := exists_scalarPair_eq q hq (sections T) (pointsPairEquiv q T y)
      ((projection_eq_one_iff q T y).mp hy)
    refine ⟨t, (cancel_mono (kernelι (π)).hom.hom).mp ((pointsPairEquiv q T).injective ?_)⟩
    exact (pair_scalarKernelPoints q T t).trans ht

private def pointsEquiv_mu_kernel (hq : (τ).IsNondegenerateQuadratic q) (T : Over (Spec Rbase)) :
    (T ⟶ (μ₂).X) ≃* (T ⟶ (kernel (π)).X) :=
  (mu.pointsEquiv (Spec Rbase) 2 T).trans
    (MulEquiv.ofBijective (scalarKernelPoints q T) (scalarKernelPoints_bijective q hq T))

private theorem pointsEquiv_mu_kernel_natural (hq : (τ).IsNondegenerateQuadratic q)
    {T T' : Over (Spec Rbase)} (f : T' ⟶ T) (x : T ⟶ (μ₂).X) :
    pointsEquiv_mu_kernel q hq T' (f ≫ x) = f ≫ pointsEquiv_mu_kernel q hq T x := by
  apply (cancel_mono (kernelι (π)).hom.hom).mp
  apply (pointsPairEquiv q T').injective
  rw [Category.assoc]
  change pointsPairEquiv q T' (scalarKernelPoints q T' (mu.pointsEquiv (Spec Rbase) 2 T' (f ≫ x)) ≫
      (kernelι (π)).hom.hom) = _
  rw [pair_scalarKernelPoints, mu.pointsEquiv_naturality]
  change _ = Corepresented.pointsEquiv _ (pairCorep q) T' (f ≫
    (scalarKernelPoints q T (mu.pointsEquiv (Spec Rbase) 2 T x) ≫ (kernelι (π)).hom.hom))
  rw [Corepresented.pointsEquiv_naturality]
  have h := pair_scalarKernelPoints q T (mu.pointsEquiv (Spec Rbase) 2 T x)
  change Corepresented.pointsEquiv _ (pairCorep q) T
      (scalarKernelPoints q T (mu.pointsEquiv (Spec Rbase) 2 T x) ≫ (kernelι (π)).hom.hom) = _ at h
  rw [h]
  apply Subtype.ext
  exact (scalarPair_map Qq ((algΓ Rbase).map f).unop (mu.pointsEquiv (Spec Rbase) 2 T x)).symm

/-- The full scheme-theoretic kernel of the Clifford projection is the actual `μ₂`. -/
def kernelIso (hq : (τ).IsNondegenerateQuadratic q) : kernel (π) ≅ μ₂ :=
  (isoOfPoints (pointsEquiv_mu_kernel q hq) (pointsEquiv_mu_kernel_natural q hq)).symm

/-- In the all-test pair coordinates the kernel comparison includes as scalar Clifford units. -/
theorem pair_kernelIso_inv (hq : (τ).IsNondegenerateQuadratic q) (T : Over (Spec Rbase))
    (x : T ⟶ (μ₂).X) :
    pointsPairEquiv q T ((x ≫ (kernelIso q hq).inv.hom.hom) ≫ (kernelι (π)).hom.hom) =
      scalarPair Qq (sections T) (mu.pointsEquiv (Spec Rbase) 2 T x) := by
  rw [kernelIso, Iso.symm_inv, comp_isoOfPoints_hom]
  exact pair_scalarKernelPoints q T _

/-- The kernel is included by the same scalar formula on affine coefficient tests. -/
theorem affinePair_kernelIso_inv (hq : (τ).IsNondegenerateQuadratic q) (A : CommAlgCat.{u} Rbase)
    (x : GroupScheme.affinePoints (μ₂) A) :
    affinePairEquiv Qq b A ((x ≫ (kernelIso q hq).inv.hom.hom) ≫ (kernelι (π)).hom.hom) =
      scalarPair Qq A (mu.affinePointsEquiv 2 ((algSpec Rbase).obj (op A)).hom x) := by
  let T := (algSpec Rbase).obj (op A)
  have h := Corepresented.map_affineSectionsIso_pointsEquiv _ (pairCorep q) A
    ((x ≫ (kernelIso q hq).inv.hom.hom) ≫ (kernelι (π)).hom.hom)
  change (Corepresented.cutFunctor (isCutOutBy Qq b)).map (Corepresented.affineSectionsIso A).hom
      (pointsPairEquiv q T ((x ≫ (kernelIso q hq).inv.hom.hom) ≫ (kernelι (π)).hom.hom)) = _ at h
  refine h.symm.trans ?_
  rw [pair_kernelIso_inv]
  apply Subtype.ext
  have he : restrictRootsOfUnity (Corepresented.affineSectionsIso A).hom.hom.toRingHom 2
      (mu.pointsEquiv (Spec Rbase) 2 T x) =
      mu.affinePointsEquiv 2 T.hom x := by
    apply Subtype.ext
    apply Units.ext
    rw [Corepresented.affineSectionsIso_hom_ringHom]
    rfl
  exact (scalarPair_map Qq (Corepresented.affineSectionsIso A).hom
    (mu.pointsEquiv (Spec Rbase) 2 T x)).trans (congrArg (fun t => (scalarPair Qq A t).val) he)

/-- The full scalar kernel is central on all relative test schemes. -/
theorem isCentral_kernel_projection (hq : (τ).IsNondegenerateQuadratic q) :
    IsCentral (kernelι (π)) := by
  rw [isCentral_kernelι_iff]
  intro T x hx
  apply mem_center.mpr
  intro T' f y
  have hx' : (f ≫ x) ≫ (π).hom.hom = 1 := by
    rw [Category.assoc, hx, MonObj.comp_one]
  obtain ⟨t, ht⟩ := exists_scalarPair_eq q hq (sections T') (pointsPairEquiv q T' (f ≫ x))
    ((projection_eq_one_iff q T' (f ≫ x)).mp hx')
  change (f ≫ x) * y = y * (f ≫ x)
  apply (pointsPairEquiv q T').injective
  rw [map_mul, map_mul, ← ht]
  apply Subtype.ext
  change (scalarPair Qq (sections T') t).val * (pointsPairEquiv q T' y).val =
    (pointsPairEquiv q T' y).val * (scalarPair Qq (sections T') t).val
  rw [scalarPair_val]
  apply Prod.ext
  · apply Units.ext
    exact Algebra.commutes _ _
  · simp

end Langlands.GroupScheme.CliffordSpin
