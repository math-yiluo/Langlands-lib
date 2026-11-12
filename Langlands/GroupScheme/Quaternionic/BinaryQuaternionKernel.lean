import Langlands.GroupScheme.Quaternionic.BinaryQuaternionGroupScheme
import Langlands.GroupScheme.Quaternionic.HyperbolicNormSquareTorus
import Langlands.GroupScheme.Torus.DiagonalizableDecomposition
import Mathlib.Data.ZMod.Basic

/-! # The actual diagonal μ₂ kernel of the binary quaternionic action -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct Matrix

namespace Langlands.GroupScheme.Quaternionic.BinaryKernel

/-- The finite character group of μ₂, in the ground-field universe. -/
abbrev TwoLattice : Type u := ULift.{u} (ZMod 2)

/-- Its distinguished generator, in multiplicative notation. -/
def twoGenerator : Multiplicative TwoLattice.{u} := Multiplicative.ofAdd ⟨1⟩

theorem twoGenerator_mul : twoGenerator.{u} * twoGenerator = 1 := by
  apply Multiplicative.toAdd.injective
  apply ULift.ext
  decide

section Characters

variable {R : Type v} [CommRing R]

/-- Evaluation of an actual character at the distinguished generator. -/
def characterUnit : (Multiplicative TwoLattice.{u} →* Rˣ) →* Rˣ where
  toFun χ := χ twoGenerator
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The evaluated unit satisfies the full square-root-of-one equation. -/
theorem characterUnit_mul (χ : Multiplicative TwoLattice.{u} →* Rˣ) :
    characterUnit χ * characterUnit χ = 1 := by
  change χ twoGenerator * χ twoGenerator = 1
  rw [← _root_.map_mul, twoGenerator_mul, _root_.map_one]

/-- The character defined by a unit whose square is one. -/
def characterOfUnit (t : Rˣ) (ht : t * t = 1) : Multiplicative TwoLattice.{u} →* Rˣ where
  toFun a := if a.toAdd.down = 0 then 1 else t
  map_one' := by simp
  map_mul' := by
    rintro ⟨a⟩ ⟨b⟩
    change (if a + b = 0 then 1 else t) =
      (if a = 0 then 1 else t) * (if b = 0 then 1 else t)
    fin_cases a <;> fin_cases b <;> norm_num [ht]
    intro hn
    exact False.elim (hn (by decide))

@[simp] theorem characterUnit_characterOfUnit (t : Rˣ) (ht : t * t = 1) :
    characterUnit (characterOfUnit t ht : Multiplicative TwoLattice.{u} →* Rˣ) = t := by
  simp [characterUnit, characterOfUnit, twoGenerator]

/-- A character of the two-element lattice is determined by its generator. -/
theorem characterUnit_injective :
    Function.Injective (characterUnit : (Multiplicative TwoLattice.{u} →* Rˣ) → Rˣ) := by
  intro χ ψ h
  apply MonoidHom.ext
  rintro ⟨a⟩
  fin_cases a
  · exact (map_one χ).trans (map_one ψ).symm
  · exact h

end Characters

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
  (σ : FirstKindInvolution K D)
  (hdim : Module.finrank K D = 4) (hsym : Module.finrank K σ.symmetricSubspace = 3)

/-- The actual finite diagonalizable group μ₂. -/
abbrev muTwo : GroupScheme (Spec (CommRingCat.of K)) :=
  (Diagonalizable.groupScheme (CommRingCat.of K) TwoLattice.{u}).toGrp

/-- A character supplies a scalar point of the actual reduced-norm-one group. -/
def scalarNormOne (R : Type u) [CommRing R] [Algebra K R] :
    (Multiplicative TwoLattice.{u} →* Rˣ) →* Langlands.CentralSimple.reducedNormOne K D R where
  toFun χ := ⟨Langlands.CentralSimple.normCoverScalarUnits K D R (characterUnit χ), by
    change Langlands.CentralSimple.reducedNormUnits K D R
      (Langlands.CentralSimple.normCoverScalarUnits K D R (characterUnit χ)) = 1
    rw [Langlands.CentralSimple.reducedNormUnits_normCoverScalarUnits K D R
      (FirstKindInvolution.reducedDegree_eq_two_of_finrank_four hdim), pow_two,
      characterUnit_mul]⟩
  map_one' := Subtype.ext (by simp)
  map_mul' _ _ := Subtype.ext (by simp)

/-- The actual diagonal embedding of μ₂ characters into the two coefficient-group factors. -/
def characterProduct (R : Type u) [CommRing R] [Algebra K R] :
    (Multiplicative TwoLattice.{u} →* Rˣ) →*
      Matrix.SpecialLinearGroup (Fin 2) R × Langlands.CentralSimple.reducedNormOne K D R :=
  (BinaryAction.diagonalSL.comp characterUnit).prod (scalarNormOne hdim R)

/-- The diagonal character product has no kernel of its own. -/
theorem characterProduct_injective (R : Type u) [CommRing R] [Algebra K R] :
    Function.Injective (characterProduct hdim R) := by
  intro χ ψ h
  apply characterUnit_injective
  apply Units.ext
  have he := congrArg (fun z : Matrix.SpecialLinearGroup (Fin 2) R ×
    Langlands.CentralSimple.reducedNormOne K D R => z.1 0 0) h
  simpa [characterProduct, BinaryAction.diagonalSL_val] using he

/-- Every diagonal μ₂ character point is in the full kernel of the product action. -/
theorem characterProduct_mem_kernel (R : Type u) [CommRing R] [Algebra K R]
    (χ : Multiplicative TwoLattice.{u} →* Rˣ) :
    BinaryAction.normOneAction σ hdim hsym R (characterProduct hdim R χ) = 1 := by
  rw [BinaryAction.normOneAction_kernel]
  have ht := characterUnit_mul χ
  have hi : (characterUnit χ)⁻¹ = characterUnit χ := (inv_eq_iff_mul_eq_one).mpr ht
  refine ⟨(characterUnit χ : R), ?_, ?_, rfl⟩
  · exact congrArg (fun t : Rˣ => (t : R)) ht
  · change (BinaryAction.diagonalSL (characterUnit χ) : Matrix (Fin 2) (Fin 2) R) = _
    rw [BinaryAction.diagonalSL_val, hi]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply]

/-- Every kernel point is the image of one actual μ₂ character, over its original ring. -/
theorem exists_characterProduct_of_mem_kernel (R : Type u) [CommRing R] [Algebra K R]
    (g : Matrix.SpecialLinearGroup (Fin 2) R)
    (b : Langlands.CentralSimple.reducedNormOne K D R)
    (h : BinaryAction.normOneAction σ hdim hsym R (g,b) = 1) :
    ∃ χ : Multiplicative TwoLattice.{u} →* Rˣ, characterProduct hdim R χ = (g,b) := by
  obtain ⟨r, hr, hg, hb⟩ := (BinaryAction.normOneAction_kernel σ hdim hsym R g b).mp h
  let t : Rˣ := ⟨r,r,hr,hr⟩
  have ht : t * t = 1 := Units.ext hr
  refine ⟨characterOfUnit t ht, ?_⟩
  apply Prod.ext
  · apply Matrix.SpecialLinearGroup.ext
    intro i j
    change (BinaryAction.diagonalSL (characterUnit (characterOfUnit t ht)) :
      Matrix (Fin 2) (Fin 2) R) i j = _
    rw [characterUnit_characterOfUnit, BinaryAction.diagonalSL_val, hg]
    fin_cases i <;> fin_cases j <;> simp [t, Matrix.scalar_apply]
  · apply Subtype.ext
    apply Units.ext
    change (Langlands.CentralSimple.normCoverScalarUnits K D R
      (characterUnit (characterOfUnit t ht)) : R ⊗[K] D) = (b.val : R ⊗[K] D)
    rw [characterUnit_characterOfUnit]
    exact hb.symm

/-- The point homomorphism from the actual finite diagonalizable μ₂ into the product. -/
def diagonalPoints (T : Over (Spec (CommRingCat.of K))) :
    (T ⟶ (muTwo (K := K)).X) →* (T ⟶ (BinaryScheme.groupScheme (K := K) (D := D)).X) :=
  (BinaryScheme.pointsEquiv T).symm.toMonoidHom.comp
    ((characterProduct hdim (BinaryScheme.coefficients T)).comp
      (Diagonalizable.characterPointsEquiv (CommRingCat.of K) TwoLattice.{u} T).toMonoidHom)

@[simp] theorem diagonalPoints_coordinates (T : Over (Spec (CommRingCat.of K)))
    (x : T ⟶ (muTwo (K := K)).X) :
    BinaryScheme.pointsEquiv T (diagonalPoints hdim T x) =
      characterProduct hdim (BinaryScheme.coefficients T)
        (Diagonalizable.characterPointsEquiv (CommRingCat.of K) TwoLattice.{u} T x) :=
  (BinaryScheme.pointsEquiv T).apply_symm_apply _

private theorem productPoints_fst_naturality
    {T T' : Over (Spec (CommRingCat.of K))} (a : T' ⟶ T)
    (x : T ⟶ (BinaryScheme.groupScheme (K := K) (D := D)).X) :
    (BinaryScheme.pointsEquiv T' (a ≫ x)).1 =
      Matrix.SpecialLinearGroup.map ((algΓ (CommRingCat.of K)).map a).unop.hom.toRingHom
        (BinaryScheme.pointsEquiv T x).1 := by
  change SpecialLinear.pointsEquiv (Fin 2) (CommRingCat.of K) T' ((a ≫ x) ≫ fst _ _) = _
  rw [Category.assoc, SpecialLinear.pointsEquiv_naturality]
  rfl

private theorem productPoints_snd_naturality
    {T T' : Over (Spec (CommRingCat.of K))} (a : T' ⟶ T)
    (x : T ⟶ (BinaryScheme.groupScheme (K := K) (D := D)).X) :
    (BinaryScheme.pointsEquiv T' (a ≫ x)).2.val =
      Units.map (Algebra.TensorProduct.map ((algΓ (CommRingCat.of K)).map a).unop.hom
        (AlgHom.id K D)).toMonoidHom (BinaryScheme.pointsEquiv T x).2.val := by
  change FiniteAlgebraUnits.pointsEquiv (Module.finBasis K D) T'
    (((a ≫ x) ≫ snd _ _) ≫ (CentralSimpleUnits.normOneι K D).hom.hom) = _
  rw [Category.assoc, Category.assoc, FiniteAlgebraUnits.pointsEquiv_naturality]
  rfl

/-- The diagonal character point construction is natural for every relative test map. -/
theorem diagonalPoints_naturality {T T' : Over (Spec (CommRingCat.of K))}
    (a : T' ⟶ T) (x : T ⟶ (muTwo (K := K)).X) :
    diagonalPoints hdim T' (a ≫ x) = a ≫ diagonalPoints hdim T x := by
  let f := ((algΓ (CommRingCat.of K)).map a).unop.hom
  let χ : Multiplicative TwoLattice.{u} →* (BinaryScheme.coefficients T)ˣ :=
    Diagonalizable.characterPointsEquiv (CommRingCat.of K) TwoLattice.{u} T x
  let χ' : Multiplicative TwoLattice.{u} →* (BinaryScheme.coefficients T')ˣ :=
    Diagonalizable.characterPointsEquiv (CommRingCat.of K) TwoLattice.{u} T' (a ≫ x)
  have ht : characterUnit χ' = Units.map f.toMonoidHom (characterUnit χ) :=
    Diagonalizable.characterPointsEquiv_naturality (CommRingCat.of K) TwoLattice.{u}
      a x twoGenerator.toAdd
  apply (BinaryScheme.pointsEquiv T').injective
  rw [diagonalPoints_coordinates]
  apply Prod.ext
  · rw [productPoints_fst_naturality, diagonalPoints_coordinates]
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    change (BinaryAction.diagonalSL (characterUnit χ') :
      Matrix (Fin 2) (Fin 2) (BinaryScheme.coefficients T')) i j =
        (Matrix.SpecialLinearGroup.map f.toRingHom
          (BinaryAction.diagonalSL (characterUnit χ)) :
            Matrix (Fin 2) (Fin 2) (BinaryScheme.coefficients T')) i j
    rw [ht]
    fin_cases i <;> fin_cases j <;> simp [BinaryAction.diagonalSL_val]
  · apply Subtype.ext
    rw [productPoints_snd_naturality, diagonalPoints_coordinates]
    apply Units.ext
    change (Langlands.CentralSimple.normCoverScalarUnits K D (BinaryScheme.coefficients T')
      (characterUnit χ') : BinaryScheme.coefficients T' ⊗[K] D) =
        Algebra.TensorProduct.map f (AlgHom.id K D)
          (Langlands.CentralSimple.normCoverScalarUnits K D (BinaryScheme.coefficients T)
            (characterUnit χ) : BinaryScheme.coefficients T ⊗[K] D)
    rw [ht]
    simp

/-- The actual diagonal morphism μ₂ → SL₂ × SL₁(D). -/
def diagonal : muTwo (K := K) ⟶ BinaryScheme.groupScheme (K := K) (D := D) :=
  homOfPoints (diagonalPoints hdim) (diagonalPoints_naturality hdim)

@[simp] theorem diagonal_points (T : Over (Spec (CommRingCat.of K)))
    (x : T ⟶ (muTwo (K := K)).X) :
    x ≫ (diagonal hdim).hom.hom = diagonalPoints hdim T x :=
  comp_homOfPoints _ _ T x

/-- The diagonal μ₂ morphism is a monomorphism on the actual relative schemes. -/
instance diagonal_mono : Mono (diagonal hdim).hom.hom where
  right_cancellation := by
    intro T x y h
    apply (Diagonalizable.characterPointsEquiv (CommRingCat.of K) TwoLattice.{u} T).injective
    apply characterProduct_injective hdim (BinaryScheme.coefficients T)
    have he := congrArg (BinaryScheme.pointsEquiv T) h
    simpa only [diagonal_points, diagonalPoints_coordinates] using he

/-- The diagonal μ₂ morphism represents the entire kernel functor on every test. -/
theorem diagonal_range : SubgroupFunctor.range (diagonal hdim) =
    SubgroupFunctor.range (kernelι (BinaryScheme.unitHom σ hdim hsym)) := by
  apply SubgroupFunctor.ext
  intro T
  ext z
  rw [SubgroupFunctor.mem_range, mem_range_kernelι_iff]
  constructor
  · rintro ⟨x, rfl⟩
    apply (BinaryScheme.matrixPointsEquiv T).injective
    rw [BinaryScheme.unitHom_points, _root_.map_one]
    change BinaryAction.normOneAction σ hdim hsym (BinaryScheme.coefficients T)
      (BinaryScheme.pointsEquiv T (x ≫ (diagonal hdim).hom.hom)) = 1
    rw [diagonal_points, diagonalPoints_coordinates]
    exact characterProduct_mem_kernel σ hdim hsym (BinaryScheme.coefficients T) _
  · intro hz
    have hm := congrArg (BinaryScheme.matrixPointsEquiv T) hz
    rw [BinaryScheme.unitHom_points, _root_.map_one] at hm
    obtain ⟨χ, hχ⟩ := exists_characterProduct_of_mem_kernel σ hdim hsym
      (BinaryScheme.coefficients T) (BinaryScheme.pointsEquiv T z).1
        (BinaryScheme.pointsEquiv T z).2 hm
    refine ⟨(Diagonalizable.characterPointsEquiv (CommRingCat.of K) TwoLattice.{u} T).symm χ, ?_⟩
    apply (BinaryScheme.pointsEquiv T).injective
    rw [diagonal_points, diagonalPoints_coordinates, MulEquiv.apply_symm_apply]
    exact hχ

/-- The actual finite diagonalizable μ₂ is isomorphic to the full product-action kernel. -/
def muTwoUnitKernelIso : muTwo (K := K) ≅ kernel (BinaryScheme.unitHom σ hdim hsym) :=
  (show (SubgroupFunctor.range (diagonal hdim)).IsRepresentedBy (diagonal hdim) from
    ⟨inferInstance, rfl⟩).isoOfIsRepresentedBy
      ⟨inferInstance, (diagonal_range σ hdim hsym).symm⟩

/-- The isomorphism preserves the original diagonal inclusion into the product. -/
@[reassoc] theorem muTwoUnitKernelIso_comp :
    (muTwoUnitKernelIso σ hdim hsym).hom ≫ kernelι (BinaryScheme.unitHom σ hdim hsym) =
      diagonal hdim :=
  SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp _ _

/-- The finite diagonalizable model makes the full kernel scheme finite over the field. -/
theorem unitKernel_isFinite : IsFinite (kernel (BinaryScheme.unitHom σ hdim hsym)).X.hom := by
  have : IsFinite (muTwo (K := K)).X.hom := by
    change IsFinite (Diagonalizable.groupScheme (CommRingCat.of K) TwoLattice.{u}).X.hom
    infer_instance
  let e := muTwoUnitKernelIso σ hdim hsym
  rw [← e.inv.hom.hom.w]
  infer_instance

variable [Infinite K]

/-- The same actual diagonal subgroup represents the isometry kernel. -/
theorem diagonal_range_isometry : SubgroupFunctor.range (diagonal hdim) =
    SubgroupFunctor.range (kernelι (BinaryScheme.isometryHom σ hdim hsym)) := by
  rw [diagonal_range σ hdim hsym]
  apply SubgroupFunctor.ext
  intro T
  ext z
  rw [mem_range_kernelι_iff, mem_range_kernelι_iff,
    BinaryScheme.unitHom_kernel, BinaryScheme.isometryHom_kernel]

/-- The actual hyperbolic isometry kernel is μ₂ as a group scheme, with its nilpotents. -/
def muTwoIsometryKernelIso : muTwo (K := K) ≅ kernel (BinaryScheme.isometryHom σ hdim hsym) :=
  (show (SubgroupFunctor.range (diagonal hdim)).IsRepresentedBy (diagonal hdim) from
    ⟨inferInstance, rfl⟩).isoOfIsRepresentedBy
      ⟨inferInstance, (diagonal_range_isometry σ hdim hsym).symm⟩

/-- This kernel isomorphism also preserves the original inclusion. -/
@[reassoc] theorem muTwoIsometryKernelIso_comp :
    (muTwoIsometryKernelIso σ hdim hsym).hom ≫ kernelι (BinaryScheme.isometryHom σ hdim hsym) =
      diagonal hdim :=
  SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp _ _

/-- The actual hyperbolic isometry morphism has a finite full kernel in every characteristic. -/
theorem isometryKernel_isFinite :
    IsFinite (kernel (BinaryScheme.isometryHom σ hdim hsym)).X.hom := by
  have : IsFinite (muTwo (K := K)).X.hom := by
    change IsFinite (Diagonalizable.groupScheme (CommRingCat.of K) TwoLattice.{u}).X.hom
    infer_instance
  let e := muTwoIsometryKernelIso σ hdim hsym
  rw [← e.inv.hom.hom.w]
  infer_instance

end Langlands.GroupScheme.Quaternionic.BinaryKernel
