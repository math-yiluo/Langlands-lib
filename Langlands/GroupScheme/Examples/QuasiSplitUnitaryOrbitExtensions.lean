import Langlands.GroupScheme.Examples.QuasiSplitUnitaryDynamic
import Langlands.GroupScheme.Dynamic.GeneralLinearOrbit

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry Algebra
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.QuasiSplitUnitary

variable {F E : Type u} [Field F] [Field E] [Algebra F E]
  [IsQuadraticExtension F E]
attribute [local instance] Algebra.TensorProduct.rightAlgebra

section Matrix
variable (R : Type u) [CommRing R] [Algebra F R]
variable (c : E ≃ₐ[F] E) (m : ℤ)

/-- The two opposite hyperbolic weight lists have the same diagonal subgroup. -/
theorem blockLeviSubgroup_weights_neg_one (A : Type u) [CommRing A] :
    GeneralLinear.blockLeviSubgroup A (weights (-1)) =
      GeneralLinear.blockLeviSubgroup A (weights 1) := by
  apply Subgroup.ext
  intro g
  simp [GeneralLinear.mem_blockLeviSubgroup, Fin.forall_fin_two, weights]

omit [IsQuadraticExtension F E] in
/-- The polynomial weight scaling commutes with the hyperbolic adjoint. -/
theorem weightScale_adjoint (s : R) (M : Matrix (Fin 2) (Fin 2) (E ⊗[F] R)) :
    GeneralLinear.weightScale (weights m) (algebraMap R (E ⊗[F] R) s)
        (adjoint (scalarConjugation R c) M) =
      adjoint (scalarConjugation R c)
        (GeneralLinear.weightScale (weights m) (algebraMap R (E ⊗[F] R) s) M) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [GeneralLinear.weightScale_apply, adjoint, weights]

/-- A triangular unitary matrix remains unitary after polynomial weight scaling. -/
def unitaryWeightScale (s : R) (g : matrixPoints R c)
    (hg : g.val ∈ GeneralLinear.blockParabolicSubgroup (E ⊗[F] R) (weights m)) :
    matrixPoints R c :=
  ⟨GeneralLinear.weightScaleHom (weights m) (algebraMap R (E ⊗[F] R) s) ⟨g.val, hg⟩, by
    dsimp only [matrixPoints]
    rw [Langlands.Shimura.AlgebraInvolution.mem_unitary_iff]
    have hu := g.property
    dsimp only [matrixPoints] at hu
    rw [Langlands.Shimura.AlgebraInvolution.mem_unitary_iff] at hu
    change g.val.val * adjoint (scalarConjugation R c) g.val.val = 1 at hu
    have ha : (adjoint (scalarConjugation R c) g.val.val).BlockTriangular
        (OrderDual.toDual ∘ weights m) := by
      change (∀ i j, weights m i < weights m j → _ = 0) at hg ⊢
      simp only [Fin.forall_fin_two, weights, Matrix.cons_val_zero, Matrix.cons_val_one,
        lt_self_iff_false, false_implies, and_true, true_and] at hg ⊢
      simpa [adjoint, hg.1, hg.2] using And.intro
        (fun h => congrArg (scalarConjugation R c) (hg.1 h))
        (fun h => congrArg (scalarConjugation R c) (hg.2 h))
    change GeneralLinear.weightScale (weights m) (algebraMap R (E ⊗[F] R) s) g.val.val *
      adjoint (scalarConjugation R c)
        (GeneralLinear.weightScale (weights m) (algebraMap R (E ⊗[F] R) s) g.val.val) = 1
    rw [← weightScale_adjoint, ← GeneralLinear.weightScale_mul (weights m) _ hg ha,
      hu, GeneralLinear.weightScale_one]⟩

end Matrix

section Scheme
variable {κ : Type u} [Fintype κ]
  (b : Module.Basis κ F (Matrix (Fin 2) (Fin 2) E)) (c : E ≃ₐ[F] E) (m : ℤ)

local notation "S" => Spec (CommRingCat.of F)
local notation "𝔸¹" => AffineLine.scheme S

theorem matrixCoordinates_injective (T : Over S) :
    Function.Injective (matrixCoordinates b c T) := by
  intro g h he
  apply (pointsEquiv b c T).injective
  exact Subtype.ext he

@[simp] theorem matrixCoordinates_weightCocharacter (T : Over S)
    (t : T ⟶ (Gm S).X) :
    matrixCoordinates b c T (t ≫ (weightCocharacter b c m).hom.hom) =
      GeneralLinear.diagonalUnits _ (weights m)
        (Units.map (algebraMap ((algΓ (CommRingCat.of F)).obj T).unop
          (E ⊗[F] ((algΓ (CommRingCat.of F)).obj T).unop)).toMonoidHom
            (Gm.pointsEquiv S T t)) := by
  change (pointsEquiv b c T (t ≫ (weightCocharacter b c m).hom.hom)).val = _
  rw [pointsEquiv_weightCocharacter]
  rfl

/-- The explicit polynomial extension attached to a triangular unitary point. -/
def unitaryOrbitExtension {T : Over S} (g : T ⟶ (groupScheme b c).X)
    (hg : matrixCoordinates b c T g ∈ GeneralLinear.blockParabolicSubgroup _ (weights m)) :
    T ⊗ 𝔸¹ ⟶ (groupScheme b c).X :=
  (pointsEquiv b c _).symm
    (unitaryWeightScale ((algΓ (CommRingCat.of F)).obj (T ⊗ 𝔸¹)).unop c m
      (AffineLine.homEquiv _ (snd T 𝔸¹)) (pointsEquiv b c _ (fst T 𝔸¹ ≫ g)) (by
        change matrixCoordinates b c _ (fst T 𝔸¹ ≫ g) ∈ _
        rw [matrixCoordinates_naturality]
        exact GeneralLinear.map_mem_blockParabolicSubgroup _ _ hg))

theorem matrixCoordinates_unitaryOrbitExtension {T : Over S}
    (g : T ⟶ (groupScheme b c).X)
    (hg : matrixCoordinates b c T g ∈ GeneralLinear.blockParabolicSubgroup _ (weights m)) :
    (matrixCoordinates b c _ (unitaryOrbitExtension b c m g hg)).val =
      GeneralLinear.weightScale (weights m)
        (algebraMap ((algΓ (CommRingCat.of F)).obj (T ⊗ 𝔸¹)).unop _
          (AffineLine.homEquiv _ (snd T 𝔸¹)))
        (matrixCoordinates b c _ (fst T 𝔸¹ ≫ g)).val := by
  change ((pointsEquiv b c _ (unitaryOrbitExtension b c m g hg)).val).val = _
  rw [unitaryOrbitExtension, MulEquiv.apply_symm_apply]
  rfl

theorem isOrbitExtension_unitaryOrbitExtension {T : Over S}
    (g : T ⟶ (groupScheme b c).X)
    (hg : matrixCoordinates b c T g ∈ GeneralLinear.blockParabolicSubgroup _ (weights m)) :
    Dynamic.IsOrbitExtension (weightCocharacter b c m) g
      (unitaryOrbitExtension b c m g hg) := by
  have hs : (T ◁ AffineLine.unitInclusion S).left.appTop
      (AffineLine.homEquiv _ (snd T 𝔸¹)) =
        (Gm.pointsEquiv S _ (snd T (Gm S).X) : Γ(_, ⊤)) := by
    rw [← AffineLine.homEquiv_comp, whiskerLeft_snd, AffineLine.homEquiv_comp_unitInclusion]
  have hM : Matrix.GeneralLinearGroup.map
      (tensorCoefficientMap ((algΓ (CommRingCat.of F)).map
        (T ◁ AffineLine.unitInclusion S)).unop.hom).toRingHom
      (matrixCoordinates b c _ (fst T 𝔸¹ ≫ g)) =
        matrixCoordinates b c _ (fst T (Gm S).X ≫ g) := by
    rw [← matrixCoordinates_naturality, whiskerLeft_fst_assoc]
  have hP : matrixCoordinates b c _ (fst T (Gm S).X ≫ g) ∈
      GeneralLinear.blockParabolicSubgroup _ (weights m) := by
    rw [matrixCoordinates_naturality]
    exact GeneralLinear.map_mem_blockParabolicSubgroup _ _ hg
  apply matrixCoordinates_injective b c _
  rw [Dynamic.orbit, map_mul, map_mul, map_inv, matrixCoordinates_weightCocharacter]
  apply Units.ext
  rw [← GeneralLinear.weightScale_units (weights m) _ hP,
    matrixCoordinates_naturality, GeneralLinear.coe_map_GL,
    matrixCoordinates_unitaryOrbitExtension, GeneralLinear.map_weightScale]
  erw [tensorCoefficientMap_algebraMap]
  rw [← GeneralLinear.coe_map_GL, hM]
  erw [Units.coe_map]
  exact congrArg (fun s =>
    GeneralLinear.weightScale (weights m)
      (algebraMap ((algΓ (CommRingCat.of F)).obj (T ⊗ (Gm S).X)).unop
        (E ⊗[F] ((algΓ (CommRingCat.of F)).obj (T ⊗ (Gm S).X)).unop) s)
      (matrixCoordinates b c _ (fst T (Gm S).X ≫ g)).val) hs

theorem matrixCoordinates_evalZero_unitaryOrbitExtension {T : Over S}
    (g : T ⟶ (groupScheme b c).X)
    (hg : matrixCoordinates b c T g ∈ GeneralLinear.blockParabolicSubgroup _ (weights m)) :
    (matrixCoordinates b c T (Dynamic.evalZero (unitaryOrbitExtension b c m g hg))).val =
      GeneralLinear.blockDiagonalPart _ (weights m) (matrixCoordinates b c T g).val := by
  have hs : (lift (𝟙 T) (toUnit T ≫ AffineLine.zeroSection S)).left.appTop
      (AffineLine.homEquiv _ (snd T 𝔸¹)) = 0 := by
    rw [← AffineLine.homEquiv_comp, lift_snd, AffineLine.homEquiv_comp_zeroSection]
  have hM : ((matrixCoordinates b c _ (fst T 𝔸¹ ≫ g)).val).map
      (tensorCoefficientMap ((algΓ (CommRingCat.of F)).map
        (lift (𝟙 T) (toUnit T ≫ AffineLine.zeroSection S))).unop.hom).toRingHom =
        (matrixCoordinates b c T g).val := by
    rw [← GeneralLinear.coe_map_GL, ← matrixCoordinates_naturality,
      lift_fst_assoc, Category.id_comp]
  rw [Dynamic.evalZero, matrixCoordinates_naturality, GeneralLinear.coe_map_GL,
    matrixCoordinates_unitaryOrbitExtension, GeneralLinear.map_weightScale]
  erw [tensorCoefficientMap_algebraMap]
  rw [hM]
  change GeneralLinear.weightScale (weights m)
    (algebraMap ((algΓ (CommRingCat.of F)).obj T).unop _
    ((lift (𝟙 T) (toUnit T ≫ AffineLine.zeroSection S)).left.appTop
      (AffineLine.homEquiv _ (snd T 𝔸¹)))) _ = _
  rw [hs]
  erw [map_zero]
  exact GeneralLinear.weightScale_zero _ hg

/-- A triangular unitary point has a conjugation orbit extending across zero. -/
theorem mem_parabolic_of_blockParabolic {T : Over S} (g : T ⟶ (groupScheme b c).X)
    (hg : matrixCoordinates b c T g ∈ GeneralLinear.blockParabolicSubgroup _ (weights m)) :
    g ∈ (Dynamic.parabolic (weightCocharacter b c m)).carrier T :=
  ⟨unitaryOrbitExtension b c m g hg, isOrbitExtension_unitaryOrbitExtension b c m g hg⟩

/-- A unitriangular unitary point has identity as its conjugation limit. -/
theorem mem_unipotent_of_blockUnipotent {T : Over S} (g : T ⟶ (groupScheme b c).X)
    (hg : matrixCoordinates b c T g ∈ GeneralLinear.blockUnipotentSubgroup _ (weights m)) :
    g ∈ (Dynamic.unipotent (weightCocharacter b c m)).carrier T := by
  obtain ⟨hP, hD⟩ := (GeneralLinear.blockUnipotent_iff _ (weights m) _).1 hg
  have hP' : matrixCoordinates b c T g ∈
      GeneralLinear.blockParabolicSubgroup _ (weights m) := hP
  refine ⟨unitaryOrbitExtension b c m g hP',
    isOrbitExtension_unitaryOrbitExtension b c m g hP', ?_⟩
  apply matrixCoordinates_injective b c T
  apply Units.ext
  rw [matrixCoordinates_evalZero_unitaryOrbitExtension, map_one]
  exact hD

/-- A block diagonal unitary point has constant conjugation orbit. -/
theorem mem_centralizer_of_blockLevi {T : Over S} (g : T ⟶ (groupScheme b c).X)
    (hg : matrixCoordinates b c T g ∈ GeneralLinear.blockLeviSubgroup _ (weights m)) :
    g ∈ (Dynamic.centralizer (weightCocharacter b c m)).carrier T := by
  rw [Dynamic.mem_centralizer]
  have hL : matrixCoordinates b c _ (fst T (Gm S).X ≫ g) ∈
      GeneralLinear.blockLeviSubgroup _ (weights m) := by
    rw [matrixCoordinates_naturality]
    exact GeneralLinear.map_mem_blockLeviSubgroup _ _ hg
  have hP : matrixCoordinates b c _ (fst T (Gm S).X ≫ g) ∈
      GeneralLinear.blockParabolicSubgroup _ (weights m) :=
    (GeneralLinear.mem_blockParabolicSubgroup _ _).2 (fun i j h => hL i j h.ne)
  apply matrixCoordinates_injective b c _
  rw [Dynamic.orbit, map_mul, map_mul, map_inv, matrixCoordinates_weightCocharacter]
  apply Units.ext
  rw [← GeneralLinear.weightScale_units (weights m) _ hP,
    GeneralLinear.weightScale_of_blockLevi (weights m) _ hL]

end Scheme
end Langlands.GroupScheme.QuasiSplitUnitary
