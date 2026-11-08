import Langlands.GroupScheme.Rational.AffineCharacterFiniteGaloisValues
import Langlands.GroupScheme.Rational.AffineCharacterNaturalValues
import Langlands.GroupScheme.Rational.CharacterBaseChange
import Langlands.GroupScheme.Dynamic.AdjointDeterminantModelIndependence
import Langlands.Geometry.Building.CentralizerNormValuation
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.FieldTheory.Galois.Infinite

/-! # Descent of affine characters along a Galois tower

For fields `k → E → L` and an affine group `G` over `k`, a character `ψ` of
`G_L` whose universal tensor value lies in `E ⊗[k] Coord G` is the base change
of an actual character of `G_E`. When `L / E` is finite Galois, it suffices that
the universal tensor value is fixed by every automorphism of `L / E`. -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.AffineCharacterTowerDescent

open Langlands.Plancherel.TorusNormKernel
open Langlands.GroupScheme.AffineCharacterFiniteGalois

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]
variable (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffine G.X.left]
variable (E L : Type u) [Field E] [Field L] [Algebra k E] [Algebra k L] [Algebra E L]
  [IsScalarTower k E L]

/-- Extension of tensor coefficients along the tower `k → E → L`. -/
def tensorExtend : E ⊗[k] Coord G →ₐ[k] L ⊗[k] Coord G :=
  Algebra.TensorProduct.map (IsScalarTower.toAlgHom k E L) (AlgHom.id k (Coord G))

@[simp]
theorem tensorExtend_tmul (c : E) (a : Coord G) :
    tensorExtend G E L (c ⊗ₜ a) = algebraMap E L c ⊗ₜ a := rfl

/-- Extending tensor coefficients along a field extension is injective. -/
theorem tensorExtend_injective : Function.Injective (tensorExtend G E L) :=
  TensorProduct.map_injective_of_flat_flat (IsScalarTower.toAlgHom k E L).toLinearMap
    (LinearMap.id : Coord G →ₗ[k] Coord G) (algebraMap E L).injective Function.injective_id

local instance testAlgebra (A : CommAlgCat.{u} E) : Algebra k A :=
  Algebra.compHom A (algebraMap k E)

local instance testTower (A : CommAlgCat.{u} E) : IsScalarTower k E A :=
  IsScalarTower.of_algebraMap_eq' rfl

omit [IsAffine G.X.left] in
/-- The base change of an affine group scheme to a field is affine. -/
theorem baseChanged_isAffine (F : Type u) [Field F] [Algebra k F]
    (T : GroupScheme (Spec (CommRingCat.of k))) [IsAffine T.X.left] :
    IsAffine (GaloisPointComparison.baseChanged k F T).X.left := by
  change IsAffine (CategoryTheory.Limits.pullback T.X.hom
    (GaloisPointComparison.baseMap k F))
  infer_instance

attribute [local instance] baseChanged_isAffine

omit [IsAffine G.X.left] in
/-- Characters of `T_E` are determined by their values over all `E`-algebras. -/
theorem ext_valueE {T : GroupScheme (Spec (CommRingCat.of k))} [IsAffine T.X.left]
    {χ₁ χ₂ : rationalCharacters (GaloisPointComparison.baseChanged k E T)}
    (h : ∀ (D : Type u) [CommRing D] [Algebra k D] [Algebra E D] [IsScalarTower k E D]
      (y : T.affinePoints (CommAlgCat.of k D)), valueE χ₁ D y = valueE χ₂ D y) :
    χ₁ = χ₂ := by
  apply rationalCharacters_ext_affinePoints
  intro A p
  have hA := h A ((pointE k E A T).symm p)
  rw [valueE_apply, valueE_apply, MulEquiv.apply_symm_apply] at hA
  exact (Gm.affineUnitsEquiv (CommRingCat.of E) A).injective hA

section Tower

variable {E L}
variable {D : Type u} [CommRing D] [Algebra k D] [Algebra E D] [Algebra L D]
  [IsScalarTower k E D] [IsScalarTower k L D] [IsScalarTower E L D]

/-- Evaluation over an `L`-algebra restricts to evaluation of `E`-coefficient tensors. -/
theorem tensorEval_comp_tensorExtend (y : G.affinePoints (CommAlgCat.of k D)) :
    ((tensorEval G L D y).restrictScalars k).comp (tensorExtend G E L) =
      (tensorEval G E D y).restrictScalars k := by
  apply Algebra.TensorProduct.ext'
  intro c a
  simp only [tensorEval, tensorExtend, AlgHom.comp_apply, AlgHom.restrictScalars_apply,
    Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply,
    IsScalarTower.coe_toAlgHom', AlgHom.id_apply]
  rw [← IsScalarTower.algebraMap_apply]

end Tower

section Model

variable (v : (E ⊗[k] Coord G)ˣ)

/-- The values defined by an `E`-coefficient tensor unit. -/
def modelValue (D : Type u) [CommRing D] [Algebra k D] [Algebra E D] [IsScalarTower k E D]
    (y : G.affinePoints (CommAlgCat.of k D)) : Dˣ :=
  Units.map (tensorEval G E D y).toMonoidHom v

/-- Model values are natural in the coefficient algebra. -/
theorem modelValue_naturality
    {D D' : Type u} [CommRing D] [Algebra k D] [Algebra E D] [IsScalarTower k E D]
    [CommRing D'] [Algebra k D'] [Algebra E D'] [IsScalarTower k E D']
    (f : D →ₐ[E] D') (y : G.affinePoints (CommAlgCat.of k D)) :
    modelValue G E v D' (Lie.affineMap G (f.restrictScalars k) y) =
      Units.map f.toMonoidHom (modelValue G E v D y) := by
  dsimp only [modelValue]
  rw [tensorEval_naturality]
  rfl

variable (ψ : rationalCharacters (GaloisPointComparison.baseChanged k L G))
variable (hv : Units.map (tensorExtend G E L).toMonoidHom v = tensorValue G L ψ)

include hv in
/-- Over an `L`-algebra the model values are the values of `ψ`. -/
theorem modelValue_eq_valueE
    {D : Type u} [CommRing D] [Algebra k D] [Algebra E D] [Algebra L D]
    [IsScalarTower k E D] [IsScalarTower k L D] [IsScalarTower E L D]
    (y : G.affinePoints (CommAlgCat.of k D)) :
    modelValue G E v D y = valueE ψ D y := by
  rw [← tensorValue_eval, ← hv]
  apply Units.ext
  exact (DFunLike.congr_fun (tensorEval_comp_tensorExtend G y) (v : E ⊗[k] Coord G)).symm

include hv in
/-- After the injective scalar extension `B → L ⊗[E] B`, the model values are the
values of `ψ`. -/
theorem modelValue_compare
    (B : Type u) [CommRing B] [Algebra k B] [Algebra E B] [IsScalarTower k E B]
    (y : G.affinePoints (CommAlgCat.of k B)) :
    Units.map (Algebra.TensorProduct.includeRight : B →ₐ[E] L ⊗[E] B).toMonoidHom
        (modelValue G E v B y) =
      valueE ψ (L ⊗[E] B)
        (Lie.affineMap G
          ((Algebra.TensorProduct.includeRight : B →ₐ[E] L ⊗[E] B).restrictScalars k) y) := by
  rw [← modelValue_naturality, modelValue_eq_valueE G E L v ψ hv]

/-- The model values satisfy the character laws, by reflection through scalar extension. -/
def modelHom (B : Type u) [CommRing B] [Algebra k B] [Algebra E B] [IsScalarTower k E B] :
    G.affinePoints (CommAlgCat.of k B) →* Bˣ where
  toFun := modelValue G E v B
  map_one' := by
    apply Units.map_injective (f :=
      (Algebra.TensorProduct.includeRight : B →ₐ[E] L ⊗[E] B).toMonoidHom)
      (Algebra.TensorProduct.includeRight_injective (RingHom.injective (algebraMap E L)))
    rw [modelValue_compare G E L v ψ hv]
    change valueE ψ (L ⊗[E] B)
      (G.affinePointMap (CommAlgCat.ofHom
        ((Algebra.TensorProduct.includeRight : B →ₐ[E] L ⊗[E] B).restrictScalars k)) 1) = _
    rw [map_one, map_one, map_one]
  map_mul' x y := by
    apply Units.map_injective (f :=
      (Algebra.TensorProduct.includeRight : B →ₐ[E] L ⊗[E] B).toMonoidHom)
      (Algebra.TensorProduct.includeRight_injective (RingHom.injective (algebraMap E L)))
    rw [map_mul, modelValue_compare G E L v ψ hv, modelValue_compare G E L v ψ hv,
      modelValue_compare G E L v ψ hv]
    change valueE ψ (L ⊗[E] B)
      (G.affinePointMap (CommAlgCat.ofHom
        ((Algebra.TensorProduct.includeRight : B →ₐ[E] L ⊗[E] B).restrictScalars k))
        (x * y)) = _
    rw [map_mul, map_mul]
    rfl

section Reconstruction

/-- The model on affine points of the actual base-changed group. -/
def descendApp (A : CommAlgCat.{u} E) :
    (GaloisPointComparison.baseChanged k E G).affinePoints A →* Aˣ :=
  (modelHom G E L v ψ hv A).comp (pointE k E A G).symm.toMonoidHom

theorem descendApp_naturality {A A' : CommAlgCat.{u} E} (f : A ⟶ A')
    (y : (GaloisPointComparison.baseChanged k E G).affinePoints A) :
    descendApp G E L v ψ hv A'
        ((GaloisPointComparison.baseChanged k E G).affinePointMap f y) =
      Units.map f.hom.toMonoidHom (descendApp G E L v ψ hv A y) := by
  change modelValue G E v A'
    ((pointE k E A' G).symm
      ((GaloisPointComparison.baseChanged k E G).affinePointMap f y)) = _
  have hp : (pointE k E A' G).symm
      ((GaloisPointComparison.baseChanged k E G).affinePointMap f y) =
      Lie.affineMap G (f.hom.restrictScalars k) ((pointE k E A G).symm y) := by
    apply (pointE k E A' G).injective
    rw [MulEquiv.apply_symm_apply]
    exact (congrArg ((GaloisPointComparison.baseChanged k E G).affinePointMap f)
      ((pointE k E A G).apply_symm_apply y)).symm.trans
        (pointE_naturality k E G f.hom ((pointE k E A G).symm y)).symm
  rw [hp]
  exact modelValue_naturality G E v f.hom _

/-- The actual character of `G_E` represented by the coefficient tensor unit. -/
def descendCharacter : rationalCharacters (GaloisPointComparison.baseChanged k E G) :=
  AffineCharacterNaturalValues.character _ (descendApp G E L v ψ hv)
    (descendApp_naturality G E L v ψ hv)

theorem descendCharacter_affineValues (A : CommAlgCat.{u} E)
    (y : (GaloisPointComparison.baseChanged k E G).affinePoints A) :
    Gm.affineUnitsEquiv (CommRingCat.of E) A
      (y ≫ (descendCharacter G E L v ψ hv).toMul.hom.hom) =
      descendApp G E L v ψ hv A y :=
  AffineCharacterNaturalValues.character_values _ _ _ A y

end Reconstruction

/-- The descended character takes the model values over every `E`-algebra,
for any compatible structure over `k`. -/
theorem valueE_descendCharacter
    (D : Type u) [CommRing D] [Algebra k D] [Algebra E D] [IsScalarTower k E D]
    (y : G.affinePoints (CommAlgCat.of k D)) :
    valueE (descendCharacter G E L v ψ hv) D y = modelValue G E v D y := by
  have h : (‹Algebra k D›) = Algebra.compHom D (algebraMap k E) :=
    Algebra.algebra_ext _ _ fun r => IsScalarTower.algebraMap_apply k E D r
  subst h
  let : Algebra k D := Algebra.compHom D (algebraMap k E)
  rw [valueE_apply, descendCharacter_affineValues]
  change modelValue G E v D ((pointE k E D G).symm (pointE k E D G y)) = _
  rw [MulEquiv.symm_apply_apply]

/-- Over an `L`-algebra the descended character has the values of `ψ`. -/
theorem valueE_descendCharacter_of_tower
    {D : Type u} [CommRing D] [Algebra k D] [Algebra E D] [Algebra L D]
    [IsScalarTower k E D] [IsScalarTower k L D] [IsScalarTower E L D]
    (y : G.affinePoints (CommAlgCat.of k D)) :
    valueE (descendCharacter G E L v ψ hv) D y = valueE ψ D y := by
  rw [valueE_descendCharacter, modelValue_eq_valueE G E L v ψ hv]

/-- Values of the descended character over an `E`-algebra are detected after the
injective scalar extension to `L`. -/
theorem valueE_descendCharacter_includeRight
    (B : Type u) [CommRing B] [Algebra k B] [Algebra E B] [IsScalarTower k E B]
    (y : G.affinePoints (CommAlgCat.of k B)) :
    Units.map (Algebra.TensorProduct.includeRight : B →ₐ[E] L ⊗[E] B).toMonoidHom
        (valueE (descendCharacter G E L v ψ hv) B y) =
      valueE ψ (L ⊗[E] B)
        (Lie.affineMap G
          ((Algebra.TensorProduct.includeRight : B →ₐ[E] L ⊗[E] B).restrictScalars k) y) := by
  rw [valueE_descendCharacter, modelValue_compare G E L v ψ hv]

omit [IsAffine G.X.left] in
/-- Rational values over `E` and `L` agree when the values over `L` agree. -/
theorem rationalCharacterEval_rationalExtend_of_valueE
    (χ : rationalCharacters (GaloisPointComparison.baseChanged k E G))
    (ψ : rationalCharacters (GaloisPointComparison.baseChanged k L G))
    (h : ∀ y : G.affinePoints (CommAlgCat.of k L), valueE χ L y = valueE ψ L y)
    (g : rationalPoints G) :
    algebraMap E L (rationalCharacterEval χ
        (GaloisPointComparison.rationalExtend k E G g) : E) =
      (rationalCharacterEval ψ (GaloisPointComparison.rationalExtend k L G g) : L) := by
  rw [← valueE_baseChangeCoeffEquiv, ← valueE_baseChangeCoeffEquiv,
    GaloisPointComparison.baseChangeCoeffEquiv_rationalExtend,
    GaloisPointComparison.baseChangeCoeffEquiv_rationalExtend, ← h]
  change (Units.map (Algebra.ofId E L).toMonoidHom (valueE χ E _) : L) = _
  rw [← valueE_naturality]
  congr 2
  change G.affinePointMap (CommAlgCat.ofHom ((Algebra.ofId E L).restrictScalars k))
      (G.affinePointMap (CommAlgCat.ofHom (Algebra.ofId k E)) _) =
    G.affinePointMap (CommAlgCat.ofHom (Algebra.ofId k L)) _
  rw [← MonoidHom.comp_apply, ← GroupScheme.affinePointMap_comp]
  congr 2
  ext

/-- The descended character has the rational values of `ψ` on extended rational points. -/
theorem rationalCharacterEval_descendCharacter (g : rationalPoints G) :
    algebraMap E L (rationalCharacterEval (descendCharacter G E L v ψ hv)
        (GaloisPointComparison.rationalExtend k E G g) : E) =
      (rationalCharacterEval ψ (GaloisPointComparison.rationalExtend k L G g) : L) :=
  rationalCharacterEval_rationalExtend_of_valueE G E L _ ψ
    (fun y => valueE_descendCharacter_of_tower G E L v ψ hv y) g

/-- If the restriction of `ψ` along a base-changed morphism is a base-changed character,
then so is the restriction of the descended character. -/
theorem characterRestrict_descendCharacter {H : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffine H.X.left] (f : H ⟶ G) (a : rationalCharacters H)
    (ha : characterRestrict
        ((GroupScheme.baseChange (GaloisPointComparison.baseMap k L)).map f) ψ =
      rationalCharacters.baseChange (GaloisPointComparison.baseMap k L) a) :
    characterRestrict ((GroupScheme.baseChange (GaloisPointComparison.baseMap k E)).map f)
        (descendCharacter G E L v ψ hv) =
      rationalCharacters.baseChange (GaloisPointComparison.baseMap k E) a := by
  apply ext_valueE
  intro D _ _ _ _ y
  rw [valueE_characterRestrict, valueE_baseChange]
  apply Units.map_injective (f :=
    (Algebra.TensorProduct.includeRight : D →ₐ[E] L ⊗[E] D).toMonoidHom)
    (Algebra.TensorProduct.includeRight_injective (RingHom.injective (algebraMap E L)))
  rw [valueE_descendCharacter_includeRight]
  have hp : ∀ {X : GroupScheme (Spec (CommRingCat.of k))} (q : H ⟶ X),
      Lie.affineMap X ((Algebra.TensorProduct.includeRight :
          D →ₐ[E] L ⊗[E] D).restrictScalars k) (y ≫ q.hom.hom) =
        Lie.affineMap H ((Algebra.TensorProduct.includeRight :
          D →ₐ[E] L ⊗[E] D).restrictScalars k) y ≫ q.hom.hom :=
    fun _ => by rw [Lie.affineMap_apply, Lie.affineMap_apply, Category.assoc]
  rw [hp, ← valueE_characterRestrict, ha, valueE_baseChange]
  have hq : Lie.affineMap H ((Algebra.TensorProduct.includeRight :
          D →ₐ[E] L ⊗[E] D).restrictScalars k) y ≫ a.toMul.hom.hom =
      GroupScheme.affinePointMap (GroupScheme.Gm (Spec (CommRingCat.of k))).toGrp
        (CommAlgCat.ofHom ((Algebra.TensorProduct.includeRight :
          D →ₐ[E] L ⊗[E] D).restrictScalars k)) (y ≫ a.toMul.hom.hom) :=
    Category.assoc _ _ _
  rw [hq, Gm.affineUnitsEquiv_naturality]
  rfl

end Model

section Galois

/-- The Galois action on the coefficients of universal tensors. -/
def tensorConj (σ : L ≃ₐ[E] L) : L ⊗[k] Coord G →ₐ[k] L ⊗[k] Coord G :=
  Algebra.TensorProduct.map ((σ : L →ₐ[E] L).restrictScalars k) (AlgHom.id k (Coord G))

@[simp]
theorem tensorConj_tmul (σ : L ≃ₐ[E] L) (c : L) (a : Coord G) :
    tensorConj G E L σ (c ⊗ₜ a) = σ c ⊗ₜ a := rfl

/-- In the coefficient basis induced by a basis of `Coord G`, the Galois action on
universal tensors acts on the coordinates. -/
theorem tensorConj_repr (σ : L ≃ₐ[E] L) (x : L ⊗[k] Coord G)
    (i : Module.Basis.ofVectorSpaceIndex k (Coord G)) :
    (Algebra.TensorProduct.basis L (Module.Basis.ofVectorSpace k (Coord G))).repr
        (tensorConj G E L σ x) i =
      σ ((Algebra.TensorProduct.basis L (Module.Basis.ofVectorSpace k (Coord G))).repr x i) := by
  induction x with
  | tmul c a =>
    rw [tensorConj_tmul, Algebra.TensorProduct.basis_repr_tmul,
      Algebra.TensorProduct.basis_repr_tmul]
    simp only [Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul, map_mul]
    rw [IsScalarTower.algebraMap_apply k E L, AlgEquiv.commutes]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

variable [IsGalois E L]

/-- A universal tensor fixed by `Gal(L/E)` has coefficients in `E`. -/
theorem mem_range_tensorExtend_of_fixed (x : L ⊗[k] Coord G)
    (hx : ∀ σ : L ≃ₐ[E] L, tensorConj G E L σ x = x) :
    x ∈ (tensorExtend G E L).range := by
  set b := Algebra.TensorProduct.basis L (Module.Basis.ofVectorSpace k (Coord G))
  rw [← b.linearCombination_repr x, Finsupp.linearCombination_apply]
  refine Subalgebra.sum_mem _ fun i _ => ?_
  obtain ⟨e, he⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (b.repr x i)).2
    fun σ => by rw [← tensorConj_repr G E L σ, hx]
  refine (AlgHom.mem_range _).2 ⟨e ⊗ₜ Module.Basis.ofVectorSpace k (Coord G) i, ?_⟩
  rw [tensorExtend_tmul, he]
  exact (Algebra.TensorProduct.basis_repr_symm_apply' _ _ _).symm

/-- A unit universal tensor fixed by `Gal(L/E)` is the extension of a unit with
coefficients in `E`. -/
theorem exists_unit_of_fixed (w : (L ⊗[k] Coord G)ˣ)
    (hw : ∀ σ : L ≃ₐ[E] L, tensorConj G E L σ (w : L ⊗[k] Coord G) = w) :
    ∃ v : (E ⊗[k] Coord G)ˣ, Units.map (tensorExtend G E L).toMonoidHom v = w := by
  have hinv : ∀ σ : L ≃ₐ[E] L,
      tensorConj G E L σ (↑w⁻¹ : L ⊗[k] Coord G) = ↑w⁻¹ := by
    intro σ
    have h := congrArg (tensorConj G E L σ) w.inv_mul
    rw [map_mul, map_one, hw σ] at h
    exact (Units.inv_eq_of_mul_eq_one_left h).symm
  obtain ⟨a, ha⟩ := (AlgHom.mem_range _).1 (mem_range_tensorExtend_of_fixed G E L _ hw)
  obtain ⟨a', ha'⟩ := (AlgHom.mem_range _).1 (mem_range_tensorExtend_of_fixed G E L _ hinv)
  refine ⟨⟨a, a', tensorExtend_injective G E L ?_, tensorExtend_injective G E L ?_⟩,
    Units.ext ha⟩
  · rw [map_mul, ha, ha', Units.mul_inv, map_one]
  · rw [map_mul, ha, ha', Units.inv_mul, map_one]

variable (ψ : rationalCharacters (GaloisPointComparison.baseChanged k L G))
variable (hψ : ∀ σ : L ≃ₐ[E] L,
  tensorConj G E L σ (tensorValue G L ψ : L ⊗[k] Coord G) = tensorValue G L ψ)

/-- The actual character of `G_E` descended from a character of `G_L` whose universal
tensor value is fixed by `Gal(L/E)`. -/
def fixedDescend : rationalCharacters (GaloisPointComparison.baseChanged k E G) :=
  descendCharacter G E L (exists_unit_of_fixed G E L _ hψ).choose ψ
    (exists_unit_of_fixed G E L _ hψ).choose_spec

/-- Over an `L`-algebra the descended character has the values of `ψ`. -/
theorem valueE_fixedDescend
    {D : Type u} [CommRing D] [Algebra k D] [Algebra E D] [Algebra L D]
    [IsScalarTower k E D] [IsScalarTower k L D] [IsScalarTower E L D]
    (y : G.affinePoints (CommAlgCat.of k D)) :
    valueE (fixedDescend G E L ψ hψ) D y = valueE ψ D y :=
  valueE_descendCharacter_of_tower G E L _ ψ _ y

/-- The descended character has the rational values of `ψ` on extended rational points. -/
theorem rationalCharacterEval_fixedDescend (g : rationalPoints G) :
    algebraMap E L (rationalCharacterEval (fixedDescend G E L ψ hψ)
        (GaloisPointComparison.rationalExtend k E G g) : E) =
      (rationalCharacterEval ψ (GaloisPointComparison.rationalExtend k L G g) : L) :=
  rationalCharacterEval_descendCharacter G E L _ ψ _ g

/-- Restrictions that are base-changed characters over `L` are base-changed over `E`. -/
theorem characterRestrict_fixedDescend {H : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffine H.X.left] (f : H ⟶ G) (a : rationalCharacters H)
    (ha : characterRestrict
        ((GroupScheme.baseChange (GaloisPointComparison.baseMap k L)).map f) ψ =
      rationalCharacters.baseChange (GaloisPointComparison.baseMap k L) a) :
    characterRestrict ((GroupScheme.baseChange (GaloisPointComparison.baseMap k E)).map f)
        (fixedDescend G E L ψ hψ) =
      rationalCharacters.baseChange (GaloisPointComparison.baseMap k E) a :=
  characterRestrict_descendCharacter G E L _ ψ _ f a ha

end Galois

end Langlands.GroupScheme.AffineCharacterTowerDescent
