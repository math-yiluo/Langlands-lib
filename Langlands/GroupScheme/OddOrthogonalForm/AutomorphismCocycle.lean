import Langlands.GroupScheme.EvenOrthogonalForm.SimilitudeCocycle
import Langlands.GroupScheme.OddOrthogonalForm.ConjugatorSection

/-! # Exact Galois cocycles for odd orthogonal forms -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.OddOrthogonalForm

open OddOrthogonalMatrix

variable {K : Type u} [Field K] {N : Type u} [Field N] [Algebra K N] {n : ℕ}
variable {H : GroupScheme (Spec (CommRingCat.of K))}
  (φ : LocalGroupIso H (splitGroup K n) (ringTest K N))

/-- The automorphisms `ψ_σ(s) = φ(s ≫ σ*) ∘ φ(s)⁻¹` of the full split odd group along
`Spec N ⟶ Spec K` obtained by comparing `φ` at a point and at its Galois translate. -/
def galoisTwist (σ : N ≃ₐ[K] N) :
    LocalGroupIso (splitGroup K n) (splitGroup K n) (ringTest K N) where
  toFun s := (φ.toFun s).symm.trans (φ.toFun (s ≫ ringTestMap K σ.toAlgHom))
  naturality t s g := by
    change φ.toFun ((t ≫ s) ≫ ringTestMap K σ.toAlgHom) ((φ.toFun (t ≫ s)).symm (t ≫ g)) =
      t ≫ φ.toFun (s ≫ ringTestMap K σ.toAlgHom) ((φ.toFun s).symm g)
    have h := φ.symm.naturality t s g
    change (φ.toFun (t ≫ s)).symm (t ≫ g) = t ≫ (φ.toFun s).symm g at h
    rw [h, Category.assoc, φ.naturality]

theorem galoisTwist_toFun (σ : N ≃ₐ[K] N) {V : Over (Spec (CommRingCat.of K))}
    (s : V ⟶ ringTest K N) (x : V ⟶ (splitGroup K n).X) :
    (galoisTwist φ σ).toFun s x =
      φ.toFun (s ≫ ringTestMap K σ.toAlgHom) ((φ.toFun s).symm x) :=
  rfl

/-- The twists compose along Galois translates: `ψ_{σσ'}(s) = ψ_σ'(s ≫ σ*) ∘ ψ_σ(s)`. -/
theorem galoisTwist_mul (σ σ' : N ≃ₐ[K] N) {V : Over (Spec (CommRingCat.of K))}
    (s : V ⟶ ringTest K N) (x : V ⟶ (splitGroup K n).X) :
    (galoisTwist φ (σ * σ')).toFun s x =
      (galoisTwist φ σ').toFun (s ≫ ringTestMap K σ.toAlgHom) ((galoisTwist φ σ).toFun s x) := by
  rw [galoisTwist_toFun, galoisTwist_toFun, galoisTwist_toFun, MulEquiv.symm_apply_apply]
  have h : ringTestMap K (σ * σ').toAlgHom =
      ringTestMap K σ.toAlgHom ≫ ringTestMap K σ'.toAlgHom := by
    rw [← ringTestMap_comp]
    rfl
  rw [h, Category.assoc]


/-- The actual cover sections implementing the Galois twists. -/
def galoisSection (hn : 2 ≤ n) (σ : N ≃ₐ[K] N) :
    ringTest K N ⟶ (splitGroup K n).X :=
  conjugatorSection hn (galoisTwist φ σ)

/-- The identity twist has identity conjugating section. -/
theorem galoisSection_one (hn : 2 ≤ n) : galoisSection φ hn 1 = 1 := by
  apply section_eq_of_conjugation_eq hn
  intro V s x
  dsimp only [galoisSection]
  rw [← localAutomorphism_eq_conjugation hn (galoisTwist φ 1) s x]
  have hid : ringTestMap K (1 : N ≃ₐ[K] N).toAlgHom = 𝟙 (ringTest K N) := by
    change ringTestMap K (AlgHom.id K N) = _
    exact ringTestMap_id K N
  simp only [galoisTwist_toFun, hid, Category.comp_id, MulEquiv.apply_symm_apply,
    MonObj.comp_one, one_mul, inv_one, mul_one]

/-- Triviality of the full centre upgrades the twist law to an exact section law. -/
theorem galoisSection_mul (hn : 2 ≤ n) (σ τ : N ≃ₐ[K] N) :
    galoisSection φ hn (σ * τ) =
      (ringTestMap K σ.toAlgHom ≫ galoisSection φ hn τ) * galoisSection φ hn σ := by
  apply section_eq_of_conjugation_eq hn
  intro V s x
  dsimp only [galoisSection]
  rw [← localAutomorphism_eq_conjugation hn (galoisTwist φ (σ * τ)) s x,
    galoisTwist_mul]
  rw [localAutomorphism_eq_conjugation hn (galoisTwist φ τ),
    localAutomorphism_eq_conjugation hn (galoisTwist φ σ)]
  simp only [MonObj.comp_mul, Category.assoc, mul_inv_rev, mul_assoc]


/-- The actual isometric matrices implementing the twists. -/
def galoisConjugator (hn : 2 ≤ n) (σ : N ≃ₐ[K] N) : GL (Index (Fin n)) N :=
  conjugatorMatrix hn (galoisTwist φ σ)

/-- The identity field automorphism has identity matrix. -/
theorem galoisConjugator_one (hn : 2 ≤ n) : galoisConjugator φ hn 1 = 1 := by
  apply Units.ext
  apply Matrix.map_injective (EvenOrthogonalForm.sectionScalars_id_injective (K := K) (N := N))
  have h := splitMatrix_conjugatorSection hn (galoisTwist φ 1) (𝟙 (ringTest K N))
  rw [Category.id_comp, ← galoisSection, galoisSection_one] at h
  change ((pointMatrix K (ringTest K N)) 1).val = _ at h
  rw [_root_.map_one] at h
  change (conjugatorMatrix hn (galoisTwist φ 1)).val.map _ =
    (1 : Matrix (Index (Fin n)) (Index (Fin n)) N).map _
  rw [Matrix.map_one _ (map_zero _) (map_one _)]
  exact h.symm

/-- The actual conjugator matrices obey an exact twisted product law. -/
theorem galoisConjugator_mul (hn : 2 ≤ n) (σ τ : N ≃ₐ[K] N) :
    galoisConjugator φ hn (σ * τ) =
      Matrix.GeneralLinearGroup.map (σ : N →+* N) (galoisConjugator φ hn τ) *
        galoisConjugator φ hn σ := by
  apply Units.ext
  apply Matrix.map_injective (EvenOrthogonalForm.sectionScalars_id_injective (K := K) (N := N))
  have hστ := splitMatrix_conjugatorSection hn (galoisTwist φ (σ * τ)) (𝟙 (ringTest K N))
  have hσ := splitMatrix_conjugatorSection hn (galoisTwist φ σ) (𝟙 (ringTest K N))
  have hτ := splitMatrix_conjugatorSection hn (galoisTwist φ τ) (ringTestMap K σ.toAlgHom)
  simp only [Category.id_comp] at hστ hσ
  have he := congrArg (fun z => splitMatrix z) (galoisSection_mul φ hn σ τ)
  change splitMatrix (galoisSection φ hn (σ * τ)) =
    (pointMatrix K (ringTest K N)
      ((ringTestMap K σ.toAlgHom ≫ galoisSection φ hn τ) * galoisSection φ hn σ)).val at he
  rw [_root_.map_mul, Units.val_mul] at he
  change splitMatrix (galoisSection φ hn (σ * τ)) =
    splitMatrix (ringTestMap K σ.toAlgHom ≫ galoisSection φ hn τ) *
      splitMatrix (galoisSection φ hn σ) at he
  dsimp only [galoisSection] at he
  rw [hστ, hσ, hτ] at he
  have hsc : sectionScalars (ringTestMap K σ.toAlgHom) =
      (sectionScalars (K := K) (𝟙 (ringTest K N))).comp (σ : N →+* N) := by
    simpa only [Category.id_comp] using
      SpecialLinearInnerForm.pointScalars_comp_ringTestMap (𝟙 (ringTest K N)) σ
  rw [hsc] at he
  refine he.trans ?_
  change _ = ((galoisConjugator φ hn τ).val.map (σ : N →+* N) *
    (galoisConjugator φ hn σ).val).map (sectionScalars (K := K) (𝟙 (ringTest K N)))
  rw [Matrix.map_mul]
  rfl

/-- Inverting the conjugators gives the usual left matrix cocycle convention. -/
def matrixCocycle (hn : 2 ≤ n) (σ : N ≃ₐ[K] N) : GL (Index (Fin n)) N :=
  (galoisConjugator φ hn σ)⁻¹

@[simp] theorem matrixCocycle_one (hn : 2 ≤ n) : matrixCocycle φ hn 1 = 1 := by
  rw [matrixCocycle, galoisConjugator_one, inv_one]

theorem matrixCocycle_mul (hn : 2 ≤ n) (σ τ : N ≃ₐ[K] N) :
    matrixCocycle φ hn (σ * τ) = matrixCocycle φ hn σ *
      Matrix.GeneralLinearGroup.map (σ : N →+* N) (matrixCocycle φ hn τ) := by
  simp only [matrixCocycle, galoisConjugator_mul, mul_inv_rev, _root_.map_inv]

end Langlands.GroupScheme.OddOrthogonalForm
