import Langlands.BruhatTits.IntegralModels.GeneralLinearIwahoriModel
import Langlands.GroupScheme.FiniteFreeAlgebraUnipotentUnits
import Langlands.BruhatTits.IntegralModels.SpecialFibre
import Langlands.GroupScheme.Rational.PseudoParabolicAmbientTransport
import Langlands.GroupScheme.Rational.SplitUnipotentTransport
import Langlands.GroupScheme.Torus.SplitReductiveProof

/-! # The reductive quotient of the special fibre of the `GL_N` Iwahori model

The special fibre of the published Iwahori model of `GL_N` is the unit group of `𝓀 ⊗ Λ`, for the
Iwahori order `Λ`. Its unipotent radical is the kernel `1 + J` of the reduction to the diagonal,
the quotient is the diagonal split torus, and the resulting positive subgroup is `I^+`. See the
paired Markdown file.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct ValuativeRel CategoryTheory.MonObj

namespace Langlands.GroupScheme.FiniteFreeAlgebraUnits

/-! ### Section units under algebra maps, isomorphisms and base change -/

section SectionUnits

variable {R : CommRingCat.{u}} {A : Type u} [Ring A] [Algebra R A] {n : ℕ}
  (b : Module.Basis (Fin n) R A)

theorem sectionTensorEquiv_tmul (t : ((algΓ R).obj (Over.mk (𝟙 (Spec R)))).unop) (y : A) :
    sectionTensorEquiv (R := R) (A := A) (t ⊗ₜ y) = WeilGm.selfSectionsAlgEquiv R t • y := by
  simp [sectionTensorEquiv]

theorem sectionTensorEquiv_map {A' : Type u} [Ring A'] [Algebra R A'] (f : A →ₐ[R] A')
    (w : ((algΓ R).obj (Over.mk (𝟙 (Spec R)))).unop ⊗[R] A) :
    sectionTensorEquiv (R := R) (A := A')
        (Algebra.TensorProduct.map (AlgHom.id R _) f w) =
      f (sectionTensorEquiv (R := R) (A := A) w) := by
  induction w using TensorProduct.inductionOn with
  | tmul s a => simp [sectionTensorEquiv]
  | add w w' hw hw' => simp only [map_add, hw, hw']

/-- Section units of the image of a section under `map b b' f` are the images under `f`. -/
theorem sectionUnitsEquiv_map {A' : Type u} [Ring A'] [Algebra R A'] {m : ℕ}
    (b' : Module.Basis (Fin m) R A') (f : A →ₐ[R] A') (x : rationalPoints (groupScheme b)) :
    sectionUnitsEquiv b' (x ≫ (map b b' f).hom.hom) =
      Units.map f.toMonoidHom (sectionUnitsEquiv b x) := by
  apply Units.ext
  change sectionTensorEquiv (R := R) (A := A')
      (pointsEquiv b' (Over.mk (𝟙 (Spec R))) (x ≫ (map b b' f).hom.hom) : _) =
    f (sectionTensorEquiv (R := R) (A := A) (pointsEquiv b (Over.mk (𝟙 (Spec R))) x : _))
  rw [pointsEquiv_map, Units.coe_map]
  exact sectionTensorEquiv_map f _

/-- Section units of the image of a section under `congrIso b b' e` are the images under `e`. -/
theorem sectionUnitsEquiv_congrIso {A' : Type u} [Ring A'] [Algebra R A'] {m : ℕ}
    (b' : Module.Basis (Fin m) R A') (e : A ≃ₐ[R] A') (x : rationalPoints (groupScheme b)) :
    sectionUnitsEquiv b' (x ≫ (congrIso b b' e).hom.hom.hom) =
      Units.map e.toAlgHom.toMonoidHom (sectionUnitsEquiv b x) := by
  apply Units.ext
  change sectionTensorEquiv (R := R) (A := A')
      (pointsEquiv b' (Over.mk (𝟙 (Spec R))) (x ≫ (congrIso b b' e).hom.hom.hom) : _) =
    e (sectionTensorEquiv (R := R) (A := A) (pointsEquiv b (Over.mk (𝟙 (Spec R))) x : _))
  rw [congrIso_hom_points, congrPointsEquiv, MulEquiv.trans_apply, Units.coe_mapEquiv]
  exact sectionTensorEquiv_map e.toAlgHom _

/-- Base change of a section along `Spec R' → Spec R`: its section units are the images of the
original ones under `a ↦ 1 ⊗ a`. -/
theorem sectionUnitsEquiv_baseChange (R' : CommRingCat.{u}) [Algebra R R']
    (x : rationalPoints (groupScheme b)) :
    sectionUnitsEquiv (b.baseChange R')
        (baseChangeSectionHom (WeilGm.baseMap R R') (groupScheme b) x ≫
          (baseChangeIso b R').hom.hom.hom) =
      Units.map (Algebra.TensorProduct.includeRight : A →ₐ[R] R' ⊗[R] A).toMonoidHom
        (sectionUnitsEquiv b x) := by
  let T := Over.mk (𝟙 (Spec R'))
  let a : (Over.map (WeilGm.baseMap R R')).obj T ⟶ Over.mk (𝟙 (Spec R)) :=
    Over.homMk (WeilGm.baseMap R R') (by simp [T])
  let : Algebra R' (WeilGm.restrictedSections R R' T) :=
    WeilGm.restrictedSectionsAlgebra R R' T
  let : IsScalarTower R R' (WeilGm.restrictedSections R R' T) :=
    WeilGm.restrictedSectionsScalarTower R R' T
  apply Units.ext
  change sectionTensorEquiv (R := R') (A := R' ⊗[R] A)
      (pointsEquiv (b.baseChange R') T
        (baseChangeSectionHom (WeilGm.baseMap R R') (groupScheme b) x ≫
          (baseChangeIso b R').hom.hom.hom) : _) =
    Algebra.TensorProduct.includeRight
      (sectionTensorEquiv (R := R) (A := A) (pointsEquiv b (Over.mk (𝟙 (Spec R))) x : _))
  rw [baseChangeIso_hom_points b R' T, basePointsEquiv_apply b R' T,
    baseChangePointsEquiv_baseChangeSectionHom, pointsEquiv_naturality]
  let G : ((algΓ R).obj (Over.mk (𝟙 (Spec R)))).unop ⊗[R] A →+ R' ⊗[R] A :=
    (sectionTensorEquiv (R := R') (A := R' ⊗[R] A)).toAlgHom.toRingHom.toAddMonoidHom.comp
      ((baseChangeTensorEquiv A R' (WeilGm.restrictedSections R R' T)).toRingHom.toAddMonoidHom.comp
        (Algebra.TensorProduct.map ((algΓ R).map a).unop.hom
          (AlgHom.id R A)).toRingHom.toAddMonoidHom)
  suffices h : ∀ z : ((algΓ R).obj (Over.mk (𝟙 (Spec R)))).unop ⊗[R] A,
      G z = Algebra.TensorProduct.includeRight (sectionTensorEquiv (R := R) (A := A) z) by
    exact h _
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul s c =>
      have hnat := ConcreteCategory.congr_hom
        (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R R'))) s
      change (Scheme.ΓSpecIso R').hom ((WeilGm.baseMap R R').appTop s) =
        algebraMap R R' ((Scheme.ΓSpecIso R).hom s) at hnat
      change sectionTensorEquiv (R := R') (A := R' ⊗[R] A)
        (baseChangeTensorEquiv A R' (WeilGm.restrictedSections R R' T)
          (Algebra.TensorProduct.map ((algΓ R).map a).unop.hom (AlgHom.id R A) (s ⊗ₜ c))) = _
      simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, baseChangeTensorEquiv_tmul]
      have hs : WeilGm.selfSectionsAlgEquiv R'
          (((algΓ R).map a).unop.hom s : ((algΓ R').obj T).unop) =
            algebraMap R R' (WeilGm.selfSectionsAlgEquiv R s) := hnat
      refine (sectionTensorEquiv_tmul (R := R') (A := R' ⊗[R] A) _ _).trans ?_
      rw [hs, sectionTensorEquiv_tmul, Algebra.TensorProduct.includeRight_apply,
        TensorProduct.tmul_smul, algebraMap_smul]
  | add z z' hz hz' =>
      rw [map_add, hz, hz', map_add, map_add]

/-- A section, base changed, transported along an algebra isomorphism and mapped by an algebra
map, is trivial exactly when the image of its unit is `1`. -/
theorem baseChange_congr_map_eq_one_iff (R' : CommRingCat.{u}) [Algebra R R']
    {A₁ : Type u} [Ring A₁] [Algebra R' A₁] {m : ℕ} (b₁ : Module.Basis (Fin m) R' A₁)
    (e : R' ⊗[R] A ≃ₐ[R'] A₁) {B : Type u} [Ring B] [Algebra R' B] {k : ℕ}
    (b' : Module.Basis (Fin k) R' B) (f : A₁ →ₐ[R'] B) (x : rationalPoints (groupScheme b)) :
    ((baseChangeSectionHom (WeilGm.baseMap R R') (groupScheme b) x ≫
        (baseChangeIso b R').hom.hom.hom) ≫ (congrIso (b.baseChange R') b₁ e).hom.hom.hom) ≫
        (map b₁ b' f).hom.hom = 1 ↔
      f (e ((1 : R') ⊗ₜ[R] (sectionUnitsEquiv b x : A))) = 1 := by
  rw [← (sectionUnitsEquiv b').map_eq_one_iff, sectionUnitsEquiv_map, sectionUnitsEquiv_congrIso,
    sectionUnitsEquiv_baseChange, Units.ext_iff]
  rfl

end SectionUnits

section OrderModel

/-- The generic point of an integral section of the neutral model of order model data is the
image under `φ` of its unit. All data are implicit, so that they are read off from the goal. -/
theorem orderModelData_integralPointMap_of_eq {R K : Type u} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] {A : Type u} [Ring A] [Algebra R A] {N : ℕ}
    {φ : A →ₐ[R] Matrix (Fin N) (Fin N) K} {n : ℕ} {b : Module.Basis (Fin n) (CommRingCat.of R) A}
    {hinj : Function.Injective φ}
    {hsurj : ∀ M : Matrix (Fin N) (Fin N) K, ∃ a : A, ∃ c ∈ nonZeroDivisors R, c • M = φ a}
    (x : (orderModelData R K N φ b hinj hsurj).neutral.integralSections)
    {M : Matrix (Fin N) (Fin N) K}
    (hM : φ (sectionUnitsEquiv (R := CommRingCat.of R) b x : A) = M) :
    (GeneralLinear.rationalPointsEquiv N (CommRingCat.of K)
        ((orderModelData R K N φ b hinj hsurj).neutral.integralPointMap x) :
          Matrix (Fin N) (Fin N) K) = M := by
  have h := unitModel_integralPointMap R K b N (orderEquiv R K N φ hinj hsurj) x
  rw [orderEquiv_tmul, one_smul] at h
  exact h.trans hM

end OrderModel

end Langlands.GroupScheme.FiniteFreeAlgebraUnits

namespace Langlands.BruhatTits.IntegralModels

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (N : ℕ)

/-- The residues of the diagonal entries are multiplicative on the Iwahori order. -/
theorem residue_mul_diag (M M' : iwahoriOrder F N) (i : Fin N) :
    IsLocalRing.residue 𝒪[F] (((M * M' : iwahoriOrder F N) : Matrix (Fin N) (Fin N) 𝒪[F]) i i) =
      IsLocalRing.residue 𝒪[F] ((M : Matrix (Fin N) (Fin N) 𝒪[F]) i i) *
        IsLocalRing.residue 𝒪[F] ((M' : Matrix (Fin N) (Fin N) 𝒪[F]) i i) := by
  rw [Subalgebra.coe_mul, Matrix.mul_apply, map_sum, ← map_mul]
  rw [Finset.sum_eq_single i]
  · intro k _ hk
    rw [map_mul]
    rcases lt_or_gt_of_ne hk with h | h
    · rw [(IsLocalRing.residue_eq_zero_iff _).mpr (M.2 i k h), zero_mul]
    · rw [(IsLocalRing.residue_eq_zero_iff _).mpr (M'.2 k i h), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- The residue of the diagonal, an algebra map from the Iwahori order to `𝓀[F]^N`. -/
def diagResidue : iwahoriOrder F N →ₐ[𝒪[F]] (Fin N → 𝓀[F]) where
  toFun M i := IsLocalRing.residue 𝒪[F] ((M : Matrix (Fin N) (Fin N) 𝒪[F]) i i)
  map_one' := by
    funext i
    simp
  map_mul' M M' := by
    funext i
    exact residue_mul_diag F N M M' i
  map_zero' := by
    funext i
    simp
  map_add' M M' := by
    funext i
    simp
  commutes' r := by
    funext i
    simp [Algebra.algebraMap_eq_smul_one, Matrix.smul_apply]

/-! ### An adapted basis of the Iwahori order -/

/-- A fixed uniformizer of `𝒪[F]`. -/
def iwahoriUniformizer : 𝒪[F] :=
  Classical.choose (IsDiscreteValuationRing.exists_irreducible 𝒪[F])

theorem iwahoriUniformizer_irreducible : Irreducible (iwahoriUniformizer F) :=
  Classical.choose_spec (IsDiscreteValuationRing.exists_irreducible 𝒪[F])

/-- The scale of the matrix unit at `p`: the uniformizer strictly below the diagonal, `1` on and
above it. -/
def unitScale (p : Fin N × Fin N) : 𝒪[F] :=
  if p.2 < p.1 then iwahoriUniformizer F else 1

theorem unitScale_ne_zero (p : Fin N × Fin N) : unitScale F N p ≠ 0 := by
  unfold unitScale
  split_ifs
  · exact (iwahoriUniformizer_irreducible F).ne_zero
  · exact one_ne_zero

/-- The scaled matrix unit `ϖ^{[j < i]} E_ij`, an element of the Iwahori order. -/
def iwahoriUnit (p : Fin N × Fin N) : iwahoriOrder F N :=
  ⟨Matrix.single p.1 p.2 (unitScale F N p), fun i j hij => by
    by_cases h : p.1 = i ∧ p.2 = j
    · obtain ⟨rfl, rfl⟩ := h
      simp only [Matrix.single_apply_same, unitScale, hij, ↓reduceIte]
      exact (IsLocalRing.mem_maximalIdeal _).mpr (iwahoriUniformizer_irreducible F).not_isUnit
    · rw [Matrix.single_apply_of_ne (h := h)]
      exact Ideal.zero_mem _⟩

theorem iwahoriUnit_coe (p : Fin N × Fin N) :
    (iwahoriUnit F N p : Matrix (Fin N) (Fin N) 𝒪[F]) = Matrix.single p.1 p.2 (unitScale F N p) :=
  rfl

theorem coe_sum_smul_iwahoriUnit (g : Fin N × Fin N → 𝒪[F]) (i j : Fin N) :
    ((∑ p, g p • iwahoriUnit F N p : iwahoriOrder F N) : Matrix (Fin N) (Fin N) 𝒪[F]) i j =
      g (i, j) * unitScale F N (i, j) := by
  rw [AddSubmonoidClass.coe_finsetSum, Matrix.sum_apply, Finset.sum_eq_single (i, j)]
  · rw [SetLike.val_smul, iwahoriUnit_coe, Matrix.smul_apply, Matrix.single_apply_same,
      smul_eq_mul]
  · intro q _ hq
    rw [SetLike.val_smul, iwahoriUnit_coe, Matrix.smul_apply, Matrix.single_apply_of_ne
      (h := fun h => hq (Prod.ext h.1 h.2)), smul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem iwahoriUnit_linearIndependent : LinearIndependent 𝒪[F] (iwahoriUnit F N) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg p
  have h := congrArg (fun M : iwahoriOrder F N => (M : Matrix (Fin N) (Fin N) 𝒪[F]) p.1 p.2) hg
  change ((∑ q, g q • iwahoriUnit F N q : iwahoriOrder F N) : Matrix (Fin N) (Fin N) 𝒪[F])
    p.1 p.2 = ((0 : iwahoriOrder F N) : Matrix (Fin N) (Fin N) 𝒪[F]) p.1 p.2 at h
  rw [coe_sum_smul_iwahoriUnit] at h
  simpa [unitScale_ne_zero] using h

theorem iwahoriUnit_span : ⊤ ≤ Submodule.span 𝒪[F] (Set.range (iwahoriUnit F N)) := by
  rintro M -
  have hdiv : ∀ p : Fin N × Fin N, ∃ c : 𝒪[F],
      (M : Matrix (Fin N) (Fin N) 𝒪[F]) p.1 p.2 = c * unitScale F N p := by
    intro p
    by_cases h : p.2 < p.1
    · have hm := M.2 p.1 p.2 h
      rw [(iwahoriUniformizer_irreducible F).maximalIdeal_eq, Ideal.mem_span_singleton'] at hm
      obtain ⟨c, hc⟩ := hm
      exact ⟨c, by simp only [unitScale, h, ↓reduceIte]; exact hc.symm⟩
    · exact ⟨(M : Matrix (Fin N) (Fin N) 𝒪[F]) p.1 p.2, by
        simp only [unitScale, h, ↓reduceIte, mul_one]⟩
  choose c hc using hdiv
  have hM : M = ∑ p, c p • iwahoriUnit F N p := by
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    rw [coe_sum_smul_iwahoriUnit, ← hc (i, j)]
  rw [hM]
  exact Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, rfl⟩)

/-- The basis of the Iwahori order by scaled matrix units. -/
def iwahoriUnitBasis : Module.Basis (Fin N × Fin N) 𝒪[F] (iwahoriOrder F N) :=
  Module.Basis.mk (iwahoriUnit_linearIndependent F N) (iwahoriUnit_span F N)

theorem iwahoriUnitBasis_apply (p : Fin N × Fin N) :
    iwahoriUnitBasis F N p = iwahoriUnit F N p :=
  Module.Basis.mk_apply _ _ _

theorem coe_apply_eq_repr_mul (x : iwahoriOrder F N) (i j : Fin N) :
    (x : Matrix (Fin N) (Fin N) 𝒪[F]) i j =
      (iwahoriUnitBasis F N).repr x (i, j) * unitScale F N (i, j) := by
  conv_lhs => rw [← (iwahoriUnitBasis F N).sum_repr x]
  simp only [iwahoriUnitBasis_apply]
  exact coe_sum_smul_iwahoriUnit F N _ i j

theorem iwahoriUnit_mul_coe (p q : Fin N × Fin N) :
    ((iwahoriUnit F N p * iwahoriUnit F N q : iwahoriOrder F N) :
        Matrix (Fin N) (Fin N) 𝒪[F]) =
      if p.2 = q.1 then Matrix.single p.1 q.2 (unitScale F N p * unitScale F N q) else 0 := by
  rw [Subalgebra.coe_mul, iwahoriUnit_coe, iwahoriUnit_coe]
  split_ifs with h
  · rw [h, Matrix.single_mul_single_same]
  · rw [Matrix.single_mul_single_of_ne (h := h)]

/-- Comparing numbers of uniformizers: `s p * s q = u * s m` with `u` a unit forces the counts of
strictly lower positions to agree. -/
theorem lowerCount_eq_of_unitScale (p q m : Fin N × Fin N) (u : 𝒪[F]) (hu : IsUnit u)
    (h : unitScale F N p * unitScale F N q = u * unitScale F N m) :
    ((if p.2 < p.1 then 1 else 0) + (if q.2 < q.1 then 1 else 0) : ℕ) =
      (if m.2 < m.1 then 1 else 0) := by
  have hϖ := iwahoriUniformizer_irreducible F
  have hnu := hϖ.not_isUnit
  have hne := hϖ.ne_zero
  unfold unitScale at h
  by_cases hp : p.2 < p.1 <;> by_cases hq : q.2 < q.1 <;> by_cases hm : m.2 < m.1 <;>
    simp only [hp, hq, hm, ↓reduceIte, mul_one, one_mul] at h ⊢
  · -- ϖ * ϖ = u * ϖ
    exact absurd (mul_right_cancel₀ hne h ▸ hu) hnu
  · -- ϖ * ϖ = u
    exact absurd (isUnit_of_mul_isUnit_left (h ▸ hu)) hnu
  · -- ϖ = u
    exact absurd (h ▸ hu) hnu
  · -- ϖ = u
    exact absurd (h ▸ hu) hnu
  · -- 1 = u * ϖ
    exact absurd (isUnit_of_mul_isUnit_right (h ▸ isUnit_one)) hnu

/-- If the coordinate at `m` of a product of two scaled matrix units is a unit, the product is
supported at `m` and the numbers of uniformizers agree. -/
theorem isUnit_repr_iwahoriUnit_mul (p q m : Fin N × Fin N)
    (h : IsUnit ((iwahoriUnitBasis F N).repr (iwahoriUnit F N p * iwahoriUnit F N q) m)) :
    p.2 = q.1 ∧ m = (p.1, q.2) ∧
      ((if p.2 < p.1 then 1 else 0) + (if q.2 < q.1 then 1 else 0) : ℕ) =
        (if m.2 < m.1 then 1 else 0) := by
  have hentry := coe_apply_eq_repr_mul F N (iwahoriUnit F N p * iwahoriUnit F N q) m.1 m.2
  rw [iwahoriUnit_mul_coe] at hentry
  have hne : (iwahoriUnitBasis F N).repr (iwahoriUnit F N p * iwahoriUnit F N q) (m.1, m.2) *
      unitScale F N (m.1, m.2) ≠ 0 :=
    mul_ne_zero h.ne_zero (unitScale_ne_zero F N _)
  rw [← hentry] at hne
  split_ifs at hentry hne with h1
  · by_cases h2 : p.1 = m.1 ∧ q.2 = m.2
    · have hm : m = (p.1, q.2) := Prod.ext h2.1.symm h2.2.symm
      subst hm
      refine ⟨h1, rfl, ?_⟩
      rw [Matrix.single_apply_same] at hentry
      exact lowerCount_eq_of_unitScale F N p q (p.1, q.2) _ h hentry
    · rw [Matrix.single_apply_of_ne (h := h2)] at hne
      exact absurd rfl hne
  · exact absurd (Matrix.zero_apply _ _) hne

/-! ### Weights of the off-diagonal scaled matrix units -/

/-- The weight `(j - i) mod N` of the off-diagonal position `(i, j)`. -/
def offWeight (p : Fin N × Fin N) : ℕ :=
  if p.1 < p.2 then p.2.val - p.1.val else N + p.2.val - p.1.val

theorem one_le_offWeight (p : Fin N × Fin N) (hp : p.1 ≠ p.2) : 1 ≤ offWeight N p := by
  unfold offWeight
  have h1 := p.1.isLt
  have h2 := p.2.isLt
  have hne : p.1.val ≠ p.2.val := fun h => hp (Fin.ext h)
  split_ifs with h
  · rw [Fin.lt_def] at h
    omega
  · omega

theorem offWeight_add (i j l : Fin N) (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l)
    (hc : ((if j < i then 1 else 0) + (if l < j then 1 else 0) : ℕ) = (if l < i then 1 else 0)) :
    offWeight N (i, j) + offWeight N (j, l) = offWeight N (i, l) := by
  unfold offWeight
  have hi := i.isLt
  have hj := j.isLt
  have hl := l.isLt
  have hij' : i.val ≠ j.val := fun h => hij (Fin.ext h)
  have hjl' : j.val ≠ l.val := fun h => hjl (Fin.ext h)
  have hil' : i.val ≠ l.val := fun h => hil (Fin.ext h)
  simp only [Fin.lt_def] at hc ⊢
  split_ifs at hc ⊢ <;> omega

/-! ### The adapted basis of the special-fibre algebra -/

/-- The off-diagonal positions. -/
abbrev OffDiag : Type := {p : Fin N × Fin N // p.1 ≠ p.2}

/-- The number of off-diagonal positions. -/
abbrev offCount : ℕ := Fintype.card (OffDiag N)

/-- Positions split into the diagonal and the off-diagonal ones. -/
def posEquiv : Fin N × Fin N ≃ Fin N ⊕ Fin (offCount N) where
  toFun p := if h : p.1 = p.2 then Sum.inl p.1 else Sum.inr (Fintype.equivFin (OffDiag N) ⟨p, h⟩)
  invFun := Sum.elim (fun i => (i, i)) (fun j => ((Fintype.equivFin (OffDiag N)).symm j).1)
  left_inv p := by
    by_cases h : p.1 = p.2
    · simp only [h, ↓reduceDIte, Sum.elim_inl]
      exact Prod.ext h.symm rfl
    · simp [h]
  right_inv x := by
    rcases x with i | j
    · simp
    · have h := ((Fintype.equivFin (OffDiag N)).symm j).2
      simp [h]

theorem posEquiv_symm_inl (i : Fin N) : (posEquiv N).symm (Sum.inl i) = (i, i) := rfl

theorem posEquiv_symm_inr (j : Fin (offCount N)) :
    (posEquiv N).symm (Sum.inr j) = ((Fintype.equivFin (OffDiag N)).symm j).1 := rfl

theorem posEquiv_symm_inr_ne (j : Fin (offCount N)) :
    ((posEquiv N).symm (Sum.inr j)).1 ≠ ((posEquiv N).symm (Sum.inr j)).2 :=
  ((Fintype.equivFin (OffDiag N)).symm j).2

/-- The basis of scaled matrix units, over `CommRingCat.of 𝒪[F]`. -/
abbrev iwahoriUnitBasisCat :
    Module.Basis (Fin N × Fin N) (CommRingCat.of 𝒪[F]) (iwahoriOrder F N) :=
  iwahoriUnitBasis F N

/-- The adapted basis of the special-fibre algebra `𝓀[F] ⊗ Λ`: diagonal units first. -/
def specialBasis :
    Module.Basis (Fin N ⊕ Fin (offCount N)) (CommRingCat.of 𝓀[F])
      ((CommRingCat.of 𝓀[F]) ⊗[CommRingCat.of 𝒪[F]] iwahoriOrder F N) :=
  ((iwahoriUnitBasisCat F N).baseChange (CommRingCat.of 𝓀[F])).reindex (posEquiv N)

theorem specialBasis_apply (x : Fin N ⊕ Fin (offCount N)) :
    specialBasis F N x = 1 ⊗ₜ iwahoriUnit F N ((posEquiv N).symm x) := by
  simp [specialBasis, iwahoriUnitBasisCat, iwahoriUnitBasis_apply]

theorem specialBasis_repr_mul (x y z : Fin N ⊕ Fin (offCount N)) :
    (specialBasis F N).repr (specialBasis F N x * specialBasis F N y) z =
      IsLocalRing.residue 𝒪[F] ((iwahoriUnitBasis F N).repr
        (iwahoriUnit F N ((posEquiv N).symm x) * iwahoriUnit F N ((posEquiv N).symm y))
        ((posEquiv N).symm z)) := by
  rw [specialBasis_apply, specialBasis_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  rw [specialBasis, Module.Basis.repr_reindex_apply, Module.Basis.baseChange_repr_tmul,
    Algebra.smul_def, mul_one]
  rfl

/-- The weight of a kernel basis vector of the special-fibre algebra. -/
abbrev specialWeight (j : Fin (offCount N)) : ℕ := offWeight N ((posEquiv N).symm (Sum.inr j))

theorem one_le_specialWeight (j : Fin (offCount N)) : 1 ≤ specialWeight N j :=
  one_le_offWeight N _ (posEquiv_symm_inr_ne N j)

/-- The weights are adapted to the products of the kernel basis vectors. -/
theorem specialWeight_le (a a' m : Fin (offCount N))
    (h : (specialBasis F N).repr (specialBasis F N (Sum.inr a) * specialBasis F N (Sum.inr a'))
      (Sum.inr m) ≠ 0) :
    specialWeight N a + specialWeight N a' ≤ specialWeight N m := by
  rw [specialBasis_repr_mul, IsLocalRing.residue_ne_zero_iff_isUnit] at h
  obtain ⟨h1, h2, h3⟩ := isUnit_repr_iwahoriUnit_mul F N _ _ _ h
  have hp := posEquiv_symm_inr_ne N a
  have hq := posEquiv_symm_inr_ne N a'
  have hm := posEquiv_symm_inr_ne N m
  set p := (posEquiv N).symm (Sum.inr a)
  set q := (posEquiv N).symm (Sum.inr a')
  set m' := (posEquiv N).symm (Sum.inr m)
  rw [h2] at hm h3
  rw [← h1] at h3
  dsimp only at hm h3
  have hpq : p.2 ≠ q.2 := by rw [h1]; exact hq
  have hadd := offWeight_add N p.1 p.2 q.2 hp hpq hm h3
  have hq' : q = (p.2, q.2) := Prod.ext h1.symm rfl
  simp only [specialWeight]
  rw [show (posEquiv N).symm (Sum.inr m) = (p.1, q.2) from h2]
  rw [show (posEquiv N).symm (Sum.inr a') = (p.2, q.2) from hq']
  exact hadd.le

/-! ### The diagonal quotient of the special-fibre algebra and its section -/

/-- The special-fibre algebra `𝓀[F] ⊗ Λ`. -/
abbrev SpecialAlgebra : Type u := (CommRingCat.of 𝓀[F]) ⊗[CommRingCat.of 𝒪[F]] iwahoriOrder F N

/-- The diagonal quotient `𝓀[F] ⊗ Λ → 𝓀[F]^N`, the base change of `diagResidue`. -/
def specialDiag : SpecialAlgebra F N →ₐ[CommRingCat.of 𝓀[F]] (Fin N → 𝓀[F]) :=
  Algebra.TensorProduct.lift (Algebra.ofId _ _) (diagResidue F N) fun _ _ => Commute.all _ _

theorem specialDiag_one_tmul (x : iwahoriOrder F N) :
    specialDiag F N (1 ⊗ₜ x) = diagResidue F N x := by
  simp [specialDiag]

theorem diagResidue_iwahoriUnit (p : Fin N × Fin N) (k : Fin N) :
    diagResidue F N (iwahoriUnit F N p) k =
      if p.1 = k ∧ p.2 = k then IsLocalRing.residue 𝒪[F] (unitScale F N p) else 0 := by
  change IsLocalRing.residue 𝒪[F] (Matrix.single p.1 p.2 (unitScale F N p) k k) = _
  simp only [Matrix.single, Matrix.of_apply]
  split_ifs <;> simp

theorem specialDiag_inl (i : Fin N) :
    specialDiag F N (specialBasis F N (Sum.inl i)) = Pi.basisFun 𝓀[F] (Fin N) i := by
  rw [specialBasis_apply, specialDiag_one_tmul, posEquiv_symm_inl]
  funext k
  rw [diagResidue_iwahoriUnit, Pi.basisFun_apply]
  by_cases h : i = k
  · subst h
    simp [unitScale]
  · simp [h, Ne.symm h]

theorem specialDiag_inr (j : Fin (offCount N)) :
    specialDiag F N (specialBasis F N (Sum.inr j)) = 0 := by
  rw [specialBasis_apply, specialDiag_one_tmul]
  funext k
  rw [diagResidue_iwahoriUnit, Pi.zero_apply]
  have hne := posEquiv_symm_inr_ne N j
  split_ifs with h
  · exact absurd (h.1.trans h.2.symm) hne
  · rfl

theorem iwahoriUnit_diag_mul (i j : Fin N) :
    iwahoriUnit F N (i, i) * iwahoriUnit F N (j, j) =
      if i = j then iwahoriUnit F N (i, i) else 0 := by
  apply Subtype.ext
  rw [iwahoriUnit_mul_coe]
  split_ifs with h
  · subst h
    simp [iwahoriUnit_coe, unitScale]
  · rfl

theorem sum_iwahoriUnit_diag : ∑ i, iwahoriUnit F N (i, i) = 1 := by
  have hsum : ∑ i, iwahoriUnit F N (i, i) =
      ∑ p, (if p.1 = p.2 then (1 : 𝒪[F]) else 0) • iwahoriUnit F N p := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [Ne.symm hj]
    · intro h
      exact absurd (Finset.mem_univ i) h
  rw [hsum]
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  rw [coe_sum_smul_iwahoriUnit]
  change _ = (1 : Matrix (Fin N) (Fin N) 𝒪[F]) i j
  by_cases h : i = j
  · subst h
    simp [unitScale]
  · simp [h, Matrix.one_apply_ne h]

/-- The diagonal section `𝓀[F]^N → 𝓀[F] ⊗ Λ`, `v ↦ Σ_i v_i ⊗ E_ii`, as a linear map. -/
def specialSectionLinear :
    (Fin N → 𝓀[F]) →ₗ[CommRingCat.of 𝓀[F]] SpecialAlgebra F N where
  toFun v := ∑ i, v i • specialBasis F N (Sum.inl i)
  map_add' v v' := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c v := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum, mul_smul]

/-- The diagonal section as an algebra map. -/
def specialSection : (Fin N → 𝓀[F]) →ₐ[CommRingCat.of 𝓀[F]] SpecialAlgebra F N :=
  AlgHom.ofLinearMap (specialSectionLinear F N)
    (by
      change ∑ i, (1 : 𝓀[F]) • specialBasis F N (Sum.inl i) = 1
      simp only [one_smul]
      rw [Finset.sum_congr rfl (fun i _ => specialBasis_apply F N (Sum.inl i))]
      simp only [posEquiv_symm_inl]
      rw [← TensorProduct.tmul_sum, sum_iwahoriUnit_diag]
      rfl)
    (by
      intro v v'
      change ∑ i, (v i * v' i) • specialBasis F N (Sum.inl i) =
        (∑ i, v i • specialBasis F N (Sum.inl i)) * ∑ j, v' j • specialBasis F N (Sum.inl j)
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum, Finset.sum_eq_single i]
      · rw [smul_mul_smul_comm, specialBasis_apply, posEquiv_symm_inl,
          Algebra.TensorProduct.tmul_mul_tmul, mul_one, iwahoriUnit_diag_mul]
        simp
      · intro j _ hj
        rw [smul_mul_smul_comm, specialBasis_apply, specialBasis_apply, posEquiv_symm_inl,
          posEquiv_symm_inl, Algebra.TensorProduct.tmul_mul_tmul, mul_one, iwahoriUnit_diag_mul]
        simp [Ne.symm hj]
      · intro h
        exact absurd (Finset.mem_univ i) h)

theorem specialDiag_comp_specialSection :
    (specialDiag F N).comp (specialSection F N) = AlgHom.id _ (Fin N → 𝓀[F]) := by
  apply AlgHom.toLinearMap_injective
  apply (Pi.basisFun (CommRingCat.of 𝓀[F]) (Fin N)).ext
  intro i
  rw [Pi.basisFun_apply]
  change specialDiag F N (∑ k, (Pi.single i (1 : 𝓀[F]) : Fin N → 𝓀[F]) k •
    specialBasis F N (Sum.inl k)) = Pi.single i 1
  rw [Finset.sum_eq_single i]
  · rw [Pi.single_eq_same, one_smul, specialDiag_inl, Pi.basisFun_apply]
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj, zero_smul]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-! ### The reductive quotient of the special fibre -/

section ReductiveQuotient

open GroupScheme GroupScheme.FiniteFreeAlgebraUnits

/-- The standard basis of the diagonal algebra `𝓀[F]^N`. -/
abbrev diagBasis : Module.Basis (Fin N) (CommRingCat.of 𝓀[F]) (Fin N → 𝓀[F]) :=
  Pi.basisFun (CommRingCat.of 𝓀[F]) (Fin N)

theorem specialDiag_basis_inl (i : Fin N) :
    specialDiag F N (specialBasis F N (Sum.inl i)) = diagBasis F N i :=
  specialDiag_inl F N i

theorem specialWeight_le_of_structureConst (a a' m : Fin (offCount N))
    (h : UnipotentPart.structureConst (specialBasis F N) a a' m ≠ 0) :
    specialWeight N a + specialWeight N a' ≤ specialWeight N m :=
  specialWeight_le F N a a' m h

/-- The universal radical element of the special-fibre algebra is nilpotent. -/
theorem specialRadical_nilpotent :
    IsNilpotent (UnipotentPart.universalRadical (specialBasis F N)) :=
  UnipotentPart.isNilpotent_universalRadical_of_weights (specialDiag F N) (specialBasis F N)
    (diagBasis F N) (specialWeight N) (specialDiag_basis_inl F N) (specialDiag_inr F N)
    (one_le_specialWeight N) (specialWeight_le F N)

/-- The unipotent kernel `1 + J` of the reduction of the special-fibre algebra to its diagonal. -/
abbrev specialRadical : GroupScheme (Spec (CommRingCat.of 𝓀[F])) :=
  UnipotentPart.groupScheme (specialDiag F N) (specialBasis F N) (specialRadical_nilpotent F N)
    (specialDiag_inr F N) (diagBasis F N) (specialDiag_basis_inl F N)

/-- The unit group of the diagonal algebra `𝓀[F]^N`, a split torus. -/
abbrev diagTorus : GroupScheme (Spec (CommRingCat.of 𝓀[F])) :=
  FiniteFreeAlgebraUnits.groupScheme (diagBasis F N)

/-- The inclusion of the unipotent kernel into the unit group of the special-fibre algebra. -/
abbrev specialRadicalInclusion :
    specialRadical F N ⟶
      FiniteFreeAlgebraUnits.groupScheme (UnipotentPart.flatBasis (specialBasis F N)) :=
  UnipotentPart.radicalInclusion (specialDiag F N) (specialBasis F N)
    (specialRadical_nilpotent F N) (specialDiag_inr F N) (diagBasis F N) (specialDiag_basis_inl F N)

/-- The unit-group map of the diagonal reduction. -/
abbrev specialDiagMap :
    FiniteFreeAlgebraUnits.groupScheme (UnipotentPart.flatBasis (specialBasis F N)) ⟶
      diagTorus F N :=
  UnipotentPart.unitMap (specialDiag F N) (specialBasis F N) (diagBasis F N)

theorem specialRadical_isUnipotentRadical :
    IsUnipotentRadical (specialRadicalInclusion F N) ∧
      RelativeRoot.IsFppfQuotient (SubgroupFunctor.range (specialRadicalInclusion F N))
        (specialDiagMap F N) :=
  UnipotentPart.isUnipotentRadical (specialDiag F N) (specialBasis F N)
    (specialRadical_nilpotent F N) (specialDiag_inr F N) (diagBasis F N) (specialDiag_basis_inl F N)
    (specialWeight N) (specialWeight_le_of_structureConst F N) (one_le_specialWeight N)
    (specialSection F N) (specialDiag_comp_specialSection F N) (isTorus_pi N 𝓀[F])

/-- The special fibre of the Iwahori model is the unit group of `𝓀[F] ⊗ Λ`, with the adapted
basis. -/
def specialFibreIso :
    (iwahoriModelData F N).neutral.specialFibre ≅
      FiniteFreeAlgebraUnits.groupScheme (UnipotentPart.flatBasis (specialBasis F N)) :=
  baseChangeIso (iwahoriBasis F N) (CommRingCat.of 𝓀[F]) ≪≫
    congrIso ((iwahoriBasis F N).baseChange (CommRingCat.of 𝓀[F]))
      (UnipotentPart.flatBasis (specialBasis F N)) AlgEquiv.refl

/-- The reductive quotient of the special fibre of the Iwahori model: the radical is the unipotent
kernel `1 + J` and the quotient is the diagonal torus. -/
def iwahoriQuotientData : SpecialFibreQuotientData (iwahoriModelData F N) where
  radical := specialRadical F N
  radicalInclusion := specialRadicalInclusion F N ≫ (specialFibreIso F N).inv
  quotient := diagTorus F N
  quotient_affine := groupScheme_isAffineHom _
  projection := (specialFibreIso F N).hom ≫ specialDiagMap F N

/-- The Iwahori quotient data is a reductive quotient. -/
theorem iwahoriQuotientData_isReductiveQuotient :
    (iwahoriQuotientData F N).IsReductiveQuotient := by
  obtain ⟨h1, h2⟩ := specialRadical_isUnipotentRadical F N
  refine ⟨h1.comp_iso (specialFibreIso F N).symm, ?_,
    (isSplitTorus_pi (CommRingCat.of 𝓀[F]) N).isConnectedReductive⟩
  change RelativeRoot.IsFppfQuotient
    (SubgroupFunctor.range (specialRadicalInclusion F N ≫ (specialFibreIso F N).symm.hom))
    ((specialFibreIso F N).symm.inv ≫ specialDiagMap F N)
  rw [SubgroupFunctor.range_comp_iso]
  exact h2.comapIso (specialFibreIso F N).symm

/-! ### The positive subgroup is `I^+` -/

/-- For a reductive quotient, a special-fibre point lies in the radical exactly when its
projection is trivial. -/
theorem SpecialFibreQuotientData.mem_radicalPoints_iff {R K : Type u} [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] [IsLocalRing R]
    {G : GroupScheme (Spec (CommRingCat.of K))} {D : RelativeComponentModelData R K G}
    (Q : SpecialFibreQuotientData D) (hQ : Q.IsReductiveQuotient)
    (y : rationalPoints D.neutral.specialFibre) :
    y ∈ Q.radicalPoints ↔ y ≫ Q.projection.hom.hom = 1 := by
  rw [← mem_range_kernelι_iff, hQ.2.1.2.2.2]
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨z, rfl⟩
  · rintro ⟨z, rfl⟩
    exact ⟨z, rfl⟩

/-- The unit of the Iwahori order attached to an integral section of the Iwahori model. -/
abbrev sectionUnit (x : (iwahoriModelData F N).neutral.integralSections) : (iwahoriOrder F N)ˣ :=
  sectionUnitsEquiv (R := CommRingCat.of 𝒪[F]) (iwahoriBasis F N) x

/-- The reduction of an integral section has trivial projection to the diagonal torus exactly
when the diagonal entries of its unit are `1` modulo the maximal ideal. -/
theorem reduction_projection_eq_one_iff
    (x : (iwahoriModelData F N).neutral.integralSections) :
    (iwahoriModelData F N).neutral.reduction x ≫
        (iwahoriQuotientData F N).projection.hom.hom = 1 ↔
      ∀ i : Fin N, IsLocalRing.residue 𝒪[F]
        (((sectionUnit F N x : iwahoriOrder F N) : Matrix (Fin N) (Fin N) 𝒪[F]) i i) = 1 := by
  have hcomp : (iwahoriModelData F N).neutral.reduction x ≫
        (iwahoriQuotientData F N).projection.hom.hom =
      (((baseChangeSectionHom (WeilGm.baseMap (CommRingCat.of 𝒪[F]) (CommRingCat.of 𝓀[F]))
          (FiniteFreeAlgebraUnits.groupScheme (iwahoriBasis F N)) x) ≫
          (baseChangeIso (iwahoriBasis F N) (CommRingCat.of 𝓀[F])).hom.hom.hom) ≫
        (congrIso ((iwahoriBasis F N).baseChange (CommRingCat.of 𝓀[F]))
          (UnipotentPart.flatBasis (specialBasis F N)) AlgEquiv.refl).hom.hom.hom) ≫
        (specialDiagMap F N).hom.hom :=
    (show _ = (baseChangeSectionHom (WeilGm.baseMap (CommRingCat.of 𝒪[F]) (CommRingCat.of 𝓀[F]))
        (FiniteFreeAlgebraUnits.groupScheme (iwahoriBasis F N)) x) ≫
        (((baseChangeIso (iwahoriBasis F N) (CommRingCat.of 𝓀[F])).hom.hom.hom ≫
        (congrIso ((iwahoriBasis F N).baseChange (CommRingCat.of 𝓀[F]))
          (UnipotentPart.flatBasis (specialBasis F N)) AlgEquiv.refl).hom.hom.hom) ≫
        (specialDiagMap F N).hom.hom) from rfl).trans (by simp only [Category.assoc])
  have key := baseChange_congr_map_eq_one_iff (iwahoriBasis F N) (CommRingCat.of 𝓀[F])
    (UnipotentPart.flatBasis (specialBasis F N)) AlgEquiv.refl (diagBasis F N) (specialDiag F N) x
  rw [hcomp]
  refine key.trans ?_
  rw [AlgEquiv.coe_refl, id_eq, specialDiag_one_tmul, funext_iff]
  rfl

/-- The matrix of the generic point of an integral section of the Iwahori model is its unit,
with entries mapped to `F`. -/
theorem iwahoriIntegralPointMap_matrix (x : (iwahoriModelData F N).neutral.integralSections) :
    (GeneralLinear.rationalPointsEquiv N (CommRingCat.of F)
        ((iwahoriModelData F N).neutral.integralPointMap x) : Matrix (Fin N) (Fin N) F) =
      ((sectionUnit F N x : iwahoriOrder F N) : Matrix (Fin N) (Fin N) 𝒪[F]).map
        (algebraMap 𝒪[F] F) := by
  delta iwahoriModelData
  refine orderModelData_integralPointMap_of_eq x ?_
  rw [iwahoriInclusion_apply]

/-- **The positive subgroup of the Iwahori quotient data is `I^+`**: the preimage in
`GL_N(𝒪[F])` of the upper unipotent group `U(𝓀[F])`. -/
theorem iwahoriQuotientData_positivePoints :
    (iwahoriQuotientData F N).positivePoints = generalLinearIwahoriPositivePoints F N := by
  have hQ := iwahoriQuotientData_isReductiveQuotient F N
  ext g
  rw [SpecialFibreQuotientData.mem_positivePoints, mem_generalLinearIwahoriPositivePoints]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [SpecialFibreQuotientData.mem_radicalPoints_iff _ hQ, reduction_projection_eq_one_iff] at hx
    refine ⟨Units.map (iwahoriOrder F N).val.toMonoidHom (sectionUnit F N x),
      ⟨fun i j hij => (sectionUnit F N x : iwahoriOrder F N).2 i j hij, fun i => ?_⟩, ?_⟩
    · rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_one, sub_eq_zero]
      exact hx i
    · apply Units.ext
      rw [iwahoriIntegralPointMap_matrix]
      rfl
  · rintro ⟨v, ⟨hl, hd⟩, hg⟩
    have hI : g ∈ (iwahoriModel F N).integralPoints := by
      rw [iwahoriModel_integralPoints, mem_generalLinearIwahoriPoints]
      exact ⟨v, hl, hg⟩
    obtain ⟨x, hx⟩ : ∃ x : (iwahoriModelData F N).neutral.integralSections,
        (iwahoriModelData F N).neutral.integralPointMap x = g := hI
    refine ⟨x, ?_, hx⟩
    rw [SpecialFibreQuotientData.mem_radicalPoints_iff _ hQ, reduction_projection_eq_one_iff]
    intro i
    have hm := congrArg (fun M : Matrix (Fin N) (Fin N) F => M i i)
      (iwahoriIntegralPointMap_matrix F N x)
    have hm' : (GeneralLinear.rationalPointsEquiv N (CommRingCat.of F) g :
        Matrix (Fin N) (Fin N) F) i i =
          algebraMap 𝒪[F] F (((sectionUnit F N x : iwahoriOrder F N) :
            Matrix (Fin N) (Fin N) 𝒪[F]) i i) := by
      rw [← hx]
      exact hm
    rw [hg] at hm'
    have heq : ((sectionUnit F N x : iwahoriOrder F N) : Matrix (Fin N) (Fin N) 𝒪[F]) i i =
        (v : Matrix (Fin N) (Fin N) 𝒪[F]) i i :=
      IsFractionRing.injective 𝒪[F] F hm'.symm
    rw [heq, ← sub_eq_zero, ← map_one (IsLocalRing.residue 𝒪[F]), ← map_sub,
      IsLocalRing.residue_eq_zero_iff]
    exact hd i

end ReductiveQuotient

end Langlands.BruhatTits.IntegralModels
