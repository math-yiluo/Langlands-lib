import Langlands.GroupScheme.Reductive.LocalRootParametrizationRigidity
import Langlands.GroupScheme.Reductive.LocalSplitRootTransport
import Langlands.GroupScheme.Torus.RelativeAdjointWeights
import Langlands.GroupScheme.Rational.TorusActionBridge
import Langlands.GroupScheme.Rational.RootKernelIdentityWeights
import Langlands.GroupScheme.HopfPrimitiveQuotient

/-! # Derivatives of root parametrizations over an arbitrary ring -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme.LocalSplitCell

variable {R : Type u} [CommRing R]

local instance affineRootLieGaIsAffineHom : IsAffineHom (Ga R).X.hom := VectorGroup.isAffineHom_groupScheme (CommRingCat.of R) 1

section Dual

/-- The dual-number test scheme `Spec A[ε]` over `Spec R`. -/
abbrev dualTest (A : Type u) [CommRing A] [Algebra R A] : Over (Spec (CommRingCat.of R)) :=
  (algSpec (CommRingCat.of R)).obj (op (CommAlgCat.of (CommRingCat.of R) (DualNumber A)))

/-- The global function `c ε` on `Spec A[ε]`. -/
def dualSection (A : Type u) [CommRing A] [Algebra R A] (c : A) :
    Γ((dualTest (R := R) A).left, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of (DualNumber A))).inv (TrivSqZeroExt.inr c)

/-- Pullback of global functions of an affine test along the spectrum of an algebra map. -/
theorem algSpec_map_appTop {A B : Type u} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
    (f : A →ₐ[CommRingCat.of R] B) (a : A) :
    ((algSpec (CommRingCat.of R)).map (CommAlgCat.ofHom f).op).left.appTop
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a) =
      (Scheme.ΓSpecIso (CommRingCat.of B)).inv (f a) := by
  change (Spec.map (CommRingCat.ofHom f.toRingHom)).appTop _ = _
  rw [HopfPrimitive.appTop_specMap_inv]
  rfl

theorem dualSection_injective (A : Type u) [CommRing A] [Algebra R A] :
    Function.Injective (dualSection (R := R) A) := by
  intro c c' h
  have h' := congrArg (Scheme.ΓSpecIso (CommRingCat.of (DualNumber A))).hom h
  simp only [dualSection, Iso.inv_hom_id_apply] at h'
  exact TrivSqZeroExt.inr_injective h'

/-- The tangent vector `ε` of `𝔾ₐ`, with coefficients in `A`. -/
def gaEpsilon (A : Type u) [CommRing A] [Algebra R A] : Additive (lieKernel (Ga R) A) :=
  Additive.ofMul ⟨VectorGroup.scalarPoint (CommRingCat.of R) (dualTest A) (dualSection A 1), by
    change (algSpec _).map (CommAlgCat.ofHom (TrivSqZeroExt.fstHom _ A A)).op ≫ _ = 1
    rw [VectorGroup.scalarPoint_comp, dualSection, algSpec_map_appTop]
    apply VectorGroup.points_ext
    intro j
    rw [VectorGroup.coordinates_scalarPoint, map_one, toAdd_one, Pi.zero_apply]
    simp⟩

theorem gaEpsilon_val (A : Type u) [CommRing A] [Algebra R A] :
    (gaEpsilon (R := R) A).toMul.val =
      rootPoint (𝟙 (Ga R)) (dualTest A) (dualSection A 1) := by
  rw [rootPoint, Grp.id_hom_hom, Category.comp_id]
  rfl

variable {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]

/-- The derivative of a map from `𝔾ₐ` at `ε` is its dual-number root point. -/
theorem targetMap_gaEpsilon_val (v : Ga R ⟶ G) (A : Type u) [CommRing A] [Algebra R A] :
    (Lie.targetMapLinear v A (gaEpsilon A)).toMul.val =
      rootPoint v (dualTest A) (dualSection A 1) := rfl

/-- Epsilon scaling of a dual-number root point scales its coordinate. -/
theorem smul_val_of_val (v : Ga R ⟶ G) {A : Type u} [CommRing A] [Algebra R A]
    (Y : Additive (lieKernel G A))
    (hY : Y.toMul.val = rootPoint v (dualTest A) (dualSection A 1)) (c : A) :
    (c • Y).toMul.val = rootPoint v (dualTest A) (dualSection A c) := by
  rw [lieKernel_smul_toMul, lieKernelScale_val, Lie.affineMap_apply, hY, comp_rootPoint,
    dualSection, algSpec_map_appTop, dualSection]
  congr 2
  apply TrivSqZeroExt.ext <;>
    simp [GeneralLinear.DualNumber.epsilonScaleAlg]

/-- Coefficient change of a dual-number root point. -/
theorem lieKernelMapLinear_val_of_val (v : Ga R ⟶ G) {A B : Type u} [CommRing A] [Algebra R A]
    [CommRing B] [Algebra R B] (f : A →ₐ[CommRingCat.of R] B)
    (Y : Additive (lieKernel G A))
    (hY : Y.toMul.val = rootPoint v (dualTest A) (dualSection A 1)) :
    (lieKernelMapLinear G f Y).toMul.val = rootPoint v (dualTest B) (dualSection B 1) := by
  rw [lieKernelMapLinear_toMul, lieKernelMap_val, Lie.affineMap_apply, hY, comp_rootPoint,
    dualSection, algSpec_map_appTop, dualSection]
  congr 2
  apply TrivSqZeroExt.ext <;>
    simp [GeneralLinear.DualNumber.coefficientAlgMap, GeneralLinear.DualNumber.coefficientMap]

/-- The derivative of a rescaled map at `ε` is the rescaled derivative. -/
theorem targetMap_scaleHom_comp_gaEpsilon (v : Ga R ⟶ G) (s : R) :
    Lie.targetMapLinear (scaleHom s ≫ v) (CommRingCat.of R) (gaEpsilon _) =
      s • Lie.targetMapLinear v (CommRingCat.of R) (gaEpsilon _) := by
  apply Additive.toMul.injective
  apply Subtype.ext
  rw [smul_val_of_val v _ (targetMap_gaEpsilon_val v _), targetMap_gaEpsilon_val,
    rootPoint_scaleHom]
  congr 1
  rw [baseScalar, dualSection, dualSection]
  change (Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R)))).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv s) * _ = _
  rw [HopfPrimitive.appTop_specMap_inv, ← map_mul]
  congr 1
  change algebraMap R (DualNumber R) s * TrivSqZeroExt.inr 1 = _
  rw [TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.inl_mul_inr, smul_eq_mul, mul_one]

/-- Base-ring scalars are detected on the tangent vector `ε`. -/
theorem smul_gaEpsilon_injective {s s' : CommRingCat.of R}
    (h : (s • gaEpsilon (R := R) (CommRingCat.of R) :
        Additive (lieKernel (Ga R) (CommRingCat.of R))) = s' • gaEpsilon (CommRingCat.of R)) :
    s = s' := by
  have hv := congrArg (fun Y : Additive (lieKernel (Ga R) (CommRingCat.of R)) => Y.toMul.val) h
  simp only at hv
  rw [smul_val_of_val (𝟙 (Ga R)) _ (gaEpsilon_val _),
    smul_val_of_val (𝟙 (Ga R)) _ (gaEpsilon_val _)] at hv
  have hc := congrArg (fun x => gaCoord x) hv
  simp only [rootPoint, Grp.id_hom_hom, Category.comp_id, gaCoord,
    VectorGroup.coordinates_scalarPoint] at hc
  exact dualSection_injective _ hc

end Dual

section Weight

variable {I : Type u} [Fintype I]
  {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
  {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G} {m : I → ℤ} {u : Ga R ⟶ G}

/-- The derivative of a root parametrization at `ε` lies in the actual exponent
weight space of its root. -/
theorem IsRootParametrization.targetMap_gaEpsilon_mem (hu : IsRootParametrization i m u) :
    Lie.targetMapLinear u (CommRingCat.of R) (gaEpsilon _) ∈
      splitTorus.exponentWeightSpace I G i m := by
  intro A _ _ t
  have hY := lieKernelMapLinear_val_of_val u (Algebra.ofId (CommRingCat.of R) A) _
    (targetMap_gaEpsilon_val u (CommRingCat.of R))
  apply Additive.toMul.injective
  apply Subtype.ext
  rw [adjoint_val, smul_val_of_val u _ hY, hY]
  have hc : Lie.constant G ((splitTorus.algebraPointsEquiv I A).symm t ≫ i.hom.hom) =
      ((algSpec _).map (CommAlgCat.ofHom (TrivSqZeroExt.inlAlgHom _ A A)).op ≫
        (splitTorus.algebraPointsEquiv I A).symm t) ≫ i.hom.hom := by
    rw [Lie.constant, Lie.affineMap_apply, Category.assoc]
  rw [hc, hu.equivariant]
  congr 1
  rw [VectorGroup.charValue_comp]
  have hv := Corepresented.charValue_torusPt (R := CommRingCat.of R) (A := A) m t
  have hv' : VectorGroup.charValue (splitTorus.exponentCharacter _ I m)
      ((algSpec (CommRingCat.of R)).obj (op (CommAlgCat.of (CommRingCat.of R) A)))
      ((splitTorus.algebraPointsEquiv I A).symm t) =
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv
        (splitTorus.exponentValue I t (Multiplicative.ofAdd m) : A) := by
    rw [← hv, Iso.hom_inv_id_apply]
    rfl
  rw [hv', algSpec_map_appTop, dualSection, dualSection]
  change (Scheme.ΓSpecIso (CommRingCat.of (DualNumber A))).inv _ *
    (Scheme.ΓSpecIso (CommRingCat.of (DualNumber A))).inv _ = _
  rw [← map_mul]
  congr 1
  rw [TrivSqZeroExt.inlAlgHom_apply, TrivSqZeroExt.inl_mul_inr, smul_eq_mul, mul_one]

omit [IsAffineHom G.X.hom] in
/-- Two parametrizations of the same nonzero root differ by a base-ring scalar,
over an arbitrary commutative ring. -/
theorem IsRootParametrization.exists_scalar_of_ne_zero {v w : Ga R ⟶ G}
    (hv : IsRootParametrization i m v) (hw : IsRootParametrization i m w) (hm : m ≠ 0) :
    ∃ c : R, v = scaleHom c ≫ w := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hm
  have hd : 0 < ∑ k, (m k).natAbs ^ 2 :=
    lt_of_lt_of_le (pow_pos (Int.natAbs_pos.mpr hj) 2)
      (Finset.single_le_sum (fun k _ => Nat.zero_le ((m k).natAbs ^ 2)) (Finset.mem_univ j))
  have hpair : ∑ k, m k * m k = ((∑ k, (m k).natAbs ^ 2 : ℕ) : ℤ) := by
    push_cast
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [sq_abs, sq]
  exact hv.exists_scalar hw m hd hpair

/-- Two parametrizations of the same nonzero root with the same derivative at
`ε` are equal, over an arbitrary commutative ring. -/
theorem IsRootParametrization.eq_of_targetMap_gaEpsilon {v w : Ga R ⟶ G}
    (hv : IsRootParametrization i m v) (hw : IsRootParametrization i m w) (hm : m ≠ 0)
    (h : Lie.targetMapLinear v (CommRingCat.of R) (gaEpsilon _) =
      Lie.targetMapLinear w (CommRingCat.of R) (gaEpsilon _)) : v = w := by
  obtain ⟨c, hc⟩ := hv.exists_scalar_of_ne_zero hw hm
  have : Mono w.hom.hom := hw.represents.1
  have hc1 : c = 1 := by
    apply smul_gaEpsilon_injective (R := R) (s := c) (s' := 1)
    apply Lie.targetMapLinear_injective w (CommRingCat.of R)
    rw [LinearMap.map_smul, LinearMap.map_smul, one_smul]
    exact (targetMap_scaleHom_comp_gaEpsilon w c).symm.trans
      ((congrArg (fun x => Lie.targetMapLinear x (CommRingCat.of R) (gaEpsilon _)) hc.symm).trans h)
  rw [hc, hc1, scaleHom_one, Category.id_comp]

/-- An automorphism fixing the torus whose differential fixes the root weight
space of a nonzero root fixes every parametrization of that root. -/
theorem IsRootParametrization.comp_eq_of_fixes_weightSpace (hu : IsRootParametrization i m u)
    (hm : m ≠ 0) (σ : G ≅ G) (hσ : i ≫ σ.hom = i)
    (hfix : ∀ Y ∈ splitTorus.exponentWeightSpace I G i m,
      Lie.targetMapLinear σ.hom (CommRingCat.of R) Y = Y) :
    u ≫ σ.hom = u := by
  apply (hu.comp_iso σ hσ).eq_of_targetMap_gaEpsilon hu hm
  rw [Lie.targetMapLinear_comp, LinearMap.comp_apply, hfix _ hu.targetMap_gaEpsilon_mem]

/-- A differential fixing a generator of a free root line fixes the whole line. -/
theorem fixes_weightSpace_of_fixes_generator (σ : G ≅ G)
    (X : CommRingCat.of R ≃ₗ[CommRingCat.of R] splitTorus.exponentWeightSpace I G i m)
    (hX : Lie.targetMapLinear σ.hom (CommRingCat.of R) (X 1).val = (X 1).val) :
    ∀ Y ∈ splitTorus.exponentWeightSpace I G i m,
      Lie.targetMapLinear σ.hom (CommRingCat.of R) Y = Y := by
  intro Y hY
  obtain ⟨r, hr⟩ := X.surjective ⟨Y, hY⟩
  have hs := congrArg Subtype.val (X.map_smul r 1)
  rw [smul_eq_mul, mul_one, hr] at hs
  change Y = r • (X 1).val at hs
  rw [hs, LinearMap.map_smul, hX]

end Weight

/-- Differentiation of the identity homomorphism is the identity. -/
theorem _root_.Langlands.GroupScheme.Lie.targetMapLinear_id
    {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
    (A : Type u) [CommRing A] [Algebra R A] :
    Lie.targetMapLinear (𝟙 G) A = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Additive.toMul.injective
  apply Subtype.ext
  exact Category.comp_id _

end Langlands.GroupScheme.LocalSplitCell
