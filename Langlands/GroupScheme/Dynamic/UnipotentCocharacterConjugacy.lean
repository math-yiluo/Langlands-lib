import Langlands.CommutativeAlgebra.GradedCocycleExtension
import Langlands.GroupScheme.AffineLinearEmbedding.Coordinate
import Langlands.GroupScheme.Dynamic.CoactionContracting
import Langlands.GroupScheme.Dynamic.DominantCombinationInclusions
import Langlands.GroupScheme.InnerAutomorphism

/-! # Conjugacy of cocharacters differing by a point of the dynamic unipotent subgroup -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite TensorProduct
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace Corepresented

open CommutativeAlgebra.GradedDVRIntegrality CommutativeAlgebra.GradedCocycle AffineLine

variable {k : Type u} [Field k] {F : CommAlgCat.{u} (CommRingCat.of k) ⥤ GrpCat.{u}}
  {B : CommAlgCat.{u} (CommRingCat.of k)} (e : (F ⋙ forget GrpCat).CorepresentableBy B)

section Comultiplication

/-- The comultiplication `B → B ⊗ B`: the classifying map of the product of the two universal
points over `Spec (B ⊗ B)`. -/
def comul : B →ₐ[k] B ⊗[k] B :=
  AffineLinearEmbedding.comul e

variable {A : Type u} [CommRing A] [Algebra k A]

/-- The product of two algebra-valued points, computed through the comultiplication. -/
theorem homEquiv_productMap_comp_comul (φ ψ : B →ₐ[k] A) :
    e.homEquiv (CommAlgCat.ofHom ((Algebra.TensorProduct.productMap φ ψ).comp (comul e))) =
      (e.homEquiv (CommAlgCat.ofHom φ) : F.obj (CommAlgCat.of k A)) *
        e.homEquiv (CommAlgCat.ofHom ψ) :=
  AffineLinearEmbedding.pt_productMap_comp_comul e
    (A := CommAlgCat.of k A) φ ψ

/-- The point of `Spec B` over `Spec A` given by a `k`-algebra map `B → A`. -/
def algPoint (φ : B →ₐ[k] A) :
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k A))) ⟶ (groupScheme F e).X :=
  (algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom φ).op

theorem pointRing_algPoint (φ : B →ₐ[k] A) :
    pointRing (algPoint e φ) = CommRingCat.ofHom (φ : B →+* A) :=
  Spec.map_injective ((specMap_pointRing _).trans rfl)

theorem pointAlgHom_algPoint (φ : B →ₐ[k] A) : pointAlgHom (algPoint e φ) = φ :=
  AlgHom.ext fun b => by
    rw [pointAlgHom_apply, pointRing_algPoint]
    rfl

theorem algPoint_pointAlgHom
    (x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k A))) ⟶ (groupScheme F e).X) :
    algPoint e (pointAlgHom x) = x :=
  hom_ext_of_pointRing (CommRingCat.hom_ext (RingHom.ext fun b =>
    congrArg (fun φ : B →ₐ[k] A => φ b) (pointAlgHom_algPoint e (pointAlgHom x))))

theorem affinePointsEquiv_algPoint (φ : B →ₐ[k] A) :
    affinePointsEquiv F e (CommAlgCat.of k A) (algPoint e φ) = e.homEquiv (CommAlgCat.ofHom φ) :=
  affinePointsEquiv_map F e (CommAlgCat.of k A) (CommAlgCat.ofHom φ)

/-- The classifying map of a product of points is the product map of the classifying maps,
precomposed with the comultiplication. -/
theorem pointAlgHom_mul
    (x y : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k A))) ⟶ (groupScheme F e).X) :
    pointAlgHom (x * y) =
      (Algebra.TensorProduct.productMap (pointAlgHom x) (pointAlgHom y)).comp (comul e) := by
  have h : algPoint e ((Algebra.TensorProduct.productMap (pointAlgHom x) (pointAlgHom y)).comp
      (comul e)) = x * y := by
    apply (affinePointsEquiv F e (CommAlgCat.of k A)).injective
    rw [affinePointsEquiv_algPoint, homEquiv_productMap_comp_comul,
      ← affinePointsEquiv_algPoint, ← affinePointsEquiv_algPoint, algPoint_pointAlgHom,
      algPoint_pointAlgHom]
    exact (map_mul (affinePointsEquiv F e (CommAlgCat.of k A)) x y).symm
  rw [← h, pointAlgHom_algPoint]

/-- The identity point over `Spec A` is classified by the counit. -/
theorem pointAlgHom_one :
    pointAlgHom (1 : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k A))) ⟶
      (groupScheme F e).X) = (Algebra.ofId k A).comp (counitAlgHom e) := by
  refine AlgHom.ext fun b => ?_
  rw [pointAlgHom_apply, pointRing_one, Spec.preimage_map]
  rfl

theorem productMap_counit_comul :
    (Algebra.TensorProduct.productMap ((Algebra.ofId k B).comp (counitAlgHom e))
      (AlgHom.id k B)).comp (comul e) = AlgHom.id k B := by
  have h := pointAlgHom_mul e (1 : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k B))) ⟶
    (groupScheme F e).X) (algPoint e (AlgHom.id k B))
  rw [one_mul, pointAlgHom_one, pointAlgHom_algPoint] at h
  exact h.symm

theorem productMap_comul_counit :
    (Algebra.TensorProduct.productMap (AlgHom.id k B)
      ((Algebra.ofId k B).comp (counitAlgHom e))).comp (comul e) = AlgHom.id k B := by
  have h := pointAlgHom_mul e (algPoint e (AlgHom.id k B))
    (1 : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k B))) ⟶ (groupScheme F e).X)
  rw [mul_one, pointAlgHom_one, pointAlgHom_algPoint] at h
  exact h.symm

end Comultiplication

section UnitPoints

theorem affinePointsEquiv_unitPoint {S : Scheme.{u}} {R : CommRingCat.{u}} (f : Spec R ⟶ S)
    (u : Rˣ) : Gm.affinePointsEquiv f (unitPoint f u) = u := by
  apply Units.ext
  rw [Gm.affinePointsEquiv_val, unitPoint, MulEquiv.apply_symm_apply]
  exact (Scheme.ΓSpecIso R).inv_hom_id_apply (u : R)

theorem affinePointsEquiv_homMk_comp {S : Scheme.{u}} {R R' : CommRingCat.{u}}
    {f : Spec R ⟶ S} {f' : Spec R' ⟶ S} (φ : R ⟶ R') (h : Spec.map φ ≫ f = f')
    (x : Over.mk f ⟶ (Gm S).X) :
    Gm.affinePointsEquiv f' ((Over.homMk (Spec.map φ) h : Over.mk f' ⟶ Over.mk f) ≫ x) =
      Units.map φ.hom.toMonoidHom (Gm.affinePointsEquiv f x) := by
  apply Units.ext
  rw [Gm.affinePointsEquiv_val, Gm.pointsEquiv_naturality, Units.coe_map, Units.coe_map,
    Gm.affinePointsEquiv_val]
  change ((Spec.map φ).appTop ≫ (Scheme.ΓSpecIso R').hom) _ = _
  rw [Scheme.ΓSpecIso_naturality]
  rfl

theorem pointRing_homMk_comp {R' : CommRingCat.{u}} {A : CommRingCat.{u}}
    {f : Spec A ⟶ Spec (CommRingCat.of k)} {f' : Spec R' ⟶ Spec (CommRingCat.of k)}
    (φ : A ⟶ R') (h : Spec.map φ ≫ f = f') (y : Over.mk f ⟶ (groupScheme F e).X) :
    pointRing ((Over.homMk (Spec.map φ) h : Over.mk f' ⟶ Over.mk f) ≫ y) = pointRing y ≫ φ := by
  apply Spec.map_injective
  rw [specMap_pointRing, Spec.map_comp, specMap_pointRing]
  rfl

variable {A : Type u} [CommRing A] [Algebra k A]

/-- Evaluation `k[T, T⁻¹] → A` at a unit, as a `k`-algebra map. -/
def evalAlgHom (a : Aˣ) : LaurentPolynomial k →ₐ[k] A where
  __ := LaurentPolynomial.eval₂ (algebraMap k A) a
  commutes' r := by
    change LaurentPolynomial.eval₂ (algebraMap k A) a (algebraMap k (LaurentPolynomial k) r) = _
    rw [LaurentPolynomial.algebraMap_apply, LaurentPolynomial.eval₂_C, Algebra.algebraMap_self,
      RingHom.id_apply]

theorem evalAlgHom_apply (a : Aˣ) (q : LaurentPolynomial k) :
    evalAlgHom a q = LaurentPolynomial.eval₂ (algebraMap k A) a q :=
  rfl

/-- The point `T = a` of `Spec k[T, T⁻¹]` over `Spec A`. -/
def laurentEvalPoint (a : Aˣ) : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k A))) ⟶
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k (LaurentPolynomial k)))) :=
  Over.homMk (Spec.map (CommRingCat.ofHom (evalAlgHom a).toRingHom)) (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (RingHom.ext fun r => (evalAlgHom a).commutes r))

/-- Every unit point factors through the coordinate unit of `Spec k[T, T⁻¹]`. -/
theorem unitPoint_eq_laurentEvalPoint_comp (a : Aˣ) :
    unitPoint (Spec.map (CommRingCat.ofHom (algebraMap k A))) a =
      laurentEvalPoint a ≫ unitPoint (Spec.map (CommRingCat.ofHom (algebraMap k (LaurentPolynomial k))))
        (Gm.relativeCoordUnit k) := by
  apply (Gm.affinePointsEquiv _).injective
  rw [affinePointsEquiv_unitPoint, laurentEvalPoint,
    affinePointsEquiv_homMk_comp (f := Spec.map (CommRingCat.ofHom
      (algebraMap k (LaurentPolynomial k)))), affinePointsEquiv_unitPoint]
  apply Units.ext
  change (a : A) = LaurentPolynomial.eval₂ (algebraMap k A) a (LaurentPolynomial.T 1)
  rw [LaurentPolynomial.eval₂_T, zpow_one]

/-- The point of `𝔾_m` over `Spec A` given by `a`, composed with `g`, is classified by the
classifying map of the universal composite followed by evaluation at `a`. -/
theorem pointAlgHom_unitPoint_comp (g : (Gm (Spec (CommRingCat.of k))).X ⟶ (groupScheme F e).X)
    (a : Aˣ) :
    pointAlgHom (unitPoint (Spec.map (CommRingCat.ofHom (algebraMap k A))) a ≫ g) =
      (evalAlgHom a).comp (pointAlgHom
        (unitPoint (Spec.map (CommRingCat.ofHom (algebraMap k (LaurentPolynomial k))))
          (Gm.relativeCoordUnit k) ≫ g)) := by
  refine AlgHom.ext fun b => ?_
  rw [AlgHom.comp_apply, pointAlgHom_apply, pointAlgHom_apply, unitPoint_eq_laurentEvalPoint_comp,
    Category.assoc, laurentEvalPoint, pointRing_homMk_comp]
  rfl

theorem isIso_unitPoint_of_eq {f : Spec (CommRingCat.of (LaurentPolynomial k)) ⟶
    Spec (CommRingCat.of k)} (hf : f = Spec.map (Gm.laurentC k)) :
    IsIso (unitPoint f (Gm.relativeCoordUnit k)) := by
  subst hf
  have h : unitPoint (Spec.map (Gm.laurentC k)) (Gm.relativeCoordUnit k) = Gm.laurentPoint k := by
    apply (Gm.affinePointsEquiv _).injective
    rw [affinePointsEquiv_unitPoint, Gm.affinePointsEquiv_laurentPoint]
  rw [h, Gm.laurentPoint]
  exact Iso.isIso_inv _

theorem ofHom_algebraMap_laurent :
    CommRingCat.ofHom (algebraMap k (LaurentPolynomial k)) = Gm.laurentC k :=
  CommRingCat.hom_ext (RingHom.ext fun r => by
    change algebraMap k (LaurentPolynomial k) r = LaurentPolynomial.C r
    rw [LaurentPolynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply])

section TwoVariables

/-- The outer coordinate unit `s` of `k[t, t⁻¹][s, s⁻¹]`. -/
abbrev outerUnit : (LaurentPolynomial (LaurentPolynomial k))ˣ :=
  Gm.relativeCoordUnit (LaurentPolynomial k)

/-- The inner coordinate unit `t` of `k[t, t⁻¹][s, s⁻¹]`. -/
abbrev innerUnit' : (LaurentPolynomial (LaurentPolynomial k))ˣ :=
  Units.map (LaurentPolynomial.C : LaurentPolynomial k →+* _).toMonoidHom (Gm.relativeCoordUnit k)

theorem algebraMap_twoVar (r : k) :
    algebraMap k (LaurentPolynomial (LaurentPolynomial k)) r =
      LaurentPolynomial.C (LaurentPolynomial.C r) := by
  rw [LaurentPolynomial.algebraMap_apply, LaurentPolynomial.algebraMap_apply,
    Algebra.algebraMap_self, RingHom.id_apply]

theorem outerUnit_zpow_val (n : ℤ) :
    ((outerUnit (k := k) ^ n : (LaurentPolynomial (LaurentPolynomial k))ˣ) :
      LaurentPolynomial (LaurentPolynomial k)) = LaurentPolynomial.T n :=
  Gm.relativeCoordUnit_zpow_val _ n

theorem innerUnit'_zpow_val (n : ℤ) :
    ((innerUnit' (k := k) ^ n : (LaurentPolynomial (LaurentPolynomial k))ˣ) :
      LaurentPolynomial (LaurentPolynomial k)) = LaurentPolynomial.C (LaurentPolynomial.T n) := by
  rw [← map_zpow, Units.coe_map, Gm.relativeCoordUnit_zpow_val]
  rfl

theorem coeff_evalAlgHom_outerUnit (q : LaurentPolynomial k) (m : ℤ) :
    (evalAlgHom (outerUnit (k := k)) q).coeff m = LaurentPolynomial.C (q.coeff m) := by
  induction q using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hp, hq,
      AddMonoidAlgebra.coeff_add, Finsupp.add_apply, map_add]
  | C_mul_T n r =>
    rw [evalAlgHom_apply, LaurentPolynomial.eval₂_C_mul_T, outerUnit_zpow_val, algebraMap_twoVar,
      ← LaurentPolynomial.single_eq_C_mul_T, ← LaurentPolynomial.single_eq_C_mul_T,
      AddMonoidAlgebra.coeff_single, AddMonoidAlgebra.coeff_single, Finsupp.single_apply,
      Finsupp.single_apply]
    split_ifs <;> simp

theorem evalAlgHom_innerUnit' (q : LaurentPolynomial k) :
    evalAlgHom (innerUnit' (k := k)) q = LaurentPolynomial.C q := by
  induction q using LaurentPolynomial.induction_on' with
  | add p q hp hq => rw [map_add, hp, hq, map_add]
  | C_mul_T n r =>
    rw [evalAlgHom_apply, LaurentPolynomial.eval₂_C_mul_T, innerUnit'_zpow_val, algebraMap_twoVar,
      ← map_mul]

theorem coeff_evalAlgHom_outerUnit_mul_innerUnit' (q : LaurentPolynomial k) (m : ℤ) :
    (evalAlgHom (outerUnit (k := k) * innerUnit') q).coeff m =
      AddMonoidAlgebra.single m (q.coeff m) := by
  induction q using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hp, hq,
      AddMonoidAlgebra.coeff_add, Finsupp.add_apply, AddMonoidAlgebra.single_add]
  | C_mul_T n r =>
    rw [evalAlgHom_apply, LaurentPolynomial.eval₂_C_mul_T,
      show (outerUnit (k := k) * innerUnit') ^ n = outerUnit ^ n * innerUnit' ^ n from
        mul_zpow (α := (LaurentPolynomial (LaurentPolynomial k))ˣ) _ _ _, Units.val_mul,
      outerUnit_zpow_val, innerUnit'_zpow_val, algebraMap_twoVar,
      show LaurentPolynomial.C (LaurentPolynomial.C r) *
          (LaurentPolynomial.T n * LaurentPolynomial.C (LaurentPolynomial.T n)) =
        LaurentPolynomial.C (LaurentPolynomial.C r * LaurentPolynomial.T n) *
          (LaurentPolynomial.T n : LaurentPolynomial (LaurentPolynomial k)) by
        rw [map_mul]; ring,
      ← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.coeff_single, Finsupp.single_apply,
      ← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    split_ifs with h
    · rw [h]
    · simp

end TwoVariables

end UnitPoints

section Conjugation

variable (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ groupScheme F e)

/-- The constants `A₀ → A₀[s, s⁻¹]`, as a `k`-algebra map. -/
def constAlgHom (A₀ : Type u) [CommRing A₀] [Algebra k A₀] : A₀ →ₐ[k] LaurentPolynomial A₀ where
  __ := (LaurentPolynomial.C : A₀ →+* LaurentPolynomial A₀)
  commutes' r := by
    change LaurentPolynomial.C (algebraMap k A₀ r) = algebraMap k (LaurentPolynomial A₀) r
    rw [LaurentPolynomial.algebraMap_apply]

/-- Conjugating a constant point by `χ(s)` over `Spec A₀[s, s⁻¹]` is classified by the coaction
followed by the classifying map on each coefficient. -/
theorem pointRing_conj_algPoint_const {A₀ : Type u} [CommRing A₀] [Algebra k A₀]
    (φ : B →ₐ[k] A₀) :
    pointRing ((unitPoint (Spec.map (CommRingCat.ofHom (algebraMap k (LaurentPolynomial A₀))))
          (Gm.relativeCoordUnit A₀) ≫ χ.hom.hom) * algPoint e ((constAlgHom A₀).comp φ) *
        (unitPoint (Spec.map (CommRingCat.ofHom (algebraMap k (LaurentPolynomial A₀))))
          (Gm.relativeCoordUnit A₀) ≫ χ.hom.hom)⁻¹) =
      coaction χ ≫ laurentCoeffMap (CommRingCat.ofHom (φ : B →+* A₀)) := by
  rw [pointRing_conj, pointRing_algPoint]
  have h : CommRingCat.ofHom (((constAlgHom A₀).comp φ : B →ₐ[k] LaurentPolynomial A₀) :
      B →+* LaurentPolynomial A₀) =
        CommRingCat.ofHom (φ : B →+* A₀) ≫ Gm.laurentC (CommRingCat.of A₀) :=
    rfl
  rw [h]
  exact congrArg (coaction χ ≫ ·)
    (laurentCoeffMap_comp_laurentC_comp_laurentEval (CommRingCat.ofHom (φ : B →+* A₀)))

theorem productMap_includeLeft_includeRight :
    Algebra.TensorProduct.productMap (Algebra.TensorProduct.includeLeft : B →ₐ[k] B ⊗[k] B)
      Algebra.TensorProduct.includeRight = AlgHom.id k (B ⊗[k] B) :=
  Algebra.TensorProduct.ext' fun a b => by
    simp only [Algebra.TensorProduct.productMap_apply_tmul, Algebra.TensorProduct.includeLeft_apply,
      Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
      one_mul, AlgHom.id_apply]

/-- The comultiplication respects total weight. -/
theorem comul_mem_tensorWeightSpan' (b : B) (d : ℤ) (hb : IsHomogeneous (coaction χ).hom d b) :
    comul e b ∈ tensorWeightSpan k (coaction χ).hom d := by
  set f₃ := Spec.map (CommRingCat.ofHom (algebraMap k (LaurentPolynomial (B ⊗[k] B))))
  set sP := unitPoint f₃ (Gm.relativeCoordUnit (B ⊗[k] B))
  set g₁ := algPoint e ((constAlgHom (B ⊗[k] B)).comp Algebra.TensorProduct.includeLeft)
  set g₂ := algPoint e ((constAlgHom (B ⊗[k] B)).comp Algebra.TensorProduct.includeRight)
  have hg : g₁ * g₂ = algPoint e ((constAlgHom (B ⊗[k] B)).comp (comul e)) := by
    rw [← algPoint_pointAlgHom e (g₁ * g₂), pointAlgHom_mul, pointAlgHom_algPoint,
      pointAlgHom_algPoint, productMap_comp_comp, productMap_includeLeft_includeRight,
      AlgHom.comp_id]
  have hconj : (sP ≫ χ.hom.hom) * (g₁ * g₂) * (sP ≫ χ.hom.hom)⁻¹ =
      ((sP ≫ χ.hom.hom) * g₁ * (sP ≫ χ.hom.hom)⁻¹) *
        ((sP ≫ χ.hom.hom) * g₂ * (sP ≫ χ.hom.hom)⁻¹) := by
    group
  have h := congrArg pointAlgHom hconj
  rw [pointAlgHom_mul e ((sP ≫ χ.hom.hom) * g₁ * (sP ≫ χ.hom.hom)⁻¹)
    ((sP ≫ χ.hom.hom) * g₂ * (sP ≫ χ.hom.hom)⁻¹)] at h
  refine comul_mem_tensorWeightSpan (isGrading_coaction χ)
    (pointAlgHom ((sP ≫ χ.hom.hom) * g₁ * (sP ≫ χ.hom.hom)⁻¹))
    (pointAlgHom ((sP ≫ χ.hom.hom) * g₂ * (sP ≫ χ.hom.hom)⁻¹)) ?_ ?_ ?_ b d hb
  · intro b n
    rw [pointAlgHom_apply, pointRing_conj_algPoint_const, CommRingCat.comp_apply,
      coeff_laurentCoeffMap]
    rfl
  · intro b n
    rw [pointAlgHom_apply, pointRing_conj_algPoint_const, CommRingCat.comp_apply,
      coeff_laurentCoeffMap]
    rfl
  · intro b n
    rw [← AlgHom.comp_apply, ← h, pointAlgHom_apply, hg, pointRing_conj_algPoint_const,
      CommRingCat.comp_apply, coeff_laurentCoeffMap]
    rfl

end Conjugation

section Main

variable (χ ψ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ groupScheme F e)

/-- The identity point over `Spec k`, as a point over the spectrum of the `k`-algebra `k`. -/
def baseHom : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k k))) :=
  Over.homMk (𝟙 _) (by
    change 𝟙 _ ≫ Spec.map (CommRingCat.ofHom (algebraMap k k)) = 𝟙 _
    rw [Category.id_comp, show CommRingCat.ofHom (algebraMap k k) = 𝟙 (CommRingCat.of k) from rfl,
      Spec.map_id])

/-- The universal point `T` of `𝔾_m` over `Spec k[T, T⁻¹]`. -/
abbrev univUnit : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k (LaurentPolynomial k)))) ⟶
    (Gm (Spec (CommRingCat.of k))).X :=
  unitPoint _ (Gm.relativeCoordUnit k)

/-- A unit point of `𝔾_m` over `Spec k[t, t⁻¹][s, s⁻¹]`. -/
abbrev twoVarPoint (a : (LaurentPolynomial (LaurentPolynomial k))ˣ) :
    Over.mk (Spec.map (CommRingCat.ofHom
      (algebraMap k (LaurentPolynomial (LaurentPolynomial k))))) ⟶
    (Gm (Spec (CommRingCat.of k))).X :=
  unitPoint _ a

theorem coeff_pointAlgHom_outer (g : (Gm (Spec (CommRingCat.of k))).X ⟶ (groupScheme F e).X)
    (b : B) (m : ℤ) :
    (pointAlgHom (twoVarPoint (outerUnit (k := k)) ≫ g) b).coeff m =
      LaurentPolynomial.C ((pointAlgHom (univUnit ≫ g) b).coeff m) := by
  rw [pointAlgHom_unitPoint_comp, AlgHom.comp_apply, coeff_evalAlgHom_outerUnit]

theorem coeff_pointAlgHom_outer_inner
    (g : (Gm (Spec (CommRingCat.of k))).X ⟶ (groupScheme F e).X) (b : B) (m : ℤ) :
    (pointAlgHom (twoVarPoint (outerUnit (k := k) * innerUnit') ≫ g) b).coeff m =
      AddMonoidAlgebra.single m ((pointAlgHom (univUnit ≫ g) b).coeff m) := by
  rw [pointAlgHom_unitPoint_comp, AlgHom.comp_apply, coeff_evalAlgHom_outerUnit_mul_innerUnit']

theorem pointRing_inner (g : (Gm (Spec (CommRingCat.of k))).X ⟶ (groupScheme F e).X) :
    pointRing (twoVarPoint (innerUnit' (k := k)) ≫ g) =
      pointRing (univUnit ≫ g) ≫ Gm.laurentC (CommRingCat.of (LaurentPolynomial k)) := by
  refine CommRingCat.hom_ext (RingHom.ext fun b => ?_)
  have h' := congrArg (fun φ : B →ₐ[k] _ => φ b) (pointAlgHom_unitPoint_comp e g (innerUnit' (k := k)))
  simp only [AlgHom.comp_apply, evalAlgHom_innerUnit'] at h'
  exact h'

theorem pointAlgHom_conj_inner (g : (Gm (Spec (CommRingCat.of k))).X ⟶ (groupScheme F e).X)
    (b : B) (j : ℤ) (hb : IsHomogeneous (coaction χ).hom j b) :
    pointAlgHom ((twoVarPoint (outerUnit (k := k)) ≫ χ.hom.hom) *
        (twoVarPoint (innerUnit' (k := k)) ≫ g) *
        (twoVarPoint (outerUnit (k := k)) ≫ χ.hom.hom)⁻¹) b =
      AddMonoidAlgebra.single j (pointAlgHom (univUnit ≫ g) b) := by
  rw [pointAlgHom_apply, pointRing_conj, pointRing_inner, laurentCoeffMap_comp_laurentC_comp_laurentEval,
    CommRingCat.comp_apply]
  have hb' : coaction χ b = AddMonoidAlgebra.single j b := hb
  rw [hb', laurentCoeffMap_single]
  rfl

theorem twoVar_cocycle :
    twoVarPoint (outerUnit (k := k) * innerUnit') ≫ (ψ.hom.hom * (χ.hom.hom)⁻¹) =
      (twoVarPoint (outerUnit (k := k)) ≫ (ψ.hom.hom * (χ.hom.hom)⁻¹)) *
        ((twoVarPoint (outerUnit (k := k)) ≫ χ.hom.hom) *
          (twoVarPoint (innerUnit' (k := k)) ≫ (ψ.hom.hom * (χ.hom.hom)⁻¹)) *
          (twoVarPoint (outerUnit (k := k)) ≫ χ.hom.hom)⁻¹) := by
  have hst : twoVarPoint (outerUnit (k := k) * innerUnit') =
      twoVarPoint (outerUnit (k := k)) * twoVarPoint innerUnit' := by
    simp only [twoVarPoint, unitPoint, map_mul]
  rw [hst]
  simp only [MonObj.comp_mul, GrpObj.comp_inv, MonObj.mul_comp]
  group

/-- The constant coefficient of a point with no negative Laurent terms, as a `k`-algebra map. -/
def constCoeffAlgHom (x : B →ₐ[k] LaurentPolynomial k) (hx : ∀ b, ∀ n < 0, (x b).coeff n = 0) :
    B →ₐ[k] k where
  toFun b := (x b).coeff 0
  map_one' := by
    rw [map_one, ← map_one (algebraMap k (LaurentPolynomial k)), algebraMap_laurent_coeff,
      if_pos rfl]
  map_mul' a b := by
    simp only
    rw [map_mul, ← toLaurent_trunc (hx a), ← toLaurent_trunc (hx b), ← map_mul, ← Nat.cast_zero,
      coeff_toLaurent_natCast, coeff_toLaurent_natCast, coeff_toLaurent_natCast,
      Polynomial.mul_coeff_zero]
  map_zero' := by
    simp only
    rw [show x 0 = 0 from map_zero x]
    rfl
  map_add' a b := by
    simp only
    rw [map_add]
    rfl
  commutes' r := by
    simp only
    rw [AlgHom.commutes, algebraMap_laurent_coeff, if_pos rfl, Algebra.algebraMap_self,
      RingHom.id_apply]

theorem constCoeffAlgHom_apply (x : B →ₐ[k] LaurentPolynomial k)
    (hx : ∀ b, ∀ n < 0, (x b).coeff n = 0) (b : B) :
    constCoeffAlgHom x hx b = (x b).coeff 0 :=
  rfl

theorem pointAlgHom_conj_const (u : B →ₐ[k] k) (b : B) (j : ℤ)
    (hb : IsHomogeneous (coaction χ).hom j b) :
    pointAlgHom ((univUnit ≫ χ.hom.hom) * algPoint e ((constAlgHom k).comp u) *
        (univUnit ≫ χ.hom.hom)⁻¹) b = AddMonoidAlgebra.single j (u b) := by
  rw [pointAlgHom_apply, pointRing_conj_algPoint_const, CommRingCat.comp_apply]
  have hb' : coaction χ b = AddMonoidAlgebra.single j b := hb
  rw [hb', laurentCoeffMap_single]
  rfl

theorem constantPoint_eq_algPoint (u : B →ₐ[k] k) :
    (groupScheme F e).constantPoint (baseHom ≫ algPoint e u)
        (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k (LaurentPolynomial k))))) =
      algPoint e ((constAlgHom k).comp u) := by
  apply hom_ext_of_pointRing
  apply Spec.map_injective
  rw [specMap_pointRing, specMap_pointRing]
  change Spec.map (CommRingCat.ofHom (algebraMap k (LaurentPolynomial k))) ≫ 𝟙 _ ≫
    Spec.map (CommRingCat.ofHom (u : B →+* k)) = Spec.map _
  rw [Category.id_comp, ← Spec.map_comp]
  congr 1

/-- Two cocharacters whose quotient is a point of `U_G(χ)` are conjugate under a rational point
of `U_G(χ)`, in the corepresented model. -/
theorem exists_conj_of_mem_unipotent
    (h : ψ.hom.hom * (χ.hom.hom)⁻¹ ∈
      (Dynamic.unipotent χ).carrier (Gm (Spec (CommRingCat.of k))).X) :
    ∃ u : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ (groupScheme F e).X,
      u ∈ (Dynamic.unipotent χ).carrier _ ∧
        (groupScheme F e).constantPoint u _ * χ.hom.hom *
          ((groupScheme F e).constantPoint u _)⁻¹ = ψ.hom.hom := by
  have hx₁ : univUnit ≫ (ψ.hom.hom * (χ.hom.hom)⁻¹) ∈ (Dynamic.unipotent χ).carrier _ :=
    (Dynamic.unipotent χ).comp_mem univUnit h
  have hxc : IsContracting (coaction χ).hom (counitAlgHom e)
      (pointAlgHom (univUnit ≫ (ψ.hom.hom * (χ.hom.hom)⁻¹))) :=
    (isContracting_pointAlgHom_iff χ _).2 hx₁
  have hcoc : ∀ b, pointAlgHom (twoVarPoint (outerUnit (k := k) * innerUnit') ≫
      (ψ.hom.hom * (χ.hom.hom)⁻¹)) b =
      Algebra.TensorProduct.productMap
        (pointAlgHom (twoVarPoint (outerUnit (k := k)) ≫ (ψ.hom.hom * (χ.hom.hom)⁻¹)))
        (pointAlgHom ((twoVarPoint (outerUnit (k := k)) ≫ χ.hom.hom) *
          (twoVarPoint (innerUnit' (k := k)) ≫ (ψ.hom.hom * (χ.hom.hom)⁻¹)) *
          (twoVarPoint (outerUnit (k := k)) ≫ χ.hom.hom)⁻¹)) (comul e b) := by
    intro b
    rw [twoVar_cocycle, pointAlgHom_mul]
    rfl
  -- the cocycle has no negative terms
  have hpos := coeff_eq_zero_of_cocycle (isGrading_coaction χ)
    (fun b n => counit_coeff_coaction χ b n) (comul_mem_tensorWeightSpan' e χ)
    (productMap_counit_comul e) (productMap_comul_counit e) hxc
    (coeff_pointAlgHom_outer e _) (fun b j hb => pointAlgHom_conj_inner e χ _ b j hb)
    (coeff_pointAlgHom_outer_inner e _) hcoc
  -- its constant coefficient is a rational point of `U_G(χ)`
  set u := constCoeffAlgHom _ hpos with hu
  have hucontr : IsContracting (coaction χ).hom (counitAlgHom e) u := by
    refine ⟨fun b n hn => ?_, fun b => ?_⟩
    · rw [hu, constCoeffAlgHom_apply, hxc.1 b n hn]
      rfl
    · rw [hu, constCoeffAlgHom_apply, hxc.2 b, algebraMap_laurent_coeff, if_pos rfl]
      rfl
  have huP : baseHom ≫ algPoint e u ∈ (Dynamic.unipotent χ).carrier _ := by
    refine (Dynamic.unipotent χ).comp_mem baseHom ?_
    rw [← isContracting_pointAlgHom_iff, pointAlgHom_algPoint]
    exact hucontr
  refine ⟨baseHom ≫ algPoint e u, huP, ?_⟩
  -- the fixed point identity `u = x(s) · (s · u)`
  have hfix := algebraMap_eq_of_cocycle (isGrading_coaction χ) u
    (fun b => constCoeffAlgHom_apply _ hpos b)
    (pointAlgHom ((univUnit ≫ χ.hom.hom) * algPoint e ((constAlgHom k).comp u) *
      (univUnit ≫ χ.hom.hom)⁻¹)) (fun b j hb => pointAlgHom_conj_const e χ u b j hb)
    (coeff_pointAlgHom_outer e _) (fun b j hb => pointAlgHom_conj_inner e χ _ b j hb)
    (coeff_pointAlgHom_outer_inner e _) hcoc
  have hu₁ : algPoint e ((constAlgHom k).comp u) =
      (univUnit ≫ (ψ.hom.hom * (χ.hom.hom)⁻¹)) *
        ((univUnit ≫ χ.hom.hom) * algPoint e ((constAlgHom k).comp u) *
          (univUnit ≫ χ.hom.hom)⁻¹) := by
    rw [← algPoint_pointAlgHom e (_ * _), pointAlgHom_mul]
    congr 1
    refine AlgHom.ext fun b => ?_
    rw [AlgHom.comp_apply, AlgHom.comp_apply, ← hfix b]
    change LaurentPolynomial.C (u b) = algebraMap k (LaurentPolynomial k) (u b)
    rw [LaurentPolynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  have hτc : univUnit ≫ (groupScheme F e).constantPoint (baseHom ≫ algPoint e u) _ =
      algPoint e ((constAlgHom k).comp u) := by
    rw [constantPoint_naturality, constantPoint_eq_algPoint]
  have key : univUnit ≫ ((groupScheme F e).constantPoint (baseHom ≫ algPoint e u) _ *
      χ.hom.hom * ((groupScheme F e).constantPoint (baseHom ≫ algPoint e u) _)⁻¹) =
      univUnit ≫ ψ.hom.hom := by
    rw [MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv, hτc]
    rw [MonObj.comp_mul, GrpObj.comp_inv] at hu₁
    calc algPoint e ((constAlgHom k).comp u) * (univUnit ≫ χ.hom.hom) *
          (algPoint e ((constAlgHom k).comp u))⁻¹
        = ((univUnit ≫ ψ.hom.hom) * (univUnit ≫ χ.hom.hom)⁻¹ *
            ((univUnit ≫ χ.hom.hom) * algPoint e ((constAlgHom k).comp u) *
              (univUnit ≫ χ.hom.hom)⁻¹)) * (univUnit ≫ χ.hom.hom) *
            (algPoint e ((constAlgHom k).comp u))⁻¹ := by
          rw [← hu₁]
      _ = univUnit ≫ ψ.hom.hom := by group
  have : IsIso (univUnit (k := k)) := isIso_unitPoint_of_eq (by rw [ofHom_algebraMap_laurent])
  exact (cancel_epi univUnit).1 key

end Main


end Corepresented

namespace Dynamic

/-- Let `G` be an affine group scheme over a field `k` and let `χ, ψ : 𝔾_m → G` be cocharacters
such that `t ↦ ψ(t) χ(t)⁻¹` is a point of `U_G(χ)`. Then `ψ = u χ u⁻¹` for a rational point
`u ∈ U_G(χ)(k)`. -/
theorem exists_unipotent_conj_of_mul_inv_mem {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (χ ψ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (h : ψ.hom.hom * (χ.hom.hom)⁻¹ ∈ (unipotent χ).carrier (Gm (Spec (CommRingCat.of k))).X) :
    ∃ u : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
      u ∈ (unipotent χ).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) ∧
        χ ≫ (G.innerIso u).hom = ψ := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  set Φ := AffineCoordinates.groupSchemeIso G with hΦ
  have hχ : χ.hom.hom = (χ ≫ Φ.inv).hom.hom ≫ Φ.hom.hom.hom := by
    rw [← Grp.comp_hom_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hψ : ψ.hom.hom = (ψ ≫ Φ.inv).hom.hom ≫ Φ.hom.hom.hom := by
    rw [← Grp.comp_hom_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have h' : (ψ ≫ Φ.inv).hom.hom * ((χ ≫ Φ.inv).hom.hom)⁻¹ ∈
      (unipotent (χ ≫ Φ.inv)).carrier (Gm (Spec (CommRingCat.of k))).X := by
    have h₁ := unipotent_le_comap χ Φ.inv _ h
    rw [SubgroupFunctor.mem_comap, MonObj.mul_comp, GrpObj.inv_comp, ← Grp.comp_hom_hom,
      ← Grp.comp_hom_hom] at h₁
    exact h₁
  obtain ⟨u', hu', hconj⟩ := Corepresented.exists_conj_of_mem_unipotent
    (AffineCoordinates.corepresentation G) (χ ≫ Φ.inv) (ψ ≫ Φ.inv) h'
  refine ⟨u' ≫ Φ.hom.hom.hom, ?_, ?_⟩
  · have h₂ := unipotent_le_comap (χ ≫ Φ.inv) Φ.hom _ hu'
    rw [SubgroupFunctor.mem_comap, Category.assoc, Iso.inv_hom_id, Category.comp_id] at h₂
    exact h₂
  · apply Grp.hom_ext
    have hc : ∀ T : Over (Spec (CommRingCat.of k)), G.constantPoint (u' ≫ Φ.hom.hom.hom) T =
        (Corepresented.groupScheme (AffineCoordinates.functor G)
          (AffineCoordinates.corepresentation G)).constantPoint u' T ≫ Φ.hom.hom.hom := by
      intro T
      simp only [constantPoint, Category.assoc]
    rw [Grp.comp_hom_hom, comp_innerIso_hom, hc, hχ, hψ, ← hconj, MonObj.mul_comp,
      MonObj.mul_comp, GrpObj.inv_comp]

end Dynamic

end Langlands.GroupScheme
