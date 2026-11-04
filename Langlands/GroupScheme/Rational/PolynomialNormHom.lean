import Langlands.GroupScheme.Rational.PolynomialAdditiveMap
import Langlands.GroupScheme.Rational.PolynomialGaloisNorm
import Langlands.GroupScheme.Rational.Characters

/-! # Actual vector-group homomorphisms from central Galois norms -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry MvPolynomial
open scoped CategoryTheory.MonObj BigOperators

namespace Langlands.GroupScheme.PolynomialPoint

variable (k : Type u) [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k)))

/-- Points of the full center on an affine test algebra. -/
abbrev centralAffinePoints (A : Type u) [CommRing A] [Algebra k A] :=
  (center G).carrier ((algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k A)))

local instance centralAffinePointsCommGroup
    (A : Type u) [CommRing A] [Algebra k A] : CommGroup (centralAffinePoints k G A) where
  __ := (inferInstance : Group (centralAffinePoints k G A))
  mul_comm x y := Subtype.ext (commute_of_mem_center x.property y.val).eq

/-- Pulling back a full central point preserves full centrality. -/
def centralAffineMap {A B : Type u} [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    (f : A →ₐ[k] B) : centralAffinePoints k G A →* centralAffinePoints k G B where
  toFun x := ⟨Lie.affineMap G f x.val,
    (center G).comp_mem ((algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom f).op) x.property⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul _ x.val y.val)

@[simp] theorem centralAffineMap_val
    {A B : Type u} [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    (f : A →ₐ[k] B) (x : centralAffinePoints k G A) :
    (centralAffineMap k G f x).val = Lie.affineMap G f x.val := rfl

variable {I J : Type} (L : Type u) [Field L] [Algebra k L]

/-- Substitute base-field polynomials while retaining the coefficient field. -/
def substituteAlg (v : I → MvPolynomial J k) :
    MvPolynomial I L →ₐ[k] MvPolynomial J L :=
  aevalTower (IsScalarTower.toAlgHom k L (MvPolynomial J L))
    (fun i => MvPolynomial.mapAlgHom (Algebra.ofId k L) (v i))

@[simp] theorem substituteAlg_C (v : I → MvPolynomial J k) (c : L) :
    substituteAlg k L v (C c) = C c := by
  simp [substituteAlg, IsScalarTower.toAlgHom_apply, MvPolynomial.algebraMap_eq]

@[simp] theorem substituteAlg_X (v : I → MvPolynomial J k) (i : I) :
    substituteAlg k L v (X i) = MvPolynomial.mapAlgHom (Algebra.ofId k L) (v i) := by
  simp [substituteAlg]

/-- Base-field substitution agrees with ordinary polynomial evaluation. -/
theorem substituteAlg_self (v : I → MvPolynomial J k) :
    substituteAlg k k v = aeval v := by
  apply MvPolynomial.algHom_ext
  intro i
  simp

variable {L} {M : Type u} [Field M] [Algebra k M]

/-- Polynomial coefficient maps commute with substitution of base-field polynomials. -/
theorem substituteAlg_map (f : L →ₐ[k] M) (v : I → MvPolynomial J k) :
    (substituteAlg k M v).comp (MvPolynomial.mapAlgHom f) =
      (MvPolynomial.mapAlgHom f).comp (substituteAlg k L v) := by
  apply AlgHom.coe_ringHom_injective
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [MvPolynomial.mapAlgHom_apply]
  · intro i
    have h : f.toRingHom.comp (algebraMap k L) = algebraMap k M :=
      RingHom.ext (fun c => f.commutes c)
    simp only [RingHom.coe_coe, AlgHom.comp_apply, MvPolynomial.mapAlgHom_apply, map_X, substituteAlg_X,
      map_map]
    change MvPolynomial.map (algebraMap k M) (v i) =
      MvPolynomial.map (f.toRingHom.comp (algebraMap k L)) (v i)
    rw [h]

/-- Substitution as a map on full central polynomial points. -/
def centralSubstitute (v : I → MvPolynomial J k) :
    centralAffinePoints k G (MvPolynomial I L) →*
      centralAffinePoints k G (MvPolynomial J L) :=
  centralAffineMap k G (substituteAlg k L v)

/-- Central coefficient maps commute with base-polynomial substitution. -/
theorem centralSubstitute_map (f : L →ₐ[k] M) (v : I → MvPolynomial J k)
    (x : centralAffinePoints k G (MvPolynomial I L)) :
    centralSubstitute k G v (centralAffineMap k G (MvPolynomial.mapAlgHom f) x) =
      centralAffineMap k G (MvPolynomial.mapAlgHom f) (centralSubstitute k G v x) := by
  apply Subtype.ext
  change Lie.affineMap G (substituteAlg k M v)
      (Lie.affineMap G (MvPolynomial.mapAlgHom f) x.val) =
    Lie.affineMap G (MvPolynomial.mapAlgHom f)
      (Lie.affineMap G (substituteAlg k L v) x.val)
  rw [← Lie.affineMap_comp, ← Lie.affineMap_comp, substituteAlg_map]

variable (L)

/-- Central polynomial points satisfying the universal-pair additive identity. -/
def centralAdditivePoints (n : ℕ) :
    Subgroup (centralAffinePoints k G (MvPolynomial (Fin n) L)) where
  carrier := {x : centralAffinePoints k G (MvPolynomial (Fin n) L) |
    centralSubstitute k G (I := Fin n) (J := Fin n ⊕ Fin n) (L := L)
      (fun i => X (Sum.inl i) + X (Sum.inr i) : Fin n → MvPolynomial (Fin n ⊕ Fin n) k) x =
    centralSubstitute k G (I := Fin n) (J := Fin n ⊕ Fin n) (L := L)
      (fun i => X (Sum.inl i) : Fin n → MvPolynomial (Fin n ⊕ Fin n) k) x *
    centralSubstitute k G (I := Fin n) (J := Fin n ⊕ Fin n) (L := L)
      (fun i => X (Sum.inr i) : Fin n → MvPolynomial (Fin n ⊕ Fin n) k) x}
  one_mem' := by simp
  mul_mem' := by
    intro x y hx hy
    simp only [Set.mem_ofPred_eq, map_mul] at *
    rw [hx, hy]
    exact mul_mul_mul_comm _ _ _ _
  inv_mem' := by
    intro x hx
    change _ = _ at hx ⊢
    rw [map_inv, map_inv, map_inv, hx, mul_inv_rev]
    exact mul_comm _ _

/-- A coefficient map preserves central additive polynomial points. -/
theorem centralAdditivePoints_map (f : L →ₐ[k] M) {n : ℕ}
    {x : centralAffinePoints k G (MvPolynomial (Fin n) L)}
    (hx : x ∈ centralAdditivePoints k G L n) :
    centralAffineMap k G (MvPolynomial.mapAlgHom f) x ∈ centralAdditivePoints k G M n := by
  change _ = _ at hx ⊢
  rw [centralSubstitute_map k G f _, centralSubstitute_map k G f _,
    centralSubstitute_map k G f _]
  rw [hx, map_mul]

/-! Renaming into `ULift I` lets small variable types use the existing
same-universe polynomial descent without changing its coefficient field. -/

/-- Rename a small variable type into the coefficient-field universe. -/
def liftVariables (I : Type) :
    MvPolynomial I L →ₐ[k] MvPolynomial (ULift.{u} I) L :=
  (MvPolynomial.rename ULift.up).restrictScalars k

/-- Undo the variable-universe renaming. -/
def lowerVariables (I : Type) :
    MvPolynomial (ULift.{u} I) L →ₐ[k] MvPolynomial I L :=
  (MvPolynomial.rename ULift.down).restrictScalars k

@[simp] theorem lowerVariables_comp_liftVariables (I : Type) :
    (lowerVariables k L I).comp (liftVariables k L I) =
      AlgHom.id k (MvPolynomial I L) := by
  apply AlgHom.ext
  intro p
  change MvPolynomial.rename ULift.down (MvPolynomial.rename ULift.up p) = p
  simp only [rename_rename, Function.comp_def]
  exact rename_id_apply p

/-- Coefficient maps commute with raising the variable universe. -/
theorem map_liftVariables (f : L →ₐ[k] M) (I : Type) :
    (MvPolynomial.mapAlgHom f).comp (liftVariables k L I) =
      (liftVariables k M I).comp (MvPolynomial.mapAlgHom f) := by
  apply AlgHom.ext
  intro p
  exact MvPolynomial.map_rename f.toRingHom ULift.up p

/-- Coefficient maps commute with lowering the variable universe. -/
theorem map_lowerVariables (f : L →ₐ[k] M) (I : Type) :
    (MvPolynomial.mapAlgHom f).comp (lowerVariables k L I) =
      (lowerVariables k M I).comp (MvPolynomial.mapAlgHom f) := by
  apply AlgHom.ext
  intro p
  exact MvPolynomial.map_rename f.toRingHom ULift.down p

variable [IsAffine G.X.left]

/-- Coefficient extension reflects equality also for small polynomial variable types. -/
theorem mapCoefficients_injective (I : Type) :
    Function.Injective (Lie.affineMap G
      (MvPolynomial.mapAlgHom (Algebra.ofId k L) :
        MvPolynomial I k →ₐ[k] MvPolynomial I L)) := by
  intro x y h
  apply (GaloisPoint.coordinates k G (MvPolynomial I k)).injective
  apply AlgHom.ext
  intro a
  apply MvPolynomial.map_injective (algebraMap k L) (algebraMap k L).injective
  rw [GaloisPoint.coordinates_apply, GaloisPoint.coordinates_apply]
  have hx := G.affinePointEvaluation_map
    (CommAlgCat.ofHom (MvPolynomial.mapAlgHom (Algebra.ofId k L))) x a
  have hy := G.affinePointEvaluation_map
    (CommAlgCat.ofHom (MvPolynomial.mapAlgHom (Algebra.ofId k L))) y a
  exact hx.symm.trans
    ((congrArg (fun z => G.affinePointEvaluation
      (CommAlgCat.of k (MvPolynomial I L)) z a) h).trans hy)

variable [FiniteDimensional k L] [IsGalois k L]

/-- Effective point descent after harmless renaming of a small variable type. -/
def descendSmallVariables (I : Type)
    (x : Lie.AffinePoints G (MvPolynomial I L))
    (hx : ∀ σ : L ≃ₐ[k] L,
      Lie.affineMap G (MvPolynomial.mapAlgHom σ.toAlgHom) x = x) :
    Lie.AffinePoints G (MvPolynomial I k) :=
  Lie.affineMap G (lowerVariables k k I)
    (descend k L (ULift.{u} I) G
      ⟨Lie.affineMap G (liftVariables k L I) x, fun σ => by
        change Lie.affineMap G (MvPolynomial.mapAlgHom σ.toAlgHom)
          (Lie.affineMap G (liftVariables k L I) x) = _
        rw [← Lie.affineMap_comp, map_liftVariables, Lie.affineMap_comp, hx σ]⟩)

/-- Extending the descended point recovers the original invariant point. -/
theorem mapCoefficients_descendSmallVariables (I : Type)
    (x : Lie.AffinePoints G (MvPolynomial I L))
    (hx : ∀ σ : L ≃ₐ[k] L,
      Lie.affineMap G (MvPolynomial.mapAlgHom σ.toAlgHom) x = x) :
    Lie.affineMap G (MvPolynomial.mapAlgHom (Algebra.ofId k L))
      (descendSmallVariables k G L I x hx) = x := by
  unfold descendSmallVariables
  rw [← Lie.affineMap_comp, map_lowerVariables, Lie.affineMap_comp]
  change Lie.affineMap G (lowerVariables k L I)
    (extend k L (ULift.{u} I) G (descend k L (ULift.{u} I) G _)) = x
  rw [extend_descend]
  change Lie.affineMap G (lowerVariables k L I)
    (Lie.affineMap G (liftVariables k L I) x) = x
  rw [← Lie.affineMap_comp, lowerVariables_comp_liftVariables, Lie.affineMap_id]

/-- Coefficient conjugation restricts to the full central polynomial points. -/
def centralConjugate (I : Type) (σ : L ≃ₐ[k] L) :
    centralAffinePoints k G (MvPolynomial I L) →*
      centralAffinePoints k G (MvPolynomial I L) :=
  centralAffineMap k G (MvPolynomial.mapAlgHom σ.toAlgHom)

omit [IsAffine G.X.left] [FiniteDimensional k L] [IsGalois k L] in
theorem centralConjugate_mul (I : Type) (σ τ : L ≃ₐ[k] L)
    (x : centralAffinePoints k G (MvPolynomial I L)) :
    centralConjugate k G L I (σ * τ) x =
      centralConjugate k G L I σ (centralConjugate k G L I τ x) := by
  apply Subtype.ext
  change Lie.affineMap G (MvPolynomial.mapAlgHom (σ * τ).toAlgHom) x.val =
    Lie.affineMap G (MvPolynomial.mapAlgHom σ.toAlgHom)
      (Lie.affineMap G (MvPolynomial.mapAlgHom τ.toAlgHom) x.val)
  rw [← Lie.affineMap_comp]
  have h : (MvPolynomial.mapAlgHom (σ * τ).toAlgHom :
      MvPolynomial I L →ₐ[k] MvPolynomial I L) =
      (MvPolynomial.mapAlgHom σ.toAlgHom).comp (MvPolynomial.mapAlgHom τ.toAlgHom) := by
    apply AlgHom.ext
    intro p
    change MvPolynomial.map _ p = MvPolynomial.map _ (MvPolynomial.map _ p)
    rw [map_map]
    rfl
  exact congrArg (fun f => Lie.affineMap G f x.val) h

/-- The product of all coefficient conjugates in the full center. -/
def centralConjugateProduct (I : Type) :
    centralAffinePoints k G (MvPolynomial I L) →*
      centralAffinePoints k G (MvPolynomial I L) where
  toFun x := ∏ σ : L ≃ₐ[k] L, centralConjugate k G L I σ x
  map_one' := by simp
  map_mul' x y := by simp [Finset.prod_mul_distrib]

omit [IsAffine G.X.left] [IsGalois k L] in
/-- Left translation permutes the conjugate product. -/
theorem centralConjugateProduct_fixed (I : Type)
    (x : centralAffinePoints k G (MvPolynomial I L)) (σ : L ≃ₐ[k] L) :
    centralConjugate k G L I σ (centralConjugateProduct k G L I x) =
      centralConjugateProduct k G L I x := by
  change centralConjugate k G L I σ
      (∏ τ : L ≃ₐ[k] L, centralConjugate k G L I τ x) =
    ∏ τ : L ≃ₐ[k] L, centralConjugate k G L I τ x
  rw [map_prod]
  exact Fintype.prod_equiv (Equiv.mulLeft σ) _ _
    (fun τ => (centralConjugate_mul k G L I σ τ x).symm)

omit [IsAffine G.X.left] [IsGalois k L] in
/-- Products of conjugates preserve the universal-pair additive identity. -/
theorem centralConjugateProduct_additive {n : ℕ}
    {x : centralAffinePoints k G (MvPolynomial (Fin n) L)}
    (hx : x ∈ centralAdditivePoints k G L n) :
    centralConjugateProduct k G L (Fin n) x ∈ centralAdditivePoints k G L n := by
  change (∏ σ : L ≃ₐ[k] L, centralConjugate k G L (Fin n) σ x) ∈ _
  apply Subgroup.prod_mem
  intro σ _
  exact centralAdditivePoints_map k G L σ.toAlgHom hx

/-- The descended polynomial point underlying the full central conjugate product. -/
def centralNormPoint {n : ℕ} (x : centralAffinePoints k G (MvPolynomial (Fin n) L)) :
    Lie.AffinePoints G (MvPolynomial (Fin n) k) :=
  descendSmallVariables k G L (Fin n) (centralConjugateProduct k G L (Fin n) x).val
    (fun σ => congrArg Subtype.val (centralConjugateProduct_fixed k G L (Fin n) x σ))

/-- Extending the descended norm recovers its actual central conjugate product. -/
theorem mapCoefficients_centralNormPoint {n : ℕ}
    (x : centralAffinePoints k G (MvPolynomial (Fin n) L)) :
    Lie.affineMap G (MvPolynomial.mapAlgHom (Algebra.ofId k L))
      (centralNormPoint k G L x) = (centralConjugateProduct k G L (Fin n) x).val :=
  mapCoefficients_descendSmallVariables k G L _ _ _

omit [IsAffine G.X.left] [FiniteDimensional k L] [IsGalois k L] in
/-- Base-polynomial evaluation is compatible with extending coefficients. -/
theorem mapCoefficients_evaluate {n : ℕ}
    (p : Lie.AffinePoints G (MvPolynomial (Fin n) k))
    (v : Fin n → MvPolynomial J k) :
    Lie.affineMap G (MvPolynomial.mapAlgHom (Algebra.ofId k L)) (evaluate p v) =
      Lie.affineMap G (substituteAlg k L v)
        (Lie.affineMap G (MvPolynomial.mapAlgHom (Algebra.ofId k L)) p) := by
  rw [evaluate, ← Lie.affineMap_comp, ← Lie.affineMap_comp]
  exact congrArg (fun f => Lie.affineMap G f p) (by
    rw [← substituteAlg_self k v]
    exact (substituteAlg_map k (Algebra.ofId k L) v).symm)

omit [FiniteDimensional k L] [IsGalois k L] in
/-- Injective coefficient extension reflects the generic additive identity. -/
theorem isAdditive_of_mapCoefficients {n : ℕ}
    (p : Lie.AffinePoints G (MvPolynomial (Fin n) k))
    (x : centralAffinePoints k G (MvPolynomial (Fin n) L))
    (hx : x ∈ centralAdditivePoints k G L n)
    (hext : Lie.affineMap G (MvPolynomial.mapAlgHom (Algebra.ofId k L)) p = x.val) :
    IsAdditive p := by
  apply mapCoefficients_injective k G L (Fin n ⊕ Fin n)
  change Lie.affineMap G (MvPolynomial.mapAlgHom (Algebra.ofId k L))
      (evaluate p (fun i => X (Sum.inl i) + X (Sum.inr i))) =
    Lie.affineMap G (MvPolynomial.mapAlgHom (Algebra.ofId k L))
      (evaluate p (fun i => X (Sum.inl i)) * evaluate p (fun i => X (Sum.inr i)))
  rw [map_mul, mapCoefficients_evaluate, mapCoefficients_evaluate,
    mapCoefficients_evaluate, hext]
  exact congrArg Subtype.val hx

/-- The descended norm polynomial point satisfies the generic additive identity. -/
theorem centralNormPoint_additive {n : ℕ}
    (x : centralAffinePoints k G (MvPolynomial (Fin n) L))
    (hx : x ∈ centralAdditivePoints k G L n) :
    IsAdditive (centralNormPoint k G L x) :=
  isAdditive_of_mapCoefficients k G L _ _
    (centralConjugateProduct_additive k G L hx) (mapCoefficients_centralNormPoint k G L x)

/-- The actual vector-group homomorphism obtained from the central Galois product. -/
def centralNormHom {n : ℕ}
    (x : centralAffinePoints k G (MvPolynomial (Fin n) L))
    (hx : x ∈ centralAdditivePoints k G L n) :
    VectorGroup.groupScheme (CommRingCat.of k) n ⟶ G :=
  homOfAdditive (centralNormPoint k G L x) (centralNormPoint_additive k G L x hx)

/-- On the universal polynomial point, the norm homomorphism extends to the full product. -/
theorem centralNormHom_extension {n : ℕ}
    (x : centralAffinePoints k G (MvPolynomial (Fin n) L))
    (hx : x ∈ centralAdditivePoints k G L n) :
    Lie.affineMap G (MvPolynomial.mapAlgHom (Algebra.ofId k L))
      (centralNormHom k G L x hx).hom.hom =
        (centralConjugateProduct k G L (Fin n) x).val := by
  rw [centralNormHom, homOfAdditive_hom]
  exact mapCoefficients_centralNormPoint k G L x

end Langlands.GroupScheme.PolynomialPoint
