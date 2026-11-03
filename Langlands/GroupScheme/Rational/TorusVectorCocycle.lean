import Langlands.GroupScheme.Rational.SplitTorusVectorCocycle
import Langlands.GroupScheme.Rational.VectorCoordinatesBaseChange
import Langlands.GroupScheme.Torus.SplittingAssembly
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Rational coboundaries for linear vector actions of tori -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct Matrix

namespace Langlands.GroupScheme

namespace AutomorphicAction.Cocycle

variable {S : Scheme.{u}} {H J V : GroupScheme S} {a : AutomorphicAction H V}

/-- Restriction of the acting group preserves an actual coboundary. -/
theorem precomp_coboundary {T : Over S} (f : J ⟶ H) (v : T ⟶ V.X) :
    (a.coboundary v).precomp f = (a.restrict f).coboundary v := by
  apply eval_ext
  intro W b h
  simp only [eval_precomp, AutomorphicAction.eval_coboundary,
    AutomorphicAction.restrict_act]

/-- Restriction along an acting-group isomorphism reflects equality of cocycles. -/
theorem precomp_iso_injective {T : Over S} (f : J ≅ H) :
    Function.Injective (fun c : a.Cocycle T => c.precomp f.hom) := by
  intro c c' hc
  apply eval_ext
  intro W b h
  have hh := congrArg
    (fun z : (a.restrict f.hom).Cocycle T => z.eval b (h ≫ f.inv.hom.hom)) hc
  have hf : f.inv.hom.hom ≫ f.hom.hom.hom = 𝟙 H.X :=
    congrArg (fun z : H ⟶ H => z.hom.hom) f.inv_hom_id
  simpa only [eval_precomp, Category.assoc, hf, Category.comp_id] using hh

end AutomorphicAction.Cocycle

namespace VectorCocycleDescent

variable (k K : Type u) [Field k] [Field K] [Algebra k K]

/-- A linear retraction of the scalar inclusion, with no finiteness or degree premise. -/
def fieldRetraction : K →ₗ[k] k := (Algebra.linearMap k K).leftInverse

@[simp]
theorem fieldRetraction_algebraMap (x : k) :
    fieldRetraction k K (algebraMap k K x) = x :=
  LinearMap.leftInverse_apply_of_inj
    (LinearMap.ker_eq_bot.mpr (algebraMap k K).injective) x

@[simp]
theorem fieldRetraction_one : fieldRetraction k K 1 = 1 := by
  simpa only [map_one] using fieldRetraction_algebraMap k K 1

variable (A : Type u) [CommRing A] [Algebra k A]

/-- Contract the extension-field factor of an arbitrary test algebra. -/
def contract : A ⊗[k] K →ₗ[A] A :=
  (TensorProduct.AlgebraTensorModule.rid k A A).toLinearMap ∘ₗ
    (fieldRetraction k K).baseChange A

@[simp]
theorem contract_tmul (a : A) (z : K) :
    contract k K A (a ⊗ₜ[k] z) = algebraMap k A (fieldRetraction k K z) * a := by
  change (fieldRetraction k K z) • a = _
  rw [Algebra.smul_def]

@[simp]
theorem contract_includeLeft (a : A) :
    contract k K A ((Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] K) a) = a := by
  simp [Algebra.TensorProduct.includeLeft_apply]

@[simp]
theorem contract_includeRight (z : K) :
    contract k K A (Algebra.TensorProduct.includeRight z) =
      algebraMap k A (fieldRetraction k K z) := by
  simp [Algebra.TensorProduct.includeRight_apply]

/-- Contraction commutes with matrices whose coefficients come from the test algebra. -/
theorem contract_mulVec {d : ℕ} (M : Matrix (Fin d) (Fin d) A)
    (x : Fin d → A ⊗[k] K) :
    (fun j => contract k K A
      (((M.map (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] K)) *ᵥ x) j)) =
      M *ᵥ (fun j => contract k K A (x j)) := by
  funext j
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum]
  apply Finset.sum_congr rfl
  intro l hl
  change contract k K A ((algebraMap A (A ⊗[k] K) (M j l)) * x l) = _
  rw [← Algebra.smul_def, map_smul]
  rfl

end VectorCocycleDescent

namespace AutomorphicAction

variable {k : Type u} [Field k]
    {H V : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom V.X.hom]
    (a : AutomorphicAction H V) {d : ℕ} (c : Lie.FiniteCoordinates V d)
    (K : Type u) [Field K] [Algebra k K]

/-- Contraction of extension coefficients commutes with the original linear action. -/
theorem coordinateAction_contract {A : Type u} [CommRing A] [Algebra k A]
    (t : Lie.AffinePoints H A) (x : Fin d → A ⊗[k] K) :
    (fun j => VectorCocycleDescent.contract k K A
      (a.coordinateAction c (CommAlgCat.of k (A ⊗[k] K))
        (Lie.affineMap H Algebra.TensorProduct.includeLeft t) x j)) =
      a.coordinateAction c (CommAlgCat.of k A) t
        (fun j => VectorCocycleDescent.contract k K A (x j)) := by
  let f : CommAlgCat.of k A ⟶ CommAlgCat.of k (A ⊗[k] K) :=
    CommAlgCat.ofHom Algebra.TensorProduct.includeLeft
  have hm := a.coordinateMatrix_naturality c f t
  rw [← a.coordinateMatrix_mulVec, ← a.coordinateMatrix_mulVec]
  change (fun j => VectorCocycleDescent.contract k K A
    (((a.coordinateMatrix c _ (H.affinePointMap f t) :
      Matrix (Fin d) (Fin d) (A ⊗[k] K)) *ᵥ x) j)) = _
  rw [hm]
  exact VectorCocycleDescent.contract_mulVec k K A
    (a.coordinateMatrix c _ t : Matrix (Fin d) (Fin d) A) x

end AutomorphicAction

namespace RelativeRoot

variable {k : Type u} [Field k]
    {H V : GroupScheme (Spec (CommRingCat.of k))} {d : ℕ}
    (e : ∀ T : Over (Spec (CommRingCat.of k)),
      (T ⟶ V.X) ≃* Multiplicative (Fin d → Γ(T.left, ⊤)))

/-- A single rational section has the expected scalar-extended coordinates on every test. -/
theorem vectorAffineCoordinates_basePoint (he : IsNaturalVectorCoordinates e)
    (v : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ V.X)
    {A : Type u} [CommRing A] [Algebra k A] :
    (vectorAffineCoordinates e A (AutomorphicAction.Cocycle.baseMap _ ≫ v)).toAdd =
      fun j => algebraMap k A
        ((vectorAffineCoordinates e k ((Lie.affineSelfTestIso _).hom ≫ v)).toAdd j) := by
  have hv : v = (Lie.affineSelfTestIso _).inv ≫
      ((Lie.affineSelfTestIso _).hom ≫ v) := by simp
  conv_lhs => rw [hv]
  rw [← Category.assoc, Lie.baseMap_comp_affineSelfTestIso_inv]
  exact he.vectorAffineCoordinates_naturality (Algebra.ofId k A) _

variable (a : AutomorphicAction H V)
    (K : Type u) [Field K] [Algebra k K]
    {A : Type u} [CommRing A] [Algebra k A] [Algebra K A] [IsScalarTower k K A]

/-- The affine pullback-point comparison intertwines actual cocycle evaluation. -/
theorem affineBaseChangeEquiv_cocycle
    (c : a.Cocycle (Over.mk (𝟙 (Spec (CommRingCat.of k)))))
    (t : Lie.AffinePoints ((GroupScheme.baseChange (algebraBaseMap k K)).obj H) A) :
    Lie.affineBaseChangeEquiv k K V A ((c.baseChange (algebraBaseMap k K)).affineEval t) =
      c.affineEval (Lie.affineBaseChangeEquiv k K H A t) := by
  change (Lie.affineBaseTestIso k K A).inv ≫
    baseChangePointsEquiv (algebraBaseMap k K) V _
      ((c.baseChange (algebraBaseMap k K)).eval _ t) = _
  rw [AutomorphicAction.Cocycle.eval_baseChange,
    AutomorphicAction.Cocycle.baseChangeEval, MulEquiv.apply_symm_apply]
  simp only [AutomorphicAction.Cocycle.eval_eq_comp_baseHom,
    AutomorphicAction.Cocycle.affineEval]
  rfl

/-- The affine pullback-point comparison intertwines actual actions. -/
theorem affineBaseChangeEquiv_act
    (t : Lie.AffinePoints ((GroupScheme.baseChange (algebraBaseMap k K)).obj H) A)
    (v : Lie.AffinePoints ((GroupScheme.baseChange (algebraBaseMap k K)).obj V) A) :
    Lie.affineBaseChangeEquiv k K V A ((a.baseChange (algebraBaseMap k K)).act t v) =
      a.act (Lie.affineBaseChangeEquiv k K H A t)
        (Lie.affineBaseChangeEquiv k K V A v) := by
  change (Lie.affineBaseTestIso k K A).inv ≫
    baseChangePointsEquiv (algebraBaseMap k K) V _ ((a.baseChange _).act t v) = _
  rw [AutomorphicAction.baseChangePointsEquiv_act, a.naturality]
  rfl

end RelativeRoot

namespace RelativeRoot

variable {k : Type u} [Field k]
    {H V : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom V.X.hom]
    (a : AutomorphicAction H V) {d : ℕ}
    (e : ∀ T : Over (Spec (CommRingCat.of k)),
      (T ⟶ V.X) ≃* Multiplicative (Fin d → Γ(T.left, ⊤)))
    (he : IsLinearVectorCoordinates a e)

include he

/-- The split-model coboundary construction transports along an actual torus isomorphism. -/
theorem exists_coboundary_of_isSplitTorus (hH : IsSplitTorus H)
    (c : a.Cocycle (Over.mk (𝟙 (Spec (CommRingCat.of k))))) :
    ∃ v : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ V.X, c = a.coboundary v := by
  classical
  obtain ⟨I, hI, ⟨f⟩⟩ := hH
  let : Fintype I := Fintype.ofFinite I
  let b := a.restrict f.inv
  let c' := c.precomp f.inv
  refine ⟨splitTorus.cocycleConjugator I b e c', ?_⟩
  apply AutomorphicAction.Cocycle.precomp_iso_injective f.symm
  change c' = (a.coboundary _).precomp f.inv
  rw [AutomorphicAction.Cocycle.precomp_coboundary]
  exact splitTorus.cocycle_eq_coboundary I b e (he.restrict f.inv) c'

/-- An actual torus cocycle becomes a coboundary over a splitting field. -/
theorem exists_splitting_coboundary (hH : IsTorus H)
    (c : a.Cocycle (Over.mk (𝟙 (Spec (CommRingCat.of k))))) :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K)
      (v : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
        ((GroupScheme.baseChange (algebraBaseMap k K)).obj V).X),
      c.baseChange (algebraBaseMap k K) =
        (a.baseChange (algebraBaseMap k K)).coboundary v := by
  obtain ⟨K, hK, hA, hsplit⟩ := hH
  let := hK
  let := hA
  let b := algebraBaseMap k K
  let : IsAffineHom ((GroupScheme.baseChange b).obj V).X.hom := by
    change IsAffineHom (CategoryTheory.Limits.pullback.snd V.X.hom b)
    infer_instance
  obtain ⟨v, hv⟩ := exists_coboundary_of_isSplitTorus
    (a.baseChange b) (vectorBaseChangeCoordinates e K) he.baseChange hsplit (c.baseChange b)
  exact ⟨K, hK, hA, v, hv⟩

/-- A primitive over an extension gives the original affine coordinate equation
over every algebra over that extension. -/
theorem cocycleCoordinates_of_baseChange_coboundary
    (K : Type u) [Field K] [Algebra k K]
    (c : a.Cocycle (Over.mk (𝟙 (Spec (CommRingCat.of k)))))
    (v : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
      ((GroupScheme.baseChange (algebraBaseMap k K)).obj V).X)
    (hc : c.baseChange (algebraBaseMap k K) =
      (a.baseChange (algebraBaseMap k K)).coboundary v)
    {A : Type u} [CommRing A] [Algebra k A] [Algebra K A] [IsScalarTower k K A]
    (t : Lie.AffinePoints H A) :
    (vectorAffineCoordinates e A (c.affineEval t)).toAdd =
      (fun j => algebraMap K A
        ((vectorAffineCoordinates (vectorBaseChangeCoordinates e K) K
          ((Lie.affineSelfTestIso _).hom ≫ v)).toAdd j)) -
        a.coordinateAction (finiteLieCoordinatesOfVector e he.1) (CommAlgCat.of k A) t
          (fun j => algebraMap K A
            ((vectorAffineCoordinates (vectorBaseChangeCoordinates e K) K
              ((Lie.affineSelfTestIso _).hom ≫ v)).toAdd j)) := by
  let tK := (Lie.affineBaseChangeEquiv k K H A).symm t
  let w := AutomorphicAction.Cocycle.baseMap
    ((algSpec (CommRingCat.of K)).obj (op (CommAlgCat.of K A))) ≫ v
  have hw := vectorAffineCoordinates_basePoint (vectorBaseChangeCoordinates e K)
    he.1.baseChange v (A := A)
  have hw' : (vectorAffineCoordinates e A
      (Lie.affineBaseChangeEquiv k K V A w)).toAdd =
      fun j => algebraMap K A
        ((vectorAffineCoordinates (vectorBaseChangeCoordinates e K) K
          ((Lie.affineSelfTestIso _).hom ≫ v)).toAdd j) := by
    rw [← vectorAffineCoordinates_baseChange he.1]
    exact hw
  have hh := congrArg
    (fun z : (a.baseChange (algebraBaseMap k K)).Cocycle
      (Over.mk (𝟙 (Spec (CommRingCat.of K)))) =>
      (vectorAffineCoordinates e A
        (Lie.affineBaseChangeEquiv k K V A (z.affineEval tK))).toAdd) hc
  rw [affineBaseChangeEquiv_cocycle,
    MulEquiv.apply_symm_apply] at hh
  simp only [AutomorphicAction.Cocycle.affineEval, AutomorphicAction.eval_coboundary] at hh
  change _ = (vectorAffineCoordinates e A
    (Lie.affineBaseChangeEquiv k K V A
      (w * (a.baseChange (algebraBaseMap k K)).act tK w⁻¹))).toAdd at hh
  rw [map_mul, affineBaseChangeEquiv_act, MulEquiv.apply_symm_apply,
    map_inv, a.act_inv, map_mul, map_inv, toAdd_mul, toAdd_inv] at hh
  rw [he.coordinateAction_eq]
  rw [← hw', ofAdd_toAdd, MulEquiv.symm_apply_apply]
  simpa only [hw', sub_eq_add_neg, AutomorphicAction.Cocycle.affineEval] using hh

/-- Contracting a primitive over an arbitrary extension gives the coboundary
coordinate identity over every original affine test algebra. -/
theorem cocycleCoordinates_contract
    (K : Type u) [Field K] [Algebra k K]
    (c : a.Cocycle (Over.mk (𝟙 (Spec (CommRingCat.of k)))))
    (v : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
      ((GroupScheme.baseChange (algebraBaseMap k K)).obj V).X)
    (hc : c.baseChange (algebraBaseMap k K) =
      (a.baseChange (algebraBaseMap k K)).coboundary v)
    {A : Type u} [CommRing A] [Algebra k A]
    (t : Lie.AffinePoints H A) :
    (vectorAffineCoordinates e A (c.affineEval t)).toAdd =
      (fun j => algebraMap k A (VectorCocycleDescent.fieldRetraction k K
        ((vectorAffineCoordinates (vectorBaseChangeCoordinates e K) K
          ((Lie.affineSelfTestIso _).hom ≫ v)).toAdd j))) -
        a.coordinateAction (finiteLieCoordinatesOfVector e he.1) (CommAlgCat.of k A) t
          (fun j => algebraMap k A (VectorCocycleDescent.fieldRetraction k K
            ((vectorAffineCoordinates (vectorBaseChangeCoordinates e K) K
              ((Lie.affineSelfTestIso _).hom ≫ v)).toAdd j))) := by
  let : Algebra K (A ⊗[k] K) := Algebra.TensorProduct.rightAlgebra
  let : IsScalarTower k K (A ⊗[k] K) := Algebra.TensorProduct.right_isScalarTower
  let f : A →ₐ[k] A ⊗[k] K := Algebra.TensorProduct.includeLeft
  have h := cocycleCoordinates_of_baseChange_coboundary a e he K c v hc
    (Lie.affineMap H f t)
  rw [← c.affineEval_naturality, he.1.vectorAffineCoordinates_naturality] at h
  have h' := congrArg
    (fun z : Fin d → A ⊗[k] K =>
      fun j => VectorCocycleDescent.contract k K A (z j)) h
  simp only [Pi.sub_apply, map_sub] at h'
  change (fun j => VectorCocycleDescent.contract k K A
      (f ((vectorAffineCoordinates e A (c.affineEval t)).toAdd j))) =
    (fun j => VectorCocycleDescent.contract k K A
      (algebraMap K (A ⊗[k] K)
        ((vectorAffineCoordinates (vectorBaseChangeCoordinates e K) K
          ((Lie.affineSelfTestIso _).hom ≫ v)).toAdd j))) -
    (fun j => VectorCocycleDescent.contract k K A
      (a.coordinateAction (finiteLieCoordinatesOfVector e he.1)
        (CommAlgCat.of k (A ⊗[k] K)) (Lie.affineMap H f t)
        (fun j => algebraMap K (A ⊗[k] K)
          ((vectorAffineCoordinates (vectorBaseChangeCoordinates e K) K
            ((Lie.affineSelfTestIso _).hom ≫ v)).toAdd j)) j)) at h'
  rw [a.coordinateAction_contract] at h'
  simpa only [f, VectorCocycleDescent.contract_includeLeft,
    Algebra.TensorProduct.right_algebraMap_apply,
    VectorCocycleDescent.contract_tmul, mul_one] using h'

/-- For an affine acting group, a vector cocycle that is a coboundary after an
arbitrary field extension is already an actual rational coboundary. -/
theorem exists_coboundary_of_baseChange [IsAffine H.X.left]
    (K : Type u) [Field K] [Algebra k K]
    (c : a.Cocycle (Over.mk (𝟙 (Spec (CommRingCat.of k)))))
    (v : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
      ((GroupScheme.baseChange (algebraBaseMap k K)).obj V).X)
    (hc : c.baseChange (algebraBaseMap k K) =
      (a.baseChange (algebraBaseMap k K)).coboundary v) :
    ∃ w : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ V.X, c = a.coboundary w := by
  let x : Fin d → k := fun j => VectorCocycleDescent.fieldRetraction k K
    ((vectorAffineCoordinates (vectorBaseChangeCoordinates e K) K
      ((Lie.affineSelfTestIso _).hom ≫ v)).toAdd j)
  let w : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ V.X :=
    (Lie.affineSelfTestIso _).inv ≫
      (vectorAffineCoordinates e k).symm (Multiplicative.ofAdd x)
  have hw {A : Type u} [CommRing A] [Algebra k A] :
      (vectorAffineCoordinates e A
        (AutomorphicAction.Cocycle.baseMap _ ≫ w)).toAdd =
        fun j => algebraMap k A (x j) := by
    dsimp only [w]
    rw [← Category.assoc, Lie.baseMap_comp_affineSelfTestIso_inv]
    change (vectorAffineCoordinates e A
      (Lie.affineMap V (Algebra.ofId k A) _)).toAdd = _
    rw [he.1.vectorAffineCoordinates_naturality, MulEquiv.apply_symm_apply]
    rfl
  refine ⟨w, ?_⟩
  apply AutomorphicAction.Cocycle.affineEval_ext
  intro A t
  apply (vectorAffineCoordinates e A).injective
  apply Multiplicative.toAdd.injective
  have h := cocycleCoordinates_contract a e he K c v hc t
  change (vectorAffineCoordinates e A (c.affineEval t)).toAdd =
    (fun j => algebraMap k A (x j)) -
      a.coordinateAction (finiteLieCoordinatesOfVector e he.1) (CommAlgCat.of k A) t
        (fun j => algebraMap k A (x j)) at h
  rw [he.coordinateAction_eq, ← hw] at h
  simp only [ofAdd_toAdd, MulEquiv.symm_apply_apply] at h
  simpa only [AutomorphicAction.Cocycle.affineEval,
    AutomorphicAction.eval_coboundary, a.act_inv, map_mul, map_inv,
    toAdd_mul, toAdd_inv, hw, sub_eq_add_neg] using h

/-- Every actual cocycle for a torus acting scalar-linearly on a vector group
is the coboundary of an actual rational point. -/
theorem exists_coboundary_of_isTorus (hH : IsTorus H)
    (c : a.Cocycle (Over.mk (𝟙 (Spec (CommRingCat.of k))))) :
    ∃ v : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ V.X, c = a.coboundary v := by
  have : IsAffine H.X.left := SplittingAssembly.isAffine_of_isTorus H hH
  obtain ⟨K, hK, hA, v, hv⟩ := exists_splitting_coboundary a e he hH c
  let := hK
  let := hA
  exact exists_coboundary_of_baseChange a e he K c v hv

/-- An actual rational coboundary point for the supplied torus vector cocycle. -/
def torusCocycleConjugator (hH : IsTorus H)
    (c : a.Cocycle (Over.mk (𝟙 (Spec (CommRingCat.of k))))) :
    Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ V.X :=
  (exists_coboundary_of_isTorus a e he hH c).choose

/-- The chosen rational point gives equality of actual cocycle morphisms. -/
theorem cocycle_eq_coboundary_of_isTorus (hH : IsTorus H)
    (c : a.Cocycle (Over.mk (𝟙 (Spec (CommRingCat.of k))))) :
    c = a.coboundary (torusCocycleConjugator a e he hH c) :=
  (exists_coboundary_of_isTorus a e he hH c).choose_spec

end RelativeRoot

end Langlands.GroupScheme
