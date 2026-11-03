import Langlands.GroupScheme.Rational.PointedCoordinateDecompositionStatement
import Langlands.GroupScheme.Torus.WeightDecomposition
import Mathlib.LinearAlgebra.DirectSum.Finsupp

/-! # Universal coaction on actual pointed affine coordinates -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory Opposite AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.PointedCoordinateWeights

section LinearAlgebra

variable {R M J : Type*}

/-- Restricting a coefficient decomposition to a submodule stable under all coefficients. -/
theorem isInternal_comap_of_finsupp [Semiring R] [AddCommMonoid M] [Module R M]
    [DecidableEq J] (W : J → Submodule R M) (N : Submodule R M) (p : M →ₗ[R] (J →₀ M))
    (hmem : ∀ (v : M) (i : J), p v i ∈ W i)
    (hdiag : ∀ (i : J) (v : W i), p (v : M) = Finsupp.single i (v : M))
    (hsum : ∀ v : M, (p v).sum (fun _ x => x) = v)
    (hN : ∀ v ∈ N, ∀ i, p v i ∈ N) :
    DirectSum.IsInternal (fun i => (W i).comap N.subtype) := by
  let q : N →ₗ[R] (J →₀ N) :=
    { toFun := fun v => Finsupp.ofSupportFinite (fun i => ⟨p v i, hN v v.2 i⟩) (by
        refine Set.Finite.subset (p v).hasFiniteSupport ?_
        intro i hi h
        exact hi (Subtype.ext h))
      map_add' := fun v w => by
        ext i
        simp [Finsupp.ofSupportFinite_coe]
      map_smul' := fun c v => by
        ext i
        simp [Finsupp.ofSupportFinite_coe] }
  have hq (v : N) (i : J) : (q v i : M) = p v i := rfl
  have hm (v : N) : Finsupp.mapRange N.subtype (map_zero _) (q v) = p v := by
    ext i
    rfl
  apply Langlands.LinearAlgebra.isInternal_of_finsupp _ q
  · intro v i
    exact hmem v i
  · intro i v
    have hv := hdiag i ⟨((v : N) : M), v.2⟩
    ext j
    rw [hq]
    simp only at hv
    rw [hv]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [Finsupp.single_eq_of_ne' hij]
  · intro v
    apply Subtype.ext
    calc (((q v).sum fun _ x => x : N) : M) = (q v).sum (fun _ x => N.subtype x) :=
          map_finsuppSum N.subtype _ _
      _ = (Finsupp.mapRange N.subtype (map_zero _) (q v)).sum (fun _ x => x) :=
          by rw [Finsupp.sum_mapRange_index (fun _ => rfl)]
      _ = (v : M) := by rw [hm, hsum]

end LinearAlgebra

variable {k : Type u} [Field k] {V : Over (Spec (CommRingCat.of k))} [IsAffineHom V.hom]

section General

variable {S S' : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Coordinates of a translate by an extended acting point, through the actual coaction. -/
theorem pointCoordinates_act_affineMap (a : PointedAction S V)
    {A B : Type u} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
    (φ : A →ₐ[k] B) (s : Lie.AffinePoints S.toGrp A) (w : Points V B) :
    pointCoordinates (a.act (Lie.affineMap S.toGrp φ s) w) =
      (Algebra.TensorProduct.lift φ (pointCoordinates w) fun _ _ => Commute.all _ _).comp
        (actionCoordinates a s) := by
  let Φ : A ⊗[k] Coord V →ₐ[k] B :=
    Algebra.TensorProduct.lift φ (pointCoordinates w) fun _ _ => Commute.all _ _
  have hs : Lie.affineMap S.toGrp Φ
      (Lie.affineMap S.toGrp Algebra.TensorProduct.includeLeft s) =
        Lie.affineMap S.toGrp φ s := by
    rw [← Lie.affineMap_comp]
    congr 1
    ext c
    simp [Φ]
  have hv : pointsMap Φ (pointCoordinates.symm Algebra.TensorProduct.includeRight :
      Points V (A ⊗[k] Coord V)) = w := by
    apply pointCoordinates.injective
    rw [pointCoordinates_naturality, Equiv.apply_symm_apply]
    ext z
    simp [Φ]
  change _ = Φ.comp (actionCoordinates a s)
  unfold actionCoordinates
  rw [← pointCoordinates_naturality, pointsMap, a.naturality]
  change _ = pointCoordinates (a.act
    (Lie.affineMap S.toGrp Φ (Lie.affineMap S.toGrp Algebra.TensorProduct.includeLeft s))
    (pointsMap Φ (pointCoordinates.symm Algebra.TensorProduct.includeRight)))
  rw [hs, hv]

namespace PointedAction

omit [IsAffineHom V.hom] in
private theorem lift_comp_ofIso_hom (a : PointedAction S V) (e : S.toGrp ≅ S'.toGrp)
    {T : Over (Spec (CommRingCat.of k))} (s : T ⟶ S'.X) (v : T ⟶ V) :
    lift s v ≫ lift (fst _ _ ≫ e.inv.hom.hom) (snd _ _) ≫ a.hom =
      a.act (s ≫ e.inv.hom.hom) v := by
  rw [← Category.assoc, comp_lift, lift_fst_assoc, lift_snd]
  rfl

/-- The actual action of `S'` obtained by acting through an isomorphism `S ≅ S'`. -/
def ofIso (a : PointedAction S V) (e : S.toGrp ≅ S'.toGrp) : PointedAction S' V where
  hom := lift (fst _ _ ≫ e.inv.hom.hom) (snd _ _) ≫ a.hom
  origin := a.origin
  one_left v := by
    rw [lift_comp_ofIso_hom, MonObj.one_comp]
    exact a.one_left v
  mul_left s t v := by
    rw [lift_comp_ofIso_hom, lift_comp_ofIso_hom, lift_comp_ofIso_hom, MonObj.mul_comp,
      a.act_mul_left]
  origin_fixed s := by
    rw [lift_comp_ofIso_hom]
    exact a.origin_fixed _

omit [IsAffineHom V.hom] in
theorem ofIso_act (a : PointedAction S V) (e : S.toGrp ≅ S'.toGrp)
    {T : Over (Spec (CommRingCat.of k))} (s : T ⟶ S'.X) (v : T ⟶ V) :
    (a.ofIso e).act s v = a.act (s ≫ e.inv.hom.hom) v :=
  lift_comp_ofIso_hom a e s v

end PointedAction

/-- The weights of the transported action are the pulled-back characters. -/
theorem weightSpace_ofIso (a : PointedAction S V) (e : S.toGrp ≅ S'.toGrp)
    (ψ : characterLattice S') :
    weightSpace (a.ofIso e) ψ = weightSpace a (characterLattice.comapIso e ψ) := by
  have hhi : e.hom.hom.hom ≫ e.inv.hom.hom = 𝟙 _ := by
    change (e.hom ≫ e.inv).hom.hom = _
    rw [e.hom_inv_id]
    rfl
  have hih : e.inv.hom.hom ≫ e.hom.hom.hom = 𝟙 _ := by
    change (e.inv ≫ e.hom).hom.hom = _
    rw [e.inv_hom_id]
    rfl
  have hχ {A : Type u} [CommRing A] [Algebra k A] (s : Lie.AffinePoints S.toGrp A) :
      Lie.characterValue (characterLattice.comapIso e ψ) s =
        Lie.characterValue ψ (s ≫ e.hom.hom.hom) := by
    change Lie.characterValue ((Additive.ofMul e.hom : S ⟶ S') ≫ ψ) s = _
    rw [Lie.characterValue_comp]
    rfl
  ext z
  constructor
  · intro h A _ _ s v
    have h' := h A (s ≫ e.hom.hom.hom) v
    rw [PointedAction.ofIso_act, Category.assoc, hhi, Category.comp_id] at h'
    rw [hχ]
    exact h'
  · intro h A _ _ s v
    have h' := h A (s ≫ e.inv.hom.hom) v
    rw [hχ, Category.assoc, hih, Category.comp_id] at h'
    rw [PointedAction.ofIso_act]
    exact h'

end General

section SplitTorus

variable (k) (I : Type u) [Fintype I] [DecidableEq I]

local notation "𝕋" => splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I

/-- Monomial coefficients on the base-changed coordinate algebra. -/
def monomialCoefficients (V : Over (Spec (CommRingCat.of k))) [IsAffineHom V.hom] :
    AddMonoidAlgebra k (I → ℤ) ⊗[k] Coord V ≃ₗ[k] ((I → ℤ) →₀ Coord V) :=
  LinearEquiv.rTensor (Coord V) (AddMonoidAlgebra.coeffLinearEquiv k) ≪≫ₗ
    TensorProduct.finsuppScalarLeft k (Coord V) (I → ℤ)

variable {k I}

omit [DecidableEq I] in
theorem monomialCoefficients_symm_apply (f : (I → ℤ) →₀ Coord V) :
    (monomialCoefficients k I V).symm f =
      f.sum fun m c => AddMonoidAlgebra.single m (1 : k) ⊗ₜ[k] c := by
  conv_lhs => rw [← Finsupp.sum_single f]
  rw [map_finsuppSum]
  refine Finsupp.sum_congr fun m _ => ?_
  simp [monomialCoefficients, LinearEquiv.trans_symm]

omit [DecidableEq I] in
theorem monomialCoefficients_single_tmul (m : I → ℤ) (c : Coord V) :
    monomialCoefficients k I V (AddMonoidAlgebra.single m (1 : k) ⊗ₜ[k] c) =
      Finsupp.single m c := by
  apply (monomialCoefficients k I V).symm.injective
  rw [LinearEquiv.symm_apply_apply, monomialCoefficients_symm_apply,
    Finsupp.sum_single_index (by simp)]

/-- The actual coaction: translation of coordinates by the universal torus point. -/
def universalCoaction (a : PointedAction 𝕋 V) :
    Coord V →ₐ[k] AddMonoidAlgebra k (I → ℤ) ⊗[k] Coord V :=
  actionCoordinates a (splitTorus.universalPoint (R := CommRingCat.of k) I)

/-- The finitely many monomial coefficients of the actual coaction. -/
def coactionCoefficients (a : PointedAction 𝕋 V) : Coord V →ₗ[k] ((I → ℤ) →₀ Coord V) :=
  (monomialCoefficients k I V).toLinearMap ∘ₗ (universalCoaction a).toLinearMap

theorem universalCoaction_eq_sum (a : PointedAction 𝕋 V) (z : Coord V) :
    universalCoaction a z =
      (coactionCoefficients a z).sum fun m c => AddMonoidAlgebra.single m (1 : k) ⊗ₜ[k] c := by
  rw [← monomialCoefficients_symm_apply]
  simp [coactionCoefficients]

/-- Coordinates of a point translated by any specialization of the universal point. -/
theorem pointCoordinates_act_universal (a : PointedAction 𝕋 V)
    {B : Type u} [CommRing B] [Algebra k B] (φ : AddMonoidAlgebra k (I → ℤ) →ₐ[k] B)
    (w : Points V B) (z : Coord V) :
    pointCoordinates (a.act (Lie.affineMap _ φ
      (splitTorus.universalPoint (R := CommRingCat.of k) I)) w) z =
      (coactionCoefficients a z).sum fun m c =>
        φ (AddMonoidAlgebra.single m 1) * pointCoordinates w c := by
  rw [pointCoordinates_act_affineMap, AlgHom.comp_apply]
  change (Algebra.TensorProduct.lift φ (pointCoordinates w) fun _ _ => Commute.all _ _)
    (universalCoaction a z) = _
  rw [universalCoaction_eq_sum, map_finsuppSum]
  simp only [Algebra.TensorProduct.lift_tmul]

/-- Monomial coefficients of a translate of a constant point. -/
theorem coeff_pointCoordinates_act_universal (a : PointedAction 𝕋 V)
    {A : Type u} [CommRing A] [Algebra k A]
    (φ : AddMonoidAlgebra k (I → ℤ) →ₐ[k] AddMonoidAlgebra A (I → ℤ)) (c : (I → ℤ) → A)
    (hφ : ∀ m, φ (AddMonoidAlgebra.single m 1) = AddMonoidAlgebra.single m (c m))
    (w : Points V A) (z : Coord V) (n : I → ℤ) :
    (pointCoordinates (a.act (Lie.affineMap _ φ
      (splitTorus.universalPoint (R := CommRingCat.of k) I))
      (pointsMap (IsScalarTower.toAlgHom k A (AddMonoidAlgebra A (I → ℤ))) w)) z).coeff n =
      c n * pointCoordinates w (coactionCoefficients a z n) := by
  classical
  rw [pointCoordinates_act_universal]
  simp only [pointCoordinates_naturality, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', hφ,
    AddMonoidAlgebra.coe_algebraMap, Function.comp_apply, AddMonoidAlgebra.single_mul_single,
    add_zero, AddMonoidAlgebra.coeff_finsuppSum, AddMonoidAlgebra.coeff_single, Algebra.algebraMap_self,
    RingHom.id_apply]
  rw [Finsupp.sum_apply, Finsupp.sum_eq_single n]
  · simp
  · intro b _ hb
    simp [Finsupp.single_eq_of_ne' hb]
  · intro _
    simp

omit [DecidableEq I] in
theorem exponentValue_map {A B : Type u} [CommRing A] [CommRing B] (g : Aˣ →* Bˣ)
    (t : I → Aˣ) (m : Multiplicative (I → ℤ)) :
    splitTorus.exponentValue I (fun i => g (t i)) m = g (splitTorus.exponentValue I t m) := by
  simp [splitTorus.exponentValue, map_prod, map_zpow]

/-- Each coaction coefficient is a coordinate weight vector for the matching character. -/
theorem coactionCoefficients_mem (a : PointedAction 𝕋 V) (z : Coord V) (m : I → ℤ) :
    coactionCoefficients a z m ∈
      weightSpace a ((splitTorus.characterLatticeEquiv k I).symm m) := by
  intro A _ _ s v
  let t := splitTorus.algebraPointsEquiv I A s
  let incl := IsScalarTower.toAlgHom k A (AddMonoidAlgebra A (I → ℤ))
  let constMap : AddMonoidAlgebra k (I → ℤ) →ₐ[k] AddMonoidAlgebra A (I → ℤ) :=
    AddMonoidAlgebra.mapAlgHom (I → ℤ) (Algebra.ofId k A)
  let τ : AddMonoidAlgebra k (I → ℤ) →ₐ[k] AddMonoidAlgebra A (I → ℤ) :=
    splitTorus.translatedEvaluation (R := CommRingCat.of k) I t
  let U : Lie.AffinePoints (𝕋).toGrp (AddMonoidAlgebra k (I → ℤ)) :=
    splitTorus.universalPoint (R := CommRingCat.of k) I
  have hcomm : Lie.affineMap (𝕋).toGrp τ U =
      Lie.affineMap (𝕋).toGrp constMap U * Lie.affineMap (𝕋).toGrp incl s := by
    have h := splitTorus.universalPoint_translatedEvaluation (R := CommRingCat.of k) I t
    rw [MulEquiv.symm_apply_apply] at h
    change Lie.affineMap (𝕋).toGrp τ U = _ at h
    rw [h]
    apply (splitTorus.algebraPointsEquiv I _).injective
    rw [map_mul, map_mul, mul_comm]
  have hpt : a.act (Lie.affineMap (𝕋).toGrp τ U) (pointsMap incl v) =
      a.act (Lie.affineMap (𝕋).toGrp constMap U) (pointsMap incl (a.act s v)) := by
    rw [hcomm, a.act_mul_left]
    congr 1
    rw [pointsMap, pointsMap, a.naturality]
    rfl
  have h1 := coeff_pointCoordinates_act_universal a τ
    (fun m => (splitTorus.exponentValue I t (Multiplicative.ofAdd m) : A))
    (fun m => (splitTorus.translatedEvaluation_single (R := CommRingCat.of k) I t m 1).trans
      (by rw [map_one, one_mul])) v z m
  have h2 := coeff_pointCoordinates_act_universal a constMap (fun _ => 1)
    (by intro m; simp [constMap]) (a.act s v) z m
  change (pointCoordinates (a.act (Lie.affineMap (𝕋).toGrp τ U) (pointsMap incl v)) z).coeff m = _
    at h1
  change (pointCoordinates (a.act (Lie.affineMap (𝕋).toGrp constMap U)
    (pointsMap incl (a.act s v))) z).coeff m = _ at h2
  rw [hpt, h2, one_mul] at h1
  rw [h1, splitTorus.characterValue_characterLatticeEquiv_symm]

/-- On a coordinate weight space the coaction is a single monomial. -/
theorem coactionCoefficients_of_mem (a : PointedAction 𝕋 V) (m : I → ℤ) (z : Coord V)
    (hz : z ∈ weightSpace a ((splitTorus.characterLatticeEquiv k I).symm m)) :
    coactionCoefficients a z = Finsupp.single m z := by
  have h := hz (AddMonoidAlgebra k (I → ℤ) ⊗[k] Coord V)
    (Lie.affineMap _ Algebra.TensorProduct.includeLeft
      (splitTorus.universalPoint (R := CommRingCat.of k) I))
    (pointCoordinates.symm Algebra.TensorProduct.includeRight)
  rw [splitTorus.characterValue_characterLatticeEquiv_symm,
    splitTorus.algebraPointsEquiv_naturality, exponentValue_map,
    splitTorus.exponentValue_universalPoint, Equiv.apply_symm_apply] at h
  change universalCoaction a z = _ at h
  rw [coactionCoefficients, LinearMap.comp_apply, AlgHom.toLinearMap_apply, h]
  simp [Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.tmul_mul_tmul, monomialCoefficients_single_tmul]

/-- The coaction coefficients sum back to the coordinate. -/
theorem coactionCoefficients_sum (a : PointedAction 𝕋 V) (z : Coord V) :
    (coactionCoefficients a z).sum (fun _ c => c) = z := by
  have h := pointCoordinates_act_universal a
    (splitTorus.evaluateUnits (R := CommRingCat.of k) I (fun _ => (1 : (Coord V)ˣ)))
    (universalPoint V) z
  have h1 : Lie.affineMap (𝕋).toGrp
      (splitTorus.evaluateUnits (R := CommRingCat.of k) I (fun _ => (1 : (Coord V)ˣ)))
      (splitTorus.universalPoint (R := CommRingCat.of k) I) = 1 := by
    rw [splitTorus.universalPoint_evaluateUnits]
    exact map_one _
  have he (m : I → ℤ) : splitTorus.evaluateUnits (R := CommRingCat.of k) I
      (fun _ => (1 : (Coord V)ˣ)) (AddMonoidAlgebra.single m 1) = 1 :=
    (splitTorus.evaluateUnits_single (R := CommRingCat.of k) I _ m 1).trans
      (by simp [splitTorus.exponentValue])
  rw [h1, a.act_one_left, coordinates_universalPoint] at h
  simpa [he] using h.symm

/-- Coaction coefficients of an augmentation function lie in the augmentation. -/
theorem coactionCoefficients_mem_augmentation (a : PointedAction 𝕋 V) {z : Coord V}
    (hz : z ∈ augmentation a) (m : I → ℤ) : coactionCoefficients a z m ∈ augmentation a := by
  have h := coeff_pointCoordinates_act_universal a (A := k)
    (AddMonoidAlgebra.mapAlgHom (I → ℤ) (Algebra.ofId k k)) (fun _ => 1)
    (by intro m; simp) (toUnit _ ≫ a.origin) z m
  have ho : pointsMap (IsScalarTower.toAlgHom k k (AddMonoidAlgebra k (I → ℤ)))
      (toUnit _ ≫ a.origin : Points V k) = toUnit _ ≫ a.origin := by
    simp only [pointsMap, comp_toUnit_assoc]
  rw [ho, a.act_origin, pointCoordinates_origin, AlgHom.comp_apply] at h
  rw [mem_augmentation] at hz ⊢
  rw [hz, map_zero, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, one_mul] at h
  exact h.symm

open Classical in
/-- An action of a group isomorphic to the standard split torus decomposes actual pointed
coordinates and their augmentation. -/
theorem isInternal_of_iso_splitTorus {S : CommGroupScheme (Spec (CommRingCat.of k))}
    (a : PointedAction S V) (e : S.toGrp ≅ (𝕋).toGrp) :
    DirectSum.IsInternal (weightSpace a) ∧
      DirectSum.IsInternal (augmentationWeightSpace a) := by
  classical
  let b := a.ofIso e
  let c : (I → ℤ) ≃+ characterLattice S :=
    (splitTorus.characterLatticeEquiv k I).symm.trans (characterLattice.comapIso e)
  let p : Coord V →ₗ[k] (characterLattice S →₀ Coord V) :=
    (Finsupp.lmapDomain (Coord V) k c).comp (coactionCoefficients b)
  have hc (m : I → ℤ) : weightSpace b ((splitTorus.characterLatticeEquiv k I).symm m) =
      weightSpace a (c m) :=
    weightSpace_ofIso a e _
  have hp (z : Coord V) (m : I → ℤ) : p z (c m) = coactionCoefficients b z m :=
    Finsupp.mapDomain_apply_of_injective c.injective (coactionCoefficients b z) m
  have hmem (z : Coord V) (χ : characterLattice S) : p z χ ∈ weightSpace a χ := by
    obtain ⟨m, rfl⟩ := c.surjective χ
    rw [hp, ← hc]
    exact coactionCoefficients_mem b z m
  have hdiag (χ : characterLattice S) (z : weightSpace a χ) :
      p (z : Coord V) = Finsupp.single χ (z : Coord V) := by
    obtain ⟨m, rfl⟩ := c.surjective χ
    have hz : (z : Coord V) ∈ weightSpace b ((splitTorus.characterLatticeEquiv k I).symm m) := by
      rw [hc]
      exact z.property
    change Finsupp.mapDomain c (coactionCoefficients b (z : Coord V)) = _
    rw [coactionCoefficients_of_mem b m z hz, Finsupp.mapDomain_single]
  have hsum (z : Coord V) : (p z).sum (fun _ y => y) = z := by
    change (Finsupp.mapDomain c (coactionCoefficients b z)).sum (fun _ y => y) = z
    rw [Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)]
    exact coactionCoefficients_sum b z
  refine ⟨Langlands.LinearAlgebra.isInternal_of_finsupp _ p hmem hdiag hsum, ?_⟩
  apply isInternal_comap_of_finsupp (weightSpace a) (augmentation a) p hmem hdiag hsum
  intro z hz χ
  obtain ⟨m, rfl⟩ := c.surjective χ
  rw [hp]
  exact coactionCoefficients_mem_augmentation b hz m

end SplitTorus

end Langlands.GroupScheme.PointedCoordinateWeights
