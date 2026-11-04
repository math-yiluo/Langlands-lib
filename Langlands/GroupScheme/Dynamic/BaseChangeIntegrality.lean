import Langlands.GroupScheme.Dynamic.BaseChangeComparison

/-! # Integrality of dynamic unipotent points through a homomorphism out of a base change

Let `G = Spec B` be a corepresented affine group of finite type over a field `k` with a
cocharacter `ν`, let `Ω` be a field extension of `k` and `π : G_Ω ⟶ H` a homomorphism to an
affine `Ω`-group. Let `R` be a DVR over `k` with geometrically reduced residue field, and assume
that nonzero finitely generated geometrically reduced `k`-algebras have `k`-points. Suppose
that the only `k`-point of `U_G(ν)` whose base change has the same image under `π` as the
identity is the identity. Then a point `u ∈ U_G(ν)(Frac R)` is defined over `R` as soon as
the functions on `H` take values in `Ω ⊗[k] R` at `π(u_Ω)`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme

namespace Corepresented

open CommutativeAlgebra.GradedDVRIntegrality

variable {k : Type u} [Field k] {F : CommAlgCat.{u} (CommRingCat.of k) ⥤ GrpCat.{u}}
  {B : CommAlgCat.{u} (CommRingCat.of k)} {e : (F ⋙ forget GrpCat).CorepresentableBy B}
  {Ω : Type u} [Field Ω] [Algebra k Ω]

section Classifying

variable {A : Type u} [CommRing A] [Algebra k A]

/-- The classifying map of the base change of the point given by `φ : B → A` is `Ω ⊗ φ`. -/
theorem classifying_bcPoint_includeRight (φ : B →ₐ[k] A) (m : Ω ⊗[k] B) :
    classifying (bcPoint F e Ω (Ω ⊗[k] A) (Algebra.TensorProduct.includeRight.comp φ)) m =
      φ.toLinearMap.lTensor Ω m := by
  induction m with
  | tmul ω b =>
    rw [classifying, Algebra.TensorProduct.lift_tmul, pointAlgHom_basePoint_bcPoint,
      LinearMap.lTensor_tmul]
    change (ω ⊗ₜ[k] (1 : A)) * ((1 : Ω) ⊗ₜ[k] φ b) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- The classifying map of the base change of a `k`-point `a` is `Ω ⊗ a` followed by
`Ω ⊗[k] k ≅ Ω`. -/
theorem classifying_bcPoint_ofId (a : B →ₐ[k] k) (m : Ω ⊗[k] B) :
    classifying (bcPoint F e Ω Ω ((Algebra.ofId k Ω).comp a)) m =
      TensorProduct.rid k Ω (a.toLinearMap.lTensor Ω m) := by
  induction m with
  | tmul ω b =>
    rw [classifying, Algebra.TensorProduct.lift_tmul, pointAlgHom_basePoint_bcPoint,
      LinearMap.lTensor_tmul, TensorProduct.rid_tmul]
    change ω * algebraMap k Ω (a b) = a b • ω
    rw [Algebra.smul_def, mul_comm]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

end Classifying

variable [Algebra.FiniteType k B]
  {H : GroupScheme (Spec (CommRingCat.of Ω))} [IsAffine H.X.left]
  (π : baseChangeGroup F e Ω ⟶ H) (ν : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ groupScheme F e)

/-- **Integrality through a comparison homomorphism.** Let `u ∈ U_G(ν)(Frac R)`. If every
function on `H` takes a value in `Ω ⊗[k] R` at `π(u_Ω)`, and the only contracting `k`-point
`a` with `π(a_Ω) = π(1)` is the counit, then `u` takes values in `R`. -/
theorem integral_of_baseChange_comparison
    (hker : ∀ a : B →ₐ[k] k, IsContracting (coaction ν).hom (counitAlgHom e) a →
      bcPoint F e Ω Ω ((Algebra.ofId k Ω).comp a) ≫ π.hom.hom =
        bcPoint F e Ω Ω ((Algebra.ofId k Ω).comp (counitAlgHom e)) ≫ π.hom.hom →
      a = counitAlgHom e)
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Algebra k R]
    (hF : Algebra.IsGeometricallyReduced k (ResidueField R))
    (hrat : ∀ (R' : Type u) [CommRing R'] [Algebra k R'] [Algebra.FiniteType k R']
      [Nontrivial R'] [Algebra.IsGeometricallyReduced k R'], Nonempty (R' →ₐ[k] k))
    (u : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k (FractionRing R)))) ⟶
      (groupScheme F e).X)
    (hu : u ∈ (Dynamic.unipotent ν).carrier _)
    (hint : ∀ f : Γ(H.X.left, ⊤), Dynamic.AffineChart.pointRing
        (bcPoint F e Ω (Ω ⊗[k] FractionRing R)
          (Algebra.TensorProduct.includeRight.comp (pointAlgHom u)) ≫ π.hom.hom) f ∈
        (Algebra.TensorProduct.map (AlgHom.id k Ω)
          (IsScalarTower.toAlgHom k R (FractionRing R))).range) :
    ∀ b : B, pointAlgHom u b ∈ (algebraMap R (FractionRing R)).range := by
  refine integral_of_contracting_tensor (isGrading_coaction ν) (counitAlgHom e)
    (counit_coeff_coaction ν) (Set.range (comparisonMap π)) ?_ ?_ hF hrat (pointAlgHom u)
    ((isContracting_pointAlgHom_iff ν u).2 hu) ?_
  · rintro _ ⟨f, rfl⟩ n
    exact ⟨_, (lTensor_weightPart_comparisonMap ν π f n).symm⟩
  · intro a ha hagree
    refine hker a ha (Dynamic.AffineChart.hom_ext_of_pointRing ?_)
    rw [pointRing_comp_eq, pointRing_comp_eq]
    refine CommRingCat.hom_ext (RingHom.ext fun f => ?_)
    change classifying _ (comparisonMap π f) = classifying _ (comparisonMap π f)
    rw [classifying_bcPoint_ofId, classifying_bcPoint_ofId, hagree _ ⟨f, rfl⟩]
  · rintro _ ⟨f, rfl⟩
    obtain ⟨z, hz⟩ := hint f
    refine ⟨z, ?_⟩
    rw [pointRing_comp_eq] at hz
    change _ = classifying _ (comparisonMap π f) at hz
    rw [classifying_bcPoint_includeRight] at hz
    exact hz

theorem specMap_algebraMap_fractionRing {R : Type u} [CommRing R] [IsDomain R] [Algebra k R] :
    Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k R)) =
      Spec.map (CommRingCat.ofHom (algebraMap k (FractionRing R))) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

/-- **Extension of a dynamic unipotent point over the DVR.** Under the hypotheses of
`integral_of_baseChange_comparison`, the point `u` extends to a point of `U_G(ν)` over `R`. -/
theorem exists_point_of_baseChange_comparison
    (hker : ∀ a : B →ₐ[k] k, IsContracting (coaction ν).hom (counitAlgHom e) a →
      bcPoint F e Ω Ω ((Algebra.ofId k Ω).comp a) ≫ π.hom.hom =
        bcPoint F e Ω Ω ((Algebra.ofId k Ω).comp (counitAlgHom e)) ≫ π.hom.hom →
      a = counitAlgHom e)
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Algebra k R]
    (hF : Algebra.IsGeometricallyReduced k (ResidueField R))
    (hrat : ∀ (R' : Type u) [CommRing R'] [Algebra k R'] [Algebra.FiniteType k R']
      [Nontrivial R'] [Algebra.IsGeometricallyReduced k R'], Nonempty (R' →ₐ[k] k))
    (u : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k (FractionRing R)))) ⟶
      (groupScheme F e).X)
    (hu : u ∈ (Dynamic.unipotent ν).carrier _)
    (hint : ∀ f : Γ(H.X.left, ⊤), Dynamic.AffineChart.pointRing
        (bcPoint F e Ω (Ω ⊗[k] FractionRing R)
          (Algebra.TensorProduct.includeRight.comp (pointAlgHom u)) ≫ π.hom.hom) f ∈
        (Algebra.TensorProduct.map (AlgHom.id k Ω)
          (IsScalarTower.toAlgHom k R (FractionRing R))).range) :
    ∃ uR : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k R))) ⟶ (groupScheme F e).X,
      uR ∈ (Dynamic.unipotent ν).carrier _ ∧
        Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))))
          specMap_algebraMap_fractionRing ≫ uR = u := by
  have hξ := integral_of_baseChange_comparison π ν hker hF hrat u hu hint
  let incl := IsScalarTower.toAlgHom k R (FractionRing R)
  have hinj : Function.Injective incl := IsFractionRing.injective R (FractionRing R)
  let ξK : B →ₐ[k] incl.range := (pointAlgHom u).codRestrict incl.range fun b => by
    obtain ⟨r, hr⟩ := hξ b
    exact ⟨r, hr⟩
  let ξR : B →ₐ[k] R := (AlgEquiv.ofInjective incl hinj).symm.toAlgHom.comp ξK
  have hcomp : ∀ b, incl (ξR b) = pointAlgHom u b := by
    intro b
    have h := congrArg Subtype.val (AlgEquiv.apply_symm_apply (AlgEquiv.ofInjective incl hinj)
      (ξK b))
    rw [AlgEquiv.ofInjective_apply] at h
    exact h
  have hc := (isContracting_pointAlgHom_iff ν u).2 hu
  refine ⟨ofAlgHom F e ξR, ?_, ?_⟩
  · rw [← isContracting_pointAlgHom_iff, pointAlgHom_ofAlgHom]
    refine ⟨fun b n hn => hinj ?_, fun b => hinj ?_⟩
    · rw [hcomp, map_zero]
      exact hc.1 b n hn
    · rw [hcomp, AlgHom.commutes]
      exact hc.2 b
  · apply hom_ext_of_pointRing
    refine CommRingCat.hom_ext (RingHom.ext fun b => ?_)
    change Spec.preimage (Spec.map _ ≫ Spec.map _) b = _
    rw [← Spec.map_comp, Spec.preimage_map]
    exact hcomp b

end Corepresented

end Langlands.GroupScheme
