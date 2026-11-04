import Langlands.GroupScheme.Unipotent.OneDimensional.Core
import Langlands.GroupScheme.Unipotent.OneDimensional.Dimension
import Langlands.GroupScheme.CorepresentedSmooth
import Langlands.AlgebraicGeometry.FieldSmoothTopologicalKrullDimProof
import Langlands.AlgebraicGeometry.FieldSmoothClosedPointStalkDimensionProof
import Mathlib.AlgebraicGeometry.Geometrically.Integral

/-! # Geometric input for the one-dimensional classification -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry Polynomial TensorProduct

namespace Langlands.GroupScheme.Unipotent.OneDimensional

open AffineLinearEmbedding

variable {k : Type u} [Field k]
  {F : CommAlgCat.{u} (CommRingCat.of k) ⥤ GrpCat.{u}}
  {B : CommAlgCat.{u} (CommRingCat.of k)}
  (e : (F ⋙ forget GrpCat).CorepresentableBy B)

/-- A smooth corepresented group has finitely generated coordinates. -/
theorem finiteType_of_smooth [Smooth (Corepresented.groupScheme F e).X.hom] :
    Algebra.FiniteType k B := by
  have : Algebra.Smooth k B := (Corepresented.smooth_groupScheme_iff (e := e)).1 inferInstance
  infer_instance

/-- A corepresented group smooth of relative dimension one has coordinates of Krull
dimension at most one. -/
theorem ringKrullDim_le_one
    [SmoothOfRelativeDimension 1 (Corepresented.groupScheme F e).X.hom] :
    ringKrullDim B ≤ 1 := by
  have : CompactSpace (Corepresented.groupScheme F e).X.left :=
    inferInstanceAs (CompactSpace (PrimeSpectrum B))
  have h := Langlands.AlgebraicGeometry.fieldSmoothTopologicalKrullDim k _
    (Corepresented.groupScheme F e).X.hom 1 inferInstance this
  change topologicalKrullDim (PrimeSpectrum B) ≤ _ at h
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim] at h
  exact_mod_cast h

/-- A corepresented group smooth of relative dimension one has a nonconstant coordinate. -/
theorem exists_not_mem_span_one [IsDomain B]
    [SmoothOfRelativeDimension 1 (Corepresented.groupScheme F e).X.hom] :
    ∃ a : B, a ∉ k ∙ (1 : B) := by
  by_contra h
  push Not at h
  have hsurj : Function.Surjective (algebraMap k B) := fun a => by
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (h a)
    exact ⟨c, by rw [← hc, Algebra.smul_def, mul_one]⟩
  let φ : k ≃+* B :=
    RingEquiv.ofBijective (algebraMap k B) ⟨(algebraMap k B).injective, hsurj⟩
  have : IsIso (CommRingCat.ofHom (algebraMap k B) : CommRingCat.of k ⟶ CommRingCat.of B) :=
    (inferInstance : IsIso φ.toCommRingCatIso.hom)
  have : IsIso (Corepresented.groupScheme F e).X.hom := by
    change IsIso (Spec.map (CommRingCat.ofHom (algebraMap k B)))
    infer_instance
  -- The scheme is a single point, at which the stalk would have dimension both `0` and `1`.
  have : Subsingleton (Spec (CommRingCat.of k)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum k))
  have : Nonempty (Spec (CommRingCat.of k)) :=
    inferInstanceAs (Nonempty (PrimeSpectrum k))
  let hX := Scheme.homeoOfIso (asIso (Corepresented.groupScheme F e).X.hom)
  have : Subsingleton (Corepresented.groupScheme F e).X.left := hX.injective.subsingleton
  let x : (Corepresented.groupScheme F e).X.left := hX.symm (Classical.arbitrary _)
  have hx : IsClosed ({x} : Set (Corepresented.groupScheme F e).X.left) := by
    rw [show ({x} : Set (Corepresented.groupScheme F e).X.left) = Set.univ from
      Set.eq_univ_of_forall fun y => Subsingleton.elim y x]
    exact isClosed_univ
  have h1 := Langlands.AlgebraicGeometry.fieldSmoothClosedPointStalkDimension k _
    (Corepresented.groupScheme F e).X.hom 1 inferInstance x hx
  have h0 := Langlands.AlgebraicGeometry.fieldSmoothClosedPointStalkDimension k _
    (Corepresented.groupScheme F e).X.hom 0 inferInstance x hx
  rw [h1] at h0
  simp at h0

/-- A smooth connected corepresented group has a domain as tensor square of its coordinates. -/
theorem isDomain_tensor [IsDomain B] [Smooth (Corepresented.groupScheme F e).X.hom]
    [ConnectedSpace (Corepresented.groupScheme F e).X.left] : IsDomain (B ⊗[k] B) := by
  let K := FractionRing B
  let : IsAffine (Corepresented.groupScheme F e).X.left := by
    change IsAffine (Spec (CommRingCat.of B))
    infer_instance
  have hgi : GeometricallyIntegral (Corepresented.groupScheme F e).X.hom :=
    smoothConnectedAffineGeometry.1 k (Corepresented.groupScheme F e)
      inferInstance inferInstance inferInstance
  have hpb := isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct k B K)
  have hint : IsIntegral (Spec (CommRingCat.of (B ⊗[k] K))) :=
    hgi.geometrically_isIntegral (Spec.map (CommRingCat.ofHom (algebraMap k K))) _ _ hpb
  have : IsDomain (B ⊗[k] K) := (affine_isIntegral_iff (CommRingCat.of (B ⊗[k] K))).1 hint
  let ι : B ⊗[k] B →ₐ[k] B ⊗[k] K :=
    Algebra.TensorProduct.map (AlgHom.id k B) (IsScalarTower.toAlgHom k B K)
  have hinj : Function.Injective ι :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := B)
      (IsScalarTower.toAlgHom k B K).toLinearMap (IsFractionRing.injective B K)
  exact hinj.isDomain ι.toRingHom

/-- A nonconstant polynomial in a nonzero primitive coordinate of a smooth group with domain
coordinates is not a unit: the coordinate defines a surjection onto the affine line. -/
theorem not_isUnit_aeval [IsDomain B] [Smooth (Corepresented.groupScheme F e).X.hom] {z : B}
    (hz : letI := bialgebra e; Bialgebra.IsPrimitiveElem k z) (hz0 : z ≠ 0) {g : k[X]}
    (hg : 0 < g.natDegree) : ¬ IsUnit (aeval z g) := by
  intro hu
  have hq := isFppfQuotient_quotientMap_of_isPrimitiveElem e hz hz0
  let φ : MvPolynomial (Fin 1) k →ₐ[k] B := MvPolynomial.aeval (fun _ : Fin 1 => z)
  have hs : Function.Surjective (PrimeSpectrum.comap (φ : MvPolynomial (Fin 1) k →+* B)) := by
    have h := hq.2.1.surj
    rw [VectorGroup.quotientMap_left] at h
    exact h
  let G' : MvPolynomial (Fin 1) k := aeval (MvPolynomial.X 0) g
  have hG : φ G' = aeval z g := by
    simp only [G', φ]
    rw [← Polynomial.aeval_algHom_apply, MvPolynomial.aeval_X]
  have hG' : ¬ IsUnit G' := by
    intro h
    have h' := h.map (MvPolynomial.aeval (fun _ : Fin 1 => (X : k[X])))
    rw [← Polynomial.aeval_algHom_apply, MvPolynomial.aeval_X,
      Polynomial.aeval_X_left_apply] at h'
    exact hg.ne' (Polynomial.natDegree_eq_zero_of_isUnit h')
  obtain ⟨m, hm, hGm⟩ := Ideal.exists_le_maximal (Ideal.span {G'})
    (by rwa [Ne, Ideal.span_singleton_eq_top])
  obtain ⟨P, hP⟩ := hs (⟨m, hm.isPrime⟩ : PrimeSpectrum (MvPolynomial (Fin 1) k))
  have hmem : G' ∈ (PrimeSpectrum.comap (φ : MvPolynomial (Fin 1) k →+* B) P).asIdeal := by
    rw [hP]
    exact hGm (Ideal.mem_span_singleton_self G')
  rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap] at hmem
  change φ G' ∈ P.asIdeal at hmem
  rw [hG] at hmem
  exact P.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem hu)

/-- **Geometric form of the core.** The coordinate ring of a connected unipotent corepresented
group smooth of relative dimension one over a perfect field is a polynomial ring in one
primitive element. -/
theorem exists_primitive_bijective_of_smooth [PerfectField k]
    [SmoothOfRelativeDimension 1 (Corepresented.groupScheme F e).X.hom]
    [ConnectedSpace (Corepresented.groupScheme F e).X.left]
    (hU : IsUnipotent (Corepresented.groupScheme F e)) :
    ∃ y : B, (letI := bialgebra e; Bialgebra.IsPrimitiveElem k y) ∧
      Function.Bijective (aeval y : k[X] →ₐ[k] B) := by
  have : Smooth (Corepresented.groupScheme F e).X.hom :=
    SmoothOfRelativeDimension.smooth 1 _
  have : IsDomain B := isDomain_of_smooth_connected e
  have : Algebra.FiniteType k B := finiteType_of_smooth e
  have : IsDomain (B ⊗[k] B) := isDomain_tensor e
  have hdim := ringKrullDim_le_one e
  exact exists_primitive_bijective e (oneMemStable_of_isUnipotent e hU)
    (exists_not_mem_span_one e)
    (fun _ _ hz0 => finite_quotient_span_singleton hdim hz0)
    (fun y t _ _ => exists_ev2_eq_zero (trdeg_le_one hdim) y t)
    (fun _ hz hz0 _ hg => not_isUnit_aeval e hz hz0 hg)

end Langlands.GroupScheme.Unipotent.OneDimensional
