import Langlands.CommutativeAlgebra.Popescu.GeometricRegularityFlatStatement
import Langlands.CommutativeAlgebra.Popescu.GeometricRegularityH1InjectiveStatement
import Langlands.CommutativeAlgebra.Popescu.FieldH1CotangentInjectiveStatement
import Langlands.CommutativeAlgebra.Popescu.GeometricRegularityFlatTools
import Langlands.CommutativeAlgebra.Popescu.FieldH1CotangentInjectiveProof
import Langlands.CommutativeAlgebra.Popescu.RegularSequenceFlat
import Langlands.CommutativeAlgebra.Popescu.RegularLocalParametersProof
import Langlands.CommutativeAlgebra.Popescu.GeometricRegularityH1InjectiveProof

/-! # Proof of Stacks 07E6 from 07E5, 07E2, 07DY and 00NQ -/

universe u

namespace Langlands.CommutativeAlgebra.Popescu

namespace GeometricRegularity

open IsLocalRing MvPolynomial

open scoped TensorProduct

section abstract

variable {k A₀ A : Type u} [Field k] [CommRing A₀] [CommRing A] [IsLocalRing A₀] [IsLocalRing A]
  [Algebra k A₀] [Algebra k A] [Algebra A₀ A] [IsScalarTower k A₀ A]
  [IsLocalHom (algebraMap A₀ A)]

/-- Under the hypotheses of `cotangent_independent`, a minimal generating family of `𝔪_{A₀}` maps
to a family in `𝔪_A` with linearly independent classes in `𝔪_A/𝔪_A²`. -/
theorem rsop_independent [IsNoetherianRing A₀]
    (hK3 : Function.Injective (Algebra.H1Cotangent.map k A (ResidueField A) (ResidueField A)))
    (hK2 : Function.Injective ((Algebra.H1Cotangent.map k k (ResidueField A₀)
      (ResidueField A)).liftBaseChange (ResidueField A)))
    (hΩ : Function.Injective (KaehlerDifferential.mapBaseChange k A₀ (ResidueField A₀)))
    (x : Fin (maximalIdeal A₀).spanFinrank → A₀)
    (hx : Ideal.span (Set.range x) = maximalIdeal A₀) (hxm : ∀ i, x i ∈ maximalIdeal A₀) :
    LinearIndependent (ResidueField A) fun i => (maximalIdeal A).toCotangent
      ⟨algebraMap A₀ A (x i), map_nonunit (algebraMap A₀ A) (x i) (hxm i)⟩ := by
  have hspanA : Submodule.span A₀
      (Set.range fun i => (⟨x i, hxm i⟩ : maximalIdeal A₀)) = ⊤ := by
    apply Submodule.map_injective_of_injective (maximalIdeal A₀).injective_subtype
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp]
    exact hx
  have hspan := (CotangentSpace.span_image_eq_top_iff (R := A₀)).mpr hspanA
  rw [← Set.range_comp] at hspan
  have hli₀ : LinearIndependent (ResidueField A₀) fun i =>
      (maximalIdeal A₀).toCotangent ⟨x i, hxm i⟩ :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hspan.ge (by
      rw [Fintype.card_fin, IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace])
  have hx₀ := (FiniteTypeIntGRing.linearIndependent_toCotangent_iff x hxm).mp hli₀
  refine (FiniteTypeIntGRing.linearIndependent_toCotangent_iff
    (fun i => algebraMap A₀ A (x i)) _).mpr ?_
  intro a ha i
  exact cotangent_independent hK3 hK2 hΩ x hxm hx₀ a ha i

end abstract

/-- Flatness and regularity of the closed fibre from a minimal generating family of `𝔪_{A₀}`
whose image has linearly independent classes in `𝔪_A/𝔪_A²`: the family is a regular sequence in
`A₀` (00NQ) and its image is weakly regular in `A`, so `A` is flat over `A₀` (07DY); the quotient
is regular local by the Library lemma on quotients by part of a regular system of parameters. -/
theorem flat_regular_of_rsop (hN3 : RegularSequenceFlatStatement.{u})
    (h00NQ : RegularLocalParametersStatement.{u}) {A₀ A : Type u} [CommRing A₀] [CommRing A]
    [IsRegularLocalRing A₀] [IsRegularLocalRing A] [Algebra A₀ A]
    [IsLocalHom (algebraMap A₀ A)]
    (x : Fin (maximalIdeal A₀).spanFinrank → A₀)
    (hx : Ideal.span (Set.range x) = maximalIdeal A₀)
    (hxm : ∀ i, algebraMap A₀ A (x i) ∈ maximalIdeal A)
    (hli : LinearIndependent (ResidueField A) fun i => (maximalIdeal A).toCotangent
      ⟨algebraMap A₀ A (x i), hxm i⟩) :
    Module.Flat A₀ A ∧ IsRegularLocalRing (A ⧸ (maximalIdeal A₀).map (algebraMap A₀ A)) := by
  have hmap : (maximalIdeal A₀).map (algebraMap A₀ A) =
      Ideal.span (Set.range fun i => algebraMap A₀ A (x i)) := by
    have := congrArg (Ideal.map (algebraMap A₀ A)) hx
    rw [Ideal.map_span, ← Set.range_comp] at this
    exact this.symm
  refine ⟨?_, ?_⟩
  · have hofList : Ideal.ofList (List.ofFn x) = maximalIdeal A₀ := by
      refine Eq.trans ?_ hx
      unfold Ideal.ofList
      congr 1
      ext y
      simp only [List.mem_ofFn, Set.mem_ofPred_eq, Set.mem_range]
    refine hN3 A₀ A (List.ofFn x) hofList (h00NQ A₀ x hx).toIsWeaklyRegular ?_
    rw [List.map_ofFn]
    exact isWeaklyRegular_of_linearIndependent h00NQ (fun i => algebraMap A₀ A (x i)) hxm hli
  · rw [hmap]
    exact FiniteTypeIntGRing.isRegularLocalRing_quotient_span_of_linearIndependent _ hxm hli

/-- Differentials of elements of a subextension: if the images in `K` of `y_i ∈ K₀` lie in a
subextension `F ⊂ K` containing the image of `K₀`, and their differentials are linearly
independent in `Ω_{F/k}`, then the `dy_i` are linearly independent in `Ω_{K₀/k}`. -/
theorem kaehler_independent_of_subfield {k K₀ K : Type u} [Field k] [Field K₀] [Field K]
    [Algebra k K₀] [Algebra k K] [Algebra K₀ K] [IsScalarTower k K₀ K]
    (F : IntermediateField k K) (hK₀F : ∀ z, algebraMap K₀ K z ∈ F) {m : ℕ}
    (y : Fin m → K₀) (z : Fin m → K) (hz : ∀ i, z i ∈ F)
    (hyz : ∀ i, algebraMap K₀ K (y i) = z i)
    (hli : LinearIndependent F fun i => KaehlerDifferential.D k F ⟨z i, hz i⟩) :
    LinearIndependent K₀ fun i => KaehlerDifferential.D k K₀ (y i) := by
  let ι : K₀ →+* F := (algebraMap K₀ K).codRestrict F hK₀F
  let _ : Algebra K₀ F := ι.toAlgebra
  have : IsScalarTower k K₀ F :=
    .of_algebraMap_eq fun c => Subtype.ext (IsScalarTower.algebraMap_apply k K₀ K c)
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have h1 := congrArg (KaehlerDifferential.map k k K₀ F) hc
  rw [map_sum, map_zero] at h1
  simp only [map_smul, KaehlerDifferential.map_D] at h1
  have h3 : ∀ j, algebraMap K₀ F (y j) = ⟨z j, hz j⟩ := fun j => Subtype.ext (hyz j)
  simp only [h3] at h1
  have h2 : ∑ j, ι (c j) • KaehlerDifferential.D k F ⟨z j, hz j⟩ = 0 := by
    rw [← h1]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact algebraMap_smul F (c j) _
  have := Fintype.linearIndependent_iff.mp hli _ h2 i
  exact (map_eq_zero_iff ι ι.injective).mp this

/-- **Stacks 07E6**, from 07E5 (1) ⇒ (3) (`GeometricRegularityH1InjectiveStatement`), 07E2
(`FieldH1CotangentInjectiveStatement`), 07DY (`RegularSequenceFlatStatement`) and 00NQ
(`RegularLocalParametersStatement`). -/
theorem geometricRegularityFlat_of (hK3 : GeometricRegularityH1InjectiveStatement.{u})
    (hK2 : FieldH1CotangentInjectiveStatement.{u}) (hN3 : RegularSequenceFlatStatement.{u})
    (h00NQ : RegularLocalParametersStatement.{u}) : GeometricRegularityFlatStatement.{u} := by
  intro k Λ _ _ _ p _ _ hreg q _ F _ m φ hF hli _ 𝔭 _ h𝔭
  classical
  have : IsNoetherianRing Λ := hreg.1
  have : IsRegularRing Λ := hreg.isRegularRing
  -- the local map `A₀ = k[y]_𝔭 → A = Λ_q`
  let g : Localization.AtPrime 𝔭 →+* Localization.AtPrime q :=
    Localization.localRingHom 𝔭 q φ h𝔭
  let _ : Algebra (Localization.AtPrime 𝔭) (Localization.AtPrime q) := g.toAlgebra
  have : IsLocalHom (algebraMap (Localization.AtPrime 𝔭) (Localization.AtPrime q)) :=
    Localization.isLocalHom_localRingHom 𝔭 q φ h𝔭
  have hg : ∀ r : MvPolynomial (Fin m) k,
      algebraMap (Localization.AtPrime 𝔭) (Localization.AtPrime q)
        (algebraMap (MvPolynomial (Fin m) k) (Localization.AtPrime 𝔭) r) =
      algebraMap Λ (Localization.AtPrime q) (φ r) := fun r =>
    Localization.localRingHom_to_map 𝔭 q φ h𝔭 r
  have : IsScalarTower k (Localization.AtPrime 𝔭) (Localization.AtPrime q) :=
    .of_algebraMap_eq fun c => by
      rw [IsScalarTower.algebraMap_apply k (MvPolynomial (Fin m) k) (Localization.AtPrime 𝔭) c,
        hg, AlgHom.commutes, ← IsScalarTower.algebraMap_apply]
  -- the residue field of `A₀` maps into `F`
  have hpoly : ∀ r : MvPolynomial (Fin m) k,
      algebraMap Λ (ResidueField (Localization.AtPrime q)) (φ r) ∈ F := by
    intro r
    induction r using MvPolynomial.induction_on with
    | C c =>
      rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, ← IsScalarTower.algebraMap_apply]
      exact F.algebraMap_mem c
    | add r s hr hs =>
      rw [map_add, map_add]
      exact add_mem hr hs
    | mul_X r i hr =>
      rw [map_mul, map_mul]
      exact mul_mem hr (hF i)
  have hresR : ∀ r : MvPolynomial (Fin m) k,
      algebraMap (ResidueField (Localization.AtPrime 𝔭)) (ResidueField (Localization.AtPrime q))
        (residue (Localization.AtPrime 𝔭)
          (algebraMap (MvPolynomial (Fin m) k) (Localization.AtPrime 𝔭) r)) =
      algebraMap Λ (ResidueField (Localization.AtPrime q)) (φ r) := by
    intro r
    show residue (Localization.AtPrime q) (algebraMap (Localization.AtPrime 𝔭)
      (Localization.AtPrime q) (algebraMap (MvPolynomial (Fin m) k) (Localization.AtPrime 𝔭) r)) = _
    rw [hg]
    rfl
  have hK₀F : ∀ z, algebraMap (ResidueField (Localization.AtPrime 𝔭))
      (ResidueField (Localization.AtPrime q)) z ∈ F := by
    intro z
    obtain ⟨y, rfl⟩ := residue_surjective z
    obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔭.primeCompl y
    have hs : IsUnit (algebraMap (MvPolynomial (Fin m) k) (Localization.AtPrime 𝔭)
        (s : MvPolynomial (Fin m) k)) := IsLocalization.map_units _ s
    have heq : residue (Localization.AtPrime 𝔭) (IsLocalization.mk' (Localization.AtPrime 𝔭) r s) =
        residue (Localization.AtPrime 𝔭)
          (algebraMap (MvPolynomial (Fin m) k) (Localization.AtPrime 𝔭) r) /
        residue (Localization.AtPrime 𝔭) (algebraMap (MvPolynomial (Fin m) k)
          (Localization.AtPrime 𝔭) (s : MvPolynomial (Fin m) k)) := by
      rw [eq_div_iff ((residue_ne_zero_iff_isUnit _).mpr hs), ← map_mul,
        IsLocalization.mk'_spec]
    rw [heq, map_div₀]
    refine div_mem ?_ ?_
    · rw [hresR]
      exact hpoly r
    · rw [hresR]
      exact hpoly s
  -- `κ₀ ⊗ Ω_{A₀/k} → Ω_{κ₀/k}` is injective
  have hliK₀ : LinearIndependent (ResidueField (Localization.AtPrime 𝔭)) fun i =>
      KaehlerDifferential.D k (ResidueField (Localization.AtPrime 𝔭))
        (residue (Localization.AtPrime 𝔭)
          (algebraMap (MvPolynomial (Fin m) k) (Localization.AtPrime 𝔭) (X i))) :=
    kaehler_independent_of_subfield F hK₀F _ _ hF (fun i => hresR (X i)) hli
  have hΩ : Function.Injective (KaehlerDifferential.mapBaseChange k (Localization.AtPrime 𝔭)
      (ResidueField (Localization.AtPrime 𝔭))) := by
    refine injective_of_span_of_linearIndependent _ (fun i =>
      (1 : ResidueField (Localization.AtPrime 𝔭)) ⊗ₜ KaehlerDifferential.D k
        (Localization.AtPrime 𝔭)
        (algebraMap (MvPolynomial (Fin m) k) (Localization.AtPrime 𝔭) (X i)))
      (span_one_tmul _ (span_D_localization k m 𝔭)) ?_
    simp only [KaehlerDifferential.mapBaseChange_tmul, one_smul, KaehlerDifferential.map_D]
    exact hliK₀
  -- regularity of `A₀` and `A`
  have : IsRegularLocalRing (Localization.AtPrime q) :=
    IsRegularRing.isRegularLocalRing_localization q
  have : IsRegularLocalRing (Localization.AtPrime 𝔭) :=
    IsRegularRing.isRegularLocalRing_localization 𝔭
  -- a minimal generating family of `𝔪_{A₀}`
  obtain ⟨x, hx⟩ := exists_fin_span_eq_maximalIdeal (Localization.AtPrime 𝔭)
  have hxm : ∀ i, x i ∈ maximalIdeal (Localization.AtPrime 𝔭) := fun i =>
    hx.le (Ideal.subset_span ⟨i, rfl⟩)
  have hli' := rsop_independent (hK3 k Λ p hreg q)
    (hK2 k (ResidueField (Localization.AtPrime 𝔭)) (ResidueField (Localization.AtPrime q)))
    hΩ x hx hxm
  obtain ⟨hflat, hregq⟩ := flat_regular_of_rsop hN3 h00NQ x hx _ hli'
  have hmap : 𝔭.map ((algebraMap Λ (Localization.AtPrime q)).comp
      (φ : MvPolynomial (Fin m) k →+* Λ)) =
      (maximalIdeal (Localization.AtPrime 𝔭)).map
        (algebraMap (Localization.AtPrime 𝔭) (Localization.AtPrime q)) := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map]
    congr 1
    exact (RingHom.ext hg).symm
  refine ⟨hflat, ?_⟩
  rw [hmap]
  exact hregq

/-- Stacks 07E6 from Stacks 07E5 (1) ⇒ (3) alone: the three other hypotheses of
`geometricRegularityFlat_of` are discharged by their published proofs. -/
theorem geometricRegularityFlat_of_h1Injective
    (hK3 : GeometricRegularityH1InjectiveStatement.{u}) : GeometricRegularityFlatStatement.{u} :=
  geometricRegularityFlat_of hK3 FieldH1.fieldH1CotangentInjective regularSequenceFlat
    regularLocalParameters

/-- **Stacks 07E6** (More on Algebra, Lemma 15.36.2). Let `k` be a field of characteristic
`p > 0`, `Λ` a geometrically regular `k`-algebra, `q` a prime of `Λ` with residue field `κ`, and
`F ⊂ κ` a finitely generated subextension of `κ/k`. If `φ : k[y₁, …, yₘ] → Λ` sends each `yᵢ`
to an element whose residue `ȳᵢ` lies in `F`, and `dȳ₁, …, dȳₘ` form a basis of `Ω_{F/k}`, then
`Λ_q` is flat over `k[y]_𝔭` (`𝔭 = φ⁻¹(q)`) and `Λ_q/𝔭Λ_q` is a regular local ring. The remaining
hypothesis of
`geometricRegularityFlat_of_h1Injective` is the published Stacks 07E5 (1) ⇒ (3). -/
theorem geometricRegularityFlat : GeometricRegularityFlatStatement.{u} :=
  geometricRegularityFlat_of_h1Injective GeometricRegularityH1.geometricRegularityH1Injective

end GeometricRegularity

end Langlands.CommutativeAlgebra.Popescu
