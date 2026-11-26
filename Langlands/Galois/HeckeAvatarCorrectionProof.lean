import Langlands.Galois.HeckeAvatarCorrection
import Langlands.ClassFieldTheory.Global.IntegralIdeleClassQuotientFinite
import Langlands.ClassFieldTheory.Global.LocalUnitPowers
import Langlands.Cohomology.Profinite.Dimension.Procyclic

/-! # Continuous integral idele correction -/

noncomputable section

universe uK uL

namespace Langlands.GaloisRepresentation

open Langlands.Global Langlands.ClassFieldTheory.Global IsDedekindDomain HeightOneSpectrum
open NumberField hiding FinitePlace InfinitePlace
open scoped NumberField RestrictedProduct Valued

variable {K : Type uK} [Field K] [NumberField K]
variable {L : Type uL} [Field L] [NumberField L]

private theorem continuous_avatarCompletionMap (e : K →+* L) (lam : FinitePlace L) :
    Continuous (avatarCompletionMap e lam) := by
  let : Algebra K L := e.toAlgebra
  let : lam.asIdeal.LiesOver (avatarPlaceBelow e lam).asIdeal := Ideal.over_under lam.asIdeal
  exact AdelicFunctoriality.FiniteExtension.continuous_completionMap (avatarPlaceBelow e lam) lam

private theorem avatarCompletionMap_diagonal (e : K →+* L) (lam : FinitePlace L) (a : Kˣ) :
    Units.map (avatarCompletionMap e lam).toMonoidHom
        (finiteIdeleProjection K (avatarPlaceBelow e lam) (diagonalUnits K a)) =
      Units.map (NumberField.FinitePlace.embedding lam).toMonoidHom
        (Units.map e.toMonoidHom a) := by
  let : Algebra K L := e.toAlgebra
  let : lam.asIdeal.LiesOver (avatarPlaceBelow e lam).asIdeal := Ideal.over_under lam.asIdeal
  apply Units.ext
  exact AdelicFunctoriality.FiniteExtension.completionMap_coe (avatarPlaceBelow e lam) lam (a : K)

omit [NumberField K] [NumberField L] in
private theorem residueCharacteristic_avatarPlaceBelow (e : K →+* L) (lam : FinitePlace L) :
    residueCharacteristic (avatarPlaceBelow e lam) = residueCharacteristic lam := by
  let : Algebra K L := e.toAlgebra
  let f : (𝓞 K ⧸ (avatarPlaceBelow e lam).asIdeal) →+* (𝓞 L ⧸ lam.asIdeal) :=
    Ideal.quotientMap lam.asIdeal (algebraMap (𝓞 K) (𝓞 L)) le_rfl
  have hinj : Function.Injective f := Ideal.quotientMap_injective
  exact ringChar.eq_iff.mpr (f.charP hinj _)

private theorem idele_factors (x : Ideles K) :
    infiniteIdelesInclusion K (ideleProductEquiv K x).1 *
      finiteIdelesInclusion K (ideleProductEquiv K x).2 = x := by
  let e := ideleProductEquiv K
  apply e.injective
  rw [map_mul]
  change e (e.symm ((e x).1, 1)) * e (e.symm (1, (e x).2)) = e x
  rw [e.apply_symm_apply, e.apply_symm_apply]
  exact Prod.ext (mul_one _) (one_mul _)

private theorem infinityCharacter_diagonal [IsTotallyComplex K] (t : InfinityType K) (a : Kˣ) :
    InfinityType.toCharacter t (Units.map
      (algebraMap K (InfiniteAdeles K)).toMonoidHom a) =
      ∏ σ : K →+* ℂ, (Units.map σ.toMonoidHom a) ^ t σ := by
  classical
  rw [InfinityType.toCharacter_apply, ← Finset.prod_fiberwise Finset.univ NumberField.InfinitePlace.mk]
  apply Finset.prod_congr rfl
  intro w _
  have hpair : Finset.univ.filter (fun σ => NumberField.InfinitePlace.mk σ = w) =
      {w.embedding, ComplexEmbedding.conjugate w.embedding} := by
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    calc
      NumberField.InfinitePlace.mk σ = w ↔
          NumberField.InfinitePlace.mk w.embedding = NumberField.InfinitePlace.mk σ := by
            rw [w.mk_embedding, eq_comm]
      _ ↔ _ := by
        rw [NumberField.InfinitePlace.mk_eq_iff, eq_comm (a := w.embedding),
          eq_comm (a := ComplexEmbedding.conjugate w.embedding)]
  have hne : w.embedding ≠ ComplexEmbedding.conjugate w.embedding := fun h =>
    IsTotallyComplex.complexEmbedding_not_isReal w.embedding
      (ComplexEmbedding.isReal_iff.mpr h.symm)
  rw [hpair, Finset.prod_pair hne]
  have hcoord : InfinityType.coordinate w (Units.map
      (algebraMap K (InfiniteAdeles K)).toMonoidHom a) = Units.map w.embedding.toMonoidHom a :=
    Units.ext (InfinityType.coordinate_diagonal w a)
  have hstar : star (Units.map w.embedding.toMonoidHom a) =
      Units.map (ComplexEmbedding.conjugate w.embedding).toMonoidHom a := Units.ext rfl
  rw [hcoord, hstar]

private theorem corrected_principal [IsTotallyComplex K] (χ : HeckeCharacter K)
    (t : InfinityType K) (ι : L →+* ℂ) (emb : (K →+* ℂ) → (K →+* L))
    (φ : FiniteIdeles K →* Lˣ) (hχ : χ.HasPrescribedInfinityComponent (InfinityType.toCharacter t))
    (hemb : ∀ σ, ι.comp (emb σ) = σ) (hφ : IsHeckeFinitePart χ ι φ)
    (lam : FinitePlace L) (a : Kˣ) :
    correctedIdeleValue t emb φ lam (diagonalUnits K a) = 1 := by
  classical
  let x := diagonalUnits K a
  let b : Lˣ := ∏ σ : K →+* ℂ, (Units.map (emb σ).toMonoidHom a) ^ t σ
  have hb : Units.map ι.toMonoidHom b = χ.atInfinity (ideleProductEquiv K x).1 := by
    rw [hχ, show (ideleProductEquiv K x).1 =
      Units.map (algebraMap K (InfiniteAdeles K)).toMonoidHom a by rfl, infinityCharacter_diagonal]
    dsimp only [b]
    rw [map_prod]
    apply Finset.prod_congr rfl
    intro σ _
    rw [map_zpow]
    congr 1
    exact Units.ext (congrArg (fun f : K →+* ℂ => f (a : K)) (hemb σ))
  have hcancel : φ (ideleProductEquiv K x).2 * b = 1 := by
    apply Units.map_injective ι.injective
    rw [map_mul, map_one, hφ.2, hb, mul_comm]
    change χ.onIdeles (infiniteIdelesInclusion K (ideleProductEquiv K x).1) *
      χ.onIdeles (finiteIdelesInclusion K (ideleProductEquiv K x).2) = 1
    rw [← map_mul, idele_factors]
    exact χ.onIdeles_diagonalUnits a
  let j : Lˣ →* (FiniteCompletion L lam)ˣ :=
    Units.map (NumberField.FinitePlace.embedding lam).toMonoidHom
  calc
    correctedIdeleValue t emb φ lam (diagonalUnits K a) = j (φ (ideleProductEquiv K x).2 * b) := by
      rw [correctedIdeleValue, map_mul]
      dsimp only [b]
      rw [map_prod]
      congr 1
      apply Finset.prod_congr rfl
      intro σ _
      rw [avatarCompletionMap_diagonal, map_zpow]
    _ = 1 := by rw [hcancel, map_one]

private def correctedIdeleHom (t : InfinityType K) (emb : (K →+* ℂ) → (K →+* L))
    (φ : FiniteIdeles K →* Lˣ) (hφ : IsOpen (φ.ker : Set (FiniteIdeles K)))
    (lam : FinitePlace L) : Ideles K →ₜ* (FiniteCompletion L lam)ˣ where
  toFun := correctedIdeleValue t emb φ lam
  map_one' := by simp [correctedIdeleValue]
  map_mul' x y := by
    simp only [correctedIdeleValue, map_mul, Prod.snd_mul, mul_zpow, Finset.prod_mul_distrib]
    ac_rfl
  continuous_toFun := by
    have hfinite := (Langlands.MonoidHom.isLocallyConstant_of_isOpen_ker φ hφ).comp
      (Units.map (NumberField.FinitePlace.embedding lam).toMonoidHom)
    refine (hfinite.continuous.comp ((ideleProductEquiv K).continuous.snd)).mul
      (continuous_finsetProd _ fun σ _ => ?_)
    exact (((continuous_avatarCompletionMap (emb σ) lam).units_map _).comp
      (finiteIdeleProjection K (avatarPlaceBelow (emb σ) lam)).continuous).zpow (t σ)

private def correctedClassHom {lam : FinitePlace L} (f : Ideles K →ₜ* (FiniteCompletion L lam)ˣ)
    (hf : ∀ a : Kˣ, f (diagonalUnits K a) = 1) : IdeleClasses K →ₜ* (FiniteCompletion L lam)ˣ where
  toMonoidHom := QuotientGroup.lift (principalIdeles K) f.toMonoidHom (by
    rintro x ⟨a, rfl⟩
    exact hf a)
  continuous_toFun := (QuotientGroup.isQuotientMap_mk (principalIdeles K)).continuous_iff.mpr
    f.continuous

private theorem corrected_infinity (t : InfinityType K) (emb : (K →+* ℂ) → (K →+* L))
    (φ : FiniteIdeles K →* Lˣ) (lam : FinitePlace L) (z : (InfiniteAdeles K)ˣ) :
    correctedIdeleValue t emb φ lam (infiniteIdelesInclusion K z) = 1 := by
  have hfinite : (ideleProductEquiv K (infiniteIdelesInclusion K z)).2 = 1 := by
    change ((ideleProductEquiv K) ((ideleProductEquiv K).symm (z, 1))).2 = 1
    rw [ContinuousMulEquiv.apply_symm_apply]
  have hcoord (v : FinitePlace K) : finiteIdeleProjection K v (infiniteIdelesInclusion K z) = 1 :=
    rfl
  simp only [correctedIdeleValue, hfinite, hcoord, map_one, one_zpow, Finset.prod_const_one, one_mul]

private theorem continuous_unitsExponent (lam : FinitePlace L) : Continuous (unitsExponent lam) := by
  apply (Langlands.MonoidHom.isLocallyConstant_of_isOpen_ker (unitsExponent lam) ?_).continuous
  have h : (↑(unitsExponent lam).ker : Set (FiniteCompletion L lam)ˣ) =
      (↑(lam.adicCompletionIntegers L).units : Set (FiniteCompletion L lam)ˣ) := by
    ext x
    exact (mem_localUnits_iff lam x).trans adicCompletionIntegers.mem_units_iff_valued_eq_one.symm
  rw [h]
  exact Submonoid.isOpen_units (Valued.isOpen_valuationSubring (FiniteCompletion L lam))

private theorem integral_exponent (ψ : Ideles K →ₜ* Multiplicative ℤ)
    (harch : ∀ z : (InfiniteAdeles K)ˣ, ψ (infiniteIdelesInclusion K z) = 1)
    (x : Ideles K) (hx : x ∈ integralIdeles K) : ψ x = 1 := by
  let : T2Space (FiniteAdeles K) :=
    inferInstanceAs (T2Space (Πʳ v : FinitePlace K,
      [FiniteCompletion K v, v.adicCompletionIntegers K]))
  let U := (integralFiniteAdeles K).toSubmonoid.units
  have : CompactSpace U := isCompact_iff_compactSpace.mp
    (Submonoid.units_isCompact (isCompact_integralFiniteAdeles K))
  let g : U →* Multiplicative ℤ :=
    (ψ.toMonoidHom.comp (finiteIdelesInclusion K).toMonoidHom).comp U.subtype
  have hg : Continuous g :=
    ψ.continuous.comp ((finiteIdelesInclusion K).continuous.comp continuous_subtype_val)
  have : Finite g.range := (isCompact_range hg).finite_of_discrete
  let y := (ideleProductEquiv K x).2
  have hy : y ∈ U := by
    refine ⟨?_, ?_⟩
    · intro v
      exact le_of_eq (hx v)
    · intro v
      exact le_of_eq ((inv_mem hx) v)
  have hg1 : g ⟨y, hy⟩ = 1 :=
    (g.range.subtype.isOfFinOrder (isOfFinOrder_of_finite (g.rangeRestrict ⟨y, hy⟩))).eq_one'
  calc
    ψ x = ψ (infiniteIdelesInclusion K (ideleProductEquiv K x).1 *
        finiteIdelesInclusion K y) := congrArg ψ (idele_factors x).symm
    _ = ψ (finiteIdelesInclusion K y) := by rw [map_mul, harch, one_mul]
    _ = 1 := hg1

private theorem class_exponent (ψ : IdeleClasses K →ₜ* Multiplicative ℤ)
    (harch : ∀ z : (InfiniteAdeles K)ˣ, ψ (ideleClassMap K (infiniteIdelesInclusion K z)) = 1)
    (c : IdeleClasses K) : ψ c = 1 := by
  have hker : integralIdeleClasses K ≤ ψ.toMonoidHom.ker := by
    intro d hd
    obtain ⟨x, hx, rfl⟩ := (mem_integralIdeleClasses_iff d).mp hd
    exact integral_exponent (ψ.comp (ideleClassMap K)) harch x hx
  let : Finite (IntegralIdeleClassQuotient K) := integralIdeleClassQuotientFinite K
  let f : IntegralIdeleClassQuotient K →* Multiplicative ℤ :=
    QuotientGroup.lift (integralIdeleClasses K) ψ.toMonoidHom hker
  exact (f.isOfFinOrder (isOfFinOrder_of_finite (QuotientGroup.mk c))).eq_one'

private def integralClassHom (lam : FinitePlace L) (ψ : IdeleClasses K →ₜ* (FiniteCompletion L lam)ˣ)
    (hψ : ∀ c, unitsExponent lam (ψ c) = 1) : IdeleClasses K →ₜ* (lam.adicCompletionIntegers L)ˣ where
  toMonoidHom := (localUnitsToIntegerUnits lam).comp
    (ψ.toMonoidHom.codRestrict (localUnits lam) hψ)
  continuous_toFun := Units.continuous_iff.2
    ⟨(Units.continuous_val.comp ψ.continuous).subtype_mk _,
      (Units.continuous_coe_inv.comp ψ.continuous).subtype_mk _⟩

private theorem integralClassHom_inclusion (lam : FinitePlace L)
    (ψ : IdeleClasses K →ₜ* (FiniteCompletion L lam)ˣ)
    (hψ : ∀ c, unitsExponent lam (ψ c) = 1) (c : IdeleClasses K) :
    completionIntegerUnitsInclusion lam (integralClassHom lam ψ hψ c) = ψ c :=
  Units.ext rfl

private theorem corrected_away (t : InfinityType K) (emb : (K →+* ℂ) → (K →+* L))
    (φ : FiniteIdeles K →* Lˣ) (lam : FinitePlace L) (v : FinitePlace K)
    (hv : residueCharacteristic v ≠ residueCharacteristic lam) (a : (FiniteCompletion K v)ˣ) :
    correctedIdeleValue t emb φ lam (finiteIdeleInclusion K v a) =
      Units.map (NumberField.FinitePlace.embedding lam).toMonoidHom (φ (singleFiniteIdele v a)) := by
  have hcoord (σ : K →+* ℂ) :
      finiteIdeleProjection K (avatarPlaceBelow (emb σ) lam) (finiteIdeleInclusion K v a) = 1 := by
    refine ideleCoordinate_ofAdicCompletion_of_ne (fun heq => hv ?_) a
    rw [← heq, residueCharacteristic_avatarPlaceBelow]
  simp only [correctedIdeleValue, hcoord, map_one, one_zpow, Finset.prod_const_one, mul_one,
    singleFiniteIdele]

/-- The actual coefficient-place correction descends and takes values in completed integer units. -/
theorem heckeAvatarIdeleCorrection : HeckeAvatarIdeleCorrectionStatement.{uK, uL} := by
  intro K _ _ _ L _ _ χ t ι emb φ hχ hemb hφ lam
  let f := correctedIdeleHom t emb φ hφ.1 lam
  let ψ := correctedClassHom (lam := lam) f (corrected_principal χ t ι emb φ hχ hemb hφ lam)
  let valHom : (FiniteCompletion L lam)ˣ →ₜ* Multiplicative ℤ :=
    ⟨unitsExponent lam, continuous_unitsExponent lam⟩
  have hψ : ∀ c, unitsExponent lam (ψ c) = 1 := by
    apply class_exponent (valHom.comp ψ)
    intro z
    change unitsExponent lam (correctedIdeleValue t emb φ lam (infiniteIdelesInclusion K z)) = 1
    rw [corrected_infinity, map_one]
  refine ⟨integralClassHom lam ψ hψ, ?_, ?_⟩
  · intro x
    rw [integralClassHom_inclusion]
    rfl
  · intro v hv a
    rw [integralClassHom_inclusion]
    exact corrected_away t emb φ lam v hv a

end Langlands.GaloisRepresentation
