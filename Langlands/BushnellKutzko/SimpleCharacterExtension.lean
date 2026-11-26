import Langlands.BushnellKutzko.SimpleCharacterRestrictionCutoff
import Langlands.BushnellKutzko.SimpleCharacterTransferGluing
import Langlands.BushnellKutzko.SimpleCharacterTransferRelativeCharacter
import Langlands.BushnellKutzko.NormalizedLevelTwistProof

/-! # Extending characters across a subgroup product -/

namespace Langlands.BushnellKutzko

noncomputable section

open scoped Pointwise

universe uF uV

/-- A complex character of an abelian subgroup extends to the ambient abelian group. -/
theorem exists_complexCharacter_extension {A : Type*} [CommGroup A] (U : Subgroup A)
    (χ : U →* ℂˣ) : ∃ χ' : A →* ℂˣ, χ'.comp U.subtype = χ := by
  obtain ⟨f, hf⟩ := (@Module.Baer.of_divisible (Additive ℂˣ) _
    divisibleByUnitsComplex).extension_property_addMonoidHom U.subtype.toAdditive
      U.subtype_injective χ.toAdditive
  exact ⟨f.toMultiplicative, MonoidHom.ext fun x => DFunLike.congr_fun hf x⟩

variable {F : Type uF} [Field F] {V : Type uV} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V

/-- Restriction of scalars identifies the pullback of `H` to the relative
endomorphism units with the intersection of `H` and the centralizer units. -/
def relativeEndUnits_comapEquivInf (β : A) (hE : IsField (elementAlgebra β))
    (H : Subgroup Aˣ) :
    letI := hE.toField
    H.comap (relativeEndUnits (F := F) (V := V) (elementAlgebra β)) ≃*
      (H ⊓ centralizerUnitGroup β : Subgroup Aˣ) := by
  letI := hE.toField
  let ι := relativeEndUnits (F := F) (V := V) (elementAlgebra β)
  have hι : Function.Injective ι := fun _ _ h =>
    Units.ext (LinearMap.restrictScalars_injective F (congrArg Units.val h))
  have hrange : ι.range = centralizerUnitGroup β := relativeEndUnits_range_eq_centralizer β hE
  let f : H.comap ι →* (H ⊓ centralizerUnitGroup β : Subgroup Aˣ) :=
    { toFun := fun x => ⟨ι x, x.prop, hrange ▸ ⟨x, rfl⟩⟩
      map_one' := Subtype.ext (map_one ι)
      map_mul' := fun x y => Subtype.ext (map_mul ι (x.val) (y.val)) }
  refine MulEquiv.ofBijective f ⟨fun x y h => Subtype.ext (hι (congrArg Subtype.val h)), ?_⟩
  intro x
  obtain ⟨y, hy⟩ : (x : Aˣ) ∈ ι.range := hrange.symm ▸ x.prop.2
  refine ⟨⟨y, ?_⟩, Subtype.ext hy⟩
  change ι y ∈ H
  rw [hy]
  exact x.prop.1

/-- A determinant-factoring character of the deeper subgroup extends across the product
with the centralizer units, provided those units normalize the deeper character. -/
theorem exists_relativeDet_character_extension {β : A} {H D : Subgroup Aˣ} (hD : D ≤ H)
    (hproduct : (H : Set Aˣ) = ((H ⊓ centralizerUnitGroup β : Subgroup Aˣ) : Set Aˣ) * (D : Set Aˣ))
    (θ : D →* ℂˣ) (hdet : factorsThroughCentralizerDet β θ)
    (hθ : ((H ⊓ centralizerUnitGroup β : Subgroup Aˣ) : Set Aˣ) ⊆ characterNormalizer θ) :
    ∃ χ : H →* ℂˣ, factorsThroughCentralizerDet β χ ∧ χ.comp (Subgroup.inclusion hD) = θ := by
  obtain ⟨hE, η, hη⟩ := hdet
  let := hE.toField
  let ι := relativeEndUnits (F := F) (V := V) (elementAlgebra β)
  let d := Units.map (LinearMap.det : Module.End (elementAlgebra β) V →* elementAlgebra β)
  let dD := d.comp (D.comap ι).subtype
  let e := relativeEndUnits_comapEquivInf β hE H
  change dD.range →* ℂˣ at η
  obtain ⟨η', hη'⟩ := exists_complexCharacter_extension dD.range η
  let φ : (H ⊓ centralizerUnitGroup β : Subgroup Aˣ) →* ℂˣ :=
    η'.comp (d.comp ((H.comap ι).subtype.comp e.symm.toMonoidHom))
  have hφ (x : H.comap ι) : φ (e x) = η' (d x) := by
    simp [φ]
  have hφD (x : D.comap ι) : φ (e ⟨x, hD x.prop⟩) = θ (ι.subgroupComap D x) := by
    rw [hφ]
    exact (DFunLike.congr_fun hη' (dD.rangeRestrict x)).trans (hη x).symm
  let U : Subgroup Aˣ := H ⊓ centralizerUnitGroup β
  have hnormal : U ≤ Subgroup.normalizer (D : Set Aˣ) := fun _ hu => (hθ hu).1
  have hjoin : H = U ⊔ D := SetLike.coe_injective <|
    hproduct.trans (Subgroup.coe_mul_of_left_le_normalizer_right U D hnormal).symm
  have hrange : ι.range = centralizerUnitGroup β := relativeEndUnits_range_eq_centralizer β hE
  obtain ⟨χ, hχU, hχD⟩ := exists_monoidHom_of_compatible_restrictions U D φ θ hnormal
    (fun u v hv => by
      simpa only [inv_inv] using (hθ (U.inv_mem u.prop)).2 v (by simpa only [inv_inv] using hv))
    (fun x hxU hxD => by
      obtain ⟨y, hy⟩ : x ∈ ι.range := hrange.symm ▸ hxU.2
      subst x
      change φ (e ⟨y, hD hxD⟩) = θ (ι.subgroupComap D ⟨y, hxD⟩)
      exact hφD ⟨y, hxD⟩)
  let χH := χ.comp (MulEquiv.subgroupCongr hjoin).toMonoidHom
  refine ⟨χH, (factorsThroughCentralizerDet_iff hE χH).mpr ?_, MonoidHom.ext hχD⟩
  intro x hx
  change χ ⟨(e x : Aˣ), _⟩ = 1
  rw [hχU, hφ, show d x = 1 from hx, map_one]

/-- Let a subgroup of the centralizer units normalize the product domain.
It normalizes a determinant-factoring character on that domain if it also normalizes
the character's restriction to the deeper subgroup. -/
theorem relativeDet_character_normalized_of_product {β : A} {H D K : Subgroup Aˣ}
    (hD : D ≤ H)
    (hproduct : (H : Set Aˣ) = ((H ⊓ centralizerUnitGroup β : Subgroup Aˣ) : Set Aˣ) * (D : Set Aˣ))
    (hK : K ≤ centralizerUnitGroup β) (hKnorm : K ≤ Subgroup.normalizer (H : Set Aˣ))
    {χ : H →* ℂˣ} (hχ : factorsThroughCentralizerDet β χ)
    (hres : (K : Set Aˣ) ⊆ characterNormalizer (χ.comp (Subgroup.inclusion hD))) :
    (K : Set Aˣ) ⊆ characterNormalizer χ := by
  intro g hg
  refine ⟨hKnorm hg, ?_⟩
  intro x hx
  have hx' : (x : Aˣ) ∈ ((H ⊓ centralizerUnitGroup β : Subgroup Aˣ) : Set Aˣ) * (D : Set Aˣ) :=
    hproduct ▸ x.prop
  obtain ⟨u, hu, d, hd, hprod⟩ := Set.mem_mul.mp hx'
  have huH : u ∈ H := hu.1
  have huB : u ∈ centralizerUnitGroup β := hu.2
  have hu' := (Subgroup.mem_normalizer_iff.mp (hKnorm hg) u).mp huH
  have hd' := (Subgroup.mem_normalizer_iff.mp (hres hg).1 d).mp hd
  have hU := factorsThroughCentralizerDet_conj_eq hχ hχ.choose (hK hg) (x := ⟨u, huH⟩) hu' huB
  have hD' := (hres hg).2 ⟨d, hd⟩ hd'
  have hx1 : x = ⟨u, huH⟩ * ⟨d, hD hd⟩ := Subtype.ext hprod.symm
  have hx2 : (⟨g * (x : Aˣ) * g⁻¹, hx⟩ : H) =
      ⟨g * u * g⁻¹, hu'⟩ * ⟨g * d * g⁻¹, hD hd'⟩ := by
    apply Subtype.ext
    change g * (x : Aˣ) * g⁻¹ = (g * u * g⁻¹) * (g * d * g⁻¹)
    rw [← hprod]
    group
  rw [hx2, hx1, map_mul, map_mul, hU]
  exact congrArg (fun z => χ ⟨u, huH⟩ * z) hD'

/-- If membership is determined by determinant factorization and the deeper restriction,
restriction is onto and its nonempty fibres are translates of the determinant-factoring
characters trivial on the deeper subgroup. -/
theorem image_fibres_of_relativeDet_extension {β : A} {H D K : Subgroup Aˣ} (hD : D ≤ H)
    (hproduct : (H : Set Aˣ) = ((H ⊓ centralizerUnitGroup β : Subgroup Aˣ) : Set Aˣ) * (D : Set Aˣ))
    (hUK : H ⊓ centralizerUnitGroup β ≤ K)
    (C : Set (H →* ℂˣ)) (C' : Set (D →* ℂˣ))
    (hC : ∀ χ : H →* ℂˣ, χ ∈ C ↔
      factorsThroughCentralizerDet β χ ∧ χ.comp (Subgroup.inclusion hD) ∈ C')
    (hC' : ∀ θ ∈ C', factorsThroughCentralizerDet β θ ∧ (K : Set Aˣ) ⊆ characterNormalizer θ) :
    let res := fun χ : H →* ℂˣ => χ.comp (Subgroup.inclusion hD)
    let X : Set (H →* ℂˣ) := {χ | res χ = 1 ∧ factorsThroughCentralizerDet β χ}
    res '' C = C' ∧ ∀ θ ∈ C, {χ ∈ C | res χ = res θ} = (fun χ => θ * χ) '' X := by
  let res := fun χ : H →* ℂˣ => χ.comp (Subgroup.inclusion hD)
  let X : Set (H →* ℂˣ) := {χ | res χ = 1 ∧ factorsThroughCentralizerDet β χ}
  change res '' C = C' ∧ ∀ θ ∈ C, {χ ∈ C | res χ = res θ} = (fun χ => θ * χ) '' X
  have hres_mul (χ θ : H →* ℂˣ) : res (χ * θ) = res χ * res θ := rfl
  have hres_inv (χ : H →* ℂˣ) : res χ⁻¹ = (res χ)⁻¹ := rfl
  constructor
  · ext θ
    constructor
    · rintro ⟨χ, hχ, rfl⟩
      exact ((hC χ).mp hχ).2
    · intro hθ
      obtain ⟨hdet, hnorm⟩ := hC' θ hθ
      obtain ⟨χ, hχ, hres⟩ := exists_relativeDet_character_extension hD hproduct
        θ hdet (fun _ hx => hnorm (hUK hx))
      exact ⟨χ, (hC χ).mpr ⟨hχ, hres.symm ▸ hθ⟩, hres⟩
  · intro θ hθ
    obtain ⟨hθdet, hθres⟩ := (hC θ).mp hθ
    ext χ
    constructor
    · rintro ⟨hχ, he⟩
      obtain ⟨hχdet, _⟩ := (hC χ).mp hχ
      refine ⟨θ⁻¹ * χ, ⟨?_, factorsThroughCentralizerDet_mul
        (factorsThroughCentralizerDet_inv hθdet) hχdet⟩, ?_⟩
      · rw [hres_mul, hres_inv, he]
        ext x
        simp
      · ext x
        simp
    · rintro ⟨χ, ⟨hχ, hχdet⟩, rfl⟩
      have he : res (θ * χ) = res θ := by
        rw [hres_mul, hχ]
        ext x
        simp
      have hmem : res (θ * χ) ∈ C' := by
        rw [he]
        exact hθres
      exact ⟨(hC _).mpr ⟨factorsThroughCentralizerDet_mul hθdet hχdet, hmem⟩, he⟩

end

end Langlands.BushnellKutzko
