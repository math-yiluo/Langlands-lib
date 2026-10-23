import Langlands.ClassField.Global.LocalUnitCohomology
import Langlands.ClassField.Global.IdeleSemilocal
import Langlands.Global.AdelicFunctoriality.LocalDegree
import Mathlib.NumberTheory.RamificationInertia.Galois

/-! # Vanishing of the second cohomology of valuation units at unramified places

For a finite place `w` of `E` over `v` with ramification index `1` and `E / F` Galois:
`Gal(E_w/F_v)` is cyclic, a uniformizer of `F_v` splits `0 → U_w → E_wˣ → ℤ → 0`
equivariantly, `H²(G, ℤ)` has at least `|G|` elements for a finite cyclic group `G`, and hence
`H²(Gal(E_w/F_v), U_w) = 0` whenever `H²(Gal(E_w/F_v), E_wˣ)` is finite with at most
`[E_w : F_v]` elements.
-/

noncomputable section

universe u

namespace Langlands.ClassField.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField Langlands.Global.AdelicFunctoriality.FiniteExtension Pointwise
open Langlands.Global.AdelicFunctoriality Langlands.Global.CompletionPadic
open Langlands.ClassFieldTheory.Local
open CategoryTheory Limits FundamentalClass

section Cyclic

variable {F E : Type u} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver v.asIdeal]

/-- The image of `decompositionHom v w` is the stabilizer of the prime ideal of `w`. -/
theorem mem_range_decompositionHom_iff_mem_stabilizer [Normal F E] (g : E ≃ₐ[F] E) :
    g ∈ (decompositionHom v w).range ↔ g ∈ MulAction.stabilizer (E ≃ₐ[F] E) w.asIdeal := by
  rw [← Subgroup.inv_mem_iff, mem_range_decompositionHom_iff, MulAction.mem_stabilizer_iff,
    HeightOneSpectrum.ext_iff, finitePlaceEquiv_asIdeal]
  have key : ∀ x : 𝓞 E, (RingOfIntegers.mapRingEquiv g⁻¹.toRingEquiv).toRingHom x = g⁻¹ • x :=
    fun x => rfl
  constructor
  · intro h
    ext x
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, ← key, ← Ideal.mem_comap, h]
  · intro h
    ext x
    rw [Ideal.mem_comap, key, ← Ideal.mem_pointwise_smul_iff_inv_smul_mem, h]

include v in
/-- The stabilizer of `w` in `Gal(E/F)` is cyclic when `w` is unramified over `v`. -/
theorem isCyclic_stabilizer [IsGalois F E] (he : w.asIdeal.ramificationIdx (𝓞 F) = 1) :
    IsCyclic (MulAction.stabilizer (E ≃ₐ[F] E) w.asIdeal) := by
  classical
  have hinert : Nat.card (w.asIdeal.inertia (E ≃ₐ[F] E)) = 1 := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn v.asIdeal w.asIdeal,
      Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal w.asIdeal (E ≃ₐ[F] E), he]
  have hbot : w.asIdeal.inertia (E ≃ₐ[F] E) = ⊥ := Subgroup.eq_bot_of_card_eq _ hinert
  have hker : (Ideal.Quotient.stabilizerHom w.asIdeal v.asIdeal (E ≃ₐ[F] E)).ker = ⊥ := by
    have h := Ideal.Quotient.map_ker_stabilizer_subtype w.asIdeal v.asIdeal (E ≃ₐ[F] E)
    rw [hbot] at h
    exact (Subgroup.map_eq_bot_iff_of_injective _ Subtype.val_injective).1 h
  have : w.asIdeal.IsMaximal := w.isMaximal
  have : v.asIdeal.IsMaximal := v.isMaximal
  let := Ideal.Quotient.field w.asIdeal
  let := Ideal.Quotient.field v.asIdeal
  have : Finite (𝓞 E ⧸ w.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient w.ne_bot
  exact isCyclic_of_injective _ ((MonoidHom.ker_eq_bot_iff _).1 hker)

/-- `Gal(E_w/F_v)` is cyclic when `w` is unramified over `v`. -/
theorem isCyclic_localGal [IsGalois F E] (he : w.asIdeal.ramificationIdx (𝓞 F) = 1) :
    IsCyclic (w.adicCompletion E ≃ₐ[v.adicCompletion F] w.adicCompletion E) := by
  have := isCyclic_stabilizer v w he
  exact isCyclic_of_injective
    ((decompositionHom v w).codRestrict (MulAction.stabilizer (E ≃ₐ[F] E) w.asIdeal)
      fun σ => (mem_range_decompositionHom_iff_mem_stabilizer v w _).1 ⟨σ, rfl⟩)
    fun σ τ h => decompositionHom_injective v w (congrArg Subtype.val h)

end Cyclic

section CyclicIntegers

variable {G : Type u} [Group G] [Finite G] [IsCyclic G]

/-- For a finite cyclic group `G`, the classes of `0, 1, …, |G| - 1` in `H²(G, ℤ)` are
distinct, so `H²(G, ℤ)` has at least `|G|` elements when it is finite. -/
theorem card_le_card_H2_trivial_integers
    [Finite (groupCohomology (Rep.trivial IntegerScalars.{u} G IntegerScalars.{u}) 2)] :
    Nat.card G ≤
      Nat.card (groupCohomology (Rep.trivial IntegerScalars.{u} G IntegerScalars.{u}) 2) := by
  classical
  have := Fintype.ofFinite G
  let _ : CommGroup G := IsCyclic.commGroup
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  set A := Rep.trivial IntegerScalars.{u} G IntegerScalars.{u} with hA
  have hker : ∀ z : A, z ∈ LinearMap.ker (Rep.applyAsHom A g - 𝟙 A).hom.toLinearMap := by
    intro z
    rw [LinearMap.mem_ker]
    change (Representation.trivial IntegerScalars.{u} G IntegerScalars.{u} g) z - z = 0
    simp
  have hnorm : ∀ z : A, A.norm.hom z = Fintype.card G • z := by
    intro z
    simp [A, Rep.norm, Representation.norm]
  let f : Fin (Nat.card G) →
      groupCohomology A 2 := fun i =>
    Rep.FiniteCyclicGroup.groupCohomologyπEven A g hg 2 even_two
      ⟨(ULift.up (i : ℤ) : A), hker _⟩
  have hf : Function.Injective f := by
    intro i j hij
    rw [Rep.FiniteCyclicGroup.groupCohomologyπEven_eq_iff] at hij
    obtain ⟨z, hz⟩ := hij
    have h2 : Fintype.card G • z = (ULift.up (i : ℤ) : A) - ULift.up (j : ℤ) :=
      (hnorm z).symm.trans hz
    have hz' : (Fintype.card G : ℤ) * z.down = (i : ℤ) - j := by
      have h3 := congrArg ULift.down h2
      change Fintype.card G • z.down = (i : ℤ) - (j : ℤ) at h3
      rw [nsmul_eq_mul] at h3
      exact h3
    have hi : (i : ℕ) < Fintype.card G := by simpa [Nat.card_eq_fintype_card] using i.2
    have hj : (j : ℕ) < Fintype.card G := by simpa [Nat.card_eq_fintype_card] using j.2
    apply Fin.ext
    have hlt : |((i : ℤ) - j)| < Fintype.card G := by
      rw [abs_lt]
      constructor <;> omega
    rw [← hz', abs_mul] at hlt
    have hcard : (0 : ℤ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
    have hzero : z.down = 0 := by
      by_contra hne
      have : (1 : ℤ) ≤ |z.down| := Int.one_le_abs hne
      rw [abs_of_pos hcard] at hlt
      nlinarith
    rw [hzero, mul_zero] at hz'
    omega
  simpa using Nat.card_le_card_of_injective f hf

end CyclicIntegers

section Split

variable {F E : Type u} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver v.asIdeal]

attribute [local instance] localUnitsAction

/-- When `w` is unramified over `v`, a uniformizer of `F_v` is a uniformizer of `E_w`: a unit of
`E_w` of exponent `-1` fixed by `Gal(E_w/F_v)`. -/
theorem exists_fixed_uniformizer (he : w.asIdeal.ramificationIdx (𝓞 F) = 1) :
    ∃ π : (w.adicCompletion E)ˣ, Multiplicative.toAdd (unitsExponent w π) = -1 ∧
      ∀ σ : w.adicCompletion E ≃ₐ[v.adicCompletion F] w.adicCompletion E, σ • π = π := by
  obtain ⟨π₀, hπ₀⟩ := exists_unitsExponent_eq_neg_one v
  refine ⟨Units.map (algebraMap (v.adicCompletion F) (w.adicCompletion E) :
    v.adicCompletion F →* w.adicCompletion E) π₀, ?_, ?_⟩
  · apply WithZero.exp_injective
    rw [← valued_units, Units.coe_map]
    change Valued.v (FiniteExtension.completionMap v w (π₀ : v.adicCompletion F)) = _
    rw [FiniteExtension.valuation_completionMap, he, pow_one, valued_units, hπ₀]
  · intro σ
    exact Units.ext (σ.commutes (π₀ : v.adicCompletion F))

variable {v w} in
/-- The unramified splitting `ℤ → E_wˣ`, `m ↦ π ^ (-m)`, for a fixed unit `π`. -/
def integersSection {π : (w.adicCompletion E)ˣ}
    (hπ : ∀ σ : w.adicCompletion E ≃ₐ[v.adicCompletion F] w.adicCompletion E, σ • π = π) :
    Rep.trivial IntegerScalars.{u}
        (w.adicCompletion E ≃ₐ[v.adicCompletion F] w.adicCompletion E) IntegerScalars.{u} ⟶
      unitsRepresentation (padicField v).Carrier (w.adicCompletion E) :=
  Rep.ofHom
    { toLinearMap :=
        { toFun := fun m => Additive.ofMul (π ^ (-m.down))
          map_add' := fun a b => by
            change Additive.ofMul (π ^ (-(a.down + b.down))) =
              Additive.ofMul (π ^ (-a.down) * π ^ (-b.down))
            rw [neg_add, zpow_add]
          map_smul' := fun r m => by
            change Additive.ofMul (π ^ (-(r.down * m.down))) =
              Additive.ofMul ((π ^ (-m.down)) ^ r.down)
            rw [← zpow_mul, show -(r.down * m.down) = -m.down * r.down by ring] }
      isIntertwining' := fun σ => by
        refine LinearMap.ext fun m => ?_
        change Additive.ofMul (π ^ (-m.down)) = Additive.ofMul (σ • π ^ (-m.down))
        rw [smul_zpow', hπ] }

variable {v w} in
/-- The unramified retraction `E_wˣ → U_w`, `x ↦ x π ^ (-ord x)`, for a fixed unit `π` of
exponent `-1`. -/
def unitsRetraction {π : (w.adicCompletion E)ˣ}
    (hπ1 : Multiplicative.toAdd (unitsExponent w π) = -1)
    (hπ : ∀ σ : w.adicCompletion E ≃ₐ[v.adicCompletion F] w.adicCompletion E, σ • π = π) :
    unitsRepresentation (padicField v).Carrier (w.adicCompletion E) ⟶
      localUnitsRepresentation v w :=
  Rep.ofHom
    { toLinearMap :=
        { toFun := fun x => Additive.ofMul (⟨@Additive.toMul (w.adicCompletion E)ˣ x *
              π ^ (Multiplicative.toAdd (unitsExponent w (@Additive.toMul (w.adicCompletion E)ˣ x))), by
            rw [localUnits, MonoidHom.mem_ker, map_mul, map_zpow]
            apply Multiplicative.toAdd.injective
            rw [toAdd_mul, toAdd_zpow, hπ1, toAdd_one, smul_eq_mul]
            ring⟩ : localUnits w)
          map_add' := fun x y => by
            apply congrArg Additive.ofMul
            apply Subtype.ext
            change @Additive.toMul (w.adicCompletion E)ˣ x * @Additive.toMul (w.adicCompletion E)ˣ y *
                π ^ (Multiplicative.toAdd (unitsExponent w
                  (@Additive.toMul (w.adicCompletion E)ˣ x * @Additive.toMul (w.adicCompletion E)ˣ y))) =
              (@Additive.toMul (w.adicCompletion E)ˣ x *
                π ^ (Multiplicative.toAdd (unitsExponent w (@Additive.toMul (w.adicCompletion E)ˣ x)))) *
              (@Additive.toMul (w.adicCompletion E)ˣ y *
                π ^ (Multiplicative.toAdd (unitsExponent w (@Additive.toMul (w.adicCompletion E)ˣ y))))
            rw [map_mul, toAdd_mul, zpow_add]
            ac_rfl
          map_smul' := fun r x => by
            apply congrArg Additive.ofMul
            apply Subtype.ext
            change @Additive.toMul (w.adicCompletion E)ˣ x ^ r.down *
                π ^ (Multiplicative.toAdd (unitsExponent w
                  (@Additive.toMul (w.adicCompletion E)ˣ x ^ r.down))) =
              (@Additive.toMul (w.adicCompletion E)ˣ x *
                π ^ (Multiplicative.toAdd (unitsExponent w (@Additive.toMul (w.adicCompletion E)ˣ x)))) ^ r.down
            rw [map_zpow, toAdd_zpow, smul_eq_mul, mul_zpow, ← zpow_mul, mul_comm r.down] }
      isIntertwining' := fun σ => by
        ext x
        apply Subtype.ext
        change σ • @Additive.toMul (w.adicCompletion E)ˣ x *
            π ^ (Multiplicative.toAdd (unitsExponent w (σ • @Additive.toMul (w.adicCompletion E)ˣ x))) =
          σ • (@Additive.toMul (w.adicCompletion E)ˣ x *
            π ^ (Multiplicative.toAdd (unitsExponent w (@Additive.toMul (w.adicCompletion E)ˣ x))))
        rw [smul_mul', smul_zpow', hπ, units_smul_eq_map v w σ (@Additive.toMul (w.adicCompletion E)ˣ x),
          unitsExponent_localAut] }

section Identities

variable {π : (w.adicCompletion E)ˣ} (hπ1 : Multiplicative.toAdd (unitsExponent w π) = -1)
  (hπ : ∀ σ : w.adicCompletion E ≃ₐ[v.adicCompletion F] w.adicCompletion E, σ • π = π)

include hπ1 in
/-- The retraction is a left inverse of the inclusion `U_w → E_wˣ`. -/
theorem localUnitsInclusion_comp_unitsRetraction :
    localUnitsInclusion v w ≫ unitsRetraction hπ1 hπ = 𝟙 _ := by
  ext x
  apply Subtype.ext
  change ((@Additive.toMul (localUnits w) x : localUnits w) : (w.adicCompletion E)ˣ) *
      π ^ (Multiplicative.toAdd (unitsExponent w
        ((@Additive.toMul (localUnits w) x : localUnits w) : (w.adicCompletion E)ˣ))) = _
  rw [(@Additive.toMul (localUnits w) x).2, toAdd_one, zpow_zero, mul_one]
  rfl

include hπ1 in
/-- The section is a right inverse of the valuation exponent `E_wˣ → ℤ`. -/
theorem integersSection_comp_unitsExponentMorphism :
    integersSection hπ ≫ unitsExponentMorphism v w = 𝟙 _ := by
  refine Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun m => ?_))
  apply ULift.ext
  change Multiplicative.toAdd (unitsExponent w (π ^ (-m.down))) = m.down
  rw [map_zpow, toAdd_zpow, hπ1, smul_eq_mul]
  ring

/-- The section followed by the retraction is zero. -/
theorem integersSection_comp_unitsRetraction :
    integersSection hπ ≫ unitsRetraction hπ1 hπ = 0 := by
  refine Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun m => ?_))
  apply congrArg Additive.ofMul
  apply Subtype.ext
  change π ^ (-m.down) * π ^ (Multiplicative.toAdd (unitsExponent w (π ^ (-m.down)))) = 1
  rw [map_zpow, toAdd_zpow, hπ1, smul_eq_mul, ← zpow_add]
  simp

end Identities

end Split

section Vanishing

variable {F E : Type u} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver v.asIdeal]

/-- The map induced in degree two by a morphism of representations, as a function. -/
private abbrev H2map {A B : Rep.{u} IntegerScalars.{u}
    (w.adicCompletion E ≃ₐ[v.adicCompletion F] w.adicCompletion E)} (f : A ⟶ B) :
    groupCohomology A 2 → groupCohomology B 2 :=
  fun a => (groupCohomology.map (MonoidHom.id _) f 2).hom a

private theorem H2map_comp_apply {A B C : Rep.{u} IntegerScalars.{u}
    (w.adicCompletion E ≃ₐ[v.adicCompletion F] w.adicCompletion E)} (f : A ⟶ B) (g : B ⟶ C)
    (a : groupCohomology A 2) : H2map v w g (H2map v w f a) = H2map v w (f ≫ g) a := by
  simp only [H2map, groupCohomology.map_id_comp]
  rfl

private theorem H2map_id_apply {A : Rep.{u} IntegerScalars.{u}
    (w.adicCompletion E ≃ₐ[v.adicCompletion F] w.adicCompletion E)}
    (a : groupCohomology A 2) : H2map v w (𝟙 A) a = a := by
  simp only [H2map, groupCohomology.map_id]
  rfl

private theorem H2map_zero_apply {A B : Rep.{u} IntegerScalars.{u}
    (w.adicCompletion E ≃ₐ[v.adicCompletion F] w.adicCompletion E)}
    (a : groupCohomology A 2) : H2map v w (0 : A ⟶ B) a = 0 := by
  simp only [H2map, groupCohomology.map, groupCohomology.cochainsMap_zero,
    HomologicalComplex.homologyMap_zero]
  rfl

/-- **Unramified vanishing.** If `w` is unramified over `v` and `H²(Gal(E_w/F_v), E_wˣ)` is
finite with at most `[E_w : F_v]` elements, then `H²(Gal(E_w/F_v), U_w) = 0`. -/
theorem isZero_H2_localUnits [IsGalois F E] (he : w.asIdeal.ramificationIdx (𝓞 F) = 1)
    [Finite (relativeCohomology (padicField v).Carrier (w.adicCompletion E) 2)]
    (hcard : Nat.card (relativeCohomology (padicField v).Carrier (w.adicCompletion E) 2) ≤
      Module.finrank (v.adicCompletion F) (w.adicCompletion E)) :
    IsZero (groupCohomology (localUnitsRepresentation v w) 2) := by
  obtain ⟨π, hπ1, hπ⟩ := exists_fixed_uniformizer v w he
  have hri := localUnitsInclusion_comp_unitsRetraction v w hπ1 hπ
  have hos := integersSection_comp_unitsExponentMorphism v w hπ1 hπ
  have hrs := integersSection_comp_unitsRetraction v w hπ1 hπ
  have hoi := (unitsValuationSequence v w).zero
  let i := H2map v w (localUnitsInclusion v w)
  let r := H2map v w (unitsRetraction hπ1 hπ)
  let s := H2map v w (integersSection hπ)
  let o := H2map v w (unitsExponentMorphism v w)
  have hri' : ∀ a, r (i a) = a := fun a => by
    simp only [r, i]
    rw [H2map_comp_apply, hri, H2map_id_apply]
  have hos' : ∀ b, o (s b) = b := fun b => by
    simp only [o, s]
    rw [H2map_comp_apply, hos, H2map_id_apply]
  have hrs' : ∀ b, r (s b) = 0 := fun b => by
    simp only [r, s]
    rw [H2map_comp_apply, hrs, H2map_zero_apply]
  have hoi' : ∀ a, o (i a) = 0 := fun a => by
    simp only [o, i]
    rw [H2map_comp_apply]
    have h0 : localUnitsInclusion v w ≫ unitsExponentMorphism v w = 0 := hoi
    rw [h0, H2map_zero_apply]
  have hr_add : ∀ a b, r (a + b) = r a + r b := fun a b => map_add _ a b
  have ho_add : ∀ a b, o (a + b) = o a + o b := fun a b => map_add _ a b
  let Φ : groupCohomology (localUnitsRepresentation v w) 2 ×
      groupCohomology (Rep.trivial IntegerScalars.{u}
        (w.adicCompletion E ≃ₐ[v.adicCompletion F] w.adicCompletion E) IntegerScalars.{u}) 2 →
      relativeCohomology (padicField v).Carrier (w.adicCompletion E) 2 :=
    fun p => i p.1 + s p.2
  have hΦ : Function.Injective Φ := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    have hb : b = b' := by
      have := congrArg o h
      simp only [Φ, ho_add, hoi', hos', zero_add] at this
      exact this
    have ha : a = a' := by
      have := congrArg r h
      simp only [Φ, hr_add, hri', hrs', add_zero] at this
      exact this
    rw [ha, hb]
  have hsinj : Function.Injective s := fun b b' h => by
    rw [← hos' b, ← hos' b', h]
  have hiinj : Function.Injective i := fun a a' h => by
    rw [← hri' a, ← hri' a', h]
  have : Finite (groupCohomology (Rep.trivial IntegerScalars.{u}
      (w.adicCompletion E ≃ₐ[v.adicCompletion F] w.adicCompletion E) IntegerScalars.{u}) 2) :=
    Finite.of_injective s hsinj
  have : Finite (groupCohomology (localUnitsRepresentation v w) 2) :=
    Finite.of_injective i hiinj
  have := isCyclic_localGal v w he
  have := FiniteExtension.local_finite v w
  have := isGalois_adicCompletion v w
  have hD : Nat.card (w.adicCompletion E ≃ₐ[v.adicCompletion F] w.adicCompletion E) =
      Module.finrank (v.adicCompletion F) (w.adicCompletion E) :=
    IsGalois.card_aut_eq_finrank _ _
  have hZ := card_le_card_H2_trivial_integers
    (G := w.adicCompletion E ≃ₐ[v.adicCompletion F] w.adicCompletion E)
  have hprod := Nat.card_le_card_of_injective Φ hΦ
  rw [Nat.card_prod] at hprod
  have hpos : 0 < Nat.card (groupCohomology (Rep.trivial IntegerScalars.{u}
      (w.adicCompletion E ≃ₐ[v.adicCompletion F] w.adicCompletion E) IntegerScalars.{u}) 2) :=
    Nat.card_pos
  have hU : Nat.card (groupCohomology (localUnitsRepresentation v w) 2) ≤ 1 := by
    by_contra hlt
    push Not at hlt
    have h1 : 2 * Nat.card (groupCohomology (Rep.trivial IntegerScalars.{u}
        (w.adicCompletion E ≃ₐ[v.adicCompletion F] w.adicCompletion E) IntegerScalars.{u}) 2) ≤
        Nat.card (groupCohomology (Rep.trivial IntegerScalars.{u}
        (w.adicCompletion E ≃ₐ[v.adicCompletion F] w.adicCompletion E) IntegerScalars.{u}) 2) :=
      le_trans (Nat.mul_le_mul_right _ hlt) (hprod.trans (hcard.trans (hD ▸ hZ)))
    omega
  have : Subsingleton (groupCohomology (localUnitsRepresentation v w) 2) :=
    Finite.card_le_one_iff_subsingleton.1 hU
  exact ModuleCat.isZero_of_subsingleton _

end Vanishing

end Langlands.ClassField.Global
