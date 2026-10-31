import Langlands.Cohomology.PrimeFreeHomotopyDescentStatement
import Langlands.Cohomology.ExtendScalarsLocalizationDescent
import Mathlib.Data.Int.Interval

/-! # Proof of descent of finite free homotopy models from a prime localization -/

universe u

open CategoryTheory Limits

noncomputable section

namespace Langlands.Cohomology.ModuleComplex

variable {R : Type u} [CommRing R]

section Assembly

variable {A : Type u} [CommRing A] (φ : R →+* A) {K : CochainComplex (ModuleCat.{u} R) ℤ}
  {F : ℤ → ModuleCat.{u} R} (D : ∀ i j, F i ⟶ F j) (σ : A)

/-- The complex with terms `A ⊗ F i` whose differential from degree `i` to
`i + 1` is `σ` times the scalar extension of `D i (i + 1)`. -/
def scaledExtendScalarsComplex
    (hD : ∀ i, (ModuleCat.extendScalars φ).map (D i (i + 1) ≫ D (i + 1) (i + 1 + 1)) = 0) :
    CochainComplex (ModuleCat.{u} A) ℤ where
  X i := (ModuleCat.extendScalars φ).obj (F i)
  d i j := if i + 1 = j then σ • (ModuleCat.extendScalars φ).map (D i j) else 0
  shape i j h := ite_eq_right h
  d_comp_d' i j k hij hjk := by
    change i + 1 = j at hij
    change j + 1 = k at hjk
    subst hij hjk
    rw [ite_eq_left rfl, ite_eq_left rfl, Linear.smul_comp, Linear.comp_smul, ← Functor.map_comp, hD,
      smul_zero, smul_zero]

variable {S : R} (hσ : σ * φ S = 1)
  (Φ : ∀ i, F i ⟶ K.X i) (Ψ : ∀ i, K.X i ⟶ F i) (H : ∀ i j, F i ⟶ F j)
  (G : ∀ i j, K.X i ⟶ K.X j)
  (hD : ∀ i, (ModuleCat.extendScalars φ).map (D i (i + 1) ≫ D (i + 1) (i + 1 + 1)) = 0)
  (hΦ : ∀ i, (ModuleCat.extendScalars φ).map (S • (Φ i ≫ K.d i (i + 1))) =
    (ModuleCat.extendScalars φ).map (D i (i + 1) ≫ Φ (i + 1)))
  (hΨ : ∀ i, (ModuleCat.extendScalars φ).map (Ψ i ≫ D i (i + 1)) =
    (ModuleCat.extendScalars φ).map (S • (K.d i (i + 1) ≫ Ψ (i + 1))))
  (hH : ∀ i, (ModuleCat.extendScalars φ).map (Φ i ≫ Ψ i) =
    (ModuleCat.extendScalars φ).map
      (D i (i + 1) ≫ H (i + 1) i + H i (i - 1) ≫ D (i - 1) i + (S * S) • 𝟙 (F i)))
  (hG : ∀ i, (ModuleCat.extendScalars φ).map (Ψ i ≫ Φ i) =
    (ModuleCat.extendScalars φ).map
      (S • (K.d i (i + 1) ≫ G (i + 1) i + G i (i - 1) ≫ K.d (i - 1) i) + (S * S) • 𝟙 (K.X i)))

include hσ in
lemma smul_smul_extendScalars_map_eq_one :
    σ * σ * φ (S * S) = 1 := by
  rw [map_mul, show σ * σ * (φ S * φ S) = (σ * φ S) * (σ * φ S) by ring, hσ, one_mul]

include hσ in
lemma smul_smul_extendScalars_map_eq_self :
    σ * σ * φ S = σ := by
  rw [mul_assoc, hσ, mul_one]

/-- A homotopy equivalence over `A` assembled from morphisms over `R` which
satisfy the identities of a homotopy equivalence up to the scalar `S` after
extension of scalars, where `σ` inverts the image of `S`. -/
def scaledExtendScalarsHomotopyEquiv :
    HomotopyEquiv (scaledExtendScalarsComplex φ D σ hD) ((baseChange φ).obj K) where
  hom :=
    { f i := σ • (ModuleCat.extendScalars φ).map (Φ i)
      comm' i j hij := by
        change i + 1 = j at hij
        subst hij
        change (σ • (ModuleCat.extendScalars φ).map (Φ i)) ≫
            (ModuleCat.extendScalars φ).map (K.d i (i + 1)) =
          (if i + 1 = i + 1 then σ • (ModuleCat.extendScalars φ).map (D i (i + 1)) else 0) ≫
            (σ • (ModuleCat.extendScalars φ).map (Φ (i + 1)))
        rw [ite_eq_left rfl, Linear.smul_comp, Linear.smul_comp, Linear.comp_smul, smul_smul,
          ← Functor.map_comp, ← Functor.map_comp, ← hΦ i, extendScalars_map_smul, smul_smul,
          smul_smul_extendScalars_map_eq_self φ σ hσ] }
  inv :=
    { f i := σ • (ModuleCat.extendScalars φ).map (Ψ i)
      comm' i j hij := by
        change i + 1 = j at hij
        subst hij
        change (σ • (ModuleCat.extendScalars φ).map (Ψ i)) ≫
            (if i + 1 = i + 1 then σ • (ModuleCat.extendScalars φ).map (D i (i + 1)) else 0) =
          (ModuleCat.extendScalars φ).map (K.d i (i + 1)) ≫
            (σ • (ModuleCat.extendScalars φ).map (Ψ (i + 1)))
        rw [ite_eq_left rfl, Linear.smul_comp, Linear.comp_smul, Linear.comp_smul, smul_smul,
          ← Functor.map_comp, ← Functor.map_comp, hΨ i, extendScalars_map_smul, smul_smul,
          smul_smul_extendScalars_map_eq_self φ σ hσ] }
  homotopyHomInvId :=
    { hom i j := if j + 1 = i then σ • (ModuleCat.extendScalars φ).map (H i j) else 0
      zero i j h := ite_eq_right h
      comm i := by
        rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel i (i + 1) from rfl),
          prevD_eq _ (show (ComplexShape.up ℤ).Rel (i - 1) i from sub_add_cancel i 1)]
        change (σ • (ModuleCat.extendScalars φ).map (Φ i)) ≫
            (σ • (ModuleCat.extendScalars φ).map (Ψ i)) =
          (if i + 1 = i + 1 then σ • (ModuleCat.extendScalars φ).map (D i (i + 1)) else 0) ≫
            (if i + 1 = i + 1 then σ • (ModuleCat.extendScalars φ).map (H (i + 1) i)
              else 0) +
          (if i - 1 + 1 = i then σ • (ModuleCat.extendScalars φ).map (H i (i - 1)) else 0) ≫
            (if i - 1 + 1 = i then σ • (ModuleCat.extendScalars φ).map (D (i - 1) i)
              else 0) + 𝟙 ((ModuleCat.extendScalars φ).obj (F i))
        rw [ite_eq_left rfl, ite_eq_left rfl, ite_eq_left (sub_add_cancel i 1), ite_eq_left (sub_add_cancel i 1)]
        simp only [Linear.smul_comp, Linear.comp_smul, smul_smul, ← Functor.map_comp]
        rw [hH i]
        simp only [Functor.map_add, Functor.map_comp, extendScalars_map_smul,
          smul_add, smul_smul, smul_smul_extendScalars_map_eq_one φ σ hσ, one_smul]
        congr 1
        exact (ModuleCat.extendScalars φ).map_id _ }
  homotopyInvHomId :=
    { hom i j := if j + 1 = i then σ • (ModuleCat.extendScalars φ).map (G i j) else 0
      zero i j h := ite_eq_right h
      comm i := by
        rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel i (i + 1) from rfl),
          prevD_eq _ (show (ComplexShape.up ℤ).Rel (i - 1) i from sub_add_cancel i 1)]
        change (σ • (ModuleCat.extendScalars φ).map (Ψ i)) ≫
            (σ • (ModuleCat.extendScalars φ).map (Φ i)) =
          (ModuleCat.extendScalars φ).map (K.d i (i + 1)) ≫
            (if i + 1 = i + 1 then σ • (ModuleCat.extendScalars φ).map (G (i + 1) i)
              else 0) +
          (if i - 1 + 1 = i then σ • (ModuleCat.extendScalars φ).map (G i (i - 1)) else 0) ≫
            (ModuleCat.extendScalars φ).map (K.d (i - 1) i) +
            𝟙 ((ModuleCat.extendScalars φ).obj (K.X i))
        rw [ite_eq_left rfl, ite_eq_left (sub_add_cancel i 1)]
        simp only [Linear.smul_comp, Linear.comp_smul, smul_smul, ← Functor.map_comp]
        rw [hG i]
        simp only [Functor.map_add, Functor.map_comp, extendScalars_map_smul,
          smul_add, smul_smul, smul_smul_extendScalars_map_eq_one φ σ hσ, one_smul,
          smul_smul_extendScalars_map_eq_self φ σ hσ]
        congr 1
        exact (ModuleCat.extendScalars φ).map_id _ }

end Assembly

/-- Descent of a homotopy equivalence, given by its components over a
localization `A` of `R`, from scalar extensions of finitely presented modules
`F i` to the scalar extension of a complex `K` of finitely presented modules,
all zero outside a finite set: over `R_r` for one `r` in the submonoid, the
scalar extensions of the `F i` form a complex homotopy equivalent to the scalar
extension of `K`. -/
lemma exists_away_homotopyEquiv_of_extendScalars {A : Type u} [CommRing A] (φ : R →+* A)
    {T : Submonoid R} (hT : T.IsLocalizationMap φ) (K : CochainComplex (ModuleCat.{u} R) ℤ)
    [∀ i, Module.FinitePresentation R (K.X i)] (F : ℤ → ModuleCat.{u} R)
    [∀ i, Module.FinitePresentation R (F i)] (s : Finset ℤ)
    (hs : ∀ i ∉ s, IsZero (F i) ∧ IsZero (K.X i))
    (dL hL : ∀ i j, (ModuleCat.extendScalars φ).obj (F i) ⟶ (ModuleCat.extendScalars φ).obj (F j))
    (fL : ∀ i, (ModuleCat.extendScalars φ).obj (F i) ⟶ (ModuleCat.extendScalars φ).obj (K.X i))
    (gL : ∀ i, (ModuleCat.extendScalars φ).obj (K.X i) ⟶ (ModuleCat.extendScalars φ).obj (F i))
    (kL : ∀ i j,
      (ModuleCat.extendScalars φ).obj (K.X i) ⟶ (ModuleCat.extendScalars φ).obj (K.X j))
    (hdd : ∀ i, dL i (i + 1) ≫ dL (i + 1) (i + 1 + 1) = 0)
    (hf : ∀ i, fL i ≫ (ModuleCat.extendScalars φ).map (K.d i (i + 1)) =
      dL i (i + 1) ≫ fL (i + 1))
    (hg : ∀ i, gL i ≫ dL i (i + 1) =
      (ModuleCat.extendScalars φ).map (K.d i (i + 1)) ≫ gL (i + 1))
    (hh : ∀ i, fL i ≫ gL i =
      dL i (i + 1) ≫ hL (i + 1) i + hL i (i - 1) ≫ dL (i - 1) i + 𝟙 _)
    (hk : ∀ i, gL i ≫ fL i =
      (ModuleCat.extendScalars φ).map (K.d i (i + 1)) ≫ kL (i + 1) i +
        kL i (i - 1) ≫ (ModuleCat.extendScalars φ).map (K.d (i - 1) i) + 𝟙 _) :
    ∃ r ∈ T, ∃ P : CochainComplex (ModuleCat.{u} (Localization.Away r)) ℤ,
      (∀ i, Nonempty (P.X i ≅
        (ModuleCat.extendScalars (algebraMap R (Localization.Away r))).obj (F i))) ∧
      Nonempty (HomotopyEquiv P ((baseChange (algebraMap R (Localization.Away r))).obj K)) := by
  -- Lift the components to `R` after multiplication by elements of `T`.
  obtain ⟨t₁, ht₁, h₁⟩ := exists_mem_forall₂_extendScalars_map_eq_smul φ hT s F F dL
    (fun i hi ↦ ⟨(hs i hi).1, (hs i hi).1⟩)
  obtain ⟨t₂, ht₂, h₂⟩ := exists_mem_forall_extendScalars_map_eq_smul φ hT s F (fun i ↦ K.X i) fL
    (fun i hi ↦ Or.inl (hs i hi).1)
  obtain ⟨t₃, ht₃, h₃⟩ := exists_mem_forall_extendScalars_map_eq_smul φ hT s (fun i ↦ K.X i) F gL
    (fun i hi ↦ Or.inl (hs i hi).2)
  obtain ⟨t₄, ht₄, h₄⟩ := exists_mem_forall₂_extendScalars_map_eq_smul φ hT s F F hL
    (fun i hi ↦ ⟨(hs i hi).1, (hs i hi).1⟩)
  obtain ⟨t₅, ht₅, h₅⟩ := exists_mem_forall₂_extendScalars_map_eq_smul φ hT s
    (fun i ↦ K.X i) (fun i ↦ K.X i) kL (fun i hi ↦ ⟨(hs i hi).2, (hs i hi).2⟩)
  obtain ⟨S, hST, hS₁, hS₂, hS₃, hS₄, hS₅⟩ :
      ∃ S ∈ T, t₁ ∣ S ∧ t₂ ∣ S ∧ t₃ ∣ S ∧ t₄ ∣ S ∧ t₅ ∣ S :=
    ⟨t₁ * t₂ * t₃ * t₄ * t₅, T.mul_mem (T.mul_mem (T.mul_mem (T.mul_mem ht₁ ht₂) ht₃) ht₄) ht₅,
      ⟨t₂ * t₃ * t₄ * t₅, by ring⟩, ⟨t₁ * t₃ * t₄ * t₅, by ring⟩, ⟨t₁ * t₂ * t₄ * t₅, by ring⟩,
      ⟨t₁ * t₂ * t₃ * t₅, by ring⟩, ⟨t₁ * t₂ * t₃ * t₄, by ring⟩⟩
  choose D hD using fun i j ↦ exists_extendScalars_map_eq_smul_of_dvd φ hS₁ (h₁ i j)
  choose Φ hΦ using fun i ↦ exists_extendScalars_map_eq_smul_of_dvd φ hS₂ (h₂ i)
  choose Ψ hΨ using fun i ↦ exists_extendScalars_map_eq_smul_of_dvd φ hS₃ (h₃ i)
  choose H hH using fun i j ↦ exists_extendScalars_map_eq_smul_of_dvd φ hS₄ (h₄ i j)
  choose G hG using fun i j ↦ exists_extendScalars_map_eq_smul_of_dvd φ hS₅ (h₅ i j)
  -- The identities of a homotopy equivalence hold up to `S` after extension to `A`.
  have eD : ∀ i, (ModuleCat.extendScalars φ).map (D i (i + 1) ≫ D (i + 1) (i + 1 + 1)) =
      (ModuleCat.extendScalars φ).map 0 := fun i ↦ by
    simp only [Functor.map_comp, hD, Linear.smul_comp, Linear.comp_smul, hdd, smul_zero,
      Functor.map_zero]
  have eΦ : ∀ i, (ModuleCat.extendScalars φ).map (S • (Φ i ≫ K.d i (i + 1))) =
      (ModuleCat.extendScalars φ).map (D i (i + 1) ≫ Φ (i + 1)) := fun i ↦ by
    simp only [extendScalars_map_smul, Functor.map_comp, hΦ, hD, Linear.smul_comp,
      Linear.comp_smul, smul_smul, hf]
  have eΨ : ∀ i, (ModuleCat.extendScalars φ).map (Ψ i ≫ D i (i + 1)) =
      (ModuleCat.extendScalars φ).map (S • (K.d i (i + 1) ≫ Ψ (i + 1))) := fun i ↦ by
    simp only [extendScalars_map_smul, Functor.map_comp, hΨ, hD, Linear.smul_comp,
      Linear.comp_smul, smul_smul, hg]
  have eH : ∀ i, (ModuleCat.extendScalars φ).map (Φ i ≫ Ψ i) =
      (ModuleCat.extendScalars φ).map
        (D i (i + 1) ≫ H (i + 1) i + H i (i - 1) ≫ D (i - 1) i + (S * S) • 𝟙 (F i)) :=
    fun i ↦ by
    simp only [Functor.map_add, extendScalars_map_smul, Functor.map_comp, hΦ, hΨ, hD, hH,
      Linear.smul_comp, Linear.comp_smul, smul_smul, hh, smul_add, map_mul]
    congr 2
    exact ((ModuleCat.extendScalars φ).map_id _).symm
  have eG : ∀ i, (ModuleCat.extendScalars φ).map (Ψ i ≫ Φ i) =
      (ModuleCat.extendScalars φ).map
        (S • (K.d i (i + 1) ≫ G (i + 1) i + G i (i - 1) ≫ K.d (i - 1) i) +
          (S * S) • 𝟙 (K.X i)) := fun i ↦ by
    simp only [Functor.map_add, extendScalars_map_smul, Functor.map_comp, hΦ, hΨ, hG,
      Linear.smul_comp, Linear.comp_smul, smul_smul, hk, smul_add, map_mul]
    congr 2
    exact ((ModuleCat.extendScalars φ).map_id _).symm
  -- These identities hold over `R` after multiplication by elements of `T`.
  obtain ⟨u₁, hu₁, k₁⟩ := exists_mem_forall_smul_eq_of_extendScalars_map_eq φ hT s F
    (fun i ↦ F (i + 1 + 1)) _ _ eD (fun i hi ↦ (hs i hi).1)
  obtain ⟨u₂, hu₂, k₂⟩ := exists_mem_forall_smul_eq_of_extendScalars_map_eq φ hT s F
    (fun i ↦ K.X (i + 1)) _ _ eΦ (fun i hi ↦ (hs i hi).1)
  obtain ⟨u₃, hu₃, k₃⟩ := exists_mem_forall_smul_eq_of_extendScalars_map_eq φ hT s
    (fun i ↦ K.X i) (fun i ↦ F (i + 1)) _ _ eΨ (fun i hi ↦ (hs i hi).2)
  obtain ⟨u₄, hu₄, k₄⟩ := exists_mem_forall_smul_eq_of_extendScalars_map_eq φ hT s F F _ _ eH
    (fun i hi ↦ (hs i hi).1)
  obtain ⟨u₅, hu₅, k₅⟩ := exists_mem_forall_smul_eq_of_extendScalars_map_eq φ hT s
    (fun i ↦ K.X i) (fun i ↦ K.X i) _ _ eG (fun i hi ↦ (hs i hi).2)
  -- Invert `S` and all `uₖ` at once.
  obtain ⟨r, hrT, hrS, hr₁, hr₂, hr₃, hr₄, hr₅⟩ :
      ∃ r ∈ T, S ∣ r ∧ u₁ ∣ r ∧ u₂ ∣ r ∧ u₃ ∣ r ∧ u₄ ∣ r ∧ u₅ ∣ r :=
    ⟨S * u₁ * u₂ * u₃ * u₄ * u₅,
      T.mul_mem (T.mul_mem (T.mul_mem (T.mul_mem (T.mul_mem hST hu₁) hu₂) hu₃) hu₄) hu₅,
      ⟨u₁ * u₂ * u₃ * u₄ * u₅, by ring⟩, ⟨S * u₂ * u₃ * u₄ * u₅, by ring⟩,
      ⟨S * u₁ * u₃ * u₄ * u₅, by ring⟩, ⟨S * u₁ * u₂ * u₄ * u₅, by ring⟩,
      ⟨S * u₁ * u₂ * u₃ * u₅, by ring⟩, ⟨S * u₁ * u₂ * u₃ * u₄, by ring⟩⟩
  have hr : IsUnit (algebraMap R (Localization.Away r) r) :=
    IsLocalization.Away.algebraMap_isUnit r
  have unit {x : R} (hx : x ∣ r) : IsUnit (algebraMap R (Localization.Away r) x) :=
    isUnit_of_dvd_unit (map_dvd _ hx) hr
  have hSu := unit hrS
  refine ⟨r, hrT,
    scaledExtendScalarsComplex _ D (↑hSu.unit⁻¹) (fun i ↦
      (extendScalars_map_eq_of_smul_eq _ (unit hr₁) (k₁ i)).trans
        (Functor.map_zero _ _ _)),
    fun i ↦ ⟨Iso.refl _⟩, ⟨scaledExtendScalarsHomotopyEquiv _ D _ hSu.val_inv_mul Φ Ψ H G _
      (fun i ↦ extendScalars_map_eq_of_smul_eq _ (unit hr₂) (k₂ i))
      (fun i ↦ extendScalars_map_eq_of_smul_eq _ (unit hr₃) (k₃ i))
      (fun i ↦ extendScalars_map_eq_of_smul_eq _ (unit hr₄) (k₄ i))
      (fun i ↦ extendScalars_map_eq_of_smul_eq _ (unit hr₅)
        (k₅ i))⟩⟩

/-- A finite free homotopy model of a bounded finite projective complex over
`R_p`, with prescribed term ranks, descends to a finite free homotopy model with
the same ranks over one localization `R_r` with `r ∉ p`. -/
theorem primeFreeHomotopyDescent : PrimeFreeHomotopyDescentStatement.{u} := by
  intro R _ K hK p _ n L hL hE he
  -- Restate the target of the homotopy equivalence with terms that are
  -- reducibly scalar extensions of the terms of `K`.
  obtain ⟨E⟩ : Nonempty (HomotopyEquiv L
      { X i := (ModuleCat.extendScalars (algebraMap R (Localization.AtPrime p))).obj (K.X i)
        d i j := (ModuleCat.extendScalars (algebraMap R (Localization.AtPrime p))).map (K.d i j)
        shape := ((baseChange (algebraMap R (Localization.AtPrime p))).obj K).shape
        d_comp_d' := ((baseChange (algebraMap R (Localization.AtPrime p))).obj K).d_comp_d' }) :=
    hE
  have hT : p.primeCompl.IsLocalizationMap (algebraMap R (Localization.AtPrime p)) :=
    (isLocalization_iff_isLocalizationMap p.primeCompl (Localization.AtPrime p)).1
      inferInstance
  obtain ⟨⟨a, b, haK, hbK⟩, hKfp⟩ := hK
  obtain ⟨⟨a', b', haL, hbL⟩, -⟩ := hL
  -- The ranks vanish outside the bounds of `L`.
  have hn : ∀ i, i < a' ∨ b' < i → n i = 0 := by
    intro i hi
    have hLi : IsZero (L.X i) := hi.elim (fun h ↦ L.isZero_of_isStrictlyGE a' i h)
      (fun h ↦ L.isZero_of_isStrictlyLE b' i h)
    have := ModuleCat.subsingleton_of_isZero hLi
    have := (he i).some.symm.toEquiv.subsingleton
    by_contra hni
    have : Nonempty (Fin (n i)) := ⟨⟨0, Nat.pos_of_ne_zero hni⟩⟩
    exact not_subsingleton (Fin (n i) → Localization.AtPrime p) inferInstance
  -- Standard free modules over `R` whose scalar extensions are the terms of `L`.
  let F : ℤ → ModuleCat.{u} R := fun i ↦ ModuleCat.of R (Fin (n i) → R)
  have hFfp : ∀ i, Module.FinitePresentation R (F i) := fun i ↦
    inferInstanceAs (Module.FinitePresentation R (Fin (n i) → R))
  have hKfp' : ∀ i, Module.FinitePresentation R (K.X i) := fun i ↦ by
    have := (hKfp i).1
    have := (hKfp i).2
    exact Module.finitePresentation_of_projective R (K.X i)
  have hFz : ∀ i, n i = 0 → IsZero (F i) := fun i hi ↦ by
    have : IsEmpty (Fin (n i)) := by rw [hi]; infer_instance
    exact ModuleCat.isZero_of_subsingleton (ModuleCat.of R (Fin (n i) → R))
  have hs : ∀ i ∉ Finset.Icc (min a a') (max b b'), IsZero (F i) ∧ IsZero (K.X i) := by
    intro i hi
    rw [Finset.mem_Icc, not_and_or, not_le, not_le, lt_min_iff, max_lt_iff] at hi
    rcases hi with ⟨h, h'⟩ | ⟨h, h'⟩
    · exact ⟨hFz i (hn i (Or.inl h')), K.isZero_of_isStrictlyGE a i h⟩
    · exact ⟨hFz i (hn i (Or.inr h')), K.isZero_of_isStrictlyLE b i h⟩
  have e : ∀ i, L.X i ≅
      (ModuleCat.extendScalars (algebraMap R (Localization.AtPrime p))).obj (F i) := fun i ↦
    ((he i).some.trans (nonempty_extendScalars_pi_equiv
      (algebraMap R (Localization.AtPrime p)) (n i)).some.symm).toModuleIso
  -- Transport the homotopy equivalence to the scalar extensions of the `F i`.
  obtain ⟨r, hr, P, hPX, ⟨EP⟩⟩ := exists_away_homotopyEquiv_of_extendScalars
    (algebraMap R (Localization.AtPrime p)) hT K F _ hs
    (fun i j ↦ (e i).inv ≫ L.d i j ≫ (e j).hom)
    (fun i j ↦ (e i).inv ≫ E.homotopyHomInvId.hom i j ≫ (e j).hom)
    (fun i ↦ (e i).inv ≫ E.hom.f i) (fun i ↦ E.inv.f i ≫ (e i).hom)
    (fun i j ↦ E.homotopyInvHomId.hom i j)
    (fun i ↦ by simp)
    (fun i ↦ by
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
      exact (e i).inv ≫= E.hom.comm i (i + 1))
    (fun i ↦ by
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
      exact (reassoc_of% (E.inv.comm i (i + 1))) _)
    (fun i ↦ by
      have hc := E.homotopyHomInvId.comm i
      rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel i (i + 1) from rfl),
        prevD_eq _ (show (ComplexShape.up ℤ).Rel (i - 1) i from sub_add_cancel i 1),
        HomologicalComplex.comp_f, HomologicalComplex.id_f] at hc
      simp [reassoc_of% hc, Preadditive.comp_add, Preadditive.add_comp])
    (fun i ↦ by
      have hc := E.homotopyInvHomId.comm i
      rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel i (i + 1) from rfl),
        prevD_eq _ (show (ComplexShape.up ℤ).Rel (i - 1) i from sub_add_cancel i 1),
        HomologicalComplex.comp_f, HomologicalComplex.id_f] at hc
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
      exact hc)
  -- The descended complex is finite free with the prescribed ranks.
  have eP : ∀ i, Nonempty (P.X i ≃ₗ[Localization.Away r] (Fin (n i) → Localization.Away r)) :=
    fun i ↦ ⟨(hPX i).some.toLinearEquiv.trans
      (nonempty_extendScalars_pi_equiv (algebraMap R (Localization.Away r)) (n i)).some⟩
  have hPz : ∀ i, i < a' ∨ b' < i → IsZero (P.X i) := by
    intro i hi
    have : IsEmpty (Fin (n i)) := by rw [hn i hi]; infer_instance
    have := (eP i).some.toEquiv.subsingleton
    exact ModuleCat.isZero_of_subsingleton _
  refine ⟨r, Ideal.mem_primeCompl_iff.1 hr, P,
    ⟨⟨a', b', (P.isStrictlyGE_iff a').2 fun i hi ↦ hPz i (Or.inl hi),
      (P.isStrictlyLE_iff b').2 fun i hi ↦ hPz i (Or.inr hi)⟩, fun i ↦ ?_⟩, ⟨EP⟩, eP⟩
  obtain ⟨f⟩ := eP i
  exact ⟨Module.Finite.equiv f.symm, Module.Free.of_equiv f.symm⟩

end Langlands.Cohomology.ModuleComplex
