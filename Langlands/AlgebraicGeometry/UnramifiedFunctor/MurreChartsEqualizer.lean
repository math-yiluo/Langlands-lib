import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreChartsAffine

/-! # The locus where two elements of `F(Spec C)` agree

For an `R`-algebra `C` and two elements `ξ₁, ξ₂` of `F(Spec C)`, `AgreeAt ξ₁ ξ₂ c` says that
`ξ₁` and `ξ₂` have the same image in `F(Spec κ(c))` for the residue field `κ(c)` at the prime
`c`. With (F1b) this holds as soon as they agree at some field point with image `c`. If the
base change of `F` to every local scheme `Spec 𝒪_{Spec R, s}` is represented by a formally
unramified scheme locally of finite type, agreement at `κ(c)` implies agreement on
`Spec C_c`, and with (F1a) and (F2) the agreement locus is open. -/

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

noncomputable section

namespace Langlands.AlgebraicGeometry.UnramifiedFunctor

namespace Charts

variable {R : CommRingCat.{u}} {F : (Over (Spec R))ᵒᵖ ⥤ Type v}
variable {C : Type u} [CommRing C] [Algebra R C]

variable (R) in
/-- The morphism `Spec κ(c) ⟶ Spec C` over `Spec R`. -/
abbrev residueOver (c : PrimeSpectrum C) :
    ovR R c.asIdeal.ResidueField ⟶ ovR R C :=
  homR (IsScalarTower.toAlgHom R C c.asIdeal.ResidueField)

/-- `ξ₁` and `ξ₂` have the same image in `F(Spec κ(c))`. -/
def AgreeAt (ξ₁ ξ₂ : F.obj (op (ovR R C))) (c : PrimeSpectrum C) : Prop :=
  F.map (residueOver R c).op ξ₁ = F.map (residueOver R c).op ξ₂

/-- A morphism from the spectrum of a field to `Spec C` with image `c` factors through
`Spec κ(c)`. -/
lemma exists_residue_factor (c : PrimeSpectrum C) {K : Type u} [Field K]
    (f : Spec (CommRingCat.of K) ⟶ Spec R) (z : Over.mk f ⟶ ovR R C)
    (hz : ∀ x, z.left x = c) :
    ∃ z₀ : Over.mk f ⟶ ovR R c.asIdeal.ResidueField, z₀ ≫ residueOver R c = z := by
  let ψ : CommRingCat.of C ⟶ CommRingCat.of K := Spec.preimage z.left
  have hψ : Spec.map ψ = z.left := Spec.map_preimage _
  have hker : ∀ y : C, ψ y = 0 ↔ y ∈ c.asIdeal := by
    intro y
    have h1 := hz (IsLocalRing.closedPoint K)
    rw [← hψ] at h1
    change PrimeSpectrum.comap ψ.hom (IsLocalRing.closedPoint K) = c at h1
    rw [← h1, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
    change _ ↔ ψ y ∈ IsLocalRing.maximalIdeal K
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_ne_zero, not_not]
  let lift : c.asIdeal.ResidueField →+* K := Ideal.ResidueField.lift c.asIdeal ψ.hom
    (fun y hy => (RingHom.mem_ker).2 ((hker y).2 hy))
    (fun y hy => isUnit_iff_ne_zero.2 fun h => hy ((hker y).1 h))
  have hlift : ∀ y : C, lift (algebraMap C c.asIdeal.ResidueField y) = ψ y :=
    Ideal.ResidueField.lift_algebraMap _ _ _ _
  refine ⟨Over.homMk (Spec.map (CommRingCat.ofHom lift)) ?_, ?_⟩
  · have hf : z.left ≫ Spec.map (CommRingCat.ofHom (algebraMap R C)) = f := Over.w z
    change Spec.map (CommRingCat.ofHom lift) ≫ Spec.map (CommRingCat.ofHom _) = f
    rw [← hf, ← hψ]
    simp only [← Spec.map_comp]
    congr 1
    ext y
    change lift (algebraMap R c.asIdeal.ResidueField y) = ψ (algebraMap R C y)
    rw [IsScalarTower.algebraMap_apply R C c.asIdeal.ResidueField, hlift]
  · ext1
    change Spec.map (CommRingCat.ofHom lift) ≫ Spec.map (CommRingCat.ofHom _) = z.left
    rw [← hψ]
    simp only [← Spec.map_comp]
    congr 1
    ext y
    exact hlift y

/-- Agreement at `κ(c)` gives agreement at every field point with image `c`. -/
lemma AgreeAt.map_eq {ξ₁ ξ₂ : F.obj (op (ovR R C))} {c : PrimeSpectrum C}
    (h : AgreeAt ξ₁ ξ₂ c) {K : Type u} [Field K] (f : Spec (CommRingCat.of K) ⟶ Spec R)
    (z : Over.mk f ⟶ ovR R C) (hz : ∀ x, z.left x = c) :
    F.map z.op ξ₁ = F.map z.op ξ₂ := by
  obtain ⟨z₀, rfl⟩ := exists_residue_factor c f z hz
  rw [op_comp, Functor.map_comp_apply, Functor.map_comp_apply, h]

/-- With (F1b), agreement at one field point with image `c` gives agreement at `κ(c)`. -/
lemma agreeAt_of_map_eq (hF : FaithfullyFlatSheaf F) {ξ₁ ξ₂ : F.obj (op (ovR R C))}
    {c : PrimeSpectrum C} {K : Type u} [Field K] (f : Spec (CommRingCat.of K) ⟶ Spec R)
    (z : Over.mk f ⟶ ovR R C) (hz : ∀ x, z.left x = c)
    (h : F.map z.op ξ₁ = F.map z.op ξ₂) : AgreeAt ξ₁ ξ₂ c := by
  obtain ⟨z₀, rfl⟩ := exists_residue_factor c f z hz
  rw [op_comp, Functor.map_comp_apply, Functor.map_comp_apply] at h
  exact map_injective_of_field hF f z₀ h

/-- If the base change of `F` to each `Spec 𝒪_{Spec R, s}` is represented by a formally
unramified scheme locally of finite type, agreement at `κ(c)` implies agreement on
`Spec C_c`. -/
lemma agreeAt_localization
    (hrep : ∀ s : Spec R, UnramifiedRepresentable (baseChange ((Spec R).fromSpecStalk s) F))
    {ξ₁ ξ₂ : F.obj (op (ovR R C))} {c : PrimeSpectrum C} (h : AgreeAt ξ₁ ξ₂ c) :
    F.map (homR (IsScalarTower.toAlgHom R C (Localization.AtPrime c.asIdeal))).op ξ₁ =
      F.map (homR (IsScalarTower.toAlgHom R C (Localization.AtPrime c.asIdeal))).op ξ₂ := by
  let L := Localization.AtPrime c.asIdeal
  let κ := c.asIdeal.ResidueField
  let r : Spec R := (ovR R L).hom (IsLocalRing.closedPoint L)
  obtain ⟨Y, q, ⟨e⟩, -, hLFT, hFU⟩ := hrep r
  let g := (Spec R).fromSpecStalk r
  obtain ⟨t, ht⟩ := exists_comp_fromSpecStalk r (ovR R L).hom (specializes_refl _)
  let E := elemEquiv g e (ovR R L) t ht
  let ρ : ovR R κ ⟶ ovR R L := homR (IsScalarTower.toAlgHom R L κ)
  have hρ : ρ ≫ homR (IsScalarTower.toAlgHom R C L) = residueOver R c := by
    rw [← homR_comp]
    congr 1
  have hagree : F.map ρ.op (F.map (homR (IsScalarTower.toAlgHom R C L)).op ξ₁) =
      F.map ρ.op (F.map (homR (IsScalarTower.toAlgHom R C L)).op ξ₂) := by
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, hρ]
    exact h
  have ht' : (ρ.left ≫ t) ≫ g = (ovR R κ).hom := by
    rw [Category.assoc, ht]
    exact Over.w ρ
  rw [← E.apply_symm_apply (F.map (homR (IsScalarTower.toAlgHom R C L)).op ξ₁),
    ← E.apply_symm_apply (F.map (homR (IsScalarTower.toAlgHom R C L)).op ξ₂),
    elemEquiv_naturality g e ρ (ρ.left ≫ t) t ht' ht,
    elemEquiv_naturality g e ρ (ρ.left ≫ t) t ht' ht] at hagree
  have hk := congrArg (fun k => k.left)
    ((elemEquiv g e (ovR R κ) (ρ.left ≫ t) ht').injective hagree)
  simp only [Over.comp_left, Over.homMk_left] at hk
  have : IsLocalHom (CommRingCat.ofHom (IsScalarTower.toAlgHom R L κ).toRingHom).hom :=
    inferInstanceAs (IsLocalHom (IsLocalRing.residue L))
  have hsymm : E.symm (F.map (homR (IsScalarTower.toAlgHom R C L)).op ξ₁) =
      E.symm (F.map (homR (IsScalarTower.toAlgHom R C L)).op ξ₂) := by
    apply Over.OverMorphism.ext
    refine eq_of_isLocalRing q _ _ ?_ ρ.left hk (IsLocalRing.closedPoint κ) ?_
    · exact (Over.w (E.symm _)).trans (Over.w (E.symm _)).symm
    · exact Spec_closedPoint (f := CommRingCat.ofHom (IsScalarTower.toAlgHom R L κ).toRingHom)
  simpa using congrArg E hsymm

/-- With (F1a), (F2) and the local representability, the agreement locus is open. -/
theorem isOpen_agreeAt (hZ : ZariskiSheaf F) (h2 : FilteredColimits F)
    (hrep : ∀ s : Spec R, UnramifiedRepresentable (baseChange ((Spec R).fromSpecStalk s) F))
    (ξ₁ ξ₂ : F.obj (op (ovR R C))) : IsOpen {c : PrimeSpectrum C | AgreeAt ξ₁ ξ₂ c} := by
  rw [isOpen_iff_forall_mem_open]
  intro c hc
  obtain ⟨a, ha⟩ := exists_away_eq_of_eq c.asIdeal.primeCompl (Localization.AtPrime c.asIdeal)
    hZ h2 ξ₁ ξ₂ (agreeAt_localization hrep hc)
  refine ⟨PrimeSpectrum.basicOpen a.val, ?_, (PrimeSpectrum.basicOpen a.val).isOpen, a.val_mem⟩
  intro c' hc'
  have hunit : IsUnit (IsScalarTower.toAlgHom R C c'.asIdeal.ResidueField a.val) := by
    refine isUnit_iff_ne_zero.2 ?_
    change algebraMap C c'.asIdeal.ResidueField a.val ≠ 0
    rw [Ne, Ideal.algebraMap_residueField_eq_zero]
    exact (PrimeSpectrum.mem_basicOpen _ _).1 hc'
  let φ : Localization.Away a.val →ₐ[R] c'.asIdeal.ResidueField :=
    IsLocalization.Away.liftAlgHom a.val hunit
  have hφ : φ.comp (IsScalarTower.toAlgHom R C (Localization.Away a.val)) =
      IsScalarTower.toAlgHom R C c'.asIdeal.ResidueField := by
    ext y
    simp [φ]
  show F.map (residueOver R c').op ξ₁ = F.map (residueOver R c').op ξ₂
  rw [residueOver, ← hφ, homR_comp, op_comp, Functor.map_comp_apply, Functor.map_comp_apply, ha]

end Charts

end Langlands.AlgebraicGeometry.UnramifiedFunctor
