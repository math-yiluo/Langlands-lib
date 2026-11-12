import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceMorphismProperties
import Langlands.AlgebraicGeometry.AlgebraicSpace.DiagonalEqualizer
import Langlands.AlgebraicGeometry.AlgebraicSpace.ExtensionProduct
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Spectra of algebras over a valuation ring as test schemes

For a scheme `S` and a morphism `s : Spec A ⟶ S`, every `A`-algebra `R` gives a test scheme
`Spec R` over `S`. This file records the functoriality of these test schemes, the pullback
square of a tensor product, the ideal cutting out the locus where two sections of a space
agree (from separatedness), and the étaleness of such loci over a chart.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace.ValuativeExistence

variable {S : Scheme.{u}} {A : Type u} [CommRing A] (s : Spec (CommRingCat.of A) ⟶ S)

/-- The spectrum of an `A`-algebra as a scheme over `S` through `s`. -/
abbrev algTest (R : Type u) [CommRing R] [Algebra A R] : Over S :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap A R)) ≫ s)

/-- The morphism of test schemes induced by an `A`-algebra map. -/
def algTestMap {R R' : Type u} [CommRing R] [CommRing R'] [Algebra A R] [Algebra A R']
    (φ : R →ₐ[A] R') : algTest s R' ⟶ algTest s R :=
  Over.homMk (Spec.map (CommRingCat.ofHom φ.toRingHom)) (by
    change Spec.map _ ≫ Spec.map _ ≫ s = Spec.map _ ≫ s
    rw [← Category.assoc, ← Spec.map_comp]
    congr 2
    ext c
    exact φ.commutes c)

/-- The structure morphism `Spec R ⟶ Spec A` as a morphism over `S`. -/
def algTestBase (R : Type u) [CommRing R] [Algebra A R] : algTest s R ⟶ Over.mk s :=
  Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap A R))) rfl

@[simp]
theorem algTestMap_left {R R' : Type u} [CommRing R] [CommRing R'] [Algebra A R] [Algebra A R']
    (φ : R →ₐ[A] R') :
    (algTestMap s φ).left = Spec.map (CommRingCat.ofHom φ.toRingHom) := rfl

theorem algTestMap_comp {R R' R'' : Type u} [CommRing R] [CommRing R'] [CommRing R'']
    [Algebra A R] [Algebra A R'] [Algebra A R''] (φ : R →ₐ[A] R') (ψ : R' →ₐ[A] R'') :
    algTestMap s (ψ.comp φ) = algTestMap s ψ ≫ algTestMap s φ := by
  ext1
  change Spec.map (CommRingCat.ofHom φ.toRingHom ≫ CommRingCat.ofHom ψ.toRingHom) =
    Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ Spec.map (CommRingCat.ofHom φ.toRingHom)
  exact Spec.map_comp _ _

theorem algTestMap_base {R R' : Type u} [CommRing R] [CommRing R'] [Algebra A R] [Algebra A R']
    (φ : R →ₐ[A] R') : algTestMap s φ ≫ algTestBase s R = algTestBase s R' := by
  ext1
  change Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  ext c
  exact φ.commutes c

/-- The spectrum of `R ⊗[A] R'` is the fibre product of the spectra over `Spec A`. -/
theorem isPullback_algTest (R R' : Type u) [CommRing R] [CommRing R'] [Algebra A R]
    [Algebra A R'] :
    IsPullback (algTestMap s (Algebra.TensorProduct.includeLeft : R →ₐ[A] R ⊗[A] R'))
      (algTestMap s (Algebra.TensorProduct.includeRight : R' →ₐ[A] R ⊗[A] R'))
      (algTestBase s R) (algTestBase s R') := by
  have hsp := isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct A R R')
  have hsp' : IsPullback
      ((Over.forget S).map
        (algTestMap s (Algebra.TensorProduct.includeLeft : R →ₐ[A] R ⊗[A] R')))
      ((Over.forget S).map
        (algTestMap s (Algebra.TensorProduct.includeRight : R' →ₐ[A] R ⊗[A] R')))
      ((Over.forget S).map (algTestBase s R)) ((Over.forget S).map (algTestBase s R')) :=
    hsp
  exact hsp'.of_map_of_faithful (Over.forget S)

/-- A morphism of test schemes factors through `Spec (R ⧸ I)` exactly when the ring map kills
`I`. -/
theorem exists_comp_mk_iff {R R' : Type u} [CommRing R] [CommRing R'] [Algebra A R]
    [Algebra A R'] (I : Ideal R) (ψ : R →ₐ[A] R') :
    (∃ z : algTest s R' ⟶ algTest s (R ⧸ I),
        z ≫ algTestMap s (Ideal.Quotient.mkₐ A I) = algTestMap s ψ) ↔
      I ≤ RingHom.ker ψ := by
  constructor
  · rintro ⟨z, hz⟩
    have h1 := congrArg (fun g => g.left) hz
    simp only [Over.comp_left, algTestMap_left] at h1
    rw [← Spec.map_preimage z.left, ← Spec.map_comp] at h1
    have h2 := Spec.map_injective h1
    intro r hr
    rw [RingHom.mem_ker]
    have h3 := congrArg (fun g => g.hom r) h2
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp,
      Function.comp_apply] at h3
    change (Spec.preimage z.left).hom (Ideal.Quotient.mk I r) = ψ r at h3
    rw [← h3, Ideal.Quotient.eq_zero_iff_mem.mpr hr, map_zero]
  · intro h
    refine ⟨algTestMap s (Ideal.Quotient.liftₐ I ψ fun r hr => h hr), ?_⟩
    rw [← algTestMap_comp]
    congr 1

section Separated

variable {X Y : AlgebraicSpace S} (f : X ⟶ Y)

/-- For a separated morphism, the locus where two sections with the same image agree is cut
out by a closed immersion. -/
theorem exists_representsEqualizer (hf : IsSeparatedMorphism f) {U : Over S}
    (ξ₁ ξ₂ : X.sections U) (h : mapSections f U ξ₁ = mapSections f U ξ₂) :
    ∃ (Z : Over S) (ι : Z ⟶ U), RepresentsEqualizer (F := X.presheaf) ι ξ₁ ξ₂ ∧
      AlgebraicGeometry.IsClosedImmersion ι.left := by
  have w : (uliftYonedaEquiv.{u + 1}.symm ξ₁ : (schemeYoneda S).obj U ⟶ X.presheaf) ≫ hom f =
      (uliftYonedaEquiv.{u + 1}.symm ξ₂ : (schemeYoneda S).obj U ⟶ X.presheaf) ≫ hom f := by
    rw [uliftYonedaEquiv_symm_comp, uliftYonedaEquiv_symm_comp]
    exact congrArg _ h
  let g : (schemeYoneda S).obj U ⟶ Limits.pullback (hom f) (hom f) :=
    pullback.lift (uliftYonedaEquiv.{u + 1}.symm ξ₁) (uliftYonedaEquiv.{u + 1}.symm ξ₂) w
  have hsq := hf.rep.isPullback g
  refine ⟨hf.rep.pullback g, hf.rep.snd g, fun T k ↦ ⟨?_, fun hxy ↦ ?_⟩,
    hf.property_snd g⟩
  · rintro ⟨z, rfl⟩
    have e₁ := congr($(hsq.w) ≫ pullback.fst (hom f) (hom f))
    have e₂ := congr($(hsq.w) ≫ pullback.snd (hom f) (hom f))
    simp only [Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd, Category.comp_id,
      g, pullback.lift_fst, pullback.lift_snd] at e₁ e₂
    have e := congrArg (fun α ↦ ((schemeYoneda S).map z ≫ α).app (op T)
      (ULift.up (𝟙 T))) (e₁.symm.trans e₂)
    simpa [schemeYoneda_app_up, uliftYonedaEquiv_apply] using e
  · let a : (schemeYoneda S).obj T ⟶ X.presheaf := uliftYonedaEquiv.{u + 1}.symm (X.pullback k ξ₁)
    have e₁ : (uliftYonedaEquiv.{u + 1}.symm (X.presheaf.map k.op ξ₁) :
        (schemeYoneda S).obj T ⟶ X.presheaf) =
        (schemeYoneda S).map k ≫ uliftYonedaEquiv.{u + 1}.symm ξ₁ :=
      uliftYonedaEquiv_symm_map _ _
    have e₂ : (uliftYonedaEquiv.{u + 1}.symm (X.presheaf.map k.op ξ₂) :
        (schemeYoneda S).obj T ⟶ X.presheaf) =
        (schemeYoneda S).map k ≫ uliftYonedaEquiv.{u + 1}.symm ξ₂ :=
      uliftYonedaEquiv_symm_map _ _
    have w' : a ≫ pullback.diagonal (hom f) = (schemeYoneda S).map k ≫ g := by
      apply pullback.hom_ext
      · simp only [a, g, Category.assoc, pullback.diagonal_fst, Category.comp_id]
        erw [pullback.lift_fst]
        exact e₁
      · simp only [a, g, Category.assoc, pullback.diagonal_snd, Category.comp_id]
        erw [pullback.lift_snd]
        exact (congrArg _ hxy).trans e₂
    obtain ⟨z, hz⟩ := (schemeYoneda S).map_surjective (hsq.lift a ((schemeYoneda S).map k) w')
    refine ⟨z, (schemeYoneda S).map_injective ?_⟩
    rw [Functor.map_comp, hz, hsq.lift_snd]

/-- For a separated morphism and two sections over `Spec R` with the same image, there is an
ideal `I` of `R` such that `Spec (R ⧸ I)` cuts out the locus where the sections agree. -/
theorem exists_ideal_representsEqualizer (hf : IsSeparatedMorphism f) {R : Type u}
    [CommRing R] [Algebra A R] (ξ₁ ξ₂ : X.sections (algTest s R))
    (h : mapSections f _ ξ₁ = mapSections f _ ξ₂) :
    ∃ I : Ideal R,
      RepresentsEqualizer (F := X.presheaf) (algTestMap s (Ideal.Quotient.mkₐ A I)) ξ₁ ξ₂ := by
  obtain ⟨Z, ι, hι, hci⟩ := exists_representsEqualizer f hf ξ₁ ξ₂ h
  obtain ⟨I, e, he⟩ := (AlgebraicGeometry.IsClosedImmersion.Spec_iff (R := CommRingCat.of R)
    (f := ι.left)).mp hci
  have hw : e.hom ≫ (algTest s (R ⧸ I)).hom = Z.hom := by
    rw [← Over.w ι, he]
    change e.hom ≫ Spec.map _ ≫ s = (e.hom ≫ Spec.map _) ≫ Spec.map _ ≫ s
    rw [Category.assoc, ← Category.assoc (Spec.map _), ← Spec.map_comp]
    rfl
  let φ : Z ≅ algTest s (R ⧸ I) := Over.isoMk e hw
  have hφ : φ.inv ≫ ι = algTestMap s (Ideal.Quotient.mkₐ A I) := by
    ext1
    simp only [Over.comp_left, φ, Over.isoMk_inv_left, he, Iso.inv_hom_id_assoc,
      algTestMap_left]
    rfl
  refine ⟨I, fun T k => ?_⟩
  rw [← hι k, ← hφ]
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨z ≫ φ.inv, (Category.assoc _ _ _)⟩
  · rintro ⟨z, rfl⟩
    exact ⟨z ≫ φ.hom, by simp⟩

/-- The ring form of an equalizer ideal: two sections agree over `Spec R'` along `ψ` exactly
when `ψ` kills the ideal. -/
theorem pullback_eq_iff_le_ker {R R' : Type u} [CommRing R] [CommRing R'] [Algebra A R]
    [Algebra A R'] {I : Ideal R} {ξ₁ ξ₂ : X.sections (algTest s R)}
    (hI : RepresentsEqualizer (F := X.presheaf) (algTestMap s (Ideal.Quotient.mkₐ A I)) ξ₁ ξ₂)
    (ψ : R →ₐ[A] R') :
    X.pullback (algTestMap s ψ) ξ₁ = X.pullback (algTestMap s ψ) ξ₂ ↔ I ≤ RingHom.ker ψ := by
  rw [← exists_comp_mk_iff s I ψ]
  exact (hI (algTestMap s ψ)).symm

end Separated

/-- Restriction of a represented section along a morphism of schemes. -/
theorem map_comp_symm {F : Presheaf S} {T U : Over S} (k : T ⟶ U) (χ : F.obj (op U)) :
    (schemeYoneda S).map k ≫ (uliftYonedaEquiv.{u + 1}.symm χ : (schemeYoneda S).obj U ⟶ F) =
      uliftYonedaEquiv.{u + 1}.symm (F.map k.op χ) :=
  (uliftYonedaEquiv_symm_map _ _).symm

/-- The quotient map `Spec (R ⧸ I) ⟶ Spec R` is a monomorphism of test schemes. -/
instance mono_algTestMap_mk {R : Type u} [CommRing R] [Algebra A R] (I : Ideal R) :
    Mono (algTestMap s (Ideal.Quotient.mkₐ A I)) := by
  have : AlgebraicGeometry.IsClosedImmersion
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :=
    AlgebraicGeometry.IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have : Mono (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) := inferInstance
  exact (Over.forget S).mono_of_mono_map this

section Chart

variable {X Y : AlgebraicSpace S} (f : X ⟶ Y) (y : Y.sections (Over.mk s))

/-- The base change `X ×_Y Spec A` of `f` along the section `y`. -/
abbrev baseChange : Presheaf S :=
  Limits.pullback (hom f) (uliftYonedaEquiv.{u + 1}.symm y : (schemeYoneda S).obj _ ⟶ _)

/-- The point of the base change given by a section `χ` over `T` and a morphism
`t : T ⟶ Spec A` with `f(χ) = y|_T`. -/
def zOf {T : Over S} (χ : X.sections T) (t : T ⟶ Over.mk s)
    (h : mapSections f T χ = Y.pullback t y) :
    (schemeYoneda S).obj T ⟶ baseChange s f y :=
  pullback.lift (uliftYonedaEquiv.{u + 1}.symm χ) ((schemeYoneda S).map t) (by
    rw [uliftYonedaEquiv_symm_comp, map_comp_symm]
    exact congrArg _ h)

@[reassoc (attr := simp)]
theorem zOf_fst {T : Over S} (χ : X.sections T) (t : T ⟶ Over.mk s)
    (h : mapSections f T χ = Y.pullback t y) :
    zOf s f y χ t h ≫ pullback.fst _ _ = uliftYonedaEquiv.{u + 1}.symm χ :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem zOf_snd {T : Over S} (χ : X.sections T) (t : T ⟶ Over.mk s)
    (h : mapSections f T χ = Y.pullback t y) :
    zOf s f y χ t h ≫ pullback.snd _ _ = (schemeYoneda S).map t :=
  pullback.lift_snd _ _ _

/-- **Étale loci over a chart.** Let `ξ` be a section over `Spec P` whose point of the base
change is étale, and `χ` a section over `Spec R` with `f(χ) = y|_R`. If the ideal `I` of
`R ⊗[A] P` cuts out the locus where the two pullbacks of `χ` and `ξ` agree, then
`Spec ((R ⊗[A] P) ⧸ I) ⟶ Spec R` is étale. -/
theorem etale_of_chart {P : Type u} [CommRing P] [Algebra A P] (ξ : X.sections (algTest s P))
    (hξ : mapSections f _ ξ = Y.pullback (algTestBase s P) y)
    (hb : IsEtale (zOf s f y ξ (algTestBase s P) hξ))
    {R : Type u} [CommRing R] [Algebra A R] (χ : X.sections (algTest s R))
    (hχ : mapSections f _ χ = Y.pullback (algTestBase s R) y) {I : Ideal (R ⊗[A] P)}
    (hI : RepresentsEqualizer (F := X.presheaf) (algTestMap s (Ideal.Quotient.mkₐ A I))
      (X.pullback (algTestMap s (Algebra.TensorProduct.includeLeft : R →ₐ[A] R ⊗[A] P)) χ)
      (X.pullback (algTestMap s (Algebra.TensorProduct.includeRight : P →ₐ[A] R ⊗[A] P)) ξ)) :
    Etale (algTestMap s ((Ideal.Quotient.mkₐ A I).comp
      (Algebra.TensorProduct.includeLeft : R →ₐ[A] R ⊗[A] P))).left := by
  set mk := algTestMap s (Ideal.Quotient.mkₐ A I)
  set iL := algTestMap s (Algebra.TensorProduct.includeLeft : R →ₐ[A] R ⊗[A] P)
  set iR := algTestMap s (Algebra.TensorProduct.includeRight : P →ₐ[A] R ⊗[A] P)
  have hL : algTestMap s ((Ideal.Quotient.mkₐ A I).comp
      (Algebra.TensorProduct.includeLeft : R →ₐ[A] R ⊗[A] P)) = mk ≫ iL :=
    algTestMap_comp _ _ _
  have hR : algTestMap s ((Ideal.Quotient.mkₐ A I).comp
      (Algebra.TensorProduct.includeRight : P →ₐ[A] R ⊗[A] P)) = mk ≫ iR :=
    algTestMap_comp _ _ _
  have heq : X.pullback (mk ≫ iL) χ = X.pullback (mk ≫ iR) ξ := by
    rw [pullback_comp, pullback_comp]
    exact (hI mk).1 ⟨𝟙 _, Category.id_comp _⟩
  have hsq := isPullback_algTest s R P
  rw [hL]
  refine hb.projection (zOf s f y χ (algTestBase s R) hχ)
    ((schemeYoneda S).map (mk ≫ iR)) (mk ≫ iL) ?_
  have hcomm : (schemeYoneda S).map (mk ≫ iR) ≫ zOf s f y ξ (algTestBase s P) hξ =
      (schemeYoneda S).map (mk ≫ iL) ≫ zOf s f y χ (algTestBase s R) hχ := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, zOf_fst, zOf_fst, map_comp_symm, map_comp_symm]
      exact congrArg _ heq.symm
    · rw [Category.assoc, Category.assoc, zOf_snd, zOf_snd, ← Functor.map_comp,
        ← Functor.map_comp]
      simp only [Category.assoc, iL, iR, algTestMap_base]
  refine isPullback_of_elements (fun T e => ?_) (fun T e e' h₁ h₂ => ?_)
    (fun T u v huv => ?_)
  · have := ConcreteCategory.congr_hom (NatTrans.congr_app hcomm T) e
    simpa only [NatTrans.comp_app_apply] using this
  · obtain ⟨T⟩ := T
    obtain ⟨e⟩ := e
    obtain ⟨e'⟩ := e'
    have h₁' : e ≫ mk ≫ iR = e' ≫ mk ≫ iR := congrArg ULift.down h₁
    have h₂' : e ≫ mk ≫ iL = e' ≫ mk ≫ iL := congrArg ULift.down h₂
    have : e ≫ mk = e' ≫ mk := hsq.hom_ext (by simpa using h₂') (by simpa using h₁')
    rw [cancel_mono] at this
    rw [this]
  · obtain ⟨T⟩ := T
    have h₁ := congrArg (fun z => (pullback.fst _ _ : baseChange s f y ⟶ _).app _ z) huv
    have h₂ := congrArg (fun z => (pullback.snd _ _ : baseChange s f y ⟶ _).app _ z) huv
    have e₁ := ConcreteCategory.congr_hom (NatTrans.congr_app (zOf_fst s f y ξ _ hξ) (op T)) u
    have e₂ := ConcreteCategory.congr_hom (NatTrans.congr_app (zOf_fst s f y χ _ hχ) (op T)) v
    have e₃ := ConcreteCategory.congr_hom (NatTrans.congr_app (zOf_snd s f y ξ _ hξ) (op T)) u
    have e₄ := ConcreteCategory.congr_hom (NatTrans.congr_app (zOf_snd s f y χ _ hχ) (op T)) v
    simp only [NatTrans.comp_app_apply] at e₁ e₂ e₃ e₄ h₁ h₂
    rw [e₁, e₂] at h₁
    rw [e₃, e₄] at h₂
    obtain ⟨u⟩ := u
    obtain ⟨v⟩ := v
    have h₁' : X.pullback u ξ = X.pullback v χ := by
      rw [schemeYoneda_app_up, schemeYoneda_app_up] at h₁
      simpa [uliftYonedaEquiv_apply] using h₁
    have h₂' : u ≫ algTestBase s P = v ≫ algTestBase s R := congrArg ULift.down h₂
    let l := hsq.lift v u h₂'.symm
    have hl : X.pullback l (X.pullback iL χ) = X.pullback l (X.pullback iR ξ) := by
      rw [← pullback_comp, ← pullback_comp, hsq.lift_fst, hsq.lift_snd, h₁']
    obtain ⟨z, hz⟩ := (hI l).2 hl
    refine ⟨ULift.up z, ?_, ?_⟩
    · change ULift.up (z ≫ mk ≫ iR) = ULift.up u
      rw [← Category.assoc, hz, hsq.lift_snd]
    · change ULift.up (z ≫ mk ≫ iL) = ULift.up v
      rw [← Category.assoc, hz, hsq.lift_fst]

end Chart

end Langlands.AlgebraicGeometry.AlgebraicSpace.ValuativeExistence
