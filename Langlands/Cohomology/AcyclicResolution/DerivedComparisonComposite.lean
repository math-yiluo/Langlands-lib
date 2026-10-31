import Langlands.Cohomology.AcyclicResolution.DerivedCompositeComparison
import Langlands.Cohomology.DerivedExactComposition
import Langlands.Cohomology.ExtendMap

/-!
# Composites of derived comparisons

For the Library's actual derived comparison `derivedCompComparison G e A hA` attached to
`e : F ⋙ G ≅ H` and an `F`-acyclic object `A`, this file proves:

* `derivedCompComparison_comp_eq`: a two-step composite of derived comparisons, computed with
  arbitrary injective resolutions and augmentation-compatible lifts.
* `derivedCompComparison_comp_factorization`: given two factorizations
  `c : F₁ ⋙ F₂ ≅ F₁' ⋙ F₂'` of one functor, the two-step derived comparisons along each
  factorization agree, up to `derivedComplexCongr` of an isomorphism `κ` between the composite
  derived functors and the image of `c`. The hypotheses are acyclicity of the coefficient object
  for `F₁`, `F₂`, `F₁'`, `F₂'` and `F₁ ⋙ F₂`, and pointwise agreement of the termwise comparisons.
* `derivedCompComparison_postcomp`: derived comparisons commute with an exact functor `P`
  through the exact-composite isomorphisms `derivedCompIso`, when the termwise comparisons do.
* Composition, identity and inverse lemmas for `derivedComplexCongr`, and
  `derivedCompIso_inv_app_comp_hom_app` comparing two exact-composite isomorphisms.
* Supporting lemmas: transport `extendHom` of natural-indexed cochain maps to integer
  extensions, naturality of `mapAugmentation` in the functor, and vanishing of right derived
  functors of `F₁ ⋙ F₂` when `F₂` preserves homology.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace Langlands.Cohomology.AcyclicResolution

section ExtendHom

variable {C : Type*} [Category* C] [Abelian C] {D : Type*} [Category* D] [Abelian D]
  {D' : Type*} [Category* D'] [Abelian D'] {E : Type*} [Category* E] [Abelian E]

/-- Transport a cochain map between the natural-indexed images of two complexes under two
additive functors to the images of their integer extensions. -/
def extendHom (H : C ⥤ E) [H.Additive] (G : D ⥤ E) [G.Additive]
    {K : CochainComplex C ℕ} {L : CochainComplex D ℕ}
    (θ : (H.mapHomologicalComplex (ComplexShape.up ℕ)).obj K ⟶
      (G.mapHomologicalComplex (ComplexShape.up ℕ)).obj L) :
    (H.mapHomologicalComplex (ComplexShape.up ℤ)).obj (K.extend ComplexShape.embeddingUpNat) ⟶
      (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (L.extend ComplexShape.embeddingUpNat) :=
  (DerivedPlus.mapExtendIso H K ComplexShape.embeddingUpNat).inv ≫
    extendMap θ ComplexShape.embeddingUpNat ≫
    (DerivedPlus.mapExtendIso G L ComplexShape.embeddingUpNat).hom

/-- Transport along integer extensions is compatible with composition. -/
@[reassoc]
lemma extendHom_comp (H : C ⥤ E) [H.Additive] (G : D ⥤ E) [G.Additive]
    (P : D' ⥤ E) [P.Additive] {K : CochainComplex C ℕ} {L : CochainComplex D ℕ}
    {M : CochainComplex D' ℕ}
    (θ : (H.mapHomologicalComplex (ComplexShape.up ℕ)).obj K ⟶
      (G.mapHomologicalComplex (ComplexShape.up ℕ)).obj L)
    (θ' : (G.mapHomologicalComplex (ComplexShape.up ℕ)).obj L ⟶
      (P.mapHomologicalComplex (ComplexShape.up ℕ)).obj M) :
    extendHom H G θ ≫ extendHom G P θ' = extendHom H P (θ ≫ θ') := by
  simp only [extendHom, Category.assoc, Iso.hom_inv_id_assoc, extendMap_comp]

/-- The image of an extended cochain map is the transport of the image of the map. -/
lemma map_extendMap_eq (G : D ⥤ E) [G.Additive] {K L : CochainComplex D ℕ} (u : K ⟶ L) :
    (G.mapHomologicalComplex (ComplexShape.up ℤ)).map
        (extendMap u ComplexShape.embeddingUpNat) =
      extendHom G G ((G.mapHomologicalComplex (ComplexShape.up ℕ)).map u) := by
  rw [extendHom, ← DerivedPlus.mapExtendIso_hom_naturality, Iso.inv_hom_id_assoc]

/-- A natural transformation on an extended complex is the transport of the natural
transformation on the original complex. -/
lemma natTrans_app_extend_eq {G G' : C ⥤ E} [G.Additive] [G'.Additive] (α : G ⟶ G')
    (K : CochainComplex C ℕ) :
    (NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app
        (K.extend ComplexShape.embeddingUpNat) =
      extendHom G G' ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℕ)).app K) := by
  have h := extendMapIso_hom_app ComplexShape.embeddingUpNat α K
  simp only [extendMapIso, Iso.symm_hom] at h
  rw [extendHom, ← reassoc_of% h, Iso.inv_hom_id, Category.comp_id]

end ExtendHom

section Augmentation

variable {C : Type*} [Category* C] [Abelian C] {D : Type*} [Category* D] [Abelian D]
  {E : Type*} [Category* E] [Abelian E]

/-- `mapAugmentation` is natural in the functor. -/
lemma mapAugmentation_natTrans {F F' : C ⥤ D} [F.Additive] [F'.Additive] (α : F ⟶ F')
    {A : C} (I : InjectiveResolution A) :
    mapAugmentation F I ≫ (NatTrans.mapHomologicalComplex α _).app I.cocomplex =
      (CochainComplex.single₀ D).map (α.app A) ≫ mapAugmentation F' I := by
  ext
  simp only [HomologicalComplex.comp_f, mapAugmentation_f_zero,
    NatTrans.mapHomologicalComplex_app_f, CochainComplex.single₀_map_f_zero]
  exact α.naturality _

/-- Applying `F₂` to a lift of the augmentation of `F₁ I` over the identity gives the
augmentation of `F₂ J` from the augmentation of `(F₁ ⋙ F₂) I`. -/
lemma mapAugmentation_comp_map {F₁ : C ⥤ D} [F₁.Additive] {F₂ : D ⥤ E} [F₂.Additive]
    {A : C} (I : InjectiveResolution A) (J : InjectiveResolution (F₁.obj A))
    (φ : (F₁.mapHomologicalComplex _).obj I.cocomplex ⟶ J.cocomplex)
    (hφ : mapAugmentation F₁ I ≫ φ = J.ι) :
    mapAugmentation (F₁ ⋙ F₂) I ≫ (F₂.mapHomologicalComplex _).map φ =
      mapAugmentation F₂ J := by
  ext
  have h0 := HomologicalComplex.congr_hom hφ 0
  simp only [HomologicalComplex.comp_f, mapAugmentation_f_zero] at h0
  simp only [HomologicalComplex.comp_f, mapAugmentation_f_zero,
    Functor.mapHomologicalComplex_map_f, Functor.comp_map]
  exact (F₂.map_comp _ _).symm.trans (congrArg F₂.map (h0.trans (Category.id_comp _).symm))

end Augmentation

universe wA wB wB' wC wE vA vB vB' vC vE uA uB uB' uC uE

section Acyclic

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasInjectiveResolutions A]
  {B : Type uB} [Category.{vB} B] [Abelian B] {C : Type uC} [Category.{vC} C] [Abelian C]

/-- Postcomposing with a homology-preserving functor keeps a right derived functor zero. -/
lemma isZero_rightDerived_comp_of_preservesHomology (F₁ : A ⥤ B) [F₁.Additive]
    (F₂ : B ⥤ C) [F₂.Additive] [F₂.PreservesHomology] (N : A) (n : ℕ)
    (h : IsZero ((F₁.rightDerived n).obj N)) :
    IsZero (((F₁ ⋙ F₂).rightDerived n).obj N) := by
  let I := injectiveResolution N
  refine IsZero.of_iso ?_ (I.isoRightDerivedObj (F₁ ⋙ F₂) n)
  apply HomologicalComplex.ExactAt.isZero_homology
  have h' : ((F₁.mapHomologicalComplex _).obj I.cocomplex).ExactAt n := by
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact h.of_iso (I.isoRightDerivedObj F₁ n).symm
  rw [HomologicalComplex.exactAt_iff] at h' ⊢
  exact h'.map F₂

end Acyclic

section CompResolution

variable {A : Type uA} [Category.{vA} A] [Abelian A]
  {B : Type uB} [Category.{vB} B] [Abelian B]
  {E : Type uE} [Category.{vE} E] [Abelian E]
  {F : A ⥤ B} [F.Additive] (G : B ⥤ E) [G.Additive] {H : A ⥤ E} [H.Additive]
  (e : F ⋙ G ≅ H)

/-- The specified integer-complex comparison is the transport of the inverse termwise
composite isomorphism. -/
lemma compResolutionIso_hom_eq (K : CochainComplex A ℕ) :
    (compResolutionIso G e K).hom =
      extendHom H G ((Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℕ)).inv.app K) :=
  rfl

end CompResolution

section TwoStep

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
  [EnoughInjectives A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B] [EnoughInjectives B]
  {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{wC} C] [EnoughInjectives C]
  {E : Type uE} [Category.{vE} E] [Abelian E] [HasDerivedCategory.{wE} E]
  {F₁ : A ⥤ B} [F₁.Additive] [PreservesFiniteLimits F₁]
  {F₂ : B ⥤ C} [F₂.Additive] [PreservesFiniteLimits F₂]
  {H₁ : B ⥤ E} [H₁.Additive] (G : C ⥤ E) [G.Additive] {K : A ⥤ E} [K.Additive]
  (e : F₂ ⋙ G ≅ H₁) (e₁ : F₁ ⋙ H₁ ≅ K)

/-- A two-step composite comparison, computed with arbitrary injective resolutions and
augmentation-compatible lifts: one source resolution model, two termwise comparisons, and a
single derived comparison of the composite lift. -/
@[reassoc]
theorem derivedCompComparison_comp_eq (N : A)
    (hN₁ : ∀ q : ℕ, IsZero ((F₁.rightDerived (q + 1)).obj N))
    (hN₂ : ∀ q : ℕ, IsZero ((F₂.rightDerived (q + 1)).obj (F₁.obj N)))
    (I : InjectiveResolution N) (J : InjectiveResolution (F₁.obj N))
    (L : InjectiveResolution (F₂.obj (F₁.obj N)))
    (φ : (F₁.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex ⟶ J.cocomplex)
    (ψ : (F₂.mapHomologicalComplex (ComplexShape.up ℕ)).obj J.cocomplex ⟶ L.cocomplex)
    (hφ : mapAugmentation F₁ I ≫ φ = J.ι) (hψ : mapAugmentation F₂ J ≫ ψ = L.ι) :
    derivedCompComparison H₁ e₁ N hN₁ ≫ derivedCompComparison G e (F₁.obj N) hN₂ =
      (derivedResolutionIso K I).hom ≫ (derivedCompResolutionIso H₁ e₁ I.cocomplex).hom ≫
        (derivedCompResolutionIso G e
          ((F₁.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)).hom ≫
        derivedComparison G L ((F₂.mapHomologicalComplex (ComplexShape.up ℕ)).map φ ≫ ψ) := by
  have := quasiIso_mapAugmentation F₁ I hN₁
  have := quasiIso_mapAugmentation F₂ J hN₂
  rw [derivedCompComparison_eq H₁ e₁ I hN₁, derivedCompComparison_eq G e J hN₂]
  simp only [derivedCompComparisonWithResolution]
  rw [derivedResolutionComparison_eq H₁ (mapAugmentation F₁ I) J φ hφ,
    derivedResolutionComparison_eq G (mapAugmentation F₂ J) L ψ hψ]
  simp only [derivedComparison, Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc]
  rw [derivedCompResolutionIso_hom_naturality_assoc G e φ]

variable {B' : Type uB'} [Category.{vB'} B'] [Abelian B'] [HasDerivedCategory.{wB'} B']
  [EnoughInjectives B']
  {F₁' : A ⥤ B'} [F₁'.Additive] [PreservesFiniteLimits F₁']
  {F₂' : B' ⥤ C} [F₂'.Additive] [PreservesFiniteLimits F₂']
  {H₁' : B' ⥤ E} [H₁'.Additive] {K' : A ⥤ E} [K'.Additive]
  (e' : F₂' ⋙ G ≅ H₁') (e₁' : F₁' ⋙ H₁' ≅ K') (κ : K ≅ K') (c : F₁ ⋙ F₂ ≅ F₁' ⋙ F₂')

/-- Two factorizations of one composite give the same two-step derived comparison, up to the
derived isomorphism induced by `κ` and the image of the factorization isomorphism `c`. The
termwise comparisons must agree (`hκ`), and the composite `F₁ ⋙ F₂` must be acyclic on `N`. -/
theorem derivedCompComparison_comp_factorization (N : A)
    (hN₁ : ∀ q : ℕ, IsZero ((F₁.rightDerived (q + 1)).obj N))
    (hN₂ : ∀ q : ℕ, IsZero ((F₂.rightDerived (q + 1)).obj (F₁.obj N)))
    (hN₁' : ∀ q : ℕ, IsZero ((F₁'.rightDerived (q + 1)).obj N))
    (hN₂' : ∀ q : ℕ, IsZero ((F₂'.rightDerived (q + 1)).obj (F₁'.obj N)))
    (hN : ∀ q : ℕ, IsZero (((F₁ ⋙ F₂).rightDerived (q + 1)).obj N))
    (hκ : ∀ Q : A, e₁.inv.app Q ≫ e.inv.app (F₁.obj Q) ≫ G.map (c.hom.app Q) =
      κ.hom.app Q ≫ e₁'.inv.app Q ≫ e'.inv.app (F₁'.obj Q)) :
    derivedCompComparison H₁ e₁ N hN₁ ≫ derivedCompComparison G e (F₁.obj N) hN₂ ≫
        (DerivedPlus.derivedComplex G ⋙ DerivedCategory.Plus.ι).map (c.hom.app N) =
      (DerivedPlus.derivedComplexCongr κ).hom.app N ≫ derivedCompComparison H₁' e₁' N hN₁' ≫
        derivedCompComparison G e' (F₁'.obj N) hN₂' := by
  let I := injectiveResolution N
  let J := injectiveResolution (F₁.obj N)
  let L := injectiveResolution (F₂.obj (F₁.obj N))
  let J' := injectiveResolution (F₁'.obj N)
  let L' := injectiveResolution (F₂'.obj (F₁'.obj N))
  have := quasiIso_mapAugmentation F₁ I hN₁
  have := quasiIso_mapAugmentation F₂ J hN₂
  have := quasiIso_mapAugmentation F₁' I hN₁'
  have := quasiIso_mapAugmentation F₂' J' hN₂'
  let ε : (CochainComplex.single₀ C).obj (F₂.obj (F₁.obj N)) ⟶
      (F₂.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        ((F₁.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex) :=
    mapAugmentation (F₁ ⋙ F₂) I
  have : QuasiIso ε := quasiIso_mapAugmentation (F₁ ⋙ F₂) I hN
  let η : (CochainComplex.single₀ C).obj (F₂'.obj (F₁'.obj N)) ⟶
      (F₂'.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        ((F₁'.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex) :=
    mapAugmentation (F₁' ⋙ F₂') I
  let γ : (F₂.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        ((F₁.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex) ⟶
      (F₂'.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        ((F₁'.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex) :=
    (NatTrans.mapHomologicalComplex c.hom _).app I.cocomplex
  let φ := lift (mapAugmentation F₁ I) (𝟙 _) J.ι
  let ψ := lift (mapAugmentation F₂ J) (𝟙 _) L.ι
  let φ' := lift (mapAugmentation F₁' I) (𝟙 _) J'.ι
  let ψ' := lift (mapAugmentation F₂' J') (𝟙 _) L'.ι
  have hφ : ε ≫ (F₂.mapHomologicalComplex _).map φ ≫ ψ = L.ι := by
    rw [← Category.assoc, mapAugmentation_comp_map I J φ (comp_lift_id _ _), comp_lift_id]
  have hφ' : η ≫ (F₂'.mapHomologicalComplex _).map φ' ≫ ψ' = L'.ι := by
    rw [← Category.assoc, mapAugmentation_comp_map I J' φ' (comp_lift_id _ _), comp_lift_id]
  have hγ : ε ≫ γ = (CochainComplex.single₀ C).map (c.hom.app N) ≫ η :=
    mapAugmentation_natTrans c.hom I
  have hnat := derivedComparison_naturality G ε η (c.hom.app N) γ hγ _ _ hφ hφ'
  have chain : (compResolutionIso H₁ e₁ I.cocomplex).hom ≫
      (compResolutionIso G e ((F₁.mapHomologicalComplex _).obj I.cocomplex)).hom ≫
      (G.mapHomologicalComplex (ComplexShape.up ℤ)).map
        (extendMap γ ComplexShape.embeddingUpNat) =
    (NatTrans.mapHomologicalComplex κ.hom (ComplexShape.up ℤ)).app
        (I.cocomplex.extend ComplexShape.embeddingUpNat) ≫
      (compResolutionIso H₁' e₁' I.cocomplex).hom ≫
      (compResolutionIso G e' ((F₁'.mapHomologicalComplex _).obj I.cocomplex)).hom := by
    simp only [compResolutionIso_hom_eq, map_extendMap_eq, natTrans_app_extend_eq,
      extendHom_comp]
    congr 1
    ext n
    simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplexCompIso_inv_app_f,
      NatTrans.mapHomologicalComplex_app_f, Functor.mapHomologicalComplex_map_f, γ]
    exact hκ _
  have key : (derivedCompResolutionIso H₁ e₁ I.cocomplex).hom ≫
      (derivedCompResolutionIso G e ((F₁.mapHomologicalComplex _).obj I.cocomplex)).hom ≫
      (derivedResolutionFunctor G).map γ =
    (DerivedPlus.resolutionCongrNatIso κ).hom.app I.cocomplex ≫
      (derivedCompResolutionIso H₁' e₁' I.cocomplex).hom ≫
      (derivedCompResolutionIso G e' ((F₁'.mapHomologicalComplex _).obj I.cocomplex)).hom := by
    have h := congrArg DerivedCategory.Q.map chain
    simp only [Functor.map_comp] at h
    exact h
  rw [derivedCompComparison_comp_eq_assoc G e e₁ N hN₁ hN₂ I J L φ ψ (comp_lift_id _ _)
      (comp_lift_id _ _),
    derivedCompComparison_comp_eq G e' e₁' N hN₁' hN₂' I J' L' φ' ψ' (comp_lift_id _ _)
      (comp_lift_id _ _),
    DerivedPlus.derivedComplexCongr_hom_resolution_assoc κ I, ← hnat, reassoc_of% key]

end TwoStep

section CongrTrans

variable {C : Type uA} [Category.{vA} C] [Abelian C] [HasDerivedCategory.{wA} C]
  [EnoughInjectives C]
  {D : Type uE} [Category.{vE} D] [Abelian D] [HasDerivedCategory.{wE} D]
  {G H P : C ⥤ D} [G.Additive] [H.Additive] [P.Additive]

omit [HasDerivedCategory C] [EnoughInjectives C] in
/-- The termwise isomorphism of a composite of natural isomorphisms is the composite. -/
lemma resolutionCongrNatIso_trans_hom_app (e : G ≅ H) (e' : H ≅ P) (K : CochainComplex C ℕ) :
    (DerivedPlus.resolutionCongrNatIso (e ≪≫ e')).hom.app K =
      (DerivedPlus.resolutionCongrNatIso e).hom.app K ≫
        (DerivedPlus.resolutionCongrNatIso e').hom.app K := by
  simp only [DerivedPlus.resolutionCongrNatIso, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app]
  refine (congrArg DerivedCategory.Q.map ?_).trans (Functor.map_comp _ _ _)
  ext
  simp

omit [HasDerivedCategory C] [EnoughInjectives C] in
/-- The termwise isomorphism of the identity is the identity. -/
lemma resolutionCongrNatIso_refl_hom_app (K : CochainComplex C ℕ) :
    (DerivedPlus.resolutionCongrNatIso (Iso.refl G)).hom.app K = 𝟙 _ := by
  simp only [DerivedPlus.resolutionCongrNatIso, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app]
  have h : (NatIso.mapHomologicalComplex (Iso.refl G) (ComplexShape.up ℤ)).hom.app
      ((ComplexShape.embeddingUpNat.extendFunctor C).obj K) = 𝟙 _ := by
    ext
    simp
  rw [h]
  exact CategoryTheory.Functor.map_id _ _

/-- `derivedComplexCongr` sends composites of natural isomorphisms to composites. -/
theorem derivedComplexCongr_trans_hom_app (e : G ≅ H) (e' : H ≅ P) (X : C) :
    (DerivedPlus.derivedComplexCongr (e ≪≫ e')).hom.app X =
      (DerivedPlus.derivedComplexCongr e).hom.app X ≫
        (DerivedPlus.derivedComplexCongr e').hom.app X := by
  rw [← cancel_mono (derivedResolutionIso P (injectiveResolution X)).hom, Category.assoc,
    DerivedPlus.derivedComplexCongr_hom_resolution, DerivedPlus.derivedComplexCongr_hom_resolution,
    DerivedPlus.derivedComplexCongr_hom_resolution_assoc, resolutionCongrNatIso_trans_hom_app]

/-- `derivedComplexCongr` sends the identity to the identity. -/
theorem derivedComplexCongr_refl_hom_app (X : C) :
    (DerivedPlus.derivedComplexCongr (Iso.refl G)).hom.app X = 𝟙 _ := by
  rw [← cancel_mono (derivedResolutionIso G (injectiveResolution X)).hom,
    DerivedPlus.derivedComplexCongr_hom_resolution, resolutionCongrNatIso_refl_hom_app,
    Category.comp_id, Category.id_comp]

/-- `derivedComplexCongr` sends inverses to inverses. -/
theorem derivedComplexCongr_symm_hom_app (e : G ≅ H) (X : C) :
    (DerivedPlus.derivedComplexCongr e.symm).hom.app X =
      (DerivedPlus.derivedComplexCongr e).inv.app X := by
  rw [← cancel_epi ((DerivedPlus.derivedComplexCongr e).hom.app X),
    ← derivedComplexCongr_trans_hom_app, Iso.self_symm_id, derivedComplexCongr_refl_hom_app,
    Iso.hom_inv_id_app]

variable {E : Type uC} [Category.{vC} E] [Abelian E] [HasDerivedCategory.{wC} E]
  (Q : D ⥤ E) [Q.Additive] [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
  {H₁ H₂ : C ⥤ E} [H₁.Additive] [H₂.Additive]

/-- Two exact-composite isomorphisms for the same composite differ by the derived isomorphism
of the comparison between their targets. -/
theorem derivedCompIso_inv_app_comp_hom_app (e₁ : G ⋙ Q ≅ H₁) (e₂ : G ⋙ Q ≅ H₂) (X : C) :
    (DerivedPlus.derivedCompIso G Q e₁).inv.app X ≫ (DerivedPlus.derivedCompIso G Q e₂).hom.app X =
      (DerivedPlus.derivedComplexCongr (e₁.symm ≪≫ e₂)).hom.app X := by
  simp only [DerivedPlus.derivedCompIso, Iso.trans_inv, Iso.trans_hom, NatTrans.comp_app,
    Category.assoc, Iso.inv_hom_id_app_assoc, derivedComplexCongr_trans_hom_app,
    derivedComplexCongr_symm_hom_app]

end CongrTrans

section ExactPostcomp

variable {C : Type uA} [Category.{vA} C] [Abelian C] [HasDerivedCategory.{wA} C]
  [EnoughInjectives C]
  {D : Type uB} [Category.{vB} D] [Abelian D] [HasDerivedCategory.{wB} D] [EnoughInjectives D]
  {E : Type uC} [Category.{vC} E] [Abelian E] [HasDerivedCategory.{wC} E]
  {E' : Type uE} [Category.{vE} E'] [Abelian E'] [HasDerivedCategory.{wE} E']
  {F : C ⥤ D} [F.Additive] [PreservesFiniteLimits F]
  (G : D ⥤ E) [G.Additive] {H : C ⥤ E} [H.Additive] (e : F ⋙ G ≅ H)
  (P : E ⥤ E') [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
  {G' : D ⥤ E'} [G'.Additive] {H' : C ⥤ E'} [H'.Additive]
  (eG : G ⋙ P ≅ G') (eH : H ⋙ P ≅ H') (e' : F ⋙ G' ≅ H')

omit [HasDerivedCategory C] [EnoughInjectives C] [HasDerivedCategory D] [EnoughInjectives D]
  [HasDerivedCategory E] [HasDerivedCategory E'] [PreservesFiniteLimits F]
  [PreservesFiniteLimits P] [PreservesFiniteColimits P] in
set_option backward.isDefEq.respectTransparency false in
/-- The specified integer-complex comparisons for `e` and `e'` are compatible with `P`, when
the termwise comparisons are. -/
lemma compResolutionIso_hom_postcomp
    (hc : ∀ X : C, eH.hom.app X ≫ e'.inv.app X = P.map (e.inv.app X) ≫ eG.hom.app (F.obj X))
    (K : CochainComplex C ℕ) :
    (Functor.mapHomologicalComplexCompIso eH (ComplexShape.up ℤ)).hom.app
        (K.extend ComplexShape.embeddingUpNat) ≫ (compResolutionIso G' e' K).hom =
      (P.mapHomologicalComplex (ComplexShape.up ℤ)).map (compResolutionIso G e K).hom ≫
        (Functor.mapHomologicalComplexCompIso eG (ComplexShape.up ℤ)).hom.app
          (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).extend
            ComplexShape.embeddingUpNat) := by
  have key : ∀ o : Option ℕ,
      eH.hom.app (extend.X K o) ≫ (DerivedPlus.extendXMapIso H' K o).inv ≫
          extend.mapX ((Functor.mapHomologicalComplexCompIso e' (ComplexShape.up ℕ)).inv.app K)
            o ≫
          (DerivedPlus.extendXMapIso G' ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K)
            o).hom =
        P.map ((DerivedPlus.extendXMapIso H K o).inv ≫
          extend.mapX ((Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℕ)).inv.app K)
            o ≫
          (DerivedPlus.extendXMapIso G ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K)
            o).hom) ≫
          eG.hom.app (extend.X ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K) o)
    | none => (P.map_isZero (H.map_isZero (extend.isZero_X K rfl))).eq_of_src _ _
    | some k => by
        simp only [DerivedPlus.extendXMapIso, Iso.refl_inv, Iso.refl_hom, extend.mapX,
          extend.X, Functor.mapHomologicalComplex_obj_X,
          Functor.mapHomologicalComplexCompIso_inv_app_f, Category.id_comp]
        erw [Category.comp_id, Category.comp_id]
        exact hc (K.X k)
  ext n
  exact key (ComplexShape.embeddingUpNat.r n)

set_option backward.isDefEq.respectTransparency false in
/-- The composite comparison commutes with exact postcomposition: under the exact-composite
isomorphisms for `eH` and `eG`, the comparison for `e'` is `P` applied to the comparison for
`e`, when the termwise comparisons are compatible. -/
theorem derivedCompComparison_postcomp (A : C)
    (hA : ∀ q : ℕ, IsZero ((F.rightDerived (q + 1)).obj A))
    (hc : ∀ X : C, eH.hom.app X ≫ e'.inv.app X = P.map (e.inv.app X) ≫ eG.hom.app (F.obj X)) :
    (DerivedPlus.derivedCompIso H P eH).hom.app A ≫ derivedCompComparison G' e' A hA =
      P.mapDerivedCategory.map (derivedCompComparison G e A hA) ≫
        (DerivedPlus.derivedCompIso G P eG).hom.app (F.obj A) := by
  let I := injectiveResolution A
  let J := injectiveResolution (F.obj A)
  have := quasiIso_mapAugmentation F I hA
  let ψ := lift (mapAugmentation F I) (𝟙 _) J.ι
  have hR : (DerivedPlus.derivedCompIso G P eG).hom.app (F.obj A) =
      P.mapDerivedCategory.map (derivedResolutionIso G J).hom ≫
        (DerivedPlus.resolutionPostcompNatIso G P).hom.app J.cocomplex ≫
        (DerivedPlus.resolutionCongrNatIso eG).hom.app J.cocomplex ≫
        (derivedResolutionIso G' J).inv := by
    rw [← cancel_mono (derivedResolutionIso G' J).hom, DerivedPlus.derivedCompIso_hom_resolution]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hL := DerivedPlus.derivedCompIso_hom_resolution H P eH I
  have hnat := ((DerivedPlus.resolutionPostcompNatIso G P).hom ≫
    (DerivedPlus.resolutionCongrNatIso eG).hom).naturality ψ
  simp only [Functor.comp_map, NatTrans.comp_app] at hnat
  have hkey : (DerivedPlus.resolutionPostcompNatIso H P).hom.app I.cocomplex ≫
      (DerivedPlus.resolutionCongrNatIso eH).hom.app I.cocomplex ≫
      (derivedCompResolutionIso G' e' I.cocomplex).hom =
    P.mapDerivedCategory.map (derivedCompResolutionIso G e I.cocomplex).hom ≫
      (DerivedPlus.resolutionPostcompNatIso G P).hom.app
        ((F.mapHomologicalComplex _).obj I.cocomplex) ≫
      (DerivedPlus.resolutionCongrNatIso eG).hom.app
        ((F.mapHomologicalComplex _).obj I.cocomplex) := by
    rw [reassoc_of% (DerivedPlus.resolutionPostcompNatIso_hom_app_comp_resolutionCongrNatIso_hom_app
        H P eH I.cocomplex),
      DerivedPlus.resolutionPostcompNatIso_hom_app_comp_resolutionCongrNatIso_hom_app]
    simp only [derivedCompResolutionIso, Functor.mapIso_hom]
    have h₁ := Functor.mapDerivedCategoryFactors_hom_naturality_assoc P
      (compResolutionIso G e I.cocomplex).hom
      (DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso eG (ComplexShape.up ℤ)).hom.app
        (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).extend
          ComplexShape.embeddingUpNat)))
    have h₂ := congrArg DerivedCategory.Q.map
      (compResolutionIso_hom_postcomp G e P eG eH e' hc I.cocomplex)
    simp only [Functor.map_comp] at h₂
    exact (congrArg (P.mapDerivedCategoryFactors.hom.app _ ≫ ·) h₂).trans h₁.symm
  simp only [derivedCompComparison, derivedCompComparisonWithResolution,
    derivedResolutionComparison, derivedComparison, Functor.map_comp, Category.assoc]
  rw [hR, ← P.mapDerivedCategory.map_comp_assoc (derivedResolutionIso G J).inv, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp, reassoc_of% hnat, ← reassoc_of% hkey,
    ← reassoc_of% hL]

end ExactPostcomp

end Langlands.Cohomology.AcyclicResolution
