/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange
public import WeilConjectures.Algebra.Homology.DerivedCategory.ReductionDatum
public import WeilConjectures.CategoryTheory.Sites.ReductionFlat
public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver

/-!
# Reduction of sheaves of modules along a surjective ring morphism

Let `f : A →+* A'` be a surjective morphism of commutative rings whose kernel is the principal
ideal `(a)`, and `(C, J)` an essentially small site. Restriction of scalars along `f` is fully
faithful on sheaves of modules (`CategoryTheory.Sheaf.restrictScalars_full`), and the reduction
`F ↦ F / a F`, the sheafification of `U ↦ F(U) / a F(U)` with scalars transported along
`A ⧸ (a) ≃+* A'`, is a reduction datum for `f` and the multiplication by `a`
(`CategoryTheory.Sheaf.reductionDatum`): with scalars restricted back to `A` it is the tensor
product `F ⊗ A ⧸ (a)` with the constant sheaf, and the reduction map is
`F ≅ F ⊗ A ⟶ F ⊗ A ⧸ (a)`, an epimorphism with kernel the image of `a` by right exactness of
`F ⊗ -`.

## Main results

- `CategoryTheory.Sheaf.restrictScalars_full`: restriction of scalars along a surjective ring
  morphism is full.
- `CategoryTheory.Sheaf.smulNatTrans`: the multiplication by `a` on sheaves of `A`-modules.
- `CategoryTheory.Sheaf.reductionDatum`: the reduction modulo a principal kernel is a reduction
  datum.
- `CategoryTheory.Sheaf.exact_smul_of_flat`: a flat sheaf preserves the exactness of
  `A --x--> A --y--> A`.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits MonoidalCategory

namespace ModuleCat

/-- Restriction of scalars along a surjective ring morphism `f : R →+* S` is full: an
`R`-linear map between `S`-modules is `S`-linear, as every scalar of `S` is the image of a
scalar of `R`. -/
lemma restrictScalars_full_of_surjective {R S : Type*} [Ring R] [Ring S] (f : R →+* S)
    (hf : Function.Surjective f) : (restrictScalars.{w} f).Full where
  map_surjective {M N} g := ⟨ofHom
    { toFun := g
      map_add' := g.hom.map_add
      map_smul' := fun r m ↦ by
        obtain ⟨a, rfl⟩ := hf r
        exact g.hom.map_smul a m }, rfl⟩

end ModuleCat

namespace CochainComplex

variable {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜] [IsGrothendieckAbelian.{w} 𝒜]
  [MonoidalCategory 𝒜] [MonoidalPreadditive 𝒜] [MonoidalClosed 𝒜] [BraidedCategory 𝒜]
  [Abelian.HasFunctorialFlatResolution 𝒜]

/-- Tensoring termwise with an object `Q` sends a quasi-isomorphism between K-flat complexes to
a quasi-isomorphism: it is the tensor product with the complex `Q[0]`. -/
lemma quasiIso_map_tensorRight_of_kFlat (Q : 𝒜) {P₁ P₂ : CochainComplex 𝒜 ℤ} (φ : P₁ ⟶ P₂)
    [QuasiIso φ] (h₁ : (HomologicalComplex.quasiIso 𝒜 (.up ℤ)).kFlat P₁)
    (h₂ : (HomologicalComplex.quasiIso 𝒜 (.up ℤ)).kFlat P₂) :
    QuasiIso (((tensorRight Q).mapHomologicalComplex (.up ℤ)).map φ) := by
  have (X : 𝒜) : PreservesColimitsOfShape ℤ ((curriedTensor 𝒜).flip.obj X) :=
    preservesColimitsOfShape_of_natIso (F := tensorLeft X)
      (NatIso.ofComponents (fun Y ↦ β_ X Y) (by intros; simp [curriedTensor]))
  have h := MorphismProperty.whiskerRight_of_kFlat _ φ
    ((HomologicalComplex.mem_quasiIso_iff _).2 inferInstance) h₁ h₂
    ((HomologicalComplex.single 𝒜 (.up ℤ) 0).obj Q)
  exact ((HomologicalComplex.quasiIso 𝒜 (.up ℤ)).arrow_mk_iso_iff
    (Arrow.isoOfNatIso (map₂HomologicalComplexFlipObjSingleIso (curriedTensor 𝒜) Q)
      (Arrow.mk φ))).1 h

/-- Let `Φ : 𝒜 ⥤ 𝒜'` be an additive functor and `res : 𝒜' ⥤ 𝒜` an exact functor reflecting
isomorphisms such that `res ∘ Φ` is tensoring with an object `Q`. Then `Φ` sends
quasi-isomorphisms between K-flat complexes to quasi-isomorphisms. -/
lemma quasiIso_map_of_iso_tensorRight {𝒜' : Type*} [Category 𝒜'] [Abelian 𝒜'] (Φ : 𝒜 ⥤ 𝒜')
    [Φ.Additive] (res : 𝒜' ⥤ 𝒜) [res.Additive] [PreservesFiniteLimits res]
    [PreservesFiniteColimits res] [res.ReflectsIsomorphisms] {Q : 𝒜}
    (T : Φ ⋙ res ≅ tensorRight Q) {P₁ P₂ : CochainComplex 𝒜 ℤ} (φ : P₁ ⟶ P₂) [QuasiIso φ]
    (h₁ : (HomologicalComplex.quasiIso 𝒜 (.up ℤ)).kFlat P₁)
    (h₂ : (HomologicalComplex.quasiIso 𝒜 (.up ℤ)).kFlat P₂) :
    QuasiIso ((Φ.mapHomologicalComplex (.up ℤ)).map φ) := by
  rw [← HomologicalComplex.quasiIso_map_iff_of_preservesHomology _ res]
  have := quasiIso_map_tensorRight_of_kFlat Q φ h₁ h₂
  exact ((HomologicalComplex.quasiIso 𝒜 (.up ℤ)).arrow_mk_iso_iff
    (Arrow.isoOfNatIso (Functor.mapHomologicalComplexCompIso T (.up ℤ))
      (Arrow.mk φ))).2 this

end CochainComplex

namespace CategoryTheory.MonoidalCategory

variable {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜] [MonoidalCategory 𝒜] [MonoidalPreadditive 𝒜]
  {R : Type*} [Semiring R] [Linear R 𝒜] [MonoidalLinear R 𝒜]

/-- Let `𝟙_ --r--> 𝟙_ --g--> X` be a short complex whose image under `F ⊗ -` is exact. Then
`F --r--> F --g'--> Y` is exact, for any `g'` identified with `F ◁ g` through the right unitor
and an isomorphism `F ⊗ X ≅ Y`. -/
lemma exact_smul_of_exact_map_tensorLeft {r : R} {X Y F : 𝒜} {g : 𝟙_ 𝒜 ⟶ X}
    (hg : (r • 𝟙 (𝟙_ 𝒜)) ≫ g = 0)
    (hS : ((ShortComplex.mk (r • 𝟙 _) g hg).map (tensorLeft F)).Exact)
    {g' : F ⟶ Y} (e : F ⊗ X ≅ Y) (he : F ◁ g ≫ e.hom = (ρ_ F).hom ≫ g')
    (hzero : (r • 𝟙 F) ≫ g' = 0) : (ShortComplex.mk (r • 𝟙 F) g' hzero).Exact := by
  have hS' : (ShortComplex.mk (F ◁ (r • 𝟙 (𝟙_ 𝒜))) (F ◁ g)
      (by rw [← MonoidalCategory.whiskerLeft_comp, hg,
        MonoidalPreadditive.whiskerLeft_zero])).Exact :=
    hS
  exact (ShortComplex.exact_iff_of_iso
    (ShortComplex.isoMk (ρ_ F) (ρ_ F) e (by simp [Linear.smul_comp]) he.symm)).1 hS'

end CategoryTheory.MonoidalCategory

namespace CategoryTheory.Sheaf

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C) {A A' : Type (u + 1)} [CommRing A] [CommRing A']

omit [EssentiallySmall.{u + 1} C] in
/-- Restriction of scalars of sheaves of modules along a surjective ring morphism is full. -/
lemma restrictScalars_full (f : A →+* A') (hf : Function.Surjective f) :
    (restrictScalars J f).Full :=
  have := ModuleCat.restrictScalars_full_of_surjective.{u + 1} f hf
  inferInstance

/-- The multiplication by a scalar `a` on sheaves of `A`-modules, as an endomorphism of the
identity functor. -/
@[simps]
def smulNatTrans (a : A) : 𝟭 (Sheaf J (ModuleCat.{u + 1} A)) ⟶ 𝟭 _ where
  app F := a • 𝟙 F

/-- The image under the constant sheaf functor of a short complex `A --x--> A --g--> X` of
`A`-modules, with first map the multiplication by `x` on the monoidal unit. -/
lemma constantSheaf_map_smul_comp {x : A} {X : ModuleCat.{u + 1} A}
    (g : 𝟙_ (ModuleCat.{u + 1} A) ⟶ X) (hg : (x • 𝟙 _) ≫ g = 0) :
    (x • 𝟙 (𝟙_ (Sheaf J (ModuleCat.{u + 1} A)))) ≫ (constantSheaf J _).map g = 0 := by
  have := (constantSheaf J (ModuleCat.{u + 1} A)).congr_map hg
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_smul,
    CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero] at this
  exact this

/-- The constant sheaf functor preserves the exactness of a short complex `A --x--> A --g--> X`
of `A`-modules, with first map the multiplication by `x` on the monoidal unit. -/
lemma exact_constantSheaf_map_smul {x : A} {X : ModuleCat.{u + 1} A}
    {g : 𝟙_ (ModuleCat.{u + 1} A) ⟶ X} (hg : (x • 𝟙 _) ≫ g = 0)
    (hS : (ShortComplex.mk (x • 𝟙 _) g hg).Exact) :
    (ShortComplex.mk _ ((constantSheaf J _).map g) (constantSheaf_map_smul_comp J g hg)).Exact := by
  refine (ShortComplex.exact_iff_of_iso ?_).1 (hS.map (constantSheaf J (ModuleCat.{u + 1} A)))
  exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp)

section Reduction

variable (f : A →+* A') (hf : Function.Surjective f)

/-- The reduction functor along a surjective ring morphism `f : A →+* A'`: the sheafification
of `U ↦ F(U) / (ker f) F(U)`, with scalars transported along `A ⧸ ker f ≃+* A'`. -/
noncomputable def reductionFunctor :
    Sheaf J (ModuleCat.{u + 1} A) ⥤ Sheaf J (ModuleCat.{u + 1} A') :=
  quotSMulTop J (RingHom.ker f) ⋙
    restrictScalars J (RingHom.quotientKerEquivOfSurjective hf).symm.toRingHom

/-- The reduction functor is additive. -/
instance : (reductionFunctor J f hf).Additive := by
  dsimp [reductionFunctor]
  infer_instance

/-- With scalars restricted back to `A`, the reduction of `F` along `f` is `F ⊗ A ⧸ ker f`. -/
noncomputable def reductionFunctorCompRestrictScalarsIso :
    reductionFunctor J f hf ⋙ restrictScalars J f ≅
      tensorRight ((constantSheaf J (ModuleCat.{u + 1} A)).obj
        (ModuleCat.of A (A ⧸ RingHom.ker f))) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (restrictScalarsCompIso J f _ _ (by ext; simp)) ≪≫
    quotSMulTopCompRestrictScalarsIso (RingHom.ker f)

/-- The projection `A ⟶ A ⧸ ker f` of constant sheaves, from the monoidal unit. -/
noncomputable def unitToConstantQuotient :
    𝟙_ (Sheaf J (ModuleCat.{u + 1} A)) ⟶
      (constantSheaf J (ModuleCat.{u + 1} A)).obj (ModuleCat.of A (A ⧸ RingHom.ker f)) :=
  (constantSheaf J (ModuleCat.{u + 1} A)).map (ModuleCat.ofHom (RingHom.ker f).mkQ)

/-- The reduction map `F ≅ F ⊗ A ⟶ F ⊗ A ⧸ ker f`, with target the reduction of `F` along `f`
with scalars restricted back to `A`. -/
@[simps]
noncomputable def reductionNatTrans :
    𝟭 (Sheaf J (ModuleCat.{u + 1} A)) ⟶ reductionFunctor J f hf ⋙ restrictScalars J f where
  app F := (ρ_ F).inv ≫ F ◁ unitToConstantQuotient J f ≫
    (reductionFunctorCompRestrictScalarsIso J f hf).inv.app F
  naturality F G φ := by
    have := (reductionFunctorCompRestrictScalarsIso J f hf).inv.naturality φ
    dsimp at this ⊢
    simp only [Category.assoc, ← this, rightUnitor_inv_naturality_assoc,
      whisker_exchange_assoc]

variable {f} {a : A}

/-- The multiplication by a generator `a` of `ker f`, followed by the projection
`A ⟶ A ⧸ ker f`, vanishes. -/
lemma smul_comp_mkQ (ha : RingHom.ker f = Ideal.span {a}) :
    (a • 𝟙 (ModuleCat.of A A)) ≫ ModuleCat.ofHom (RingHom.ker f).mkQ = 0 := by
  refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
  simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply, ModuleCat.hom_smul,
    LinearMap.smul_apply, ModuleCat.hom_id, LinearMap.id_apply, ModuleCat.hom_zero,
    LinearMap.zero_apply, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero, ha, smul_eq_mul]
  exact Ideal.mul_mem_right x _ (Ideal.mem_span_singleton_self a)

/-- The short complex of `A`-modules `A --a--> A ⟶ A ⧸ ker f` is exact when `ker f = (a)`. -/
lemma exact_smul_mkQ (ha : RingHom.ker f = Ideal.span {a}) :
    (ShortComplex.mk (a • 𝟙 _) (ModuleCat.ofHom (RingHom.ker f).mkQ)
      (smul_comp_mkQ ha)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro x hx
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 (ha ▸ (Submodule.Quotient.mk_eq_zero _).1 hx)
  exact ⟨b, by simp [mul_comm]⟩

omit [EssentiallySmall.{u + 1} C] in
/-- The multiplication by a generator `a` of `ker f` vanishes on restrictions of scalars of
sheaves of `A'`-modules. -/
lemma smulNatTrans_app_restrictScalars_obj (ha : RingHom.ker f = Ideal.span {a})
    (X : Sheaf J (ModuleCat.{u + 1} A')) :
    (smulNatTrans J a).app ((restrictScalars J f).obj X) = 0 := by
  have hfa : f a = 0 := by
    rw [← RingHom.mem_ker, ha]
    exact Ideal.mem_span_singleton_self a
  ext U x
  dsimp
  erw [NatTrans.app_smul]
  exact (ModuleCat.restrictScalars.smul_def (M := X.obj.obj U) f a x).trans (by rw [hfa, zero_smul])

/-- The multiplication by `a` kills the projection of constant sheaves `A ⟶ A ⧸ ker f`. -/
lemma smul_unitToConstantQuotient (ha : RingHom.ker f = Ideal.span {a}) :
    a • unitToConstantQuotient J f = 0 := by
  have := constantSheaf_map_smul_comp J _ (smul_comp_mkQ ha)
  rwa [Linear.smul_comp, Category.id_comp] at this

/-- The reduction map is killed by the multiplication by a generator `a` of `ker f`. -/
lemma smulNatTrans_app_comp_reductionNatTrans_app (ha : RingHom.ker f = Ideal.span {a})
    (F : Sheaf J (ModuleCat.{u + 1} A)) :
    (smulNatTrans J a).app F ≫ (reductionNatTrans J f hf).app F = 0 := by
  have h : (a • 𝟙 F) ≫ (ρ_ F).inv ≫ F ◁ unitToConstantQuotient J f = 0 :=
    calc _ = (ρ_ F).inv ≫ F ◁ (a • unitToConstantQuotient J f) := by simp
      _ = 0 := by
        rw [smul_unitToConstantQuotient J ha, MonoidalPreadditive.whiskerLeft_zero, comp_zero]
  rw [smulNatTrans_app, reductionNatTrans_app, reassoc_of% h, zero_comp]

/-- The projection of constant sheaves `A ⟶ A ⧸ ker f` is an epimorphism. -/
instance : Epi (unitToConstantQuotient J f) := by
  have : Epi (ModuleCat.ofHom (RingHom.ker f).mkQ) :=
    (ModuleCat.epi_iff_surjective _).2 (Submodule.mkQ_surjective _)
  exact (constantSheaf J (ModuleCat.{u + 1} A)).map_epi _

/-- The reduction map is an epimorphism. -/
instance epi_reductionNatTrans_app (F : Sheaf J (ModuleCat.{u + 1} A)) :
    Epi ((reductionNatTrans J f hf).app F) := by
  have : Epi (F ◁ unitToConstantQuotient J f) := (tensorLeft F).map_epi _
  rw [reductionNatTrans_app]
  infer_instance

/-- The kernel of the reduction map is the image of the multiplication by a generator `a` of
`ker f`: tensoring with `F` preserves the exactness of `A --a--> A ⟶ A ⧸ ker f ⟶ 0`. -/
lemma exact_reductionNatTrans_app (ha : RingHom.ker f = Ideal.span {a})
    (F : Sheaf J (ModuleCat.{u + 1} A)) :
    (ShortComplex.mk _ _ (smulNatTrans_app_comp_reductionNatTrans_app J hf ha F)).Exact :=
  MonoidalCategory.exact_smul_of_exact_map_tensorLeft _
    ((exact_constantSheaf_map_smul J _ (exact_smul_mkQ ha)).map_of_epi_of_preservesCokernel
      (tensorLeft F) (inferInstanceAs (Epi (unitToConstantQuotient J f))) inferInstance)
    ((reductionFunctorCompRestrictScalarsIso J f hf).app F).symm
    (by simp [unitToConstantQuotient]) _

end Reduction

/-- **The reduction along a surjective ring morphism with principal kernel is a reduction
datum.** For `f : A →+* A'` surjective with kernel `(a)`, the reduction `F ↦ F / a F`, with
scalars transported to `A'`, together with the reduction map `F ⟶ F / a F`, is a reduction
datum for restriction of scalars along `f` and the multiplication by `a`. -/
noncomputable def reductionDatum (f : A →+* A') (hf : Function.Surjective f) (a : A)
    (ha : RingHom.ker f = Ideal.span {a}) :
    Functor.ReductionDatum (restrictScalars J f) (smulNatTrans J a) where
  Φ := reductionFunctor J f hf
  r := reductionNatTrans J f hf
  σ_app_obj := smulNatTrans_app_restrictScalars_obj J ha
  σ_comp_r := smulNatTrans_app_comp_reductionNatTrans_app J hf ha
  epi_r := epi_reductionNatTrans_app J hf
  exact := exact_reductionNatTrans_app J hf ha
  quasiIso_map φ _ h₁ h₂ := by
    have := restrictScalars_full J f hf
    exact CochainComplex.quasiIso_map_of_iso_tensorRight _ _
      (reductionFunctorCompRestrictScalarsIso J f hf) φ h₁ h₂

/-- **A flat sheaf preserves the exactness of `A --x--> A --y--> A`.** If `F` is a flat sheaf of
`A`-modules and the multiplications by `x` and `y` form an exact sequence `A ⟶ A ⟶ A`, then so
do the multiplications by `x` and `y` on `F`. -/
lemma exact_smul_of_flat {F : Sheaf J (ModuleCat.{u + 1} A)} (hF : ObjectProperty.flat F)
    (x y : A) (hxy : x * y = 0)
    (hex : Function.Exact (fun b : A ↦ x * b) (fun b : A ↦ y * b)) :
    (ShortComplex.mk (x • 𝟙 F) (y • 𝟙 F) (by simp [smul_smul, mul_comm y x, hxy])).Exact := by
  have h₀ : (x • 𝟙 (ModuleCat.of A A)) ≫ (y • 𝟙 (ModuleCat.of A A)) = 0 := by
    simp [smul_smul, mul_comm y x, hxy]
  have hS₀ : (ShortComplex.mk _ _ h₀).Exact := by
    rw [ShortComplex.moduleCat_exact_iff]
    intro b hb
    obtain ⟨c, rfl⟩ := (hex b).1 (by simpa using hb)
    exact ⟨c, by simp⟩
  have : PreservesFiniteLimits (tensorLeft F) := hF.tensorLeft.1
  have : PreservesFiniteColimits (tensorLeft F) := hF.tensorLeft.2
  exact MonoidalCategory.exact_smul_of_exact_map_tensorLeft _
    ((exact_constantSheaf_map_smul J h₀ hS₀).map (tensorLeft F)) (ρ_ F) (by
      have hy : (constantSheaf J (ModuleCat.{u + 1} A)).map (y • 𝟙 (ModuleCat.of A A)) =
          y • 𝟙 (𝟙_ (Sheaf J (ModuleCat.{u + 1} A))) := by
        rw [CategoryTheory.Functor.map_smul, CategoryTheory.Functor.map_id]
        rfl
      erw [hy]
      simp) _

end CategoryTheory.Sheaf
