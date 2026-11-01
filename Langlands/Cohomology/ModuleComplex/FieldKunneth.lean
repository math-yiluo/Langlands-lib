import Langlands.Cohomology.ModuleComplex.TensorSignsUpNat
import Mathlib.Algebra.Homology.BifunctorHomotopy
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Injective
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.DirectSum.Module
import Mathlib.RingTheory.SimpleModule.InjectiveProjective

/-!
# Algebraic Künneth formula over a field

For a field `K` and cochain complexes `C D : CochainComplex (ModuleCat K) ℕ`, the
cohomology of the total complex `HomologicalComplex.mapBifunctor C D (curriedTensor _) (up ℕ)`
in degree `n` is `⨁_{a + b = n} Hᵃ(C) ⊗_K Hᵇ(D)`.

Route: every `K`-module is injective and projective. Choosing sections of
`C.cycles n ⟶ C.homology n` gives a quasi-isomorphism from the complex of homologies (with
zero differential) to `C`, which is a homotopy equivalence because all terms are injective.
Total complexes preserve homotopy equivalences, and the total complex of two complexes with
zero differential has zero differential, so its cohomology is its term, a direct sum of
tensor products.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex

namespace Langlands.Cohomology.ModuleComplex.FieldKunneth

universe u

section Bifunctor

variable {C₁ C₂ D I₁ I₂ J : Type*} [Category* C₁] [Category* C₂] [Category* D]
  [Preadditive C₁] [Preadditive C₂] [Preadditive D]
  {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
  (F : C₁ ⥤ C₂ ⥤ D) [F.Additive] [∀ X₁, (F.obj X₁).Additive]
  (c : ComplexShape J) [DecidableEq J] [TotalComplexShape c₁ c₂ c]
  [∀ (K₁ : HomologicalComplex C₁ c₁) (K₂ : HomologicalComplex C₂ c₂),
    HasMapBifunctor K₁ K₂ F c]

lemma mapBifunctorMap_comp {K₁ L₁ M₁ : HomologicalComplex C₁ c₁}
    {K₂ L₂ M₂ : HomologicalComplex C₂ c₂}
    (f₁ : K₁ ⟶ L₁) (g₁ : L₁ ⟶ M₁) (f₂ : K₂ ⟶ L₂) (g₂ : L₂ ⟶ M₂) :
    mapBifunctorMap f₁ f₂ F c ≫ mapBifunctorMap g₁ g₂ F c =
      mapBifunctorMap (f₁ ≫ g₁) (f₂ ≫ g₂) F c := by
  ext j i₁ i₂ h
  simp [NatTrans.naturality_assoc]

lemma mapBifunctorMap_id (K₁ : HomologicalComplex C₁ c₁) (K₂ : HomologicalComplex C₂ c₂) :
    mapBifunctorMap (𝟙 K₁) (𝟙 K₂) F c = 𝟙 _ := by
  ext j i₁ i₂ h
  simp

/-- Total complexes of a bifunctor send pairs of homotopy equivalences to homotopy
equivalences. -/
def mapBifunctorHomotopyEquiv {K₁ L₁ : HomologicalComplex C₁ c₁}
    {K₂ L₂ : HomologicalComplex C₂ c₂}
    (e₁ : HomotopyEquiv K₁ L₁) (e₂ : HomotopyEquiv K₂ L₂) :
    HomotopyEquiv (mapBifunctor K₁ K₂ F c) (mapBifunctor L₁ L₂ F c) where
  hom := mapBifunctorMap e₁.hom e₂.hom F c
  inv := mapBifunctorMap e₁.inv e₂.inv F c
  homotopyHomInvId :=
    (Homotopy.ofEq (mapBifunctorMap_comp F c _ _ _ _)).trans
      (((mapBifunctorMapHomotopy₁ e₁.homotopyHomInvId _ F c).trans
        (mapBifunctorMapHomotopy₂ _ e₂.homotopyHomInvId F c)).trans
          (Homotopy.ofEq (mapBifunctorMap_id F c _ _)))
  homotopyInvHomId :=
    (Homotopy.ofEq (mapBifunctorMap_comp F c _ _ _ _)).trans
      (((mapBifunctorMapHomotopy₁ e₁.homotopyInvHomId _ F c).trans
        (mapBifunctorMapHomotopy₂ _ e₂.homotopyInvHomId F c)).trans
          (Homotopy.ofEq (mapBifunctorMap_id F c _ _)))

end Bifunctor

section ZeroDifferential

variable {𝒞 : Type*} [Category* 𝒞] [Preadditive 𝒞] [CategoryWithHomology 𝒞]

/-- The cohomology of an `ℕ`-indexed cochain complex with zero differentials is its term. -/
def homologyIsoXOfDEqZero (A : CochainComplex 𝒞 ℕ) (hA : ∀ i j, A.d i j = 0) (n : ℕ) :
    A.homology n ≅ A.X n :=
  (A.isoHomologyπ _ n rfl (hA _ _)).symm ≪≫ A.iCyclesIso n _ rfl (hA _ _)

end ZeroDifferential

variable {K : Type u} [Field K]

instance injective_moduleCat (X : ModuleCat.{u} K) : Injective X :=
  Module.injective_object_of_injective_module (inj := Module.injective_of_isSemisimpleRing K X)

instance projective_moduleCat (X : ModuleCat.{u} K) : Projective X :=
  have : Module.Projective K X := Module.projective_of_isSemisimpleRing K X
  inferInstance

section HomologyComplex

variable (C : CochainComplex (ModuleCat.{u} K) ℕ)

/-- The cochain complex of the cohomology objects of `C`, with zero differentials. -/
@[simps]
abbrev homologyComplex : CochainComplex (ModuleCat.{u} K) ℕ where
  X n := C.homology n
  d _ _ := 0

/-- A chosen section of `C.homologyπ n`, which exists because `C.homology n` is projective. -/
def homologySection (n : ℕ) : C.homology n ⟶ C.cycles n :=
  Projective.factorThru (𝟙 _) (C.homologyπ n)

@[reassoc (attr := simp)]
lemma homologySection_homologyπ (n : ℕ) : homologySection C n ≫ C.homologyπ n = 𝟙 _ :=
  Projective.factorThru_comp _ _

/-- The cochain map from the complex of cohomology objects to `C` given by the chosen
sections followed by the inclusions of cycles. -/
@[simps]
def homologyComplexι : homologyComplex C ⟶ C where
  f n := homologySection C n ≫ C.iCycles n
  comm' i j _ := by
    rw [homologyComplex_d, zero_comp, Category.assoc, iCycles_d, comp_zero]

lemma cyclesMap_homologyComplexι (n : ℕ) :
    cyclesMap (homologyComplexι C) n = (homologyComplex C).iCycles n ≫ homologySection C n := by
  rw [← cancel_mono (C.iCycles n), cyclesMap_i, homologyComplexι_f, Category.assoc]

lemma homologyMap_homologyComplexι (n : ℕ) :
    homologyMap (homologyComplexι C) n =
      ((homologyComplex C).isoHomologyπ _ n rfl (homologyComplex_d C _ _)).inv ≫
        ((homologyComplex C).iCyclesIso n _ rfl (homologyComplex_d C _ _)).hom := by
  rw [← cancel_epi ((homologyComplex C).isoHomologyπ _ n rfl (homologyComplex_d C _ _)).hom,
    Iso.hom_inv_id_assoc, isoHomologyπ_hom, homologyπ_naturality, cyclesMap_homologyComplexι,
    Category.assoc, homologySection_homologyπ, Category.comp_id, iCyclesIso_hom]

instance quasiIso_homologyComplexι : QuasiIso (homologyComplexι C) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap, homologyMap_homologyComplexι]
  infer_instance

/-- Over a field, every `ℕ`-indexed cochain complex is homotopy equivalent to its complex of
cohomology objects. -/
def homotopyEquivHomologyComplex : HomotopyEquiv (homologyComplex C) C :=
  ((CochainComplex.quasiIso_iff_of_injective (homologyComplexι C)).1 inferInstance).choose

end HomologyComplex

section Total

variable (A B : CochainComplex (ModuleCat.{u} K) ℕ)

lemma mapBifunctor_d_eq_zero (hA : ∀ i j, A.d i j = 0) (hB : ∀ i j, B.d i j = 0) (i j : ℕ) :
    (mapBifunctor A B (curriedTensor (ModuleCat.{u} K)) (ComplexShape.up ℕ)).d i j = 0 := by
  apply mapBifunctor.hom_ext
  intro i₁ i₂ h
  rw [mapBifunctor.d_eq, Preadditive.comp_add, mapBifunctor.ι_D₁, mapBifunctor.ι_D₂,
    mapBifunctor.d₁_eq' _ _ _ _ (show (ComplexShape.up ℕ).Rel i₁ (i₁ + 1) from rfl),
    mapBifunctor.d₂_eq' _ _ _ _ _ (show (ComplexShape.up ℕ).Rel i₂ (i₂ + 1) from rfl), hA, hB]
  simp

/-- The degree-`n` term of the total tensor complex of `A` and `B` is
`⨁_{a + b = n} Aᵃ ⊗_K Bᵇ`. -/
def mapBifunctorXIso (n : ℕ) :
    (mapBifunctor A B (curriedTensor (ModuleCat.{u} K)) (ComplexShape.up ℕ)).X n ≅
      ModuleCat.of K (DirectSum {ab : ℕ × ℕ // ab.1 + ab.2 = n} fun ab =>
        TensorProduct K (A.X ab.1.1) (B.X ab.1.2)) :=
  ModuleCat.coprodIsoDirectSum _

end Total

/-- **Algebraic Künneth formula over a field.** For cochain complexes `C`, `D` of
`K`-modules indexed by `ℕ`, the degree-`n` cohomology of their total tensor complex is
`⨁_{a + b = n} Hᵃ(C) ⊗_K Hᵇ(D)`. -/
def kunnethIso (C D : CochainComplex (ModuleCat.{u} K) ℕ) (n : ℕ) :
    (mapBifunctor C D (curriedTensor (ModuleCat.{u} K)) (ComplexShape.up ℕ)).homology n ≅
      ModuleCat.of K (DirectSum {ab : ℕ × ℕ // ab.1 + ab.2 = n} fun ab =>
        TensorProduct K (C.homology ab.1.1) (D.homology ab.1.2)) :=
  ((mapBifunctorHomotopyEquiv (curriedTensor (ModuleCat.{u} K)) (ComplexShape.up ℕ)
      (homotopyEquivHomologyComplex C) (homotopyEquivHomologyComplex D)).toHomologyIso n).symm ≪≫
    homologyIsoXOfDEqZero _
      (mapBifunctor_d_eq_zero _ _ (fun _ _ => rfl) (fun _ _ => rfl)) n ≪≫
    mapBifunctorXIso (homologyComplex C) (homologyComplex D) n

end Langlands.Cohomology.ModuleComplex.FieldKunneth
