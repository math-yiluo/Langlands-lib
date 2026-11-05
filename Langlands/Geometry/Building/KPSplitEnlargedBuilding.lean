import Langlands.Geometry.Building.KPEnlargedBuilding
import Langlands.BruhatTits.Cartan.CentralizerRealComparison

/-! # Actual split-component coordinates for the enlarged building -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace Langlands.Plancherel
open Langlands.BruhatTits

namespace Langlands.Geometry.Building

variable {F : Type u} [Field F]

/-- An actual split component together with the explicit real restriction comparison. -/
structure SplitComponentComparison (G : GroupScheme (Spec (CommRingCat.of F))) where
  A : CommGroupScheme (Spec (CommRingCat.of F))
  a : A.toGrp ⟶ G
  isSplitComponent : IsSplitComponent a
  bijective : Function.Bijective (Cartan.restrictionEvaluation a)

namespace SplitComponentComparison

variable {G : GroupScheme (Spec (CommRingCat.of F))}

/-- The integral injectivity and finite-index inputs remain explicit. -/
def ofIntegralInputs {A : CommGroupScheme (Spec (CommRingCat.of F))}
    (a : A.toGrp ⟶ G) (ha : IsSplitComponent a)
    (hinj : Function.Injective (characterRestrict a))
    [(characterRestrict a).range.FiniteIndex] : SplitComponentComparison G where
  A := A
  a := a
  isSplitComponent := ha
  bijective := Cartan.restrictionEvaluation_bijective
    ha.isCentralSplitTorus.isSplitSubtorus.1 a hinj

variable (C : SplitComponentComparison G)

/-- The actual real cocharacter space, with a dedicated actual group action. -/
def CentralSpace : Type u := V C.A

instance : AddCommGroup C.CentralSpace := inferInstanceAs (AddCommGroup (V C.A))
instance : Module ℝ C.CentralSpace := inferInstanceAs (Module ℝ (V C.A))

/-- Actual restriction evaluation, bundled using the supplied bijectivity. -/
def centralEquiv : C.CentralSpace ≃ₗ[ℝ] CentralFactor G :=
  (LinearEquiv.ofBijective (Cartan.restrictionEvaluation C.a) C.bijective).trans
    (CentralFactor.dualEquiv G).symm

@[simp] theorem centralEquiv_apply (v : C.CentralSpace) :
    CentralFactor.dualEquiv G (C.centralEquiv v) = Cartan.restrictionEvaluation C.a v :=
  rfl

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/-- Negative of the existing positive valuation for the actual split-component morphism. -/
def translation : rationalPoints G →* Multiplicative C.CentralSpace where
  toFun g := Multiplicative.ofAdd (-(Cartan.centralizerValuation C.a C.bijective g).toAdd)
  map_one' := by
    change -(Cartan.centralizerValuation C.a C.bijective 1).toAdd = 0
    simp
  map_mul' g h := by
    change -(Cartan.centralizerValuation C.a C.bijective (g * h)).toAdd =
      -(Cartan.centralizerValuation C.a C.bijective g).toAdd +
        -(Cartan.centralizerValuation C.a C.bijective h).toAdd
    simp only [map_mul, toAdd_mul, neg_add]

instance : MulAction (rationalPoints G) C.CentralSpace where
  smul g v := v + (C.translation g).toAdd
  one_smul v := by change v + (C.translation 1).toAdd = v; simp
  mul_smul g h v := by
    change v + (C.translation (g * h)).toAdd =
      (v + (C.translation h).toAdd) + (C.translation g).toAdd
    simp only [map_mul, toAdd_mul]
    abel

@[simp] theorem smul_eq (g : rationalPoints G) (v : C.CentralSpace) :
    g • v = v - (show C.CentralSpace from
      (Cartan.centralizerValuation C.a C.bijective g).toAdd) := rfl

theorem centralEquiv_valuation (g : rationalPoints G) :
    C.centralEquiv (Cartan.centralizerValuation C.a C.bijective g).toAdd =
      (show CentralFactor G from (rationalNormLogarithm G g).toAdd) := by
  apply (CentralFactor.dualEquiv G).injective
  change (LinearEquiv.ofBijective
    (Cartan.restrictionEvaluation C.a) C.bijective)
      ((LinearEquiv.ofBijective
        (Cartan.restrictionEvaluation C.a) C.bijective).symm
          (rationalNormLogarithm G g).toAdd) = _
  exact (LinearEquiv.ofBijective
    (Cartan.restrictionEvaluation C.a) C.bijective).apply_symm_apply _

theorem centralEquiv_translation (g : rationalPoints G) :
    C.centralEquiv (C.translation g).toAdd = (CentralFactor.translation G g).toAdd := by
  change C.centralEquiv (-(show C.CentralSpace from
    (Cartan.centralizerValuation C.a C.bijective g).toAdd)) =
    -(show CentralFactor G from (rationalNormLogarithm G g).toAdd)
  rw [map_neg, C.centralEquiv_valuation]

theorem centralEquiv_smul (g : rationalPoints G) (v : C.CentralSpace) :
    C.centralEquiv (g • v) = g • C.centralEquiv v := by
  change C.centralEquiv (v + (C.translation g).toAdd) =
    C.centralEquiv v + (CentralFactor.translation G g).toAdd
  rw [map_add, C.centralEquiv_translation]

/-- Character coordinates have positive valuation and negative translation. -/
theorem smul_eval (g : rationalPoints G) (v : C.CentralSpace)
    (χ : rationalCharacters G) :
    eval C.A (Cartan.characterRestriction C.a χ) (g • v) =
      eval C.A (Cartan.characterRestriction C.a χ) v -
        ((rationalCharacterValuation G g).toAdd χ : ℝ) := by
  change eval C.A (Cartan.characterRestriction C.a χ)
    ((show V C.A from v) - (Cartan.centralizerValuation C.a C.bijective g).toAdd) = _
  rw [map_sub, Cartan.centralizerValuation_spec]

theorem translation_ker : C.translation.ker = rationalCommonNormKernel G := by
  ext g
  rw [← CentralFactor.translation_ker G]
  change (C.translation g).toAdd = 0 ↔ (CentralFactor.translation G g).toAdd = 0
  rw [← C.centralEquiv_translation, ← map_zero C.centralEquiv]
  exact ⟨congrArg C.centralEquiv, fun hg => C.centralEquiv.injective hg⟩

theorem smul_eq_self_iff (g : rationalPoints G) (v : C.CentralSpace) :
    g • v = v ↔ g ∈ rationalCommonNormKernel G := by
  rw [← C.translation_ker]
  change v + (C.translation g).toAdd = v ↔ (C.translation g).toAdd = 0
  exact add_eq_left

theorem centralStabilizer_eq (v : C.CentralSpace) :
    MulAction.stabilizer (rationalPoints G) v = rationalCommonNormKernel G := by
  ext g
  exact C.smul_eq_self_iff g v

variable [IsAffineHom G.X.hom] (B : ValuationBuildingData G)

/-- The enlarged product in the actual split-component cocharacter coordinates. -/
abbrev EnlargedBuilding : Type u := B.ReducedBuilding × C.CentralSpace

/-- The enlarged base apartment in the same actual cocharacter coordinates. -/
abbrev EnlargedApartment : Type u := B.Apartment × C.CentralSpace

def enlargedApartmentMap (x : C.EnlargedApartment B) : C.EnlargedBuilding B :=
  (B.apartmentMap x.1, x.2)

theorem normalizer_smul_enlargedApartmentMap (n : normalizerPoints B.i)
    (x : C.EnlargedApartment B) :
    (n : rationalPoints G) • C.enlargedApartmentMap B x =
      C.enlargedApartmentMap B (n • x) := by
  exact Prod.ext (B.normalizer_smul_apartmentMap n x.1) rfl

theorem enlargedApartmentMap_injective (hB : Function.Injective B.apartmentMap) :
    Function.Injective (C.enlargedApartmentMap B) := by
  intro x y hxy
  exact Prod.ext (hB (congrArg (fun z : C.EnlargedBuilding B => z.1) hxy))
    (congrArg (fun z : C.EnlargedBuilding B => z.2) hxy)

/-- Identity on the supplied reduced building, actual restriction on the central factor. -/
def enlargedEquiv : C.EnlargedBuilding B ≃ B.EnlargedBuilding :=
  Equiv.prodCongr (Equiv.refl _) C.centralEquiv.toEquiv

def apartmentEquiv : C.EnlargedApartment B ≃ B.EnlargedApartment :=
  Equiv.prodCongr (Equiv.refl _) C.centralEquiv.toEquiv

@[simp] theorem enlargedEquiv_apply (x : C.EnlargedBuilding B) :
    C.enlargedEquiv B x = (x.1, C.centralEquiv x.2) := rfl

@[simp] theorem apartmentEquiv_apply (x : C.EnlargedApartment B) :
    C.apartmentEquiv B x = (x.1, C.centralEquiv x.2) := rfl

theorem enlargedEquiv_smul (g : rationalPoints G) (x : C.EnlargedBuilding B) :
    C.enlargedEquiv B (g • x) = g • C.enlargedEquiv B x := by
  exact Prod.ext rfl (C.centralEquiv_smul g x.2)

theorem apartmentEquiv_smul (n : normalizerPoints B.i) (x : C.EnlargedApartment B) :
    C.apartmentEquiv B (n • x) = n • C.apartmentEquiv B x := by
  exact Prod.ext rfl (C.centralEquiv_smul (n : rationalPoints G) x.2)

@[simp] theorem enlargedEquiv_apartmentMap (x : C.EnlargedApartment B) :
    C.enlargedEquiv B (C.enlargedApartmentMap B x) =
      B.enlargedApartmentMap (C.apartmentEquiv B x) := rfl

def enlargedApartmentImage : Set (C.EnlargedBuilding B) :=
  Set.range (C.enlargedApartmentMap B)

def enlargedTranslatedApartment (g : rationalPoints G) : Set (C.EnlargedBuilding B) :=
  g • C.enlargedApartmentImage B

def enlargedTranslatedApartmentMap (g : rationalPoints G) (x : C.EnlargedApartment B) :
    C.EnlargedBuilding B := g • C.enlargedApartmentMap B x

theorem range_enlargedTranslatedApartmentMap (g : rationalPoints G) :
    Set.range (C.enlargedTranslatedApartmentMap B g) =
      C.enlargedTranslatedApartment B g := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨C.enlargedApartmentMap B x, ⟨x, rfl⟩, rfl⟩
  · rintro ⟨z, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, rfl⟩

theorem enlargedTranslatedApartment_eq_prod (g : rationalPoints G) :
    C.enlargedTranslatedApartment B g =
      (g • B.apartmentImage) ×ˢ (Set.univ : Set C.CentralSpace) := by
  rw [← C.range_enlargedTranslatedApartmentMap, ← B.range_translatedApartmentMap]
  ext y
  constructor
  · rintro ⟨⟨x, v⟩, rfl⟩
    exact ⟨⟨x, rfl⟩, Set.mem_univ _⟩
  · rintro ⟨⟨x, hx⟩, _⟩
    refine ⟨(x, g⁻¹ • y.2), ?_⟩
    exact Prod.ext hx (smul_inv_smul g y.2)

theorem enlargedApartmentImage_eq_prod :
    C.enlargedApartmentImage B = B.apartmentImage ×ˢ (Set.univ : Set C.CentralSpace) := by
  simpa only [enlargedTranslatedApartment, one_smul] using
    C.enlargedTranslatedApartment_eq_prod B 1

theorem enlargedEquiv_translatedApartmentMap (g : rationalPoints G)
    (x : C.EnlargedApartment B) :
    C.enlargedEquiv B (C.enlargedTranslatedApartmentMap B g x) =
      B.enlargedTranslatedApartmentMap g (C.apartmentEquiv B x) :=
  C.enlargedEquiv_smul B g (C.enlargedApartmentMap B x)

def enlargedProjection (x : C.EnlargedBuilding B) : B.ReducedBuilding := x.1

def enlargedZeroSection (y : B.ReducedBuilding) : C.EnlargedBuilding B := (y, 0)

@[simp] theorem enlargedProjection_smul (g : rationalPoints G) (x : C.EnlargedBuilding B) :
    C.enlargedProjection B (g • x) = g • C.enlargedProjection B x := rfl

@[simp] theorem enlargedProjection_zeroSection (y : B.ReducedBuilding) :
    C.enlargedProjection B (C.enlargedZeroSection B y) = y := rfl

theorem enlargedProjection_surjective : Function.Surjective (C.enlargedProjection B) :=
  fun y => ⟨C.enlargedZeroSection B y, rfl⟩

theorem enlargedZeroSection_smul (g : rationalCommonNormKernel G) (y : B.ReducedBuilding) :
    C.enlargedZeroSection B (g • y) = g • C.enlargedZeroSection B y := by
  apply Prod.ext
  · rfl
  · exact ((C.smul_eq_self_iff (g : rationalPoints G) 0).mpr g.property).symm

@[simp] theorem enlargedProjection_enlargedEquiv (x : C.EnlargedBuilding B) :
    B.enlargedProjection (C.enlargedEquiv B x) = C.enlargedProjection B x := rfl

@[simp] theorem enlargedEquiv_zeroSection (y : B.ReducedBuilding) :
    C.enlargedEquiv B (C.enlargedZeroSection B y) = B.enlargedZeroSection y := by
  exact Prod.ext rfl (map_zero C.centralEquiv)

def centralTranslate (v : C.CentralSpace) (x : C.EnlargedBuilding B) :
    C.EnlargedBuilding B := (x.1, x.2 + v)

@[simp] theorem centralTranslate_zero (x : C.EnlargedBuilding B) :
    C.centralTranslate B 0 x = x := by
  exact Prod.ext rfl (add_zero x.2)

theorem centralTranslate_add (v w : C.CentralSpace) (x : C.EnlargedBuilding B) :
    C.centralTranslate B (v + w) x = C.centralTranslate B w (C.centralTranslate B v x) := by
  exact Prod.ext rfl (add_assoc x.2 v w).symm

@[simp] theorem enlargedProjection_centralTranslate (v : C.CentralSpace)
    (x : C.EnlargedBuilding B) :
    C.enlargedProjection B (C.centralTranslate B v x) = C.enlargedProjection B x := rfl

theorem centralTranslate_smul (v : C.CentralSpace) (g : rationalPoints G)
    (x : C.EnlargedBuilding B) :
    C.centralTranslate B v (g • x) = g • C.centralTranslate B v x := by
  apply Prod.ext
  · rfl
  · change (x.2 + (C.translation g).toAdd) + v =
      (x.2 + v) + (C.translation g).toAdd
    abel

theorem enlargedProjection_eq_iff (x y : C.EnlargedBuilding B) :
    C.enlargedProjection B x = C.enlargedProjection B y ↔
      ∃ v : C.CentralSpace, C.centralTranslate B v x = y := by
  constructor
  · intro h
    refine ⟨y.2 - x.2, Prod.ext h ?_⟩
    change x.2 + (y.2 - x.2) = y.2
    abel
  · rintro ⟨v, rfl⟩
    rfl

@[simp] theorem enlargedEquiv_centralTranslate (v : C.CentralSpace)
    (x : C.EnlargedBuilding B) :
    C.enlargedEquiv B (C.centralTranslate B v x) =
      B.centralTranslate (C.centralEquiv v) (C.enlargedEquiv B x) := by
  exact Prod.ext rfl (map_add C.centralEquiv x.2 v)

/-- Full point stabilizer under the actual split-product action. -/
def enlargedStabilizer (x : C.EnlargedBuilding B) : Subgroup (rationalPoints G) :=
  MulAction.stabilizer (rationalPoints G) x

/-- Pointwise stabilizer under the actual split-product action. -/
def enlargedPointwiseFixer (Y : Set (C.EnlargedBuilding B)) : Subgroup (rationalPoints G) :=
  fixingSubgroup (rationalPoints G) Y

theorem enlargedStabilizer_eq_canonical (x : C.EnlargedBuilding B) :
    C.enlargedStabilizer B x = B.enlargedStabilizer (C.enlargedEquiv B x) := by
  ext g
  change g • x = x ↔ g • C.enlargedEquiv B x = C.enlargedEquiv B x
  rw [← C.enlargedEquiv_smul, Equiv.apply_eq_iff_eq]

theorem enlargedStabilizer_eq_compactStabilizer (x : C.EnlargedBuilding B) :
    C.enlargedStabilizer B x = B.compactStabilizer (C.enlargedProjection B x) := by
  rw [C.enlargedStabilizer_eq_canonical, B.enlargedStabilizer_eq_compactStabilizer]
  rfl

theorem enlargedStabilizer_eq_inf (x : C.EnlargedBuilding B) :
    C.enlargedStabilizer B x =
      rationalCommonNormKernel G ⊓ B.fixer (C.enlargedProjection B x) := by
  rw [C.enlargedStabilizer_eq_canonical, B.enlargedStabilizer_eq_inf]
  rfl

theorem enlargedStabilizer_central_independent (y : B.ReducedBuilding)
    (v w : C.CentralSpace) :
    C.enlargedStabilizer B (y, v) = C.enlargedStabilizer B (y, w) := by
  rw [C.enlargedStabilizer_eq_compactStabilizer, C.enlargedStabilizer_eq_compactStabilizer]
  rfl

theorem mem_enlargedPointwiseFixer {Y : Set (C.EnlargedBuilding B)} {g : rationalPoints G} :
    g ∈ C.enlargedPointwiseFixer B Y ↔ ∀ x ∈ Y, g • x = x :=
  mem_fixingSubgroup_iff (rationalPoints G)

theorem enlargedPointwiseFixer_eq_canonical (Y : Set (C.EnlargedBuilding B)) :
    C.enlargedPointwiseFixer B Y =
      B.enlargedPointwiseFixer (C.enlargedEquiv B '' Y) := by
  ext g
  rw [C.mem_enlargedPointwiseFixer, B.mem_enlargedPointwiseFixer]
  constructor
  · intro hg z
    rintro ⟨x, hx, rfl⟩
    rw [← C.enlargedEquiv_smul, hg x hx]
  · intro hg x hx
    apply (C.enlargedEquiv B).injective
    rw [C.enlargedEquiv_smul]
    exact hg _ ⟨x, hx, rfl⟩

theorem enlargedPointwiseFixer_eq_inf {Y : Set (C.EnlargedBuilding B)} (hY : Y.Nonempty) :
    C.enlargedPointwiseFixer B Y =
      rationalCommonNormKernel G ⊓ B.pointwiseFixer (C.enlargedProjection B '' Y) := by
  rw [C.enlargedPointwiseFixer_eq_canonical,
    B.enlargedPointwiseFixer_eq_inf (hY.image (C.enlargedEquiv B)), Set.image_image]
  rfl

theorem enlargedProjection_image_prod (Ω : Set B.ReducedBuilding) :
    C.enlargedProjection B '' (Ω ×ˢ (Set.univ : Set C.CentralSpace)) = Ω := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx.1
  · intro hy
    exact ⟨(y, 0), ⟨hy, Set.mem_univ _⟩, rfl⟩

theorem enlargedPointwiseFixer_prod {Ω : Set B.ReducedBuilding} (hΩ : Ω.Nonempty) :
    C.enlargedPointwiseFixer B (Ω ×ˢ (Set.univ : Set C.CentralSpace)) =
      rationalCommonNormKernel G ⊓ B.pointwiseFixer Ω := by
  obtain ⟨y, hy⟩ := hΩ
  have hY : (Ω ×ˢ (Set.univ : Set C.CentralSpace)).Nonempty :=
    ⟨(y, 0), hy, Set.mem_univ _⟩
  rw [C.enlargedPointwiseFixer_eq_inf B hY, C.enlargedProjection_image_prod]

@[simp] theorem enlargedPointwiseFixer_empty :
    C.enlargedPointwiseFixer B ∅ = ⊤ := fixingSubgroup_empty _ _

end SplitComponentComparison

end Langlands.Geometry.Building
