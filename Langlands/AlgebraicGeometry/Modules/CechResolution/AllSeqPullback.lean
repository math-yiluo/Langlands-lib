import Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeqCohomology
import Langlands.AlgebraicGeometry.Modules.CechResolution.BaseChange
import Langlands.AlgebraicGeometry.Modules.CohomologyPullbackResolution
import Langlands.AlgebraicGeometry.Modules.SectionPullbackBridge
import Langlands.AlgebraicGeometry.Modules.PullbackUnit

/-!
# Ordered Čech maps along index maps compute the canonical pullback

Let `g : Y ⟶ X` be a morphism of schemes, `U : ι → X.Opens` and `V : κ → Y.Opens` finite
families, and `α : κ → ι` an index map with `V j ≤ g⁻¹ U (α j)`. For a map of modules
`a : M ⟶ g_* N`, the factors `sheafOn M (inter U (α ∘ τ)) ⟶ g_* sheafOn N (inter V τ)` assemble
to a map of sheafified ordered Čech complexes `AllSeq.complex U M ⟶ g_* AllSeq.complex V N`
compatible with the augmentations over `a`. No monotonicity or injectivity of `α` is needed.

Over an affine base, the general resolution description of the canonical pushforward
comparison (`DerivedSections.resolutionComparison_comp_canonicalPushforwardCohomologyMap`)
then identifies the canonical maps with the maps induced on ordered Čech cohomology.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

namespace Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeq

open Langlands.Cohomology

section Map

attribute [local instance] preservesBiproduct_of_preservesProduct

variable {X Y : Scheme.{u}} (g : Y ⟶ X) {M : X.Modules} {N : Y.Modules}
  (a : M ⟶ (Scheme.Modules.pushforward g).obj N)
  {ι κ : Type u} {U : ι → X.Opens} {V : κ → Y.Opens} (α : κ → ι)
  (hα : ∀ j, V j ≤ g ⁻¹ᵁ U (α j))

lemma preimage_inter {n : ℕ} (σ : Fin n → ι) : g ⁻¹ᵁ inter U σ = ⨅ a, g ⁻¹ᵁ U (σ a) := by
  apply Opens.ext
  simp only [inter, Cech.inter, Opens.coe_iInf, Scheme.Hom.coe_preimage, Set.preimage_iInter]

include hα in
lemma inter_le_preimage {n : ℕ} (τ : Fin n → κ) : inter V τ ≤ g ⁻¹ᵁ inter U (α ∘ τ) := by
  rw [preimage_inter]
  exact le_iInf fun b => (inter_le_apply τ b).trans (hα (τ b))

variable [Fintype ι] [Fintype κ]

/-- The degree-`p` map, assembled from the factor maps on intersections. -/
def termMap (p : ℕ) : term U M p ⟶ (Scheme.Modules.pushforward g).obj (term V N p) :=
  (isBilimitOfPreserves (Scheme.Modules.pushforward g)
    (biproduct.isBilimit (fun τ : Fin (p + 1) → κ => sheafOn N (inter V τ)))).isLimit.lift
      (Fan.mk _ (fun τ : Fin (p + 1) → κ =>
        biproduct.π (fun σ : Fin (p + 1) → ι => sheafOn M (inter U σ)) (α ∘ τ) ≫
          sheafOnPushforward g a (inter_le_preimage g α hα τ)))

@[reassoc]
lemma termMap_π (p : ℕ) (τ : Fin (p + 1) → κ) :
    termMap g a α hα p ≫
        (Scheme.Modules.pushforward g).map
          (biproduct.π (fun τ : Fin (p + 1) → κ => sheafOn N (inter V τ)) τ) =
      biproduct.π (fun σ : Fin (p + 1) → ι => sheafOn M (inter U σ)) (α ∘ τ) ≫
        sheafOnPushforward g a (inter_le_preimage g α hα τ) :=
  (isBilimitOfPreserves (Scheme.Modules.pushforward g)
    (biproduct.isBilimit _)).isLimit.fac _ ⟨τ⟩

/-- The degreewise maps commute with the ordered Čech differentials. -/
lemma termMap_d (p : ℕ) :
    termMap g a α hα p ≫ (Scheme.Modules.pushforward g).map (d V N p) =
      d U M p ≫ termMap g a α hα (p + 1) := by
  apply pushforward_biproduct_hom_ext g
    (fun τ : Fin (p + 2) → κ => sheafOn N (inter V τ))
  intro t
  rw [Category.assoc, ← Functor.map_comp]
  refine (congrArg (fun k => termMap g a α hα p ≫ (Scheme.Modules.pushforward g).map k)
      (d_π V N p t)).trans ?_
  rw [Functor.map_sum, Category.assoc, termMap_π, ← Category.assoc, d_π]
  simp only [Functor.map_zsmul, Functor.map_comp, Preadditive.comp_sum,
    Preadditive.sum_comp, Preadditive.comp_zsmul, Preadditive.zsmul_comp,
    ← Category.assoc]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  have hπ := termMap_π g a α hα p (t ∘ j.succAbove)
  have hr := res_sheafOnPushforward g a (inter_le_comp (α ∘ t) j.succAbove)
    (inter_le_comp t j.succAbove) (inter_le_preimage g α hα (t ∘ j.succAbove))
    (inter_le_preimage g α hα t)
  refine (congrArg (fun k => k ≫ (Scheme.Modules.pushforward g).map
    (res N (inter_le_comp t j.succAbove))) hπ).trans ?_
  rw [Category.assoc, ← hr, ← Category.assoc]
  rfl

/-- The map of sheafified ordered Čech complexes induced by `a : M ⟶ g_* N` and `α`. -/
def complexMap :
    complex U M ⟶
      ((Scheme.Modules.pushforward g).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (complex V N) :=
  CochainComplex.ofHom (termMap g a α hα) (fun p => by
    change termMap g a α hα p ≫
        (Scheme.Modules.pushforward g).map ((complex V N).d p (p + 1)) =
      (complex U M).d p (p + 1) ≫ termMap g a α hα (p + 1)
    simpa only [complex, CochainComplex.of_d] using termMap_d g a α hα p)

@[simp]
lemma complexMap_f (p : ℕ) : (complexMap g a α hα).f p = termMap g a α hα p := rfl

/-- The degree-zero augmentation square. -/
lemma augmentation_termMap :
    augmentation U M ≫ termMap g a α hα 0 =
      a ≫ (Scheme.Modules.pushforward g).map (augmentation V N) := by
  apply pushforward_biproduct_hom_ext g
    (fun σ : Fin (0 + 1) → κ => sheafOn N (inter V σ))
  intro s
  rw [Category.assoc, termMap_π, ← Category.assoc, augmentation_π, Category.assoc,
    ← Functor.map_comp]
  exact (unit_sheafOnPushforward g a _).trans
    (congrArg (fun k => a ≫ (Scheme.Modules.pushforward g).map k)
      (augmentation_π V N s).symm)

/-- The full augmentation square for the map induced by `a` and `α`. -/
lemma aug_complexMap :
    aug U M ≫ complexMap g a α hα =
      (CochainComplex.single₀ X.Modules).map a ≫
        AcyclicResolution.mapResolutionAugmentation (Scheme.Modules.pushforward g)
          (aug V N) := by
  ext : 1
  simpa only [HomologicalComplex.comp_f, CochainComplex.single₀_map_f_zero,
    AcyclicResolution.mapResolutionAugmentation_f_zero, aug,
    CochainComplex.fromSingle₀Equiv_symm_apply_f_zero, complexMap_f] using
    augmentation_termMap g a α hα

end Map

section Cohomology

open DerivedSections

attribute [local instance] HasDerivedCategory.standard

variable {R : CommRingCat.{u}} {X Y : Over (Spec R)} (h : Y ⟶ X)
  {M : X.left.Modules} {N : Y.left.Modules}
  (a : M ⟶ (Scheme.Modules.pushforward h.left).obj N)
  {ι κ : Type u} [Fintype ι] [Fintype κ] (U : ι → X.left.Opens) (V : κ → Y.left.Opens)
  (α : κ → ι) (hα : ∀ j, V j ≤ h.left ⁻¹ᵁ U (α j))
  (hU : ⨆ i, U i = ⊤) (hV : ⨆ j, V j = ⊤)

/-- The map of ordered Čech cochain complexes induced by `a` and `α`, transported from the
sheafified complexes through the sections isomorphisms. -/
def cochainMap :
    cochainComplex X.hom U M ⟶ cochainComplex Y.hom V N :=
  (sectionsComplexIso X.hom U M).inv ≫
    (((relativeGlobalSections X.hom).mapHomologicalComplex _).map (complexMap h.left a α hα) ≫
      ((Functor.mapHomologicalComplexCompIso (relativePushforwardSectionsIso h)
        (ComplexShape.up ℕ)).app (complex V N)).hom) ≫
    (sectionsComplexIso Y.hom V N).hom

include hU hV in
/-- **Ordered Čech description of the canonical pushforward comparison.** The comparison map
of the ordered Čech resolution of `M`, followed by cohomology of `a` and the canonical
pushforward comparison, is the map on ordered Čech cohomology induced by `a` and `α`,
followed by the comparison map of the ordered Čech resolution of `N`. -/
theorem resolutionComparison_comp_canonicalPushforwardCohomologyMap (n : ℕ) :
    haveI := quasiIso_aug U M hU
    haveI := quasiIso_aug V N hV
    AcyclicResolution.resolutionComparison (relativeGlobalSections X.hom) (aug U M) n ≫
        (relativeCohomology X.hom n).map a ≫ canonicalPushforwardCohomologyMap h N n =
      HomologicalComplex.homologyMap
          (((relativeGlobalSections X.hom).mapHomologicalComplex _).map
              (complexMap h.left a α hα) ≫
            ((Functor.mapHomologicalComplexCompIso (relativePushforwardSectionsIso h)
              (ComplexShape.up ℕ)).app (complex V N)).hom) n ≫
        AcyclicResolution.resolutionComparison (relativeGlobalSections Y.hom) (aug V N) n := by
  have := quasiIso_aug U M hU
  have := quasiIso_aug V N hV
  exact DerivedSections.resolutionComparison_comp_canonicalPushforwardCohomologyMap h a
    (aug U M) (aug V N) (complexMap h.left a α hα) (aug_complexMap h.left a α hα) n

variable [IsSeparated X.hom] [IsSeparated Y.hom] [M.IsQuasicoherent] [N.IsQuasicoherent]
  (hUa : ∀ i, IsAffineOpen (U i)) (hVa : ∀ j, IsAffineOpen (V j))

/-- **Ordered Čech description of the canonical pushforward comparison**, on the cohomology of
the ordered Čech cochain complexes. -/
theorem cohomologyIso_comp_canonicalPushforwardCohomologyMap (n : ℕ) :
    (cohomologyIso X.hom U M hU hUa n).hom ≫
        (relativeCohomology X.hom n).map a ≫ canonicalPushforwardCohomologyMap h N n =
      HomologicalComplex.homologyMap (cochainMap h a U V α hα) n ≫
        (cohomologyIso Y.hom V N hV hVa n).hom := by
  have key := resolutionComparison_comp_canonicalPushforwardCohomologyMap h a U V α hα hU hV n
  have e : HomologicalComplex.homologyMap (cochainMap h a U V α hα) n ≫
      HomologicalComplex.homologyMap (sectionsComplexIso Y.hom V N).inv n =
      HomologicalComplex.homologyMap (sectionsComplexIso X.hom U M).inv n ≫
        HomologicalComplex.homologyMap
          (((relativeGlobalSections X.hom).mapHomologicalComplex _).map
              (complexMap h.left a α hα) ≫
            ((Functor.mapHomologicalComplexCompIso (relativePushforwardSectionsIso h)
              (ComplexShape.up ℕ)).app (complex V N)).hom) n := by
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp, cochainMap]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [cohomologyIso, cohomologyIso]
  simp only [Iso.trans_hom, Functor.mapIso_hom, asIso_hom, Iso.symm_hom, Category.assoc]
  rw [key]
  exact ((reassoc_of% e) _).symm

/-- **Ordered Čech description of the canonical cohomology pullback.** For `V` covering `Y`
with `V j ≤ h⁻¹ U (α j)`, the canonical pullback `relativeCohomologyPullback h M n` is computed
by the ordered Čech map of the adjunction unit and `α`. -/
theorem cohomologyIso_comp_relativeCohomologyPullback
    [((Scheme.Modules.pullback h.left).obj M).IsQuasicoherent] (n : ℕ) :
    (cohomologyIso X.hom U M hU hUa n).hom ≫ relativeCohomologyPullback h M n =
      HomologicalComplex.homologyMap
          (cochainMap h ((Scheme.Modules.pullbackPushforwardAdjunction h.left).unit.app M)
            U V α hα) n ≫
        (cohomologyIso Y.hom V ((Scheme.Modules.pullback h.left).obj M) hV hVa n).hom := by
  rw [relativeCohomologyPullback_eq_unit_pushforward]
  exact cohomologyIso_comp_canonicalPushforwardCohomologyMap h _ U V α hα hU hV hUa hVa n

/-- Coefficient form: the canonical pullback followed by a coefficient map
`b : h^* M ⟶ N` is computed by the ordered Čech map of the adjoint of `b`. -/
theorem cohomologyIso_comp_relativeCohomologyPullback_coefficient
    (b : (Scheme.Modules.pullback h.left).obj M ⟶ N) (n : ℕ) :
    (cohomologyIso X.hom U M hU hUa n).hom ≫ relativeCohomologyPullback h M n ≫
        (relativeCohomology Y.hom n).map b =
      HomologicalComplex.homologyMap
          (cochainMap h ((Scheme.Modules.pullbackPushforwardAdjunction h.left).homEquiv _ _ b)
            U V α hα) n ≫
        (cohomologyIso Y.hom V N hV hVa n).hom := by
  rw [relativeCohomologyPullback_coefficient]
  exact cohomologyIso_comp_canonicalPushforwardCohomologyMap h _ U V α hα hU hV hUa hVa n

end Cohomology

section Elements

open DerivedSections

variable {R : CommRingCat.{u}} {X Y : Over (Spec R)} (h : Y ⟶ X)

/-- The pushforward-sections identification acts as the identity on underlying sections. -/
lemma relativePushforwardSectionsIso_hom_app_apply (F : Y.left.Modules)
    (y : (relativeGlobalSections X.hom).obj ((Scheme.Modules.pushforward h.left).obj F)) :
    ((relativePushforwardSectionsIso h).hom.app F) y =
      (show (relativeGlobalSections Y.hom).obj F from y) := by
  unfold relativePushforwardSectionsIso relativeGlobalSectionsCompIso
  change ((Scheme.Modules.pushforwardCongr h.w).hom.app _).app ⊤ y = _
  exact pushforwardCongr_hom_app_top h.w _ _

/-- Two composites of restriction maps between the same opens agree. -/
lemma map_map_eq {Z : Scheme.{u}} (N : Z.Modules) {A B B' C : Z.Opens} (f₁ : op B ⟶ op C)
    (f₂ : op A ⟶ op B) (g₁ : op B' ⟶ op C) (g₂ : op A ⟶ op B') (z : Γ(N, A)) :
    N.presheaf.map f₁ (N.presheaf.map f₂ z) = N.presheaf.map g₁ (N.presheaf.map g₂ z) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← N.presheaf.map_comp,
    ← N.presheaf.map_comp]
  rfl

variable {M : X.left.Modules} {N : Y.left.Modules}
  (a : M ⟶ (Scheme.Modules.pushforward h.left).obj N)
  {ι κ : Type u} [Fintype ι] [Fintype κ] (U : ι → X.left.Opens) (V : κ → Y.left.Opens)
  (α : κ → ι) (hα : ∀ j, V j ≤ h.left ⁻¹ᵁ U (α j))

lemma toCochainFun_sectionsComplexIso_inv {π : X.left ⟶ Spec R} (p : ℕ) (c : cochain π U M p) :
    toCochainFun U M ((sectionsComplexIso π U M).inv.f p c) = c := by
  have e : (sectionsComplexIso π U M).hom.f p ((sectionsComplexIso π U M).inv.f p c) = c := by
    rw [← ConcreteCategory.comp_apply, ← HomologicalComplex.comp_f, Iso.inv_hom_id,
      HomologicalComplex.id_f, ConcreteCategory.id_apply]
  exact e

/-- The ordered Čech map induced by `a` and `α`, on cochains:
`(cochainMap c) τ = (a (c (α ∘ τ)))|_{inter V τ}`. -/
lemma cochainMap_f_apply (p : ℕ) (c : cochain X.hom U M p) (τ : Fin (p + 1) → κ) :
    (cochainMap h a U V α hα).f p c τ =
      N.presheaf.map (homOfLE (inter_le_preimage h.left α hα τ)).op
        (a.app (inter U (α ∘ τ)) (c (α ∘ τ))) := by
  set x := (sectionsComplexIso X.hom U M).inv.f p c with hxdef
  have hx : toCochainFun U M x = c := toCochainFun_sectionsComplexIso_inv U p c
  have e1 : (cochainMap h a U V α hα).f p c =
      toCochainFun V N ((termMap h.left a α hα p).app ⊤ x) := by
    simp only [cochainMap, HomologicalComplex.comp_f]
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
    change toCochainFun V N (((relativePushforwardSectionsIso h).hom.app (term V N p))
      ((termMap h.left a α hα p).app ⊤ x)) = _
    rw [relativePushforwardSectionsIso_hom_app_apply]
  rw [e1, ← hx]
  have e2 := congrArg (fun f => f.app ⊤ x) (termMap_π h.left a α hα p τ)
  simp only [comp_app_apply, Scheme.Modules.pushforward_map_app, sheafOnPushforward_app] at e2
  simp only [toCochainFun, cr_def, toSec]
  erw [e2]
  rw [ConcreteCategory.comp_apply, app_map_apply]
  exact map_map_eq N _ _ _ _ _

/-- For the structure sheaves and the structure map `𝒪_X ⟶ h_* 𝒪_Y`, the ordered Čech map is
the pullback of cochains of functions: `(cochainMap c) τ = h^♯ (c (α ∘ τ))|_{inter V τ}`. -/
lemma cochainMap_unit_f_apply (p : ℕ)
    (c : cochain X.hom U (SheafOfModules.unit X.left.ringCatSheaf) p) (τ : Fin (p + 1) → κ) :
    (cochainMap h (Langlands.Scheme.Modules.unitToPushforwardUnit h.left) U V α hα).f p c τ =
      h.left.appLE (inter U (α ∘ τ)) (inter V τ) (inter_le_preimage h.left α hα τ)
        (c (α ∘ τ)) := by
  rw [cochainMap_f_apply]
  rfl

end Elements

section Unit

open DerivedSections

attribute [local instance] HasDerivedCategory.standard

variable {R : CommRingCat.{u}} {X Y : Over (Spec R)} (h : Y ⟶ X)
  {ι κ : Type u} [Fintype ι] [Fintype κ] (U : ι → X.left.Opens) (V : κ → Y.left.Opens)
  (α : κ → ι) (hα : ∀ j, V j ≤ h.left ⁻¹ᵁ U (α j))
  (hU : ⨆ i, U i = ⊤) (hV : ⨆ j, V j = ⊤) [IsSeparated X.hom] [IsSeparated Y.hom]
  (hUa : ∀ i, IsAffineOpen (U i)) (hVa : ∀ j, IsAffineOpen (V j))

omit [IsSeparated X.hom] [IsSeparated Y.hom] in
/-- The adjoint of the structure-sheaf comparison `h^* 𝒪_X ≅ 𝒪_Y` is the structure map
`𝒪_X ⟶ h_* 𝒪_Y`. -/
lemma homEquiv_pullbackUnitIso_hom :
    (Scheme.Modules.pullbackPushforwardAdjunction h.left).homEquiv _ _
        (Langlands.Scheme.Modules.pullbackUnitIso h.left).hom =
      Langlands.Scheme.Modules.unitToPushforwardUnit h.left :=
  SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _

/-- **Ordered Čech description of the canonical structure-sheaf pullback.** With the unit
comparison `h^* 𝒪_X ≅ 𝒪_Y`, the canonical pullback on structure-sheaf cohomology is computed by
pulling back ordered Čech cochains of functions along `h` and `α`. -/
theorem cohomologyIso_comp_relativeCohomologyPullback_unit (n : ℕ) :
    (cohomologyIso X.hom U (SheafOfModules.unit X.left.ringCatSheaf) hU hUa n).hom ≫
        relativeCohomologyPullback h (SheafOfModules.unit X.left.ringCatSheaf) n ≫
        (relativeCohomology Y.hom n).map (Langlands.Scheme.Modules.pullbackUnitIso h.left).hom =
      HomologicalComplex.homologyMap
          (cochainMap h (Langlands.Scheme.Modules.unitToPushforwardUnit h.left) U V α hα) n ≫
        (cohomologyIso Y.hom V (SheafOfModules.unit Y.left.ringCatSheaf) hV hVa n).hom := by
  rw [cohomologyIso_comp_relativeCohomologyPullback_coefficient h U V α hα hU hV hUa hVa,
    homEquiv_pullbackUnitIso_hom]

end Unit

end Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeq
