import Langlands.AlgebraicGeometry.Picard.LocalTwoAxisTrivialityProof
import Langlands.AlgebraicGeometry.Picard.TwoAxisValuationClassSurjectivity
import Langlands.AlgebraicGeometry.Picard.TwoAxisCarrierIsoAbelian
import Langlands.AlgebraicGeometry.Picard.TwoAxisClassMurreConditionsStatement
import Langlands.AlgebraicGeometry.Picard.LineBundleIsoClassGroup
import Langlands.AlgebraicGeometry.Modules.PullbackTensorProof

/-! # Nilpotent injectivity (strong F5) for the two-axis class presheaf -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.Scheme.Modules

namespace TwoAxisRigidifiedLineBundle

open Langlands.AbelianScheme TwoAxisFamily

local notation "cl" => LineBundle.isoClass pullbackTensorComparisonIsIso
local notation "pb" => LineBundle.pullbackHom pullbackTensorComparisonIsIso

section NilpotentInjective

/-- A pulled-back class is trivial exactly when the pulled-back sheaf is the structure sheaf. -/
private lemma pb_isoClass_eq_one_iff {X Y : Scheme.{u}} (f : X ⟶ Y) (L : LineBundle Y) :
    pb f (cl L) = 1 ↔
      Nonempty ((Scheme.Modules.pullback f).obj L.obj ≅ structureSheaf X) := by
  rw [LineBundle.pullbackHom_isoClass,
    ← LineBundle.isoClass_trivial pullbackTensorComparisonIsIso, LineBundle.isoClass_eq_iff]
  exact ⟨fun ⟨e⟩ ↦ ⟨(LineBundle.forget X).mapIso e⟩, fun ⟨e⟩ ↦ ⟨ObjectProperty.isoMk _ e⟩⟩

/-- Pullback of classes along an isomorphism of schemes is injective. -/
private lemma pb_injective_of_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] :
    Function.Injective (pb f) := by
  intro a b hab
  have h := congrArg (pb (inv f)) hab
  rwa [LineBundle.pullbackHom_comp_eq _ _ _ (IsIso.inv_hom_id f),
    LineBundle.pullbackHom_comp_eq _ _ _ (IsIso.inv_hom_id f),
    LineBundle.pullbackHom_id, LineBundle.pullbackHom_id] at h

/-- Every class of line bundles has a representative. -/
private lemma exists_isoClass_eq {X : Scheme.{u}}
    (q : LineBundle.IsoClasses pullbackTensorComparisonIsIso X) :
    ∃ L : LineBundle X, cl L = q := by
  induction q using LineBundle.IsoClasses.ind with | h L => exact ⟨L, rfl⟩

variable {S' X Y Z : Scheme.{u}} {e : S' ⟶ X} {t : S' ⟶ Y} {i : X ⟶ Z} {j : Y ⟶ Z}
  {h : e ≫ i = t ≫ j}

/-- The class of the underlying line bundle of a two-axis-rigidified line bundle. -/
private abbrev carrierClass (L : TwoAxisRigidifiedLineBundle e t i j h) :
    LineBundle.IsoClasses pullbackTensorComparisonIsIso Z :=
  cl ⟨L.obj.carrier, L.property⟩

private lemma pb_first_carrierClass (L : TwoAxisRigidifiedLineBundle e t i j h) :
    pb i (carrierClass L) = 1 :=
  (pb_isoClass_eq_one_iff i _).mpr ⟨L.obj.rigidification.first.symm⟩

private lemma pb_second_carrierClass (L : TwoAxisRigidifiedLineBundle e t i j h) :
    pb j (carrierClass L) = 1 :=
  (pb_isoClass_eq_one_iff j _).mpr ⟨L.obj.rigidification.second.symm⟩

variable {S : Scheme.{u}} (A : Langlands.AbelianScheme S)

/-- The two self-product comparisons for the composite test object, in the order not covered
by `compProductHom_inv`. -/
private lemma compProductInv_comp_hom {T : Over S} {W : Scheme.{u}} (b : W ⟶ T.left) :
    compProductInv A b ≫ compProductHom A b = 𝟙 _ := by
  apply pullback.hom_ext
  · simp only [compProductHom, compProductInv, cartesianMumfordProductMap, Category.assoc,
      cartesianSelfProductMap_fst, cartesianSelfProductMap_fst_assoc, Iso.inv_hom_id,
      Category.comp_id, Category.id_comp]
  · simp only [compProductHom, compProductInv, cartesianMumfordProductMap, Category.assoc,
      cartesianSelfProductMap_snd, cartesianSelfProductMap_snd_assoc, Iso.inv_hom_id,
      Category.comp_id, Category.id_comp]

/-- A morphism into the self-product whose base projection factors through `b` factors through
the product map of the test-scheme morphism `compTestHom b`. -/
private lemma exists_factor_productMap {T : Over S} {W V : Scheme.{u}} (b : W ⟶ T.left)
    (k : V ⟶ (mumfordProduct (abelian A T)).left) (w : V ⟶ W)
    (hk : k ≫ (mumfordProduct (abelian A T)).hom = w ≫ b) :
    ∃ l : V ⟶ (mumfordProduct (abelian A (Over.mk (b ≫ T.hom)))).left,
      l ≫ productMap A (compTestHom b) = k := by
  refine ⟨pullback.lift k w hk ≫ (mumfordProductBaseChangeIso (abelian A T) b).inv ≫
    compProductInv A b, ?_⟩
  rw [← compProductHom_baseChangeMap A b, Category.assoc, Category.assoc,
    reassoc_of% (compProductInv_comp_hom A b), ← mumfordProductBaseChangeIso_hom_fst,
    Iso.inv_hom_id_assoc]
  exact pullback.lift_fst _ _ _

/-- The first axis of the categorical self-product is the first unit axis of the explicit
self-product. -/
private lemma firstAxis_comp {B : Scheme.{u}} (G : Langlands.AbelianScheme B) :
    (prod.lift (𝟙 G.X) (Over.mkIdTerminal.from G.X ≫ (1 : Over.mk (𝟙 B) ⟶ G.X))).left ≫
      (Over.prodLeftIsoPullback G.X G.X).hom = mumfordSection G := by
  apply pullback.hom_ext
  · rw [Category.assoc, Over.prodLeftIsoPullback_hom_fst, ← Over.comp_left, prod.lift_fst]
    simp [mumfordSection, relativeSection]
  · rw [Category.assoc, Over.prodLeftIsoPullback_hom_snd, ← Over.comp_left, prod.lift_snd]
    simp [mumfordSection, relativeSection]
    rfl

/-- The second axis of the categorical self-product is the second unit axis of the explicit
self-product. -/
private lemma secondAxis_comp {B : Scheme.{u}} (G : Langlands.AbelianScheme B) :
    (prod.lift (Over.mkIdTerminal.from G.X ≫ (1 : Over.mk (𝟙 B) ⟶ G.X)) (𝟙 G.X)).left ≫
      (Over.prodLeftIsoPullback G.X G.X).hom = twoAxisSecond G := by
  apply pullback.hom_ext
  · rw [Category.assoc, Over.prodLeftIsoPullback_hom_fst, ← Over.comp_left, prod.lift_fst]
    simp [twoAxisSecond]
    rfl
  · rw [Category.assoc, Over.prodLeftIsoPullback_hom_snd, ← Over.comp_left, prod.lift_snd]
    simp [twoAxisSecond]

/-- Over a local ring `B`, class restriction to `B ⧸ I` is injective for every proper ideal
`I`. -/
theorem classesPullback_injective_local (B : Type u) [CommRing B] [IsLocalRing B]
    (I : Ideal B) (hI : I ≠ ⊤) (g : Spec (CommRingCat.of B) ⟶ S) :
    Function.Injective (classesPullback A
      (compTestHom (T := Over.mk g)
        (Spec.map (CommRingCat.ofHom (algebraMap B (B ⧸ I)))))) := by
  intro x y hxy
  induction x using Quotient.inductionOn with
  | h L =>
  induction y using Quotient.inductionOn with
  | h M =>
  obtain ⟨φ⟩ := Quotient.exact hxy
  let b := Spec.map (CommRingCat.ofHom (algebraMap B (B ⧸ I)))
  let G := abelian A (Over.mk g)
  let π₀ := Over.prodLeftIsoPullback G.X G.X
  -- the class of `L ⊗ M⁻¹` on the categorical self-product
  let c : LineBundle.IsoClasses pullbackTensorComparisonIsIso (G.X ⨯ G.X).left :=
    pb π₀.hom (carrierClass L / carrierClass M)
  -- agreement after restriction along the product map
  have hP : pb (productMap A (compTestHom (T := Over.mk g) b)) (carrierClass L) =
      pb (productMap A (compTestHom (T := Over.mk g) b)) (carrierClass M) :=
    let φc : (Scheme.Modules.pullback (productMap A (compTestHom (T := Over.mk g) b))).obj
          L.obj.carrier ≅
        (Scheme.Modules.pullback (productMap A (compTestHom (T := Over.mk g) b))).obj
          M.obj.carrier :=
      (TwoAxisRigidifiedModule.forget _ _ _ _ _).mapIso ((ObjectProperty.ι _).mapIso φ)
    LineBundle.isoClass_eq_of_iso (ObjectProperty.isoMk _ φc)
  -- the two axes
  have h₁ : pb (prod.lift (𝟙 G.X)
      (Over.mkIdTerminal.from G.X ≫ (1 : Over.mk (𝟙 _) ⟶ G.X))).left c = 1 := by
    simp only [c]
    rw [LineBundle.pullbackHom_comp_eq _ _ _ (firstAxis_comp G), map_div,
      pb_first_carrierClass, pb_first_carrierClass, div_one]
  have h₂ : pb (prod.lift (Over.mkIdTerminal.from G.X ≫ (1 : Over.mk (𝟙 _) ⟶ G.X))
      (𝟙 G.X)).left c = 1 := by
    simp only [c]
    rw [LineBundle.pullbackHom_comp_eq _ _ _ (secondAxis_comp G), map_div,
      pb_second_carrierClass, pb_second_carrierClass, div_one]
  -- the closed fibre
  let s : Spec (CommRingCat.of B) := IsLocalRing.closedPoint B
  have hIs : I ≤ s.asIdeal := IsLocalRing.le_maximalIdeal hI
  let ψ : B ⧸ I →+* s.asIdeal.ResidueField :=
    Ideal.Quotient.lift I (algebraMap B s.asIdeal.ResidueField)
      (fun a ha ↦ Ideal.algebraMap_residueField_eq_zero.mpr (hIs ha))
  have hres : (Spec (CommRingCat.of B)).fromSpecResidueField s =
      Spec.map (Scheme.Spec.residueFieldIso (CommRingCat.of B) s).inv ≫
        Spec.map (CommRingCat.ofHom ψ) ≫ b := by
    rw [← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField]
    congr 1
    rw [← Spec.map_comp]
    congr 1
  have h₃ : pb ((G.X ⨯ G.X).hom.fiberι s) c = 1 := by
    obtain ⟨l, hl⟩ := exists_factor_productMap A (T := Over.mk g) b
      ((G.X ⨯ G.X).hom.fiberι s ≫ π₀.hom)
      ((G.X ⨯ G.X).hom.fiberToSpecResidueField s ≫
        Spec.map (Scheme.Spec.residueFieldIso (CommRingCat.of B) s).inv ≫
        Spec.map (CommRingCat.ofHom ψ)) (by
          change ((G.X ⨯ G.X).hom.fiberι s ≫ π₀.hom) ≫
              pullback.fst G.X.hom G.X.hom ≫ G.X.hom = _
          rw [Category.assoc, Over.prodLeftIsoPullback_hom_fst_assoc, Over.w,
            Scheme.Hom.fiber_fac]
          simp only [Category.assoc]
          exact congrArg (fun k ↦ (G.X ⨯ G.X).hom.fiberToSpecResidueField s ≫ k) hres)
    show pb ((G.X ⨯ G.X).hom.fiberι s) (pb π₀.hom (carrierClass L / carrierClass M)) = 1
    rw [LineBundle.pullbackHom_comp, ← hl, ← LineBundle.pullbackHom_comp, map_div, map_div]
    exact div_eq_one.mpr (congrArg _ hP)
  -- local two-axis triviality over the local base
  obtain ⟨Λ, hΛ⟩ := exists_isoClass_eq c
  have t₁ := (pb_isoClass_eq_one_iff _ Λ).mp (by rw [hΛ]; exact h₁)
  have t₂ := (pb_isoClass_eq_one_iff _ Λ).mp (by rw [hΛ]; exact h₂)
  have t₃ := (pb_isoClass_eq_one_iff _ Λ).mp (by rw [hΛ]; exact h₃)
  obtain ⟨U, hsU, hU⟩ := localTwoAxisTriviality (Spec (CommRingCat.of B)) G.X G.X
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    1 1 Λ s t₁ t₂ t₃
  have hUtop : U = ⊤ := (IsLocalRing.closedPoint_mem_iff U).mp hsU
  subst hUtop
  have : IsIso (⊤ : (Spec (CommRingCat.of B)).Opens).ι := (Scheme.topIso _).isIso_hom
  have hc : c = 1 := by
    apply pb_injective_of_isIso (pullback.fst (G.X ⨯ G.X).hom
      (⊤ : (Spec (CommRingCat.of B)).Opens).ι)
    rw [map_one, ← hΛ]
    exact (pb_isoClass_eq_one_iff _ Λ).mpr hU
  have hLM : carrierClass L = carrierClass M :=
    div_eq_one.mp (pb_injective_of_isIso π₀.hom (hc.trans (map_one _).symm))
  obtain ⟨f⟩ := LineBundle.isoClass_eq_iff.mp hLM
  obtain ⟨φ'⟩ := nonempty_iso_of_carrierIso G (L := L) (M := M)
    ((LineBundle.forget _).mapIso f)
  exact Quotient.sound ⟨φ'⟩

end NilpotentInjective

end TwoAxisRigidifiedLineBundle

open TwoAxisRigidifiedLineBundle in
/-- **Nilpotent injectivity (strong F5).** For every abelian scheme over the spectrum of a
noetherian ring, the two-axis class presheaf is injective on restriction from a local artinian
ring to its quotient by a nilpotent ideal. -/
theorem noetherianTwoAxisClassNilpotentInjective :
    NoetherianTwoAxisClassNilpotentInjectiveStatement.{u} := by
  intro R _ _ A B _ _ _ I hI f
  have hItop : I ≠ ⊤ := by
    rintro rfl
    obtain ⟨n, hn⟩ := hI
    rw [Ideal.top_pow, Ideal.zero_eq_bot] at hn
    exact top_ne_bot hn
  exact classesPullback_injective_local A B I hItop f

end Langlands.AlgebraicGeometry.Picard
