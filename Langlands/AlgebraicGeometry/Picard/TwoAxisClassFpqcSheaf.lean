import Langlands.AlgebraicGeometry.Picard.RigidifiedClassesAffineSheaf
import Langlands.AlgebraicGeometry.Picard.RigidifiedClassesZariskiSheafGeneral
import Langlands.AlgebraicGeometry.Picard.RigidifiedRelativeIsoUniqueness
import Langlands.AlgebraicGeometry.Sites.OverFppfSheaf
import Langlands.AlgebraicGeometry.Modules.LineBundleIsoDescentProof
import Langlands.AlgebraicGeometry.Modules.LineBundleDescentEffectiveProof
import Langlands.AlgebraicGeometry.Picard.RigidifiedPullbackProofs
import Langlands.AlgebraicGeometry.Picard.RigidifiedCarrierIso
import Langlands.AlgebraicGeometry.Picard.LineBundleIsoClassGroup
import Langlands.AlgebraicGeometry.Modules.PullbackTensorProof
import Langlands.AlgebraicGeometry.Picard.TwoAxisRigidifiedClassPresheaf
import Langlands.AlgebraicGeometry.Picard.TwoAxisCarrierIsoAbelian
import Langlands.AlgebraicGeometry.Picard.SelfProductBaseChange
import Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof
import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreCriterionStatement

/-! # The two-axis class presheaf is an fpqc sheaf -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace Langlands.AlgebraicGeometry.OverFppfSheaf

variable {S : Scheme.{u}} (G : (Over S)ᵒᵖ ⥤ Type (u + 1))

/-- **Site reduction, fpqc version.** A presheaf of types on `Over S` is an fpqc sheaf as soon
as it is a Zariski sheaf and satisfies the singleton sheaf condition along every lift to
`Over S` of a flat surjective morphism of affine schemes. -/
theorem isSheaf_fpqcTopology_over
    (hzar : Presieve.IsSheaf (Scheme.zariskiTopology.over S) G)
    (haff : ∀ {R R' : CommRingCat.{u}} (φ : R ⟶ R'), Flat (Spec.map φ) →
      Surjective (Spec.map φ) → ∀ s : Spec R ⟶ S, Presieve.IsSheafFor G
        (.singleton (Over.homMk (Spec.map φ) : Over.mk (Spec.map φ ≫ s) ⟶ Over.mk s))) :
    Presieve.IsSheaf (Scheme.fpqcTopology.over S) G := by
  refine isSheaf_over_of_isSheaf_ext G _ ?_
  rw [Scheme.fpqcTopology_eq_propQCTopology, isSheaf_type_propQCTopology_iff]
  refine ⟨isSheaf_ext_of_isSheaf_over G _ hzar, fun {R R'} φ hf hs ↦ ?_⟩
  have : Flat (Spec.map φ) := hf
  have : Surjective (Spec.map φ) := hs
  have : IsRegularEpi (Spec.map φ) := isRegularEpi_of_flat_of_surjective_of_isAffine _
  exact isSheafFor_singleton_ext G _
    (.singleton_of_isRepresentable_of_effectiveEpi _ _) (haff φ hf hs)

end Langlands.AlgebraicGeometry.OverFppfSheaf

namespace Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundle

open Langlands.SchemeModule.RigidifiedModule

variable {S X : Scheme.{u}} (f : X ⟶ S) (ε : S ⟶ X)
  (section_eq : ε ≫ f = 𝟙 S)

/-- Under the universal structure-sheaf condition, the rigidified class presheaf is an fpqc
sheaf on the entire slice. -/
lemma classPresheaf_isSheaf_fpqc
    (hO : ∀ (T : Over S) (U : T.left.Opens),
      IsIso (((relativeProjection f).app T).app U)) :
    Presieve.IsSheaf (Scheme.fpqcTopology.over S)
      (classPresheaf pullbackCoherence f ε section_eq) := by
  have unique := relative_iso_subsingleton f ε section_eq hO
  exact OverFppfSheaf.isSheaf_fpqcTopology_over _
    (classPresheaf_isSheaf_zariski_of_unique f ε section_eq unique)
    (fun φ hf hs s ↦ classPresheaf_isSheafFor_affine f ε section_eq
      Langlands.Scheme.Modules.LineBundleIsoDescent.lineBundleIsoDescent
      Langlands.Scheme.Modules.lineBundleDescentEffective unique φ hf hs s)

end Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundle

namespace Langlands.AlgebraicGeometry.Picard.TwoAxisClassFpqc

section Transfer

variable {C : Type*} [Category C] {F G H : Cᵒᵖ ⥤ Type*}

/-- Transfer of a sheaf condition along componentwise injections `Φ : F → G` whose image is
cut out by two natural maps `Ψ₁ Ψ₂ : G → H` taking the value of a compatible family `z`. -/
lemma isSheafFor_of_injective
    (Φ : ∀ T : C, F.obj (op T) → G.obj (op T))
    (hΦ : ∀ {T U : C} (h : T ⟶ U) (x : F.obj (op U)),
      Φ T (F.map h.op x) = G.map h.op (Φ U x))
    (hinj : ∀ T, Function.Injective (Φ T))
    (Ψ₁ Ψ₂ : ∀ T : C, G.obj (op T) → H.obj (op T))
    (hΨ₁ : ∀ {T U : C} (h : T ⟶ U) (g : G.obj (op U)),
      Ψ₁ T (G.map h.op g) = H.map h.op (Ψ₁ U g))
    (hΨ₂ : ∀ {T U : C} (h : T ⟶ U) (g : G.obj (op U)),
      Ψ₂ T (G.map h.op g) = H.map h.op (Ψ₂ U g))
    (z : ∀ T : C, H.obj (op T))
    (hz : ∀ {T U : C} (h : T ⟶ U), H.map h.op (z U) = z T)
    (hΦΨ₁ : ∀ T x, Ψ₁ T (Φ T x) = z T) (hΦΨ₂ : ∀ T x, Ψ₂ T (Φ T x) = z T)
    (himage : ∀ T g, Ψ₁ T g = z T → Ψ₂ T g = z T → ∃ x, Φ T x = g)
    {X : C} {P : Presieve X} (hG : Presieve.IsSheafFor G P)
    (hH : Presieve.IsSeparatedFor H P) :
    Presieve.IsSheafFor F P := by
  intro x hx
  let y : Presieve.FamilyOfElements G P := fun Y f hf ↦ Φ Y (x f hf)
  have hy : y.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ w
    change G.map g₁.op (Φ Y₁ (x f₁ h₁)) = G.map g₂.op (Φ Y₂ (x f₂ h₂))
    rw [← hΦ, ← hΦ, hx g₁ g₂ h₁ h₂ w]
  obtain ⟨g, hg, -⟩ := hG y hy
  have h₁ : Ψ₁ X g = z X := hH.ext fun Y f hf ↦ by
    rw [← hΨ₁, hg f hf, hz]
    exact hΦΨ₁ _ _
  have h₂ : Ψ₂ X g = z X := hH.ext fun Y f hf ↦ by
    rw [← hΨ₂, hg f hf, hz]
    exact hΦΨ₂ _ _
  obtain ⟨t, rfl⟩ := himage X g h₁ h₂
  refine ⟨t, fun Y f hf ↦ hinj Y ?_, fun t' ht' ↦ hinj X ?_⟩
  · rw [hΦ]
    exact hg f hf
  · refine hG.isSeparatedFor.ext fun Y f hf ↦ ?_
    rw [← hΦ, ← hΦ, ht' f hf, hΦ]
    exact (hg f hf).symm

end Transfer

open Langlands.AbelianScheme TwoAxisFamily Langlands.SchemeModule

local notation "PC" => LineBundle.IsoClasses Langlands.Scheme.Modules.pullbackTensorComparisonIsIso
local notation "pb" => LineBundle.pullbackHom Langlands.Scheme.Modules.pullbackTensorComparisonIsIso

section Carrier

variable {S X : Scheme.{u}} (f : X ⟶ S) (ε : S ⟶ X) (hε : ε ≫ f = 𝟙 S)

/-- The class of the underlying line bundle of a rigidified class. -/
def carrierClass (T : Over S) :
    RigidifiedLineBundle.Classes f ε hε T → PC ((relativeSpace f).obj T) :=
  Quotient.map (RigidifiedLineBundle.forget _).obj
    (fun _ _ ⟨e⟩ ↦ ⟨(RigidifiedLineBundle.forget _).mapIso e⟩)

lemma carrierClass_injective (T : Over S) : Function.Injective (carrierClass f ε hε T) := by
  intro q r
  induction q using Quotient.inductionOn with | h L => ?_
  induction r using Quotient.inductionOn with | h M => ?_
  intro h
  obtain ⟨e⟩ := LineBundle.isoClass_eq_iff.mp h
  exact Quotient.sound (RigidifiedLineBundle.nonempty_iso_of_forget_iso
    Langlands.Scheme.Modules.pullbackTensorComparisonIsIso ((relativeProjection f).app T)
    (relativeSection_projection f ε hε T) e)

lemma carrierClass_map {T U : Over S} (h : T ⟶ U)
    (c : (RigidifiedLineBundle.classPresheaf RigidifiedModule.pullbackCoherence f ε hε).obj
      (op U)) :
    carrierClass f ε hε T
        ((RigidifiedLineBundle.classPresheaf RigidifiedModule.pullbackCoherence f ε hε).map
          h.op c) =
      pb ((relativeSpace f).map h) (carrierClass f ε hε U c) := by
  induction c using Quotient.inductionOn with | h L => rfl

lemma carrierClass_trivial (T : Over S) :
    carrierClass f ε hε T
      (Quotient.mk _ (RigidifiedLineBundle.trivial ((relativeSection f ε hε).app T))) = 1 :=
  rfl

lemma exists_carrierClass_eq (T : Over S) (m : PC ((relativeSpace f).obj T))
    (hm : pb ((relativeSection f ε hε).app T) m = 1) :
    ∃ c, carrierClass f ε hε T c = m := by
  induction m using LineBundle.IsoClasses.ind with | h L => ?_
  rw [LineBundle.pullbackHom_isoClass, ← LineBundle.isoClass_trivial] at hm
  obtain ⟨e⟩ := LineBundle.isoClass_eq_iff.mp hm
  exact ⟨Quotient.mk _ (RigidifiedLineBundle.ofLineBundle L
    ((LineBundle.forget T.left).mapIso e).symm), rfl⟩

end Carrier

section TwoAxisCarrier

variable {S : Scheme.{u}} (B : Langlands.AbelianScheme S)

/-- Two-axis-rigidified line bundles on the self-product of an abelian scheme. -/
abbrev TwoAxisObj :=
  TwoAxisRigidifiedLineBundle (unitSection B) (unitSection B) (mumfordSection B)
    (twoAxisSecond B) (twoAxis_unit_comp B)

/-- The class of the underlying line bundle of a two-axis-rigidified class. -/
def twoAxisCarrierClass :
    Quotient (isIsomorphicSetoid (TwoAxisObj B)) → PC (mumfordProduct B).left :=
  Quotient.map (TwoAxisRigidifiedLineBundle.forget _ _ _ _ _).obj
    (fun _ _ ⟨e⟩ ↦ ⟨(TwoAxisRigidifiedLineBundle.forget _ _ _ _ _).mapIso e⟩)

lemma twoAxisCarrierClass_injective : Function.Injective (twoAxisCarrierClass B) := by
  intro q r
  induction q using Quotient.inductionOn with | h L => ?_
  induction r using Quotient.inductionOn with | h M => ?_
  intro h
  obtain ⟨e⟩ := LineBundle.isoClass_eq_iff.mp h
  exact Quotient.sound (TwoAxisRigidifiedLineBundle.nonempty_iso_of_carrierIso B
    ((LineBundle.forget _).mapIso e))

lemma twoAxisCarrierClass_first (c : Quotient (isIsomorphicSetoid (TwoAxisObj B))) :
    pb (mumfordSection B) (twoAxisCarrierClass B c) = 1 := by
  induction c using Quotient.inductionOn with | h L => ?_
  exact LineBundle.isoClass_eq_of_iso (ObjectProperty.isoMk _ L.obj.rigidification.first.symm)

lemma twoAxisCarrierClass_second (c : Quotient (isIsomorphicSetoid (TwoAxisObj B))) :
    pb (twoAxisSecond B) (twoAxisCarrierClass B c) = 1 := by
  induction c using Quotient.inductionOn with | h L => ?_
  exact LineBundle.isoClass_eq_of_iso (ObjectProperty.isoMk _ L.obj.rigidification.second.symm)

lemma exists_twoAxisCarrierClass_eq (m : PC (mumfordProduct B).left)
    (h₁ : pb (mumfordSection B) m = 1) (h₂ : pb (twoAxisSecond B) m = 1) :
    ∃ c, twoAxisCarrierClass B c = m := by
  induction m using LineBundle.IsoClasses.ind with | h D => ?_
  rw [LineBundle.pullbackHom_isoClass, ← LineBundle.isoClass_trivial] at h₁ h₂
  obtain ⟨e₁⟩ := LineBundle.isoClass_eq_iff.mp h₁
  obtain ⟨e₂⟩ := LineBundle.isoClass_eq_iff.mp h₂
  obtain ⟨ρ⟩ := nonempty_twoAxisRigidification B D ⟨(LineBundle.forget _).mapIso e₁⟩
    ⟨(LineBundle.forget _).mapIso e₂⟩
  exact ⟨Quotient.mk _ (TwoAxisRigidifiedLineBundle.ofLineBundle D ρ), rfl⟩

end TwoAxisCarrier

section Product

variable {S : Scheme.{u}} (A : Langlands.AbelianScheme S)

/-- The structure morphism of the self-product `A ×_S A` over the base. -/
def fP : (mumfordProduct A).left ⟶ S := (mumfordProduct A).hom

/-- The unit section `(e, e)` of the self-product. -/
abbrev eP : S ⟶ (mumfordProduct A).left := unitSection A ≫ mumfordSection A

lemma eP_comp : eP A ≫ fP A = 𝟙 S := by
  change unitSection A ≫ mumfordSection A ≫ pullback.fst A.X.hom A.X.hom ≫ A.X.hom = 𝟙 S
  rw [reassoc_of% (TwoAxisRigidifiedLineBundle.mumfordSection_fst A), unitSection_comp]

instance : Smooth (fP A) := by
  change Smooth (pullback.fst A.X.hom A.X.hom ≫ A.X.hom); infer_instance

instance : IsProper (fP A) := by
  change IsProper (pullback.fst A.X.hom A.X.hom ≫ A.X.hom); infer_instance

instance : GeometricallyConnected (fP A) := by
  change GeometricallyConnected (pullback.fst A.X.hom A.X.hom ≫ A.X.hom)
  exact GeometricallyConnected.comp _ _

lemma relativeProjection_fP_app_isIso (T : Over S) (U : T.left.Opens) :
    IsIso (((relativeProjection (fP A)).app T).app U) := by
  change IsIso ((pullback.fst T.hom (fP A)).app U)
  exact smoothProperConnectedGlobalFunctions _ _ (pullback.fst T.hom (fP A))
    inferInstance inferInstance inferInstance U

end Product

section Comparison

variable {S : Scheme.{u}} (A : Langlands.AbelianScheme S)

@[reassoc (attr := simp)]
lemma relativeSection_fst' {X : Scheme.{u}} (f : X ⟶ S) (ε : S ⟶ X) (hε : ε ≫ f = 𝟙 S)
    (T : Over S) : (relativeSection f ε hε).app T ≫ pullback.fst T.hom f = 𝟙 T.left :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma relativeSection_snd' {X : Scheme.{u}} (f : X ⟶ S) (ε : S ⟶ X) (hε : ε ≫ f = 𝟙 S)
    (T : Over S) : (relativeSection f ε hε).app T ≫ pullback.snd T.hom f = T.hom ≫ ε :=
  pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
lemma relativeSpace_map_fst' {X : Scheme.{u}} (f : X ⟶ S) {T U : Over S} (h : T ⟶ U) :
    (relativeSpace f).map h ≫ pullback.fst U.hom f = pullback.fst T.hom f ≫ h.left :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma relativeSpace_map_snd' {X : Scheme.{u}} (f : X ⟶ S) {T U : Over S} (h : T ⟶ U) :
    (relativeSpace f).map h ≫ pullback.snd U.hom f = pullback.snd T.hom f :=
  pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
lemma mumfordSection_fst' (B : Langlands.AbelianScheme S) :
    mumfordSection B ≫ pullback.fst B.X.hom B.X.hom = 𝟙 B.X.left :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma mumfordSection_snd' (B : Langlands.AbelianScheme S) :
    mumfordSection B ≫ pullback.snd B.X.hom B.X.hom = B.X.hom ≫ unitSection B :=
  pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
lemma twoAxisSecond_fst' (B : Langlands.AbelianScheme S) :
    twoAxisSecond B ≫ pullback.fst B.X.hom B.X.hom = B.X.hom ≫ unitSection B :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma twoAxisSecond_snd' (B : Langlands.AbelianScheme S) :
    twoAxisSecond B ≫ pullback.snd B.X.hom B.X.hom = 𝟙 B.X.left :=
  pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
lemma unitSection_comp' (B : Langlands.AbelianScheme S) :
    unitSection B ≫ B.X.hom = 𝟙 S :=
  unitSection_comp B

lemma mumfordSection_fP : mumfordSection A ≫ fP A = A.X.hom := by
  change mumfordSection A ≫ pullback.fst A.X.hom A.X.hom ≫ A.X.hom = A.X.hom
  simp

lemma twoAxisSecond_fP : twoAxisSecond A ≫ fP A = A.X.hom := by
  change twoAxisSecond A ≫ pullback.fst A.X.hom A.X.hom ≫ A.X.hom = A.X.hom
  simp

/-- The self-product of the base change is the base change of the self-product. -/
def productIso (T : Over S) :
    (mumfordProduct (abelian A T)).left ≅ (relativeSpace (fP A)).obj T :=
  mumfordProductBaseChangeIso A T.hom ≪≫ pullbackSymmetry _ _

@[reassoc (attr := simp)]
lemma productIso_hom_fst (T : Over S) :
    (productIso A T).hom ≫ pullback.fst T.hom (fP A) =
      pullback.fst (abelian A T).X.hom (abelian A T).X.hom ≫ (abelian A T).X.hom := by
  change (selfProductBaseChangeIso A.X.hom T.hom).hom ≫ (pullbackSymmetry _ _).hom ≫
    pullback.fst _ _ = _
  rw [pullbackSymmetry_hom_comp_fst]
  exact selfProductBaseChangeIso_hom_snd A.X.hom T.hom

@[reassoc (attr := simp)]
lemma productIso_hom_snd (T : Over S) :
    (productIso A T).hom ≫ pullback.snd T.hom (fP A) = mumfordProductBaseChangeMap A T.hom := by
  change (selfProductBaseChangeIso A.X.hom T.hom).hom ≫ (pullbackSymmetry _ _).hom ≫
    pullback.snd _ _ = _
  rw [pullbackSymmetry_hom_comp_snd]
  exact selfProductBaseChangeIso_hom_fst A.X.hom T.hom

@[reassoc (attr := simp)]
lemma baseChangeMap_fst (T : Over S) :
    mumfordProductBaseChangeMap A T.hom ≫ pullback.fst A.X.hom A.X.hom =
      pullback.fst (abelian A T).X.hom (abelian A T).X.hom ≫ pullback.fst A.X.hom T.hom :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma baseChangeMap_snd (T : Over S) :
    mumfordProductBaseChangeMap A T.hom ≫ pullback.snd A.X.hom A.X.hom =
      pullback.snd (abelian A T).X.hom (abelian A T).X.hom ≫ pullback.fst A.X.hom T.hom :=
  pullback.lift_snd _ _ _

lemma section_productIso (T : Over S) :
    (relativeSection (fP A) (eP A) (eP_comp A)).app T =
      (unitSection (abelian A T) ≫ mumfordSection (abelian A T)) ≫ (productIso A T).hom := by
  apply pullback.hom_ext
  · simp
  · apply pullback.hom_ext <;> simp [eP]

lemma section_productIso_inv (T : Over S) :
    (relativeSection (fP A) (eP A) (eP_comp A)).app T ≫ (productIso A T).inv =
      unitSection (abelian A T) ≫ mumfordSection (abelian A T) := by
  rw [section_productIso]; simp

@[reassoc]
lemma productMap_productIso {T U : Over S} (h : T ⟶ U) :
    productMap A h ≫ (productIso A U).hom =
      (productIso A T).hom ≫ (relativeSpace (fP A)).map h := by
  apply pullback.hom_ext
  · simp
  · simp only [Category.assoc, productIso_hom_snd, relativeSpace_map_snd']
    apply pullback.hom_ext <;> simp

lemma productIso_inv_productMap {T U : Over S} (h : T ⟶ U) :
    (productIso A T).inv ≫ productMap A h =
      (relativeSpace (fP A)).map h ≫ (productIso A U).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, ← productMap_productIso, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

/-- The axis `A_T → (A ×_S A)_T` induced by a section `s` of the first projection. -/
def axis (s : A.X.left ⟶ (mumfordProduct A).left) (hs : s ≫ fP A = A.X.hom) (T : Over S) :
    (relativeSpace A.X.hom).obj T ⟶ (relativeSpace (fP A)).obj T :=
  pullback.map T.hom A.X.hom T.hom (fP A) (𝟙 _) s (𝟙 S) (by simp) (by simp [hs])

variable (s : A.X.left ⟶ (mumfordProduct A).left) (hs : s ≫ fP A = A.X.hom)

@[reassoc (attr := simp)]
lemma axis_fst (T : Over S) :
    axis A s hs T ≫ pullback.fst T.hom (fP A) = pullback.fst T.hom A.X.hom := by
  simp [axis]

@[reassoc (attr := simp)]
lemma axis_snd (T : Over S) :
    axis A s hs T ≫ pullback.snd T.hom (fP A) = pullback.snd T.hom A.X.hom ≫ s := by
  simp [axis]

@[reassoc]
lemma axis_naturality {T U : Over S} (h : T ⟶ U) :
    axis A s hs T ≫ (relativeSpace (fP A)).map h =
      (relativeSpace A.X.hom).map h ≫ axis A s hs U := by
  apply pullback.hom_ext <;> simp

lemma section_axis (hs' : unitSection A ≫ s = eP A) (T : Over S) :
    (relativeSection A.X.hom (unitSection A) (unitSection_comp A)).app T ≫ axis A s hs T =
      𝟙 T.left ≫ (relativeSection (fP A) (eP A) (eP_comp A)).app T := by
  apply pullback.hom_ext
  · simp
  · simp only [Category.assoc, axis_snd, relativeSection_snd'_assoc, relativeSection_snd',
      Category.id_comp]
    rw [hs']

lemma mumfordSection_productIso (T : Over S) :
    mumfordSection (abelian A T) ≫ (productIso A T).hom =
      (pullbackSymmetry A.X.hom T.hom).hom ≫ axis A (mumfordSection A) (mumfordSection_fP A) T := by
  apply pullback.hom_ext
  · simp only [Category.assoc, productIso_hom_fst, mumfordSection_fst'_assoc,
      axis_fst, pullbackSymmetry_hom_comp_fst]
    rfl
  · simp only [Category.assoc, productIso_hom_snd, axis_snd, pullbackSymmetry_hom_comp_snd_assoc]
    apply pullback.hom_ext
    · simp
    · simp only [Category.assoc, baseChangeMap_snd, mumfordSection_snd'_assoc, mumfordSection_snd']
      rw [unit_fst]
      exact (pullback.condition_assoc _).symm

lemma twoAxisSecond_productIso (T : Over S) :
    twoAxisSecond (abelian A T) ≫ (productIso A T).hom =
      (pullbackSymmetry A.X.hom T.hom).hom ≫ axis A (twoAxisSecond A) (twoAxisSecond_fP A) T := by
  apply pullback.hom_ext
  · simp only [Category.assoc, productIso_hom_fst, twoAxisSecond_fst'_assoc,
      axis_fst, pullbackSymmetry_hom_comp_fst, unitSection_comp', Category.comp_id]
    rfl
  · simp only [Category.assoc, productIso_hom_snd, axis_snd, pullbackSymmetry_hom_comp_snd_assoc]
    apply pullback.hom_ext
    · simp only [Category.assoc, baseChangeMap_fst, twoAxisSecond_fst'_assoc,
        twoAxisSecond_fst']
      rw [unit_fst]
      exact (pullback.condition_assoc _).symm
    · simp only [Category.assoc, baseChangeMap_snd, twoAxisSecond_snd'_assoc]
      rw [twoAxisSecond_snd', Category.comp_id]

lemma axis_productIso_inv {T : Over S}
    (s' : (abelian A T).X.left ⟶ (mumfordProduct (abelian A T)).left)
    (h : s' ≫ (productIso A T).hom = (pullbackSymmetry A.X.hom T.hom).hom ≫ axis A s hs T) :
    axis A s hs T ≫ (productIso A T).inv = (pullbackSymmetry A.X.hom T.hom).inv ≫ s' := by
  rw [Iso.comp_inv_eq, Category.assoc, h, Iso.inv_hom_id_assoc]

end Comparison

section Maps

variable {S : Scheme.{u}} (A : Langlands.AbelianScheme S)

lemma relativeProjection_app_isIso' (T : Over S) (U : T.left.Opens) :
    IsIso (((relativeProjection A.X.hom).app T).app U) := by
  change IsIso ((pullback.fst T.hom A.X.hom).app U)
  exact smoothProperConnectedGlobalFunctions _ _ (pullback.fst T.hom A.X.hom)
    inferInstance inferInstance inferInstance U

lemma pb_injective_of_isIso {X Y : Scheme.{u}} (e : X ≅ Y) :
    Function.Injective (pb e.inv) := by
  intro a b h
  have := congrArg (pb e.hom) h
  rwa [LineBundle.pullbackHom_comp, LineBundle.pullbackHom_comp, Iso.hom_inv_id,
    LineBundle.pullbackHom_id, LineBundle.pullbackHom_id] at this

variable (s : A.X.left ⟶ (mumfordProduct A).left) (hs : s ≫ fP A = A.X.hom)
  (hs' : unitSection A ≫ s = eP A)

/-- Pullback of rigidified classes on the self-product along an axis. -/
def axisPullback (T : Over S) :
    RigidifiedLineBundle.Classes (fP A) (eP A) (eP_comp A) T →
      RigidifiedLineBundle.Classes A.X.hom (unitSection A) (unitSection_comp A) T :=
  Quotient.map
    (RigidifiedLineBundle.pullback (axis A s hs T) (𝟙 T.left) (section_axis A s hs hs' T)).obj
    (fun _ _ ⟨e⟩ ↦ ⟨(RigidifiedLineBundle.pullback _ _ _).mapIso e⟩)

lemma carrierClass_axisPullback (T : Over S)
    (c : RigidifiedLineBundle.Classes (fP A) (eP A) (eP_comp A) T) :
    carrierClass A.X.hom (unitSection A) (unitSection_comp A) T (axisPullback A s hs hs' T c) =
      pb (axis A s hs T) (carrierClass (fP A) (eP A) (eP_comp A) T c) := by
  induction c using Quotient.inductionOn with | h L => rfl

lemma axisPullback_map {T U : Over S} (h : T ⟶ U)
    (g : (RigidifiedLineBundle.classPresheaf RigidifiedModule.pullbackCoherence (fP A) (eP A)
      (eP_comp A)).obj (op U)) :
    axisPullback A s hs hs' T
        ((RigidifiedLineBundle.classPresheaf RigidifiedModule.pullbackCoherence (fP A) (eP A)
          (eP_comp A)).map h.op g) =
      (RigidifiedLineBundle.classPresheaf RigidifiedModule.pullbackCoherence A.X.hom
        (unitSection A) (unitSection_comp A)).map h.op (axisPullback A s hs hs' U g) := by
  apply carrierClass_injective A.X.hom (unitSection A) (unitSection_comp A) T
  rw [carrierClass_map, carrierClass_axisPullback, carrierClass_axisPullback, carrierClass_map,
    LineBundle.pullbackHom_comp, LineBundle.pullbackHom_comp, axis_naturality]

/-- The trivial rigidified class on the abelian scheme. -/
def unitClass (T : Over S) :
    RigidifiedLineBundle.Classes A.X.hom (unitSection A) (unitSection_comp A) T :=
  Quotient.mk _ (RigidifiedLineBundle.trivial
    ((relativeSection A.X.hom (unitSection A) (unitSection_comp A)).app T))

lemma carrierClass_unitClass (T : Over S) :
    carrierClass A.X.hom (unitSection A) (unitSection_comp A) T (unitClass A T) = 1 :=
  rfl

lemma unitClass_map {T U : Over S} (h : T ⟶ U) :
    (RigidifiedLineBundle.classPresheaf RigidifiedModule.pullbackCoherence A.X.hom
        (unitSection A) (unitSection_comp A)).map h.op (unitClass A U) = unitClass A T := by
  apply carrierClass_injective A.X.hom (unitSection A) (unitSection_comp A) T
  rw [carrierClass_map, carrierClass_unitClass, carrierClass_unitClass, map_one]

lemma toProduct_aux (T : Over S) (c : TwoAxisRigidifiedLineBundle.Classes A T) :
    pb ((relativeSection (fP A) (eP A) (eP_comp A)).app T)
      (pb (productIso A T).inv (twoAxisCarrierClass (abelian A T) c)) = 1 := by
  rw [LineBundle.pullbackHom_comp, section_productIso_inv, ← LineBundle.pullbackHom_comp,
    twoAxisCarrierClass_first, map_one]

/-- The comparison map from two-axis classes to one-section classes on the self-product. -/
def toProduct (T : Over S) (c : TwoAxisRigidifiedLineBundle.Classes A T) :
    RigidifiedLineBundle.Classes (fP A) (eP A) (eP_comp A) T :=
  Classical.choose (exists_carrierClass_eq (fP A) (eP A) (eP_comp A) T _ (toProduct_aux A T c))

lemma carrierClass_toProduct (T : Over S) (c : TwoAxisRigidifiedLineBundle.Classes A T) :
    carrierClass (fP A) (eP A) (eP_comp A) T (toProduct A T c) =
      pb (productIso A T).inv (twoAxisCarrierClass (abelian A T) c) :=
  Classical.choose_spec
    (exists_carrierClass_eq (fP A) (eP A) (eP_comp A) T _ (toProduct_aux A T c))

lemma twoAxisCarrierClass_map {T U : Over S} (h : T ⟶ U)
    (c : TwoAxisRigidifiedLineBundle.Classes A U) :
    twoAxisCarrierClass (abelian A T) (TwoAxisRigidifiedLineBundle.classesPullback A h c) =
      pb (productMap A h) (twoAxisCarrierClass (abelian A U) c) := by
  induction c using Quotient.inductionOn with | h L => rfl

lemma toProduct_map {T U : Over S} (h : T ⟶ U)
    (x : (TwoAxisRigidifiedLineBundle.classPresheaf A).obj (op U)) :
    toProduct A T ((TwoAxisRigidifiedLineBundle.classPresheaf A).map h.op x) =
      (RigidifiedLineBundle.classPresheaf RigidifiedModule.pullbackCoherence (fP A) (eP A)
        (eP_comp A)).map h.op (toProduct A U x) := by
  apply carrierClass_injective (fP A) (eP A) (eP_comp A) T
  rw [carrierClass_map, carrierClass_toProduct, carrierClass_toProduct]
  change pb (productIso A T).inv (twoAxisCarrierClass (abelian A T)
    (TwoAxisRigidifiedLineBundle.classesPullback A h x)) = _
  rw [twoAxisCarrierClass_map, LineBundle.pullbackHom_comp, LineBundle.pullbackHom_comp,
    productIso_inv_productMap]

lemma toProduct_injective (T : Over S) : Function.Injective (toProduct A T) := by
  intro c d h
  have := congrArg (carrierClass (fP A) (eP A) (eP_comp A) T) h
  rw [carrierClass_toProduct, carrierClass_toProduct] at this
  exact twoAxisCarrierClass_injective _ (pb_injective_of_isIso (productIso A T) this)

lemma axisPullback_toProduct {T : Over S}
    (s' : (abelian A T).X.left ⟶ (mumfordProduct (abelian A T)).left)
    (hs'' : s' ≫ (productIso A T).hom =
      (pullbackSymmetry A.X.hom T.hom).hom ≫ axis A s hs T)
    (h₁ : ∀ c, pb s' (twoAxisCarrierClass (abelian A T) c) = 1)
    (c : TwoAxisRigidifiedLineBundle.Classes A T) :
    axisPullback A s hs hs' T (toProduct A T c) = unitClass A T := by
  apply carrierClass_injective A.X.hom (unitSection A) (unitSection_comp A) T
  rw [carrierClass_axisPullback, carrierClass_toProduct, carrierClass_unitClass,
    LineBundle.pullbackHom_comp, axis_productIso_inv A s hs s' hs'',
    ← LineBundle.pullbackHom_comp]
  exact (congrArg (pb _) (h₁ c)).trans (map_one _)

lemma axisPullback_eq_unitClass {T : Over S}
    (s' : (abelian A T).X.left ⟶ (mumfordProduct (abelian A T)).left)
    (hs'' : s' ≫ (productIso A T).hom =
      (pullbackSymmetry A.X.hom T.hom).hom ≫ axis A s hs T)
    (g : RigidifiedLineBundle.Classes (fP A) (eP A) (eP_comp A) T)
    (hg : axisPullback A s hs hs' T g = unitClass A T) :
    pb s' (pb (productIso A T).hom (carrierClass (fP A) (eP A) (eP_comp A) T g)) = 1 := by
  have := congrArg (carrierClass A.X.hom (unitSection A) (unitSection_comp A) T) hg
  rw [carrierClass_axisPullback, carrierClass_unitClass] at this
  rw [LineBundle.pullbackHom_comp, hs'', ← LineBundle.pullbackHom_comp]
  exact (congrArg (pb _) this).trans (map_one _)

lemma exists_toProduct_eq (T : Over S)
    (g : RigidifiedLineBundle.Classes (fP A) (eP A) (eP_comp A) T)
    (h₁ : axisPullback A (mumfordSection A) (mumfordSection_fP A) rfl T g = unitClass A T)
    (h₂ : axisPullback A (twoAxisSecond A) (twoAxisSecond_fP A) (twoAxis_unit_comp A).symm T g =
      unitClass A T) :
    ∃ c, toProduct A T c = g := by
  obtain ⟨c, hc⟩ := exists_twoAxisCarrierClass_eq (abelian A T)
    (pb (productIso A T).hom (carrierClass (fP A) (eP A) (eP_comp A) T g))
    (axisPullback_eq_unitClass A _ _ _ _ (mumfordSection_productIso A T) g h₁)
    (axisPullback_eq_unitClass A _ _ _ _ (twoAxisSecond_productIso A T) g h₂)
  refine ⟨c, carrierClass_injective (fP A) (eP A) (eP_comp A) T ?_⟩
  rw [carrierClass_toProduct, hc, LineBundle.pullbackHom_comp, Iso.inv_hom_id,
    LineBundle.pullbackHom_id]

end Maps

end Langlands.AlgebraicGeometry.Picard.TwoAxisClassFpqc

namespace Langlands.AlgebraicGeometry.Picard.TwoAxisRigidifiedLineBundle

open Langlands.AbelianScheme TwoAxisFamily Langlands.SchemeModule TwoAxisClassFpqc

variable {S : Scheme.{u}} (A : Langlands.AbelianScheme S)

/-- **The two-axis class presheaf is an fpqc sheaf.** For an abelian scheme `A` over `S`, the
presheaf of isomorphism classes of two-axis-rigidified line bundles on the base-changed
self-products is a sheaf for the fpqc topology on `Over S`. -/
theorem classPresheaf_isSheaf_fpqc :
    Presieve.IsSheaf (Scheme.fpqcTopology.over S) (classPresheaf A) := by
  have hG := RigidifiedLineBundle.classPresheaf_isSheaf_fpqc (fP A) (eP A) (eP_comp A)
    (relativeProjection_fP_app_isIso A)
  have hH := RigidifiedLineBundle.classPresheaf_isSheaf_fpqc A.X.hom (unitSection A)
    (unitSection_comp A) (relativeProjection_app_isIso' A)
  intro T R hR
  exact isSheafFor_of_injective (toProduct A) (toProduct_map A) (toProduct_injective A)
    (axisPullback A (mumfordSection A) (mumfordSection_fP A) rfl)
    (axisPullback A (twoAxisSecond A) (twoAxisSecond_fP A) (twoAxis_unit_comp A).symm)
    (axisPullback_map A _ _ _) (axisPullback_map A _ _ _)
    (unitClass A) (unitClass_map A)
    (fun T' c ↦ axisPullback_toProduct A _ _ _ _ (mumfordSection_productIso A T')
      (twoAxisCarrierClass_first _) c)
    (fun T' c ↦ axisPullback_toProduct A _ _ _ _ (twoAxisSecond_productIso A T')
      (twoAxisCarrierClass_second _) c)
    (exists_toProduct_eq A) (hG R hR) (hH R hR).isSeparatedFor

end Langlands.AlgebraicGeometry.Picard.TwoAxisRigidifiedLineBundle

namespace Langlands.AlgebraicGeometry.UnramifiedFunctor

variable {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type*}

/-- An fpqc sheaf on `Over S` satisfies Murre's condition (F1a). -/
lemma zariskiSheaf_of_isSheaf_fpqc (hF : Presieve.IsSheaf (Scheme.fpqcTopology.over S) F) :
    ZariskiSheaf F := by
  intro T 𝒰
  rw [Presieve.isSheafFor_iff_generate]
  apply hF
  rw [GrothendieckTopology.mem_over_iff]
  change Sieve.overEquiv _ (Sieve.ofArrows _ _) ∈ _
  rw [Sieve.overEquiv_ofArrows]
  exact Scheme.zariskiTopology_le_fpqcTopology _ (Scheme.Cover.mem_grothendieckTopology 𝒰)

/-- An fpqc sheaf on `Over S` satisfies Murre's condition (F1b). -/
lemma faithfullyFlatSheaf_of_isSheaf_fpqc
    (hF : Presieve.IsSheaf (Scheme.fpqcTopology.over S) F) :
    FaithfullyFlatSheaf F := by
  intro T' T g h₁ h₂ h₃
  rw [Presieve.isSheafFor_iff_generate]
  apply hF
  rw [GrothendieckTopology.mem_over_iff, ← Presieve.ofArrows_pUnit.{0}]
  change Sieve.overEquiv _ (Sieve.ofArrows _ _) ∈ _
  rw [Sieve.overEquiv_ofArrows]
  change Sieve.generate (Presieve.ofArrows (fun _ : PUnit.{1} ↦ T'.left) (fun _ ↦ g.left)) ∈ _
  rw [Presieve.ofArrows_pUnit]
  exact Precoverage.generate_mem_toGrothendieck (Scheme.Hom.singleton_mem_fpqcPrecoverage g.left)

end Langlands.AlgebraicGeometry.UnramifiedFunctor
