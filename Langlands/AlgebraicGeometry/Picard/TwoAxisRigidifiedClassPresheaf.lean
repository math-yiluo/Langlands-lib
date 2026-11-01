import Langlands.AlgebraicGeometry.Picard.TwoAxisRigidifiedLineBundle
import Langlands.AbelianScheme.LieBaseChange

/-! # The presheaf of compatible two-axis-rigidified line-bundle classes -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Picard

namespace TwoAxisFamily

open Langlands.AbelianScheme

variable {S : Scheme.{u}} (A : Langlands.AbelianScheme S)

/-- The actual abelian scheme after the chosen test-scheme base change. -/
abbrev abelian (T : Over S) := (baseChange T.hom).obj A

/-- The map between the actual carriers of two direct base changes. -/
def carrierMap {T U : Over S} (h : T ⟶ U) :
    (abelian A T).X.left ⟶ (abelian A U).X.left :=
  pullback.lift (pullback.fst A.X.hom T.hom)
    (pullback.snd A.X.hom T.hom ≫ h.left) (by
      rw [Category.assoc, Over.w h]
      exact pullback.condition)

@[reassoc (attr := simp)]
lemma carrierMap_fst {T U : Over S} (h : T ⟶ U) :
    carrierMap A h ≫ pullback.fst A.X.hom U.hom = pullback.fst A.X.hom T.hom :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma carrierMap_snd {T U : Over S} (h : T ⟶ U) :
    carrierMap A h ≫ (abelian A U).X.hom = (abelian A T).X.hom ≫ h.left :=
  pullback.lift_snd _ _ _

@[simp]
lemma carrierMap_id (T : Over S) : carrierMap A (𝟙 T) = 𝟙 (abelian A T).X.left := by
  apply pullback.hom_ext
  · simp
  · change carrierMap A (𝟙 T) ≫ (abelian A T).X.hom =
      𝟙 (abelian A T).X.left ≫ (abelian A T).X.hom
    simp

@[simp]
lemma carrierMap_comp {T U V : Over S} (h : T ⟶ U) (k : U ⟶ V) :
    carrierMap A (h ≫ k) = carrierMap A h ≫ carrierMap A k := by
  apply pullback.hom_ext
  · simp
  · change carrierMap A (h ≫ k) ≫ (abelian A V).X.hom =
      (carrierMap A h ≫ carrierMap A k) ≫ (abelian A V).X.hom
    simp [Category.assoc]

/-- The functor whose objects are the actual base-changed carrier schemes. -/
def carrier : Over S ⥤ Scheme.{u} where
  obj T := (abelian A T).X.left
  map h := carrierMap A h
  map_id := carrierMap_id A
  map_comp := carrierMap_comp A

@[reassoc (attr := simp)]
lemma unit_fst (T : Over S) :
    unitSection (abelian A T) ≫ pullback.fst A.X.hom T.hom =
      T.hom ≫ unitSection A := by
  exact Langlands.GroupScheme.identitySection_baseChange_fst T.hom A.toGrp

/-- The actual unit sections commute with every test-scheme map. -/
@[reassoc]
lemma unit_naturality {T U : Over S} (h : T ⟶ U) :
    unitSection (abelian A T) ≫ carrierMap A h =
      h.left ≫ unitSection (abelian A U) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, carrierMap_fst, unit_fst, Over.w_assoc]
  · change (unitSection (abelian A T) ≫ carrierMap A h) ≫ (abelian A U).X.hom =
      (h.left ≫ unitSection (abelian A U)) ≫ (abelian A U).X.hom
    rw [Category.assoc, carrierMap_snd, ← Category.assoc, unitSection_comp,
      Category.id_comp, Category.assoc, unitSection_comp, Category.comp_id]

/-- The map on the actual self-products of the direct base changes. -/
def productMap {T U : Over S} (h : T ⟶ U) :
    (mumfordProduct (abelian A T)).left ⟶ (mumfordProduct (abelian A U)).left :=
  pullback.lift
    (pullback.fst (abelian A T).X.hom (abelian A T).X.hom ≫ carrierMap A h)
    (pullback.snd (abelian A T).X.hom (abelian A T).X.hom ≫ carrierMap A h) (by
      simp only [Category.assoc, carrierMap_snd]
      exact pullback.condition_assoc h.left)

@[reassoc (attr := simp)]
lemma productMap_fst {T U : Over S} (h : T ⟶ U) :
    productMap A h ≫ pullback.fst (abelian A U).X.hom (abelian A U).X.hom =
      pullback.fst (abelian A T).X.hom (abelian A T).X.hom ≫ carrierMap A h :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma productMap_snd {T U : Over S} (h : T ⟶ U) :
    productMap A h ≫ pullback.snd (abelian A U).X.hom (abelian A U).X.hom =
      pullback.snd (abelian A T).X.hom (abelian A T).X.hom ≫ carrierMap A h :=
  pullback.lift_snd _ _ _

@[simp]
lemma productMap_id (T : Over S) :
    productMap A (𝟙 T) = 𝟙 (mumfordProduct (abelian A T)).left := by
  apply pullback.hom_ext <;> simp

@[simp]
lemma productMap_comp {T U V : Over S} (h : T ⟶ U) (k : U ⟶ V) :
    productMap A (h ≫ k) = productMap A h ≫ productMap A k := by
  apply pullback.hom_ext <;> simp [Category.assoc]

/-- The functor of actual self-products after test-scheme base change. -/
def product : Over S ⥤ Scheme.{u} where
  obj T := (mumfordProduct (abelian A T)).left
  map h := productMap A h
  map_id := productMap_id A
  map_comp := productMap_comp A

/-- The first actual unit axes commute with test-scheme maps. -/
@[reassoc]
lemma first_naturality {T U : Over S} (h : T ⟶ U) :
    mumfordSection (abelian A T) ≫ productMap A h =
      carrierMap A h ≫ mumfordSection (abelian A U) := by
  apply pullback.hom_ext
  · simp only [mumfordSection, relativeSection, Category.assoc, productMap_fst,
      pullback.lift_fst, pullback.lift_fst_assoc, Category.id_comp, Category.comp_id]
  · simp only [Category.assoc, productMap_snd, pullback.lift_snd_assoc,
      mumfordSection, relativeSection, pullback.lift_snd]
    simp only [unit_naturality, carrierMap_snd_assoc]

/-- The second actual unit axes commute with test-scheme maps. -/
@[reassoc]
lemma second_naturality {T U : Over S} (h : T ⟶ U) :
    twoAxisSecond (abelian A T) ≫ productMap A h =
      carrierMap A h ≫ twoAxisSecond (abelian A U) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, productMap_fst, twoAxisSecond, pullback.lift_fst,
      pullback.lift_fst_assoc]
    simp only [unit_naturality, carrierMap_snd_assoc]
  · simp only [twoAxisSecond, Category.assoc, productMap_snd, pullback.lift_snd,
      pullback.lift_snd_assoc, Category.id_comp, Category.comp_id]

end TwoAxisFamily

namespace TwoAxisRigidifiedLineBundle

open Langlands.AbelianScheme TwoAxisFamily

variable {S : Scheme.{u}} (A : Langlands.AbelianScheme S)

/-- Actual line bundles on the actual base-changed self-product, with compatible
trivializations along its two unit axes. -/
abbrev relative (T : Over S) :=
  TwoAxisRigidifiedLineBundle (unitSection (abelian A T)) (unitSection (abelian A T))
    (mumfordSection (abelian A T)) (twoAxisSecond (abelian A T))
    (twoAxis_unit_comp (abelian A T))

/-- Canonical pullback for every morphism of test schemes over the original base. -/
def relativePullback {T U : Over S} (h : T ⟶ U) :
    relative A U ⥤ relative A T :=
  pullback (productMap A h) (carrierMap A h) (carrierMap A h) h.left
    (first_naturality A h) (second_naturality A h)
    (unit_naturality A h) (unit_naturality A h)

/-- Pullback by an identity test map is naturally isomorphic to the identity. -/
def relativePullbackId (T : Over S) :
    relativePullback A (𝟙 T) ≅ 𝟭 (relative A T) :=
  pullbackCongr (productMap_id A T) (carrierMap_id A T) (carrierMap_id A T) rfl
    _ _ _ _ _ _ _ _ ≪≫ pullbackId _ _ _ _ _

/-- Iterated pullback is naturally isomorphic to pullback by the composite test map. -/
def relativePullbackComp {T U V : Over S} (h : T ⟶ U) (k : U ⟶ V) :
    relativePullback A k ⋙ relativePullback A h ≅ relativePullback A (h ≫ k) :=
  pullbackComp (productMap A k) (carrierMap A k) (carrierMap A k) k.left
    (productMap A h) (carrierMap A h) (carrierMap A h) h.left
    _ _ _ _ _ _ _ _
    (by rw [← productMap_comp, ← carrierMap_comp]; exact first_naturality A (h ≫ k))
    (by rw [← productMap_comp, ← carrierMap_comp]; exact second_naturality A (h ≫ k))
    (by rw [← carrierMap_comp]; exact unit_naturality A (h ≫ k))
    (by rw [← carrierMap_comp]; exact unit_naturality A (h ≫ k)) ≪≫
      pullbackCongr (productMap_comp A h k).symm (carrierMap_comp A h k).symm
        (carrierMap_comp A h k).symm rfl _ _ _ _ _ _ _ _

/-- Isomorphism classes preserve the actual line bundle and both chosen compatible
trivializations as the data of a representative. -/
abbrev Classes (T : Over S) :=
  Quotient (isIsomorphicSetoid (relative A T))

/-- Pullback on classes is induced by the actual compatible pullback functor. -/
def classesPullback {T U : Over S} (h : T ⟶ U) :
    Classes A U → Classes A T :=
  Quotient.map (relativePullback A h).obj
    (fun _ _ ⟨e⟩ ↦ ⟨(relativePullback A h).mapIso e⟩)

/-- The unconditional presheaf of compatible two-axis-rigidified line-bundle classes. -/
def classPresheaf : (Over S)ᵒᵖ ⥤ Type (u + 1) where
  obj T := Classes A T.unop
  map h := TypeCat.ofHom (classesPullback A h.unop)
  map_id T := by
    ext q
    refine Quotient.inductionOn q (fun L ↦ ?_)
    exact Quotient.sound ⟨(relativePullbackId A T.unop).app L⟩
  map_comp h k := by
    ext q
    refine Quotient.inductionOn q (fun L ↦ ?_)
    exact Quotient.sound ⟨((relativePullbackComp A k.unop h.unop).app L).symm⟩

end TwoAxisRigidifiedLineBundle

end Langlands.AlgebraicGeometry.Picard
