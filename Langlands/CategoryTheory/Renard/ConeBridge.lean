import Mathlib.CategoryTheory.IsConnected
import Mathlib.CategoryTheory.Limits.IsLimit

/-!
# Renard's general cone and cocone definitions

The concrete universal property after Renard (A.IV.1.2) works for every index
category. Connectedness repairs only the preliminary constant-transformation
claim. See the paired Markdown for the original source and arrow corrections.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Langlands.CategoryTheory.Renard

universe vJ vC uJ uC

/-- Renard's diagonal functor is Mathlib's actual constant-functor functor. -/
abbrev diagonal (J : Type uJ) [Category.{vJ} J] (C : Type uC) [Category.{vC} C] :
    C ⥤ J ⥤ C := Functor.const J

variable {J : Type uJ} [Category.{vJ} J] {C : Type uC} [Category.{vC} C]

@[simp] theorem diagonal_obj_obj (X : C) (j : J) :
    ((diagonal J C).obj X).obj j = X := rfl

@[simp] theorem diagonal_obj_map (X : C) {i j : J} (f : i ⟶ j) :
    ((diagonal J C).obj X).map f = 𝟙 X := rfl

@[simp] theorem diagonal_map_app {X Y : C} (f : X ⟶ Y) (j : J) :
    ((diagonal J C).map f).app j = f := rfl

/-- Nonemptiness gives faithfulness, as in Mathlib. -/
theorem diagonal_faithful [Nonempty J] : (diagonal J C).Faithful := inferInstance

/-- Connectedness gives the fullness missing from the source's preliminary claim. -/
theorem diagonal_full [IsConnected J] : (diagonal J C).Full := inferInstance

/-- The corrected auxiliary Hom correspondence, restricted to connected indices. -/
def connectedConstantHomEquiv [IsConnected J] (X Y : C) :
    (X ⟶ Y) ≃ ((diagonal J C).obj X ⟶ (diagonal J C).obj Y) :=
  (Functor.FullyFaithful.ofFullyFaithful (diagonal J C)).homEquiv

@[simp] theorem connectedConstantHomEquiv_apply_app [IsConnected J]
    {X Y : C} (f : X ⟶ Y) (j : J) :
    (connectedConstantHomEquiv (J := J) X Y f).app j = f := rfl

@[simp] theorem connectedConstantHomEquiv_symm_eq_app [IsConnected J]
    {X Y : C} (α : (diagonal J C).obj X ⟶ (diagonal J C).obj Y) (j : J) :
    (connectedConstantHomEquiv X Y).symm α = α.app j :=
  NatTrans.congr_app ((connectedConstantHomEquiv X Y).apply_symm_apply α) j

/-- Naturality forces components to agree on a preconnected index. -/
theorem constant_components_eq [IsPreconnected J] {X Y : C}
    (α : (diagonal J C).obj X ⟶ (diagonal J C).obj Y) (i j : J) :
    α.app i = α.app j := nat_trans_from_is_connected α i j

variable {D : J ⥤ C}

/-- The concrete unique factorization after (A.IV.1.2), with its vertex retained. -/
def ConeUniversal (t : Cone D) : Prop :=
  ∀ s : Cone D, ∃! f : s.pt ⟶ t.pt, ∀ j : J, f ≫ t.π.app j = s.π.app j

/-- The dual concrete unique factorization for A.IV.2. -/
def CoconeUniversal (t : Cocone D) : Prop :=
  ∀ s : Cocone D, ∃! f : t.pt ⟶ s.pt, ∀ j : J, t.ι.app j ≫ f = s.ι.app j

/-- Construct the actual limit witness directly from concrete unique factorization. -/
def isLimitOfConeUniversal {t : Cone D} (h : ConeUniversal t) : IsLimit t :=
  IsLimit.ofExistsUnique h

/-- Construct the actual colimit witness directly from concrete unique factorization. -/
def isColimitOfCoconeUniversal {t : Cocone D} (h : CoconeUniversal t) : IsColimit t :=
  IsColimit.ofExistsUnique h

theorem coneUniversal_of_isLimit {t : Cone D} (h : IsLimit t) : ConeUniversal t :=
  h.existsUnique

theorem coconeUniversal_of_isColimit {t : Cocone D} (h : IsColimit t) : CoconeUniversal t :=
  h.existsUnique

theorem coneUniversal_iff_nonempty_isLimit (t : Cone D) :
    ConeUniversal t ↔ Nonempty (IsLimit t) :=
  ⟨fun h => ⟨isLimitOfConeUniversal h⟩, fun ⟨h⟩ => coneUniversal_of_isLimit h⟩

theorem coconeUniversal_iff_nonempty_isColimit (t : Cocone D) :
    CoconeUniversal t ↔ Nonempty (IsColimit t) :=
  ⟨fun h => ⟨isColimitOfCoconeUniversal h⟩, fun ⟨h⟩ => coconeUniversal_of_isColimit h⟩

/-- The actual Hom equivalence of (A.IV.1.1), without an index restriction. -/
abbrev limitHomEquiv {t : Cone D} (h : IsLimit t) (Y : C) :
    (Y ⟶ t.pt) ≃ ((diagonal J C).obj Y ⟶ D) := h.homEquiv

/-- The dual actual Hom equivalence, without an index restriction. -/
abbrev colimitHomEquiv {t : Cocone D} (h : IsColimit t) (Y : C) :
    (t.pt ⟶ Y) ≃ (D ⟶ (diagonal J C).obj Y) := h.homEquiv

@[simp] theorem limitHomEquiv_apply_app {t : Cone D} (h : IsLimit t)
    {Y : C} (f : Y ⟶ t.pt) (j : J) :
    (limitHomEquiv h Y f).app j = f ≫ t.π.app j := rfl

@[simp] theorem colimitHomEquiv_apply_app {t : Cocone D} (h : IsColimit t)
    {Y : C} (f : t.pt ⟶ Y) (j : J) :
    (colimitHomEquiv h Y f).app j = t.ι.app j ≫ f := rfl

@[simp] theorem limitHomEquiv_symm_app {t : Cone D} (h : IsLimit t)
    {Y : C} (α : (diagonal J C).obj Y ⟶ D) (j : J) :
    (limitHomEquiv h Y).symm α ≫ t.π.app j = α.app j :=
  h.homEquiv_symm_π_app α j

@[simp] theorem colimitHomEquiv_symm_app {t : Cocone D} (h : IsColimit t)
    {Y : C} (α : D ⟶ (diagonal J C).obj Y) (j : J) :
    t.ι.app j ≫ (colimitHomEquiv h Y).symm α = α.app j :=
  h.ι_app_homEquiv_symm α j

theorem limitHomEquiv_naturality {t : Cone D} (h : IsLimit t)
    {Y Z : C} (g : Z ⟶ Y) (f : Y ⟶ t.pt) :
    limitHomEquiv h Z (g ≫ f) = (diagonal J C).map g ≫ limitHomEquiv h Y f := by
  ext j
  exact Category.assoc g f (t.π.app j)

theorem colimitHomEquiv_naturality {t : Cocone D} (h : IsColimit t)
    {Y Z : C} (f : t.pt ⟶ Y) (g : Y ⟶ Z) :
    colimitHomEquiv h Z (f ≫ g) = colimitHomEquiv h Y f ≫ (diagonal J C).map g := by
  ext j
  exact (Category.assoc (t.ι.app j) f g).symm

theorem limitHomEquiv_symm_naturality {t : Cone D} (h : IsLimit t)
    {Y Z : C} (α : (diagonal J C).obj Y ⟶ D) (g : Z ⟶ Y) :
    (limitHomEquiv h Z).symm ((diagonal J C).map g ≫ α) =
      g ≫ (limitHomEquiv h Y).symm α := h.homEquiv_symm_naturality α g

theorem colimitHomEquiv_symm_naturality {t : Cocone D} (h : IsColimit t)
    {Y Z : C} (α : D ⟶ (diagonal J C).obj Y) (g : Y ⟶ Z) :
    (colimitHomEquiv h Z).symm (α ≫ (diagonal J C).map g) =
      (colimitHomEquiv h Y).symm α ≫ g := h.homEquiv_symm_naturality α g

/-- The natural form of (A.IV.1.1), with the necessary universe lift. -/
abbrev limitNatIso {t : Cone D} (h : IsLimit t) :
    yoneda.obj t.pt ⋙ uliftFunctor.{uJ} ≅ D.cones := h.natIso

/-- The natural dual, with the same necessary universe lift. -/
abbrev colimitNatIso {t : Cocone D} (h : IsColimit t) :
    coyoneda.obj (op t.pt) ⋙ uliftFunctor.{uJ} ≅ D.cocones := h.natIso

@[simp] theorem limitNatIso_hom_app {t : Cone D} (h : IsLimit t)
    (Y : C) (f : ULift.{uJ} (Y ⟶ t.pt)) (j : J) :
    ((limitNatIso h).hom.app (op Y) f).app j = f.down ≫ t.π.app j := rfl

@[simp] theorem colimitNatIso_hom_app {t : Cocone D} (h : IsColimit t)
    (Y : C) (f : ULift.{uJ} (t.pt ⟶ Y)) (j : J) :
    ((colimitNatIso h).hom.app Y f).app j = t.ι.app j ≫ f.down := rfl

/-- Canonical isomorphism in the actual category of cones. -/
abbrev limitConeIso {s t : Cone D} (h : IsLimit s) (k : IsLimit t) : s ≅ t :=
  h.uniqueUpToIso k

/-- Canonical isomorphism in the actual category of cocones. -/
abbrev colimitCoconeIso {s t : Cocone D} (h : IsColimit s) (k : IsColimit t) : s ≅ t :=
  h.uniqueUpToIso k

abbrev limitPointIso {s t : Cone D} (h : IsLimit s) (k : IsLimit t) : s.pt ≅ t.pt :=
  h.conePointUniqueUpToIso k

abbrev colimitPointIso {s t : Cocone D} (h : IsColimit s) (k : IsColimit t) : s.pt ≅ t.pt :=
  h.coconePointUniqueUpToIso k

@[simp] theorem limitPointIso_hom_comp {s t : Cone D}
    (h : IsLimit s) (k : IsLimit t) (j : J) :
    (limitPointIso h k).hom ≫ t.π.app j = s.π.app j :=
  h.conePointUniqueUpToIso_hom_comp k j

@[simp] theorem limitPointIso_inv_comp {s t : Cone D}
    (h : IsLimit s) (k : IsLimit t) (j : J) :
    (limitPointIso h k).inv ≫ s.π.app j = t.π.app j :=
  h.conePointUniqueUpToIso_inv_comp k j

@[simp] theorem comp_colimitPointIso_hom {s t : Cocone D}
    (h : IsColimit s) (k : IsColimit t) (j : J) :
    s.ι.app j ≫ (colimitPointIso h k).hom = t.ι.app j :=
  h.comp_coconePointUniqueUpToIso_hom k j

@[simp] theorem comp_colimitPointIso_inv {s t : Cocone D}
    (h : IsColimit s) (k : IsColimit t) (j : J) :
    t.ι.app j ≫ (colimitPointIso h k).inv = s.ι.app j :=
  h.comp_coconePointUniqueUpToIso_inv k j

/-- A vertex isomorphism preserving all cone legs is the canonical one. -/
theorem limitPointIso_eq {s t : Cone D} (h : IsLimit s) (k : IsLimit t)
    (e : s.pt ≅ t.pt) (he : ∀ j, e.hom ≫ t.π.app j = s.π.app j) :
    e = limitPointIso h k := Iso.ext (k.uniq s e.hom he)

/-- A vertex isomorphism preserving all cocone legs is the canonical one. -/
theorem colimitPointIso_eq {s t : Cocone D} (h : IsColimit s) (k : IsColimit t)
    (e : s.pt ≅ t.pt) (he : ∀ j, s.ι.app j ≫ e.hom = t.ι.app j) :
    e = colimitPointIso h k := Iso.ext (h.uniq t e.hom he)

section Counterexample

/-- The explicit two-object discrete index used in the source correction. -/
abbrev TwoPointIndex := Discrete Bool

/-- Its components send the singleton to false and true respectively. -/
def twoPointTransformation :
    (diagonal TwoPointIndex (Type 0)).obj PUnit ⟶
      (diagonal TwoPointIndex (Type 0)).obj Bool :=
  Discrete.natTrans (fun j => ↾fun _ => j.as)

@[simp] theorem twoPointTransformation_app (b : Bool) (x : PUnit) :
    twoPointTransformation.app (Discrete.mk b) x = b := rfl

/-- Intrinsic failure of surjectivity for this explicit transformation. -/
theorem twoPointTransformation_not_diagonal :
    ¬ ∃ f : PUnit ⟶ Bool,
      (diagonal TwoPointIndex (Type 0)).map f = twoPointTransformation := by
  rintro ⟨f, hf⟩
  have hfalse : f PUnit.unit = false :=
    ConcreteCategory.congr_hom (NatTrans.congr_app hf (Discrete.mk false)) PUnit.unit
  have htrue : f PUnit.unit = true :=
    ConcreteCategory.congr_hom (NatTrans.congr_app hf (Discrete.mk true)) PUnit.unit
  exact Bool.false_ne_true (hfalse.symm.trans htrue)

/-- A two-object index is nonempty, so nonemptiness cannot repair fullness. -/
theorem twoPointIndex_nonempty : Nonempty TwoPointIndex := ⟨Discrete.mk false⟩

end Counterexample

section EmptyIndex

abbrev EmptyIndex := Discrete PEmpty

/-- Empty constant functors cannot recover even these distinct named vertices. -/
theorem empty_constant_functors_eq :
    (diagonal EmptyIndex (Type 0)).obj PUnit =
      (diagonal EmptyIndex (Type 0)).obj Bool := by
  apply CategoryTheory.Functor.ext
  all_goals
    intro j
    exact PEmpty.elim j.as

/-- The named vertices in the preceding equality really are different. -/
theorem punit_ne_bool : (PUnit : Type 0) ≠ Bool := by
  intro h
  have hs : Subsingleton Bool := h ▸ (inferInstance : Subsingleton PUnit)
  exact Bool.false_ne_true (hs.elim false true)

/-- Empty cone data retain the supplied vertex as an actual field. -/
def emptyCone (X : Type 0) : Cone ((diagonal EmptyIndex (Type 0)).obj PUnit) where
  pt := X
  π := Discrete.natTrans (fun j => PEmpty.elim j.as)

/-- Empty cocone data also retain the supplied vertex. -/
def emptyCocone (X : Type 0) : Cocone ((diagonal EmptyIndex (Type 0)).obj PUnit) where
  pt := X
  ι := Discrete.natTrans (fun j => PEmpty.elim j.as)

@[simp] theorem emptyCone_pt (X : Type 0) : (emptyCone X).pt = X := rfl
@[simp] theorem emptyCocone_pt (X : Type 0) : (emptyCocone X).pt = X := rfl

theorem emptyCone_vertices_differ : (emptyCone PUnit).pt ≠ (emptyCone Bool).pt := punit_ne_bool

theorem emptyCocone_vertices_differ :
    (emptyCocone PUnit).pt ≠ (emptyCocone Bool).pt := punit_ne_bool

end EmptyIndex

section ScopeConsumers

/-- A small limiting cone in Type for an arbitrary index, including an empty one. -/
def singletonCone (J : Type uJ) [Category.{vJ} J] :
    Cone ((diagonal J (Type 0)).obj PUnit) where
  pt := PUnit
  π := 𝟙 _

def singletonConeIsLimit (J : Type uJ) [Category.{vJ} J] :
    IsLimit (singletonCone J) where
  lift _ := ↾fun _ => PUnit.unit
  fac _ _ := by ext x; exact Subsingleton.elim (α := PUnit) _ _
  uniq _ _ _ := by ext x; exact Subsingleton.elim (α := PUnit) _ _

/-- A small colimiting cocone in Type for an arbitrary index, including an empty one. -/
def emptyTypeCocone (J : Type uJ) [Category.{vJ} J] :
    Cocone ((diagonal J (Type 0)).obj PEmpty) where
  pt := PEmpty
  ι := 𝟙 _

def emptyTypeCoconeIsColimit (J : Type uJ) [Category.{vJ} J] :
    IsColimit (emptyTypeCocone J) where
  desc _ := ↾PEmpty.elim
  fac _ _ := by ext x; exact PEmpty.elim x
  uniq _ _ _ := by ext x; exact PEmpty.elim x

/-- Checked consumers of both directions of the bridge on a disconnected index. -/
theorem twoPoint_limit_consumer : ConeUniversal (singletonCone TwoPointIndex) :=
  (coneUniversal_iff_nonempty_isLimit _).2 ⟨singletonConeIsLimit TwoPointIndex⟩

theorem twoPoint_colimit_consumer : Nonempty (IsColimit (emptyTypeCocone TwoPointIndex)) :=
  (coconeUniversal_iff_nonempty_isColimit _).1
    (coconeUniversal_of_isColimit (emptyTypeCoconeIsColimit TwoPointIndex))

/-- Checked consumers of both directions of the bridge on the empty index. -/
theorem empty_limit_consumer : Nonempty (IsLimit (singletonCone EmptyIndex)) :=
  (coneUniversal_iff_nonempty_isLimit _).1
    (coneUniversal_of_isLimit (singletonConeIsLimit EmptyIndex))

theorem empty_colimit_consumer : CoconeUniversal (emptyTypeCocone EmptyIndex) :=
  (coconeUniversal_iff_nonempty_isColimit _).2 ⟨emptyTypeCoconeIsColimit EmptyIndex⟩

end ScopeConsumers

end Langlands.CategoryTheory.Renard
