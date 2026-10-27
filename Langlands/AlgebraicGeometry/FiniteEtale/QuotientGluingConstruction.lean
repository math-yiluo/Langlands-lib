import Langlands.AlgebraicGeometry.FiniteEtale.AffineQuotientCoconeProof
import Langlands.AlgebraicGeometry.FiniteEtale.InvariantAlgebraLocalizationProof
import Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski
import Mathlib.Tactic.DepRewrite

noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Langlands.AlgebraicGeometry.FiniteEtale

open _root_.AlgebraicGeometry

namespace QuotientGluing

/-! ### Invariants commute with principal localization -/

section Algebra

variable {R R' A B G : Type u} [CommRing R] [CommRing R'] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R' B] [Algebra A B] [Group G] [Finite G]
  [MulSemiringAction G A] [MulSemiringAction G B] [SMulCommClass G R A] [SMulCommClass G R' B]

/-- If `B` is the localization of `A` away from the image of `r : R`, compatibly with the
group actions, then the invariants of `B` are the localization of the invariants of `A`
away from `r`. -/
theorem isLocalizationAway_fixedPoints (r : R) [IsLocalization.Away (algebraMap R A r) B]
    (hequiv : ∀ (g : G) (a : A), algebraMap A B (g • a) = g • algebraMap A B a)
    (φ : FixedPoints.subalgebra R A G →+* FixedPoints.subalgebra R' B G)
    (hφ : ∀ a, (φ a : B) = algebraMap A B a) :
    letI := φ.toAlgebra
    IsLocalization.Away (algebraMap R (FixedPoints.subalgebra R A G) r)
      (FixedPoints.subalgebra R' B G) := by
  let := φ.toAlgebra
  let : Algebra R B := ((algebraMap A B).comp (algebraMap R A)).toAlgebra
  have : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq' rfl
  have hfixR (g : G) (x : R) : g • algebraMap R B x = algebraMap R B x := by
    change g • algebraMap A B (algebraMap R A x) = algebraMap A B (algebraMap R A x)
    rw [← hequiv, smul_algebraMap]
  have : SMulCommClass G R B := ⟨fun g x b => by
    rw [Algebra.smul_def, Algebra.smul_def, smul_mul', hfixR]⟩
  have hval (a : FixedPoints.subalgebra R A G) :
      ((algebraMap (FixedPoints.subalgebra R A G) (FixedPoints.subalgebra R' B G) a :
        FixedPoints.subalgebra R' B G) : B) = algebraMap A B a := hφ a
  refine IsLocalization.Away.mk _ ?_ ?_ ?_
  · -- the image of `r` is a unit, with invariant inverse
    set x := algebraMap (FixedPoints.subalgebra R A G) (FixedPoints.subalgebra R' B G)
      (algebraMap R (FixedPoints.subalgebra R A G) r)
    have hx : (x : B) = algebraMap A B (algebraMap R A r) := hval _
    have hu : IsUnit (x : B) := by
      rw [hx]
      exact IsLocalization.Away.algebraMap_isUnit (algebraMap R A r)
    obtain ⟨w, hw⟩ := hu.exists_right_inv
    have hwfix (g : G) : g • w = w := by
      apply hu.mul_left_cancel
      have hxg : g • (x : B) = x := x.2 g
      calc (x : B) * g • w = g • ((x : B) * w) := by rw [smul_mul', hxg]
        _ = (x : B) * w := by rw [hw, smul_one]
    exact IsUnit.of_mul_eq_one (M := FixedPoints.subalgebra R' B G) ⟨w, hwfix⟩ (Subtype.ext hw)
  · intro b
    obtain ⟨a, ha, n, hn⟩ :=
      invariantAlgebraLocalization R A B G r hequiv (b : B) (fun g => b.2 g)
    refine ⟨n, ⟨a, ha⟩, Subtype.ext ?_⟩
    have e : algebraMap A B ((algebraMap R (FixedPoints.subalgebra R A G) r ^ n :
        FixedPoints.subalgebra R A G) : A) = algebraMap R B (r ^ n) := by
      rw [Subalgebra.coe_pow, map_pow, map_pow]
      rfl
    rw [Subalgebra.coe_mul, ← map_pow, hval, hval, e, mul_comm]
    exact hn.symm
  · intro a a' h
    have h' : algebraMap A B a = algebraMap A B a' := by
      rw [← hval, ← hval, h]
    obtain ⟨n, hn⟩ := IsLocalization.Away.exists_of_eq (algebraMap R A r) h'
    exact ⟨n, Subtype.ext (by simpa using hn)⟩

end Algebra

/-! ### The group action on sections over the base -/

section Construction

variable {S : Scheme.{u}} {G : Type u} [Group G] (D : SingleObj G ⥤ Cover S)

/-- The structure morphism of the acted-on cover. -/
abbrev coverHom : coverScheme D ⟶ S := (D.obj (SingleObj.star G)).obj.hom

/-- The automorphism of the acted-on scheme induced by a group element. -/
abbrev coverMap (g : G) : coverScheme D ⟶ coverScheme D :=
  (D.map (SingleObj.toEnd G g)).hom.left

theorem coverMap_comp_coverHom (g : G) : coverMap D g ≫ coverHom D = coverHom D :=
  Over.w (D.map (SingleObj.toEnd G g)).hom

theorem coverMap_one : coverMap D 1 = 𝟙 _ := by
  simp [coverMap]

theorem coverMap_mul (g h : G) : coverMap D (g * h) = coverMap D h ≫ coverMap D g := by
  simp [coverMap]

theorem appLE_eq_of_eq {X Y : Scheme.{u}} {a b : X ⟶ Y} (h : a = b) (U : Y.Opens) (V : X.Opens)
    (e : V ≤ a ⁻¹ᵁ U) : a.appLE U V e = b.appLE U V (h ▸ e) := by
  subst h
  rfl

theorem preimage_coverHom_le (g : G) (U : S.Opens) :
    coverHom D ⁻¹ᵁ U ≤ coverMap D g ⁻¹ᵁ coverHom D ⁻¹ᵁ U := by
  rw [← Scheme.Hom.comp_preimage, coverMap_comp_coverHom]

/-- The contravariant ring map on sections over the preimage of `U` induced by `g`. -/
def sectionAction (U : S.Opens) (g : G) :
    Γ(coverScheme D, coverHom D ⁻¹ᵁ U) ⟶ Γ(coverScheme D, coverHom D ⁻¹ᵁ U) :=
  (coverMap D g).appLE _ _ (preimage_coverHom_le D g U)

theorem sectionAction_one (U : S.Opens) : sectionAction D U 1 = 𝟙 _ := by
  rw [sectionAction, appLE_eq_of_eq (coverMap_one D), Scheme.Hom.appLE, Scheme.Hom.id_app,
    Category.id_comp]
  exact (coverScheme D).presheaf.map_id _

theorem sectionAction_mul (U : S.Opens) (g h : G) :
    sectionAction D U (g * h) = sectionAction D U g ≫ sectionAction D U h := by
  rw [sectionAction, sectionAction, sectionAction, Scheme.Hom.appLE_comp_appLE]
  exact appLE_eq_of_eq (coverMap_mul D g h) _ _ _

theorem app_comp_sectionAction (U : S.Opens) (g : G) :
    (coverHom D).app U ≫ sectionAction D U g = (coverHom D).app U := by
  rw [sectionAction, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
  exact appLE_eq_of_eq (coverMap_comp_coverHom D g) _ _ _

theorem sectionAction_inv_apply (U : S.Opens) (g : G) (a : Γ(coverScheme D, coverHom D ⁻¹ᵁ U)) :
    (sectionAction D U g).hom ((sectionAction D U g⁻¹).hom a) = a := by
  rw [← CommRingCat.comp_apply, ← sectionAction_mul, inv_mul_cancel, sectionAction_one]
  rfl

theorem sectionAction_app_mul (U : S.Opens) (g : G) (r : Γ(S, U))
    (a : Γ(coverScheme D, coverHom D ⁻¹ᵁ U)) :
    (sectionAction D U g).hom (((coverHom D).app U).hom r * a) =
      ((coverHom D).app U).hom r * (sectionAction D U g).hom a := by
  rw [map_mul]
  congr 1
  exact congrArg (fun φ => CommRingCat.Hom.hom φ r) (app_comp_sectionAction D U g)

/-- The restriction of sections along `V ≤ U`, between preimages in the cover. -/
def sectionRes {U V : S.Opens} (h : V ≤ U) :
    Γ(coverScheme D, coverHom D ⁻¹ᵁ U) ⟶ Γ(coverScheme D, coverHom D ⁻¹ᵁ V) :=
  (coverScheme D).presheaf.map (homOfLE ((coverHom D).preimage_mono h)).op

theorem sectionAction_comp_sectionRes {U V : S.Opens} (h : V ≤ U) (g : G) :
    sectionAction D U g ≫ sectionRes D h = sectionRes D h ≫ sectionAction D V g := by
  rw [sectionAction, sectionAction, sectionRes, Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]

/-- Sections of the cover over the preimage of `U`, as a type carrying the group action. -/
def sectionRing (U : S.Opens) : Type u := Γ(coverScheme D, coverHom D ⁻¹ᵁ U)

instance (U : S.Opens) : CommRing (sectionRing D U) :=
  inferInstanceAs (CommRing Γ(coverScheme D, coverHom D ⁻¹ᵁ U))

instance (U : S.Opens) : Algebra Γ(S, U) (sectionRing D U) :=
  ((coverHom D).app U).hom.toAlgebra

theorem sectionRing_algebraMap_apply (U : S.Opens) (r : Γ(S, U)) :
    algebraMap Γ(S, U) (sectionRing D U) r = ((coverHom D).app U).hom r := rfl

/-- The left action: `g` acts through the ring map induced by `g⁻¹`. -/
instance (U : S.Opens) : MulSemiringAction G (sectionRing D U) where
  smul g a := (sectionAction D U g⁻¹).hom a
  one_smul a := by
    change (sectionAction D U 1⁻¹).hom a = a
    rw [inv_one, sectionAction_one]
    rfl
  mul_smul g h a := by
    change (sectionAction D U (g * h)⁻¹).hom a =
      (sectionAction D U g⁻¹).hom ((sectionAction D U h⁻¹).hom a)
    rw [mul_inv_rev, sectionAction_mul]
    rfl
  smul_zero g := map_zero (sectionAction D U g⁻¹).hom
  smul_add g := map_add (sectionAction D U g⁻¹).hom
  smul_one g := map_one (sectionAction D U g⁻¹).hom
  smul_mul g := map_mul (sectionAction D U g⁻¹).hom

theorem sectionRing_smul_def (U : S.Opens) (g : G) (a : sectionRing D U) :
    g • a = (sectionAction D U g⁻¹).hom a := rfl

instance (U : S.Opens) : SMulCommClass G Γ(S, U) (sectionRing D U) where
  smul_comm g r a := sectionAction_app_mul D U g⁻¹ r a

/-- The invariant subalgebra of sections over the preimage of `U`. -/
abbrev invariantRing (U : S.Opens) : Subalgebra Γ(S, U) (sectionRing D U) :=
  FixedPoints.subalgebra Γ(S, U) (sectionRing D U) G

theorem mem_invariantRing_iff (U : S.Opens) (a : sectionRing D U) :
    a ∈ invariantRing D U ↔ ∀ g : G, (sectionAction D U g).hom a = a := by
  change (∀ g : G, g • a = a) ↔ _
  constructor
  · intro h g
    have hg := h g⁻¹
    rw [sectionRing_smul_def, inv_inv] at hg
    exact hg
  · intro h g
    exact h g⁻¹

/-- A ring map into sections over a preimage, viewed as a map into the type synonym. -/
def toSectionRing {T : CommRingCat.{u}} (U : S.Opens)
    (φ : T ⟶ Γ(coverScheme D, coverHom D ⁻¹ᵁ U)) : T →+* sectionRing D U :=
  φ.hom

/-- The inclusion of invariants, as a morphism of commutative rings. -/
def invariantInclusion (U : S.Opens) :
    CommRingCat.of (invariantRing D U) ⟶ Γ(coverScheme D, coverHom D ⁻¹ᵁ U) :=
  CommRingCat.ofHom (invariantRing D U).val.toRingHom

theorem invariantInclusion_injective (U : S.Opens) :
    Function.Injective (invariantInclusion D U).hom := Subtype.val_injective

theorem invariantInclusion_comp_sectionAction (U : S.Opens) (g : G) :
    invariantInclusion D U ≫ sectionAction D U g = invariantInclusion D U := by
  ext c
  exact (mem_invariantRing_iff D U c.1).mp c.2 g

/-! ### The invariant presheaf on the base -/

/-- Restriction maps invariants to invariants. -/
def invariantRes {U V : S.Opens} (h : V ≤ U) :
    CommRingCat.of (invariantRing D U) ⟶ CommRingCat.of (invariantRing D V) :=
  CommRingCat.ofHom ((toSectionRing D V (sectionRes D h)).restrict _ _ fun a ha =>
    (mem_invariantRing_iff D V _).mpr fun g => by
      have h1 := congrArg (fun φ => CommRingCat.Hom.hom φ a) (sectionAction_comp_sectionRes D h g)
      simp only [CommRingCat.comp_apply] at h1
      rw [(mem_invariantRing_iff D U a).mp ha g] at h1
      exact h1.symm)

theorem invariantRes_val {U V : S.Opens} (h : V ≤ U) (a : invariantRing D U) :
    ((invariantRes D h).hom a : sectionRing D V) = (sectionRes D h).hom a.1 := rfl

/-- The presheaf of invariant sections on the base. -/
def invariantDiagram : S.Opensᵒᵖ ⥤ CommRingCat where
  obj U := .of (invariantRing D U.unop)
  map {U V} i := invariantRes D i.unop.le
  map_id U := by
    ext a
    change ((coverScheme D).presheaf.map (𝟙 _)).hom a.1 = a.1
    rw [CategoryTheory.Functor.map_id]
    rfl
  map_comp {U V W} i j := by
    ext a
    change ((coverScheme D).presheaf.map _).hom a.1 =
      ((coverScheme D).presheaf.map _).hom (((coverScheme D).presheaf.map _).hom a.1)
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl

/-- The structure map from the base into the invariant presheaf. -/
def invariantDiagramMap : S.presheaf ⟶ invariantDiagram D where
  app U := CommRingCat.ofHom (algebraMap Γ(S, U.unop) (invariantRing D U.unop))
  naturality {U V} i := by
    ext x
    exact Subtype.ext congr($((coverHom D).naturality i) x)

open Scheme.AffineZariskiSite in
theorem coequifibered_invariantDiagramMap [Finite G] :
    ((toOpensFunctor S).op.whiskerLeft (invariantDiagramMap D)).Coequifibered := by
  refine coequifibered_iff_forall_isLocalizationAway.mpr fun U r ↦ ?_
  let X := coverScheme D
  let f := coverHom D
  let inst : Algebra Γ(X, f ⁻¹ᵁ U.1) Γ(X, f ⁻¹ᵁ S.basicOpen r) :=
    (X.presheaf.map (homOfLE (f.preimage_mono (S.basicOpen_le r))).op).hom.toAlgebra
  have hloc : IsLocalization.Away ((f.app U.1).hom r) Γ(X, f ⁻¹ᵁ S.basicOpen r) := by
    let : Algebra Γ(X, f ⁻¹ᵁ U.1) Γ(X, X.basicOpen (f.app _ r)) :=
      (X.presheaf.map (homOfLE (X.basicOpen_le _)).op).hom.toAlgebra
    dsimp +instances [inst]
    rw! (castMode := .all) [f.preimage_basicOpen r]
    exact isLocalization_basicOpen_of_qcqs (f.isCompact_preimage U.2.isCompact)
        (f.isQuasiSeparated_preimage U.2.isQuasiSeparated) (f.app _ r)
  let : Algebra (sectionRing D U.1) (sectionRing D (S.basicOpen r)) :=
    (sectionRes D (S.basicOpen_le r)).hom.toAlgebra
  have : IsLocalization.Away ((algebraMap Γ(S, U.1) (sectionRing D U.1)) r)
      (sectionRing D (S.basicOpen r)) := hloc
  have hequiv (g : G) (a : sectionRing D U.1) :
      algebraMap (sectionRing D U.1) (sectionRing D (S.basicOpen r)) (g • a) =
        g • algebraMap (sectionRing D U.1) (sectionRing D (S.basicOpen r)) a := by
    change (sectionRes D (S.basicOpen_le r)).hom ((sectionAction D U.1 g⁻¹).hom a) =
      (sectionAction D (S.basicOpen r) g⁻¹).hom ((sectionRes D (S.basicOpen_le r)).hom a)
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, sectionAction_comp_sectionRes]
  exact isLocalizationAway_fixedPoints r hequiv (invariantRes D (S.basicOpen_le r)).hom
    (fun _ => rfl)

/-! ### Gluing the invariant spectra -/

section Gluing

variable [Finite G]

open Scheme.AffineZariskiSite

/-- The relative gluing datum of spectra of invariant sections over affine opens of the base. -/
def quotientGlueData : (directedCover S).RelativeGluingData :=
  relativeGluingData (coequifibered_invariantDiagramMap D)

instance : ((quotientGlueData D).functor ⋙ Scheme.forget).IsLocallyDirected :=
  Scheme.Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..

/-- The glued quotient scheme. -/
def gluedQuotient : Scheme.{u} := (quotientGlueData D).glued

/-- The structure morphism of the glued quotient. -/
def gluedStructure : gluedQuotient D ⟶ S := (quotientGlueData D).toBase

/-- The open cover of the glued quotient by spectra of invariant sections. -/
def gluedCover : (gluedQuotient D).OpenCover := (quotientGlueData D).cover

theorem gluedCover_f_gluedStructure (U : S.AffineZariskiSite) :
    (gluedCover D).f U ≫ gluedStructure D =
      Spec.map ((invariantDiagramMap D).app (op U.1)) ≫ U.2.fromSpec :=
  colimit.ι_desc _ _

theorem gluedCover_f (U : S.AffineZariskiSite) :
    (gluedCover D).f U = colimit.ι (quotientGlueData D).functor U := by
  simp [gluedCover]

theorem gluedStructure_preimage (U : S.AffineZariskiSite) :
    gluedStructure D ⁻¹ᵁ U.1 = ((gluedCover D).f U).opensRange := by
  simpa using! (quotientGlueData D).toBase_preimage_eq_opensRange_ι U

/-- A target-local property holds for the glued structure morphism once it holds for the
spectra of the invariant structure maps over affine opens. -/
theorem gluedStructure_of {P : MorphismProperty Scheme.{u}} [IsZariskiLocalAtTarget P]
    (h : ∀ U : S.AffineZariskiSite, P (Spec.map ((invariantDiagramMap D).app (op U.1)))) :
    P (gluedStructure D) := by
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := P) _ (iSup_affineOpens_eq_top _)]
  intro U
  let e := IsOpenImmersion.isoOfRangeEq (gluedStructure D ⁻¹ᵁ U.1).ι ((gluedCover D).f ⟨U.1, U.2⟩)
      (by simpa using congr($(gluedStructure_preimage D ⟨U.1, U.2⟩).1))
  rw [← MorphismProperty.cancel_left_of_respectsIso P e.inv,
    ← MorphismProperty.cancel_right_of_respectsIso P _ U.2.isoSpec.hom]
  convert! h ⟨U.1, U.2⟩
  rw [← cancel_mono U.2.fromSpec]
  simp [IsAffineOpen.isoSpec_hom, e, gluedCover_f_gluedStructure]

/-! ### The quotient map -/

/-- The pieces of the quotient map over the preimages of affine opens of the base: the spectra
of the inclusions of invariants. -/
def gluedMapPiece (U : ((directedCover S).pullback₁ (coverHom D)).I₀) :
    ((directedCover S).pullback₁ (coverHom D)).X U ⟶ gluedQuotient D :=
  (pullbackRestrictIsoRestrict (coverHom D) U.1).hom ≫
    (coverHom D ⁻¹ᵁ U.1).toSpecΓ ≫ Spec.map (invariantInclusion D U.1) ≫ (gluedCover D).f U

theorem gluedMapPiece_compat {U V : ((directedCover S).pullback₁ (coverHom D)).I₀} (i : U ⟶ V) :
    Scheme.Cover.trans ((directedCover S).pullback₁ (coverHom D)) i ≫ gluedMapPiece D V =
      gluedMapPiece D U := by
  have : (pullbackRestrictIsoRestrict (coverHom D) U.1).inv ≫
      Scheme.Cover.trans ((directedCover S).pullback₁ (coverHom D)) i ≫
      (pullbackRestrictIsoRestrict (coverHom D) V.1).hom = (coverScheme D).homOfLE
        ((coverHom D).preimage_mono (toOpens_mono i.1.1)) := by
    rw [← cancel_mono (Scheme.Opens.ι _)]
    simp +instances [Scheme.Cover.trans, Scheme.Cover.locallyDirectedPullbackCover]
  unfold gluedMapPiece
  rw [← Iso.inv_comp_eq, reassoc_of% this, ← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_assoc,
    ← Spec.map_comp_assoc]
  simp only [gluedCover_f]
  rw [← colimit.w (quotientGlueData D).functor i]
  dsimp [quotientGlueData, relativeGluingData]
  rw [← Spec.map_comp_assoc]
  rfl

/-- The quotient map into the glued quotient, glued from the spectra of the inclusions of
invariants over the preimages of affine opens. -/
def gluedMap : coverScheme D ⟶ gluedQuotient D :=
  Scheme.OpenCover.glueMorphismsOfLocallyDirected
    ((directedCover S).pullback₁ (coverHom D)) (gluedMapPiece D) (gluedMapPiece_compat D)

theorem ι_gluedMap (U : S.AffineZariskiSite) :
    (coverHom D ⁻¹ᵁ U.1).ι ≫ gluedMap D = (coverHom D ⁻¹ᵁ U.1).toSpecΓ ≫
      Spec.map (invariantInclusion D U.1) ≫ (gluedCover D).f U := by
  rw [← cancel_epi (pullbackRestrictIsoRestrict (coverHom D) U.1).hom, ← Category.assoc]
  trans ((directedCover S).pullback₁ (coverHom D)).f U ≫ gluedMap D
  · congr 1
    simp
    rfl
  exact Scheme.OpenCover.map_glueMorphismsOfLocallyDirected _ _ (gluedMapPiece_compat D) _

theorem fromSpec_gluedMap (U : S.AffineZariskiSite) :
    (U.2.preimage (coverHom D)).fromSpec ≫ gluedMap D =
      Spec.map (invariantInclusion D U.1) ≫ (gluedCover D).f U := by
  rw [← IsAffineOpen.isoSpec_inv_ι, Category.assoc, ι_gluedMap,
    IsAffineOpen.isoSpec_inv_toSpecΓ_assoc]

omit [Finite G] in
/-- Morphisms out of the acted-on scheme are determined on the spectra of sections over
preimages of affine opens. -/
theorem coverScheme_hom_ext {Z : Scheme.{u}} {a b : coverScheme D ⟶ Z}
    (h : ∀ U : S.AffineZariskiSite, (U.2.preimage (coverHom D)).fromSpec ≫ a =
      (U.2.preimage (coverHom D)).fromSpec ≫ b) : a = b := by
  refine Scheme.Cover.hom_ext ((coverScheme D).openCoverOfIsOpenCover _
    (.comap (iSup_affineOpens_eq_top S) (coverHom D).base.1)) _ _ fun U ↦ ?_
  change (coverHom D ⁻¹ᵁ U.1).ι ≫ a = (coverHom D ⁻¹ᵁ U.1).ι ≫ b
  rw [← IsAffineOpen.isoSpec_hom_fromSpec (U.2.preimage (coverHom D)), Category.assoc,
    Category.assoc, h ⟨U.1, U.2⟩]

omit [Finite G] in
theorem invariantDiagramMap_comp_invariantInclusion (U : S.Opens) :
    (invariantDiagramMap D).app (op U) ≫ invariantInclusion D U = (coverHom D).app U := by
  ext r
  rfl

theorem gluedMap_gluedStructure : gluedMap D ≫ gluedStructure D = coverHom D := by
  refine coverScheme_hom_ext D fun U => ?_
  rw [reassoc_of% fromSpec_gluedMap, gluedCover_f_gluedStructure, ← Spec.map_comp_assoc,
    invariantDiagramMap_comp_invariantInclusion, Scheme.Hom.app_eq_appLE,
    IsAffineOpen.SpecMap_appLE_fromSpec]

omit [Finite G] in
theorem fromSpec_coverMap (U : S.AffineZariskiSite) (g : G) :
    (U.2.preimage (coverHom D)).fromSpec ≫ coverMap D g =
      Spec.map (sectionAction D U.1 g) ≫ (U.2.preimage (coverHom D)).fromSpec :=
  (IsAffineOpen.SpecMap_appLE_fromSpec _ _ _ _).symm

theorem coverMap_gluedMap (g : G) : coverMap D g ≫ gluedMap D = gluedMap D := by
  refine coverScheme_hom_ext D fun U => ?_
  rw [reassoc_of% fromSpec_coverMap, fromSpec_gluedMap, ← Spec.map_comp_assoc,
    invariantInclusion_comp_sectionAction]

end Gluing

/-! ### Finiteness and étaleness of the glued quotient -/

section FiniteEtale

theorem sectionRing_finite (U : S.AffineZariskiSite) :
    Module.Finite Γ(S, U.1) (sectionRing D U.1) :=
  (coverHom D).finite_app U.1 U.2

theorem sectionRing_etale (U : S.AffineZariskiSite) :
    Algebra.Etale Γ(S, U.1) (sectionRing D U.1) := by
  have h := HasRingHomProperty.appLE @Etale (coverHom D) inferInstance ⟨U.1, U.2⟩
    ⟨_, U.2.preimage (coverHom D)⟩ le_rfl
  rw [← Scheme.Hom.app_eq_appLE] at h
  exact h

variable [IsLocallyNoetherian S] [Finite G]

theorem invariantRing_finite_etale (U : S.AffineZariskiSite) :
    Module.Finite Γ(S, U.1) (invariantRing D U.1) ∧
      Algebra.Etale Γ(S, U.1) (invariantRing D U.1) := by
  have : IsNoetherianRing Γ(S, U.1) := IsLocallyNoetherian.component_noetherian ⟨U.1, U.2⟩
  have := sectionRing_finite D U
  have := sectionRing_etale D U
  exact invariantAlgebraFiniteEtale Γ(S, U.1) (sectionRing D U.1) G

instance : IsFinite (gluedStructure D) :=
  gluedStructure_of D fun U => by
    rw [IsFinite.SpecMap_iff]
    change (algebraMap Γ(S, U.1) (invariantRing D U.1)).Finite
    rw [RingHom.finite_algebraMap]
    exact (invariantRing_finite_etale D U).1

instance : Etale (gluedStructure D) :=
  gluedStructure_of D fun U => by
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    change (algebraMap Γ(S, U.1) (invariantRing D U.1)).Etale
    rw [RingHom.etale_algebraMap]
    exact (invariantRing_finite_etale D U).2

end FiniteEtale

end Construction

end QuotientGluing

end Langlands.AlgebraicGeometry.FiniteEtale
