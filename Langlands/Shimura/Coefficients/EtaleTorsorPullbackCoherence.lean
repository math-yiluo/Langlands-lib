import Langlands.Shimura.Coefficients.EtaleTorsorPullbackFunctoriality

/-! # Coherence of actual geometric torsor base change -/

noncomputable section

universe u uI vI

namespace Langlands.Shimura.Coefficients

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X Z V W : Scheme.{u}}

/-- Equal base morphisms induce the canonical fiber-product comparison. -/
def etaleObjectPullbackCongr {f k : Z ⟶ X} (h : f = k) :
    etaleObjectPullback f ≅ etaleObjectPullback k :=
  MorphismProperty.Over.pullbackCongr h

/-- The object-level comparison uses the actual single-to-iterated pullback. -/
def etaleObjectPullbackComp (f : Z ⟶ X) (g : V ⟶ Z) :
    etaleObjectPullback (g ≫ f) ≅ etaleObjectPullback f ⋙ etaleObjectPullback g :=
  MorphismProperty.Over.pullbackComp g f

@[reassoc (attr := simp)] theorem etaleObjectPullbackCongr_hom_fst
    {f k : Z ⟶ X} (h : f = k) (U : X.Etale) :
    ((etaleObjectPullbackCongr h).hom.app U).left ≫ pullback.fst U.hom k =
      pullback.fst U.hom f :=
  MorphismProperty.Over.pullbackCongr_hom_app_left_fst h U

@[reassoc (attr := simp)] theorem etaleObjectPullbackCongr_hom_snd
    {f k : Z ⟶ X} (h : f = k) (U : X.Etale) :
    ((etaleObjectPullbackCongr h).hom.app U).left ≫ pullback.snd U.hom k =
      pullback.snd U.hom f :=
  ((etaleObjectPullbackCongr h).hom.app U).w

@[reassoc (attr := simp)] theorem etaleObjectPullbackComp_hom_fst_fst
    (f : Z ⟶ X) (g : V ⟶ Z) (U : X.Etale) :
    ((etaleObjectPullbackComp f g).hom.app U).left ≫
        pullback.fst (pullback.snd U.hom f) g ≫ pullback.fst U.hom f =
      pullback.fst U.hom (g ≫ f) :=
  MorphismProperty.Over.pullbackComp_left_fst_fst g f U

@[reassoc (attr := simp)] theorem etaleObjectPullbackComp_hom_snd
    (f : Z ⟶ X) (g : V ⟶ Z) (U : X.Etale) :
    ((etaleObjectPullbackComp f g).hom.app U).left ≫
        pullback.snd (pullback.snd U.hom f) g =
      pullback.snd U.hom (g ≫ f) :=
  ((etaleObjectPullbackComp f g).hom.app U).w

@[reassoc (attr := simp)] theorem etaleObjectPullback_map_fst
    (f : Z ⟶ X) {U U' : X.Etale} (a : U ⟶ U') :
    ((etaleObjectPullback f).map a).left ≫ pullback.fst U'.hom f =
      pullback.fst U.hom f ≫ a.left := by
  simp [etaleObjectPullback]

@[reassoc (attr := simp)] theorem etaleObjectPullback_map_snd
    (f : Z ⟶ X) {U U' : X.Etale} (a : U ⟶ U') :
    ((etaleObjectPullback f).map a).left ≫ pullback.snd U'.hom f =
      pullback.snd U.hom f :=
  ((etaleObjectPullback f).map a).w

/-- The intermediate-base coordinate is the direct new-base coordinate followed by g. -/
@[reassoc (attr := simp)] theorem etaleObjectPullbackComp_hom_fst_snd
    (f : Z ⟶ X) (g : V ⟶ Z) (U : X.Etale) :
    ((etaleObjectPullbackComp f g).hom.app U).left ≫
        pullback.fst (pullback.snd U.hom f) g ≫ pullback.snd U.hom f =
      pullback.snd U.hom (g ≫ f) ≫ g := by
  rw [pullback.condition, etaleObjectPullbackComp_hom_snd_assoc]

/-- Inserting an identity on the target base gives the identity comparison. -/
theorem etaleObjectPullbackComp_id_target (f : Z ⟶ X) (U : X.Etale) :
    (etaleObjectPullbackComp (𝟙 X) f).hom.app U ≫
        (etaleObjectPullback f).map ((etaleObjectPullbackId X).hom.app U) =
      (etaleObjectPullbackCongr (Category.comp_id f)).hom.app U := by
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext
  · change
      (((etaleObjectPullbackComp (𝟙 X) f).hom.app U).left ≫
        ((etaleObjectPullback f).map ((etaleObjectPullbackId X).hom.app U)).left) ≫
        pullback.fst U.hom f =
      ((etaleObjectPullbackCongr (Category.comp_id f)).hom.app U).left ≫
        pullback.fst U.hom f
    erw [Category.assoc,
      etaleObjectPullback_map_fst f ((etaleObjectPullbackId X).hom.app U),
      etaleObjectPullbackId_hom_app_left,
      etaleObjectPullbackComp_hom_fst_fst, etaleObjectPullbackCongr_hom_fst]
  · change
      (((etaleObjectPullbackComp (𝟙 X) f).hom.app U).left ≫
        ((etaleObjectPullback f).map ((etaleObjectPullbackId X).hom.app U)).left) ≫
        pullback.snd U.hom f =
      ((etaleObjectPullbackCongr (Category.comp_id f)).hom.app U).left ≫
        pullback.snd U.hom f
    erw [Category.assoc,
      etaleObjectPullback_map_snd f ((etaleObjectPullbackId X).hom.app U),
      etaleObjectPullbackComp_hom_snd, etaleObjectPullbackCongr_hom_snd]

/-- Inserting an identity on the source base gives the identity comparison. -/
theorem etaleObjectPullbackComp_id_source (f : Z ⟶ X) (U : X.Etale) :
    (etaleObjectPullbackComp f (𝟙 Z)).hom.app U ≫
        (etaleObjectPullbackId Z).hom.app ((etaleObjectPullback f).obj U) =
      (etaleObjectPullbackCongr (Category.id_comp f)).hom.app U := by
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext
  · change
      (((etaleObjectPullbackComp f (𝟙 Z)).hom.app U).left ≫
        pullback.fst (pullback.snd U.hom f) (𝟙 Z)) ≫ pullback.fst U.hom f =
      ((etaleObjectPullbackCongr (Category.id_comp f)).hom.app U).left ≫
        pullback.fst U.hom f
    simp only [Category.assoc, etaleObjectPullbackComp_hom_fst_fst,
      etaleObjectPullbackCongr_hom_fst]
  · change
      (((etaleObjectPullbackComp f (𝟙 Z)).hom.app U).left ≫
        pullback.fst (pullback.snd U.hom f) (𝟙 Z)) ≫ pullback.snd U.hom f =
      ((etaleObjectPullbackCongr (Category.id_comp f)).hom.app U).left ≫
        pullback.snd U.hom f
    simp only [Category.assoc, pullback.condition, Category.comp_id,
      etaleObjectPullbackComp_hom_snd, etaleObjectPullbackCongr_hom_snd]

/-- The two successive-composition routes agree, including associativity of base maps. -/
theorem etaleObjectPullbackComp_assoc (f : Z ⟶ X) (g : V ⟶ Z) (h : W ⟶ V)
    (U : X.Etale) :
    (etaleObjectPullbackComp f (h ≫ g)).hom.app U ≫
        (etaleObjectPullbackComp g h).hom.app ((etaleObjectPullback f).obj U) =
      (etaleObjectPullbackCongr (Category.assoc h g f)).hom.app U ≫
        (etaleObjectPullbackComp (g ≫ f) h).hom.app U ≫
        (etaleObjectPullback h).map ((etaleObjectPullbackComp f g).hom.app U) := by
  let a : pullback U.hom ((h ≫ g) ≫ f) ⟶
      pullback (pullback.snd U.hom f) (h ≫ g) :=
    ((etaleObjectPullbackComp f (h ≫ g)).hom.app U).left
  let b : pullback (pullback.snd U.hom f) (h ≫ g) ⟶
      pullback (pullback.snd (pullback.snd U.hom f) g) h :=
    ((etaleObjectPullbackComp g h).hom.app ((etaleObjectPullback f).obj U)).left
  let c : pullback U.hom ((h ≫ g) ≫ f) ⟶ pullback U.hom (h ≫ g ≫ f) :=
    ((etaleObjectPullbackCongr (Category.assoc h g f)).hom.app U).left
  let d : pullback U.hom (h ≫ g ≫ f) ⟶ pullback (pullback.snd U.hom (g ≫ f)) h :=
    ((etaleObjectPullbackComp (g ≫ f) h).hom.app U).left
  let k : pullback U.hom (g ≫ f) ⟶ pullback (pullback.snd U.hom f) g :=
    ((etaleObjectPullbackComp f g).hom.app U).left
  let e : pullback (pullback.snd U.hom (g ≫ f)) h ⟶
      pullback (pullback.snd (pullback.snd U.hom f) g) h :=
    ((etaleObjectPullback h).map ((etaleObjectPullbackComp f g).hom.app U)).left
  have aff : a ≫ pullback.fst (pullback.snd U.hom f) (h ≫ g) ≫
      pullback.fst U.hom f = pullback.fst U.hom ((h ≫ g) ≫ f) :=
    etaleObjectPullbackComp_hom_fst_fst f (h ≫ g) U
  have asnd : a ≫ pullback.snd (pullback.snd U.hom f) (h ≫ g) =
      pullback.snd U.hom ((h ≫ g) ≫ f) :=
    etaleObjectPullbackComp_hom_snd f (h ≫ g) U
  have bff : b ≫ pullback.fst (pullback.snd (pullback.snd U.hom f) g) h ≫
      pullback.fst (pullback.snd U.hom f) g =
      pullback.fst (pullback.snd U.hom f) (h ≫ g) :=
    etaleObjectPullbackComp_hom_fst_fst g h ((etaleObjectPullback f).obj U)
  have bsnd : b ≫ pullback.snd (pullback.snd (pullback.snd U.hom f) g) h =
      pullback.snd (pullback.snd U.hom f) (h ≫ g) :=
    etaleObjectPullbackComp_hom_snd g h ((etaleObjectPullback f).obj U)
  have cf : c ≫ pullback.fst U.hom (h ≫ g ≫ f) =
      pullback.fst U.hom ((h ≫ g) ≫ f) :=
    etaleObjectPullbackCongr_hom_fst (Category.assoc h g f) U
  have cs : c ≫ pullback.snd U.hom (h ≫ g ≫ f) =
      pullback.snd U.hom ((h ≫ g) ≫ f) :=
    etaleObjectPullbackCongr_hom_snd (Category.assoc h g f) U
  have dff : d ≫ pullback.fst (pullback.snd U.hom (g ≫ f)) h ≫
      pullback.fst U.hom (g ≫ f) = pullback.fst U.hom (h ≫ g ≫ f) :=
    etaleObjectPullbackComp_hom_fst_fst (g ≫ f) h U
  have ds : d ≫ pullback.snd (pullback.snd U.hom (g ≫ f)) h =
      pullback.snd U.hom (h ≫ g ≫ f) :=
    etaleObjectPullbackComp_hom_snd (g ≫ f) h U
  have kff : k ≫ pullback.fst (pullback.snd U.hom f) g ≫
      pullback.fst U.hom f = pullback.fst U.hom (g ≫ f) :=
    etaleObjectPullbackComp_hom_fst_fst f g U
  have ks : k ≫ pullback.snd (pullback.snd U.hom f) g =
      pullback.snd U.hom (g ≫ f) :=
    etaleObjectPullbackComp_hom_snd f g U
  have ef : e ≫ pullback.fst (pullback.snd (pullback.snd U.hom f) g) h =
      pullback.fst (pullback.snd U.hom (g ≫ f)) h ≫ k :=
    etaleObjectPullback_map_fst h ((etaleObjectPullbackComp f g).hom.app U)
  have es : e ≫ pullback.snd (pullback.snd (pullback.snd U.hom f) g) h =
      pullback.snd (pullback.snd U.hom (g ≫ f)) h :=
    etaleObjectPullback_map_snd h ((etaleObjectPullbackComp f g).hom.app U)
  apply MorphismProperty.Over.Hom.ext
  change a ≫ b = c ≫ d ≫ e
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp only [Category.assoc, reassoc_of% ef, reassoc_of% bff, aff, kff, dff, cf]
      · simp only [Category.assoc, reassoc_of% ef, reassoc_of% bsnd,
          pullback.condition, pullback.condition_assoc, reassoc_of% ks,
          reassoc_of% asnd, reassoc_of% ds, reassoc_of% cs]
    · simp only [Category.assoc, reassoc_of% es, pullback.condition,
        reassoc_of% bsnd, reassoc_of% asnd, reassoc_of% ds, reassoc_of% cs]
  · simp only [Category.assoc, es, bsnd, asnd, ds, cs]

variable {I : Type uI} [Category.{vI} I] (D : I ⥤ GrpCat.{u})

/-- Equality of base maps transports the complete varying-group cover diagram. -/
def etaleTorsorDiagramPullbackCongr {f k : Z ⟶ X} (e : f = k) :
    etaleTorsorDiagramPullback f D ≅ etaleTorsorDiagramPullback k D :=
  EquivariantDiagram.mapFunctorCongr (etaleObjectPullbackCongr e)

@[simp] theorem etaleTorsorDiagramPullbackCongr_hom_app_hom_app
    {f k : Z ⟶ X} (e : f = k) (Y : EquivariantDiagram D X.Etale) (i : I) :
    ((etaleTorsorDiagramPullbackCongr D e).hom.app Y).hom.app i =
      (etaleObjectPullbackCongr e).hom.app (Y.action i).V := rfl

@[simp] theorem etaleTorsorDiagramPullbackId_hom_app_hom_app
    (Y : EquivariantDiagram D X.Etale) (i : I) :
    ((etaleTorsorDiagramPullbackId D).hom.app Y).hom.app i =
      (etaleObjectPullbackId X).hom.app (Y.action i).V := by
  change _ ≫ 𝟙 _ = _
  exact Category.comp_id _

@[simp] theorem etaleTorsorDiagramPullbackComp_hom_app_hom_app
    (f : Z ⟶ X) (g : V ⟶ Z) (Y : EquivariantDiagram D X.Etale) (i : I) :
    ((etaleTorsorDiagramPullbackComp f D g).hom.app Y).hom.app i =
      (etaleObjectPullbackComp f g).hom.app (Y.action i).V := by
  change _ ≫ 𝟙 _ = _
  exact Category.comp_id _

/-- Target-base identity coherence for every action and index transition. -/
theorem etaleTorsorDiagramPullbackComp_id_target (f : Z ⟶ X)
    (Y : EquivariantDiagram D X.Etale) :
    (etaleTorsorDiagramPullbackComp (𝟙 X) D f).hom.app Y ≫
        (etaleTorsorDiagramPullback f D).map
          ((etaleTorsorDiagramPullbackId D).hom.app Y) =
      (etaleTorsorDiagramPullbackCongr D (Category.comp_id f)).hom.app Y := by
  apply EquivariantDiagram.Hom.ext
  apply NatTrans.ext
  funext i
  change
    ((etaleTorsorDiagramPullbackComp (𝟙 X) D f).hom.app Y).hom.app i ≫
        (etaleObjectPullback f).map
          (((etaleTorsorDiagramPullbackId D).hom.app Y).hom.app i) = _
  rw [etaleTorsorDiagramPullbackComp_hom_app_hom_app,
    etaleTorsorDiagramPullbackId_hom_app_hom_app,
    etaleTorsorDiagramPullbackCongr_hom_app_hom_app]
  exact etaleObjectPullbackComp_id_target f (Y.action i).V

/-- Source-base identity coherence for every action and index transition. -/
theorem etaleTorsorDiagramPullbackComp_id_source (f : Z ⟶ X)
    (Y : EquivariantDiagram D X.Etale) :
    (etaleTorsorDiagramPullbackComp f D (𝟙 Z)).hom.app Y ≫
        (etaleTorsorDiagramPullbackId D).hom.app
          ((etaleTorsorDiagramPullback f D).obj Y) =
      (etaleTorsorDiagramPullbackCongr D (Category.id_comp f)).hom.app Y := by
  apply EquivariantDiagram.Hom.ext
  apply NatTrans.ext
  funext i
  change
    ((etaleTorsorDiagramPullbackComp f D (𝟙 Z)).hom.app Y).hom.app i ≫
        ((etaleTorsorDiagramPullbackId D).hom.app
          ((etaleTorsorDiagramPullback f D).obj Y)).hom.app i = _
  rw [etaleTorsorDiagramPullbackComp_hom_app_hom_app,
    etaleTorsorDiagramPullbackId_hom_app_hom_app,
    etaleTorsorDiagramPullbackCongr_hom_app_hom_app]
  exact etaleObjectPullbackComp_id_source f (Y.action i).V

/-- The two triple-base-change routes coincide as equivariant diagram maps. -/
theorem etaleTorsorDiagramPullbackComp_assoc
    (f : Z ⟶ X) (g : V ⟶ Z) (h : W ⟶ V) (Y : EquivariantDiagram D X.Etale) :
    (etaleTorsorDiagramPullbackComp f D (h ≫ g)).hom.app Y ≫
        (etaleTorsorDiagramPullbackComp g D h).hom.app
          ((etaleTorsorDiagramPullback f D).obj Y) =
      (etaleTorsorDiagramPullbackCongr D (Category.assoc h g f)).hom.app Y ≫
        (etaleTorsorDiagramPullbackComp (g ≫ f) D h).hom.app Y ≫
        (etaleTorsorDiagramPullback h D).map
          ((etaleTorsorDiagramPullbackComp f D g).hom.app Y) := by
  apply EquivariantDiagram.Hom.ext
  apply NatTrans.ext
  funext i
  change
    ((etaleTorsorDiagramPullbackComp f D (h ≫ g)).hom.app Y).hom.app i ≫
        ((etaleTorsorDiagramPullbackComp g D h).hom.app
          ((etaleTorsorDiagramPullback f D).obj Y)).hom.app i =
      ((etaleTorsorDiagramPullbackCongr D (Category.assoc h g f)).hom.app Y).hom.app i ≫
        ((etaleTorsorDiagramPullbackComp (g ≫ f) D h).hom.app Y).hom.app i ≫
        (etaleObjectPullback h).map
          (((etaleTorsorDiagramPullbackComp f D g).hom.app Y).hom.app i)
  rw [etaleTorsorDiagramPullbackComp_hom_app_hom_app,
    etaleTorsorDiagramPullbackComp_hom_app_hom_app,
    etaleTorsorDiagramPullbackCongr_hom_app_hom_app,
    etaleTorsorDiagramPullbackComp_hom_app_hom_app,
    etaleTorsorDiagramPullbackComp_hom_app_hom_app]
  exact etaleObjectPullbackComp_assoc f g h (Y.action i).V

end Langlands.Shimura.Coefficients
