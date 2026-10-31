import Langlands.AbelianScheme.CotangentBaseChangeNaturalityStatement
import Langlands.AlgebraicGeometry.RelativeDifferentialsBaseChangeTransport

/-! # Naturality of the actual cotangent base-change maps -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands

private def sectionPullbackIso {K X Y : AlgebraicGeometry.Scheme.{u}}
    (eX : K ⟶ X) (eY : K ⟶ Y) (g : X ⟶ Y) (h : eX ≫ g = eY) :
    pullback eY ≅ pullback g ⋙ pullback eX :=
  (pullbackCongr h).symm ≪≫ (pullbackComp eX g).symm

private lemma sectionPullbackIso_comp {K X Y Z : AlgebraicGeometry.Scheme.{u}}
    (eX : K ⟶ X) (eY : K ⟶ Y) (eZ : K ⟶ Z) (g : X ⟶ Y) (h : Y ⟶ Z)
    (wg : eX ≫ g = eY) (wh : eY ≫ h = eZ) (M : Z.Modules) :
    (sectionPullbackIso eY eZ h wh).hom.app M ≫
        (sectionPullbackIso eX eY g wg).hom.app ((pullback h).obj M) =
      (sectionPullbackIso eX eZ (g ≫ h) (by rw [← Category.assoc, wg, wh])).hom.app M ≫
        (pullback eX).map ((pullbackComp g h).inv.app M) := by
  subst eY
  subst eZ
  have hassoc := NatTrans.congr_app (pseudofunctor_associativity eX g h) M
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app] at hassoc
  erw [Category.id_comp (obj := K.Modules)] at hassoc
  apply (cancel_mono ((pullbackComp eX g).hom.app ((pullback h).obj M) ≫
    (pullbackComp (eX ≫ g) h).hom.app M)).1
  simp only [sectionPullbackIso, Iso.trans_hom, Iso.symm_hom,
    pullbackCongr, eqToIso.inv, eqToHom_refl, Category.id_comp,
    Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [hassoc]
  rw [Iso.inv_hom_id_app]
  rfl

private lemma sectionPullbackIso_pullback {K L X Y : AlgebraicGeometry.Scheme.{u}}
    (k : L ⟶ K) (eX : K ⟶ X) (eY : K ⟶ Y) (g : X ⟶ Y)
    (w : eX ≫ g = eY) (M : Y.Modules) :
    (pullback k).map ((sectionPullbackIso eX eY g w).hom.app M) ≫
        (pullbackComp k eX).hom.app ((pullback g).obj M) =
      (pullbackComp k eY).hom.app M ≫
        (sectionPullbackIso (k ≫ eX) (k ≫ eY) g
          (by rw [Category.assoc, w])).hom.app M := by
  subst eY
  have h := sectionPullbackIso_comp k (k ≫ eX) (k ≫ eX ≫ g) eX g rfl
    (Category.assoc k eX g) M
  simp only [sectionPullbackIso, Iso.trans_hom, Iso.symm_hom, pullbackCongr,
    eqToIso.inv, eqToHom_refl, Category.id_comp] at h ⊢
  apply (cancel_epi ((pullbackComp k (eX ≫ g)).inv.app M)).mp
  apply (cancel_mono ((pullbackComp k eX).inv.app ((pullback g).obj M))).mp
  simp only [Category.assoc, Iso.hom_inv_id_app, Iso.inv_hom_id_app_assoc]
  erw [Category.comp_id (obj := L.Modules)]
  exact h.symm

private def sectionSquareMap {K X Y S T : AlgebraicGeometry.Scheme.{u}}
    (g : X ⟶ Y) (b : T ⟶ S) {fX : X ⟶ T} {fY : Y ⟶ S}
    (w : g ≫ fY = fX ≫ b)
    (eX : K ⟶ X) (eY : K ⟶ Y) (h : eX ≫ g = eY) :
    (pullback eY).obj (Scheme.relativeDifferentials fY) ⟶
      (pullback eX).obj (Scheme.relativeDifferentials fX) :=
  (sectionPullbackIso eX eY g h).hom.app (Scheme.relativeDifferentials fY) ≫
    (pullback eX).map (Scheme.relativeDifferentialsSquareMap g b w)

private lemma sectionSquareMap_comp {K X Y Z S T U : AlgebraicGeometry.Scheme.{u}}
    (g : X ⟶ Y) (h : Y ⟶ Z) (b : U ⟶ T) (c : T ⟶ S)
    {fX : X ⟶ U} {fY : Y ⟶ T} {fZ : Z ⟶ S}
    (wg : g ≫ fY = fX ≫ b) (wh : h ≫ fZ = fY ≫ c)
    (eX : K ⟶ X) (eY : K ⟶ Y) (eZ : K ⟶ Z)
    (hg : eX ≫ g = eY) (hh : eY ≫ h = eZ) :
    sectionSquareMap h c wh eY eZ hh ≫ sectionSquareMap g b wg eX eY hg =
      sectionSquareMap (g ≫ h) (b ≫ c)
        (by rw [Category.assoc, wh, ← Category.assoc, wg, Category.assoc])
        eX eZ (by rw [← Category.assoc, hg, hh]) := by
  dsimp only [sectionSquareMap]
  have hn := (sectionPullbackIso eX eY g hg).hom.naturality
    (Scheme.relativeDifferentialsSquareMap h c wh)
  dsimp only [Functor.comp_map] at hn
  simp only [Category.assoc]
  rw [reassoc_of% hn,
    reassoc_of% (sectionPullbackIso_comp eX eY eZ g h hg hh)]
  simp only [← Functor.map_comp]
  rw [Scheme.relativeDifferentialsSquareMap_comp]

private lemma sectionSquareMap_pullback {K L X Y S T : AlgebraicGeometry.Scheme.{u}}
    (k : L ⟶ K) (g : X ⟶ Y) (b : T ⟶ S) {fX : X ⟶ T} {fY : Y ⟶ S}
    (w : g ≫ fY = fX ≫ b)
    (eX : K ⟶ X) (eY : K ⟶ Y) (h : eX ≫ g = eY) :
    (pullback k).map (sectionSquareMap g b w eX eY h) ≫
        (pullbackComp k eX).hom.app (Scheme.relativeDifferentials fX) =
      (pullbackComp k eY).hom.app (Scheme.relativeDifferentials fY) ≫
        sectionSquareMap g b w (k ≫ eX) (k ≫ eY) (by rw [Category.assoc, h]) := by
  dsimp only [sectionSquareMap]
  have hn := (pullbackComp k eX).hom.naturality
    (Scheme.relativeDifferentialsSquareMap g b w)
  dsimp only [Functor.comp_map] at hn
  rw [Functor.map_comp, Category.assoc, hn]
  rw [← Category.assoc, sectionPullbackIso_pullback]
  simp only [Category.assoc]

private lemma sectionSquareMap_congr {K X Y S T : AlgebraicGeometry.Scheme.{u}}
    {g g' : X ⟶ Y} {b b' : T ⟶ S} {fX : X ⟶ T} {fY : Y ⟶ S}
    (hg : g = g') (hb : b = b')
    (w : g ≫ fY = fX ≫ b) (w' : g' ≫ fY = fX ≫ b')
    (eX : K ⟶ X) (eY : K ⟶ Y) (h : eX ≫ g = eY) (h' : eX ≫ g' = eY) :
    sectionSquareMap g b w eX eY h = sectionSquareMap g' b' w' eX eY h' := by
  subst g'
  subst b'
  rfl

namespace GroupScheme

variable {S T : AlgebraicGeometry.Scheme.{u}}

private lemma cotangentMap_eq_sectionSquareMap {G H : GroupScheme S} (f : G ⟶ H) :
    cotangentMap f = sectionSquareMap f.hom.hom.left (𝟙 S)
      (by simpa only [Category.comp_id] using f.hom.hom.w)
      G.identitySection H.identitySection (identitySection_naturality f) := by
  rfl

private lemma cotangentBaseChangeMap_eq_sectionSquareMap (b : T ⟶ S) (G : GroupScheme S) :
    cotangentBaseChangeMap b G =
      (pullbackComp b G.identitySection).hom.app (Scheme.relativeDifferentials G.X.hom) ≫
        sectionSquareMap (Limits.pullback.fst G.X.hom b) b Limits.pullback.condition
          ((baseChange b).obj G).identitySection (b ≫ G.identitySection)
          (identitySection_baseChange_fst b G) := by
  simp only [cotangentBaseChangeMap, cotangentBaseChangePullbackIso,
    sectionSquareMap, sectionPullbackIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Scheme.relativeDifferentialsBaseChangeMap, Category.assoc]

set_option maxHeartbeats 1000000 in
/-- The actual cotangent base-change map is natural in a group-scheme homomorphism. -/
lemma cotangentBaseChangeMap_naturality (b : T ⟶ S) {G H : GroupScheme S}
    (f : G ⟶ H) :
    (pullback b).map (cotangentMap f) ≫ cotangentBaseChangeMap b G =
      cotangentBaseChangeMap b H ≫ cotangentMap ((baseChange b).map f) := by
  rw [cotangentMap_eq_sectionSquareMap, cotangentBaseChangeMap_eq_sectionSquareMap,
    cotangentBaseChangeMap_eq_sectionSquareMap, cotangentMap_eq_sectionSquareMap]
  rw [← Category.assoc, sectionSquareMap_pullback]
  simp only [Category.assoc]
  rw [sectionSquareMap_comp, sectionSquareMap_comp]
  apply (cancel_epi ((pullbackComp b H.identitySection).hom.app
    (Scheme.relativeDifferentials H.X.hom))).mpr
  apply sectionSquareMap_congr
  · exact (Limits.pullback.lift_fst _ _ _).symm
  · simp

/-- The group-scheme component of cotangent base-change naturality. -/
theorem cotangentBaseChangeNaturality (S : AlgebraicGeometry.Scheme.{u}) :
    CotangentBaseChangeNaturalityStatement S := by
  intro T b G H f
  exact cotangentBaseChangeMap_naturality b f

end GroupScheme

namespace AbelianScheme

/-- Cotangent base change is natural in actual abelian-scheme homomorphisms. -/
lemma cotangentBaseChangeMap_naturality {S T : AlgebraicGeometry.Scheme.{u}}
    (b : T ⟶ S) {A B : AbelianScheme S} (f : A ⟶ B) :
    (pullback b).map (GroupScheme.cotangentMap (groupHom f)) ≫
        GroupScheme.cotangentBaseChangeMap b A.toGrp =
      GroupScheme.cotangentBaseChangeMap b B.toGrp ≫
        GroupScheme.cotangentMap (groupHom ((baseChange b).map f)) :=
  GroupScheme.cotangentBaseChangeMap_naturality b (groupHom f)

/-- The abelian-scheme specialization of cotangent base-change naturality. -/
theorem cotangentBaseChangeNaturality (S : AlgebraicGeometry.Scheme.{u}) :
    CotangentBaseChangeNaturalityStatement S := by
  intro T b A B f
  exact cotangentBaseChangeMap_naturality b f

end AbelianScheme

/-- The general cotangent naturality square and its actual abelian specialization. -/
theorem cotangentBaseChangeNaturalityStatements (S : AlgebraicGeometry.Scheme.{u}) :
    CotangentBaseChangeNaturalityStatements S :=
  ⟨GroupScheme.cotangentBaseChangeNaturality S, AbelianScheme.cotangentBaseChangeNaturality S⟩

end Langlands
