import Langlands.Geometry.Analytic.GroundFieldExtensionCoherence
import Langlands.Geometry.Analytic.GroundFieldExtensionQuasiIsoProof
import Langlands.Geometry.Analytic.CompatibleStrongLocalization

/-! # Coherent scalar extension on localized compatible analytic atlases -/

noncomputable section

universe u v

namespace Langlands.Analytic.CompleteUltrametricField

open _root_.CategoryTheory CompatibleAtlasPresentation
open AffinoidAtlasPresentation.GroundFieldExtension
open AffinoidAtlasPresentation.GroundFieldExtension.CompleteField

variable {K L M N : CompleteUltrametricField.{u}}

/-- The compatible atlas category in a common universe containing the fields. -/
abbrev CompatibleCategory (K : CompleteUltrametricField.{u}) :=
  CompatibleAtlasPresentation.{u, max u v, max u v} K

/-- The analytic category obtained by localizing compatible analytic atlases. -/
abbrev CompatibleAnalyticCategory (K : CompleteUltrametricField.{u}) :=
  LocalizedCategory.{u, max u v, max u v} (K := K.carrier)

private abbrev Q (K : CompleteUltrametricField.{u}) :
    K.CompatibleCategory.{u, v} ⥤ K.CompatibleAnalyticCategory.{u, v} :=
  localizationFunctor

/-- Change of ground field in the localization of compatible atlases. -/
def localizedExtend (f : K ⟶ L) :
    K.CompatibleAnalyticCategory.{u, v} ⥤ L.CompatibleAnalyticCategory.{u, v} :=
  descend (compatibleExtend f ⋙ Q L) fun A B s hs => by
    let := f.normedAlgebra
    exact Localization.inverts (Q L) (quasiIsomorphisms (K := L.carrier))
      ((compatibleExtend f).map s) (groundFieldExtensionQuasiIso K L s hs)

theorem localizedExtend_factor (f : K ⟶ L) :
    Q.{u, v} K ⋙ localizedExtend f = compatibleExtend f ⋙ Q L :=
  localizationFunctor_descend _ _

@[simp]
theorem localizedExtend_obj (f : K ⟶ L) (A : K.CompatibleCategory.{u, v}) :
    (localizedExtend f).obj ((Q K).obj A) = (Q L).obj ((compatibleExtend f).obj A) :=
  rfl

@[simp]
theorem localizedExtend_map (f : K ⟶ L) {A B : K.CompatibleCategory.{u, v}} (g : A ⟶ B) :
    (localizedExtend f).map ((Q K).map g) = (Q L).map ((compatibleExtend f).map g) :=
  Functor.congr_hom (localizedExtend_factor f) g

private def localizedExtendIdHom (K : CompleteUltrametricField.{u}) :
    localizedExtend.{u, v} (𝟙 K) ⟶ 𝟭 _ :=
  Localization.Construction.natTransExtension
    (eqToHom (localizedExtend_factor.{u, v} (𝟙 K)) ≫
      Functor.whiskerRight (compatibleExtendId K) (Q K) ≫
      eqToHom ((Functor.id_comp (Q K)).trans (Functor.comp_id (Q K)).symm))

private theorem localizedExtendIdHom_app (A : K.CompatibleCategory.{u, v}) :
    (localizedExtendIdHom K).app ((Q K).obj A) = (Q K).map ((compatibleExtendId K).app A) := by
  simp only [localizedExtendIdHom, Localization.Construction.natTransExtension_app]
  change (𝟙 _) ≫ (Q K).map ((compatibleExtendId K).app A) ≫ 𝟙 _ = _
  simp

/-- Identity extension becomes invertible by inverting the actual unit projection. -/
def localizedExtendId (K : CompleteUltrametricField.{u}) :
    localizedExtend.{u, v} (𝟙 K) ≅ 𝟭 _ := by
  let : ∀ X, IsIso ((localizedExtendIdHom.{u, v} K).app X) := fun X => by
    obtain ⟨A, rfl⟩ := (localizedObjectEquiv (K := K.carrier)).surjective X
    change IsIso ((localizedExtendIdHom K).app ((Q K).obj A))
    rw [localizedExtendIdHom_app]
    exact Localization.inverts (Q K) (quasiIsomorphisms (K := K.carrier)) _
      (IndexedAffinoidAtlas.GroundFieldExtension.unitCompatibleMap_isQuasiIso K A.presentation)
  let : IsIso (localizedExtendIdHom.{u, v} K) := NatIso.isIso_of_isIso_app _
  exact asIso (localizedExtendIdHom K)

@[simp]
theorem localizedExtendId_hom_app (A : K.CompatibleCategory.{u, v}) :
    (localizedExtendId K).hom.app ((Q K).obj A) = (Q K).map ((compatibleExtendId K).app A) :=
  localizedExtendIdHom_app A

private theorem localizedExtendComp_factor (f : K ⟶ L) (g : L ⟶ M) :
    Q.{u, v} K ⋙ (localizedExtend f ⋙ localizedExtend g) =
      (compatibleExtend f ⋙ compatibleExtend g) ⋙ Q M := by
  change (Q K ⋙ localizedExtend f) ⋙ localizedExtend g = _
  rw [localizedExtend_factor]
  change compatibleExtend f ⋙ (Q L ⋙ localizedExtend g) = _
  rw [localizedExtend_factor]
  rfl

/-- The tower isomorphism on the compatible localization is the descent of
the bounded tower comparisons on charts. -/
def localizedExtendComp (f : K ⟶ L) (g : L ⟶ M) :
    localizedExtend.{u, v} (f ≫ g) ≅ localizedExtend.{u, v} f ⋙ localizedExtend.{u, v} g := by
  let C := compatibleExtend.{u, v} (f ≫ g)
  let D := compatibleExtend.{u, v} f ⋙ compatibleExtend.{u, v} g
  let E := localizedExtend.{u, v} (f ≫ g)
  let F := localizedExtend.{u, v} f ⋙ localizedExtend.{u, v} g
  let W := quasiIsomorphisms (K := K.carrier)
  letI : Localization.Lifting (Q K) W (C ⋙ Q M) E :=
    ⟨eqToIso (localizedExtend_factor (f ≫ g))⟩
  letI : Localization.Lifting (Q K) W (D ⋙ Q M) F :=
    ⟨eqToIso (localizedExtendComp_factor f g)⟩
  exact Localization.liftNatIso (Q K) W (C ⋙ Q M) (D ⋙ Q M) E F
    (Functor.isoWhiskerRight (compatibleExtendComp f g) (Q M))

@[simp]
theorem localizedExtendComp_hom_app (f : K ⟶ L) (g : L ⟶ M) (A : K.CompatibleCategory.{u, v}) :
    (localizedExtendComp f g).hom.app ((Q K).obj A) =
      (Q M).map ((compatibleExtendComp f g).hom.app A) := by
  simp only [localizedExtendComp, Localization.liftNatIso_hom, Localization.liftNatTrans_app,
    Localization.Lifting.iso, eqToIso.hom, eqToIso.inv, eqToHom_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app]
  change (𝟙 _) ≫ (Q M).map ((compatibleExtendComp f g).hom.app A) ≫ 𝟙 _ = _
  simp

set_option maxHeartbeats 600000 in
private theorem localizedExtend_id_left_obj (f : K ⟶ L) (B : K.CompatibleCategory.{u, v}) :
    (localizedExtendComp.{u, v} (𝟙 K) f).hom.app ((Q K).obj B) ≫
      (localizedExtend.{u, v} f).map ((localizedExtendId.{u, v} K).hom.app ((Q K).obj B)) =
      eqToHom (congrArg (fun e => (localizedExtend.{u, v} e).obj ((Q K).obj B)) (Category.id_comp f)) := by
  have hunit := localizedExtendId_hom_app (K := K) B
  have hmap := (congrArg (fun p => (localizedExtend.{u, v} f).map p) hunit).trans
    (localizedExtend_map f ((compatibleExtendId K).app B))
  let t := (compatibleExtendComp (𝟙 K) f).hom.app B
  let e := (compatibleExtend f).map ((compatibleExtendId K).app B)
  let h := congrArg (fun g => (compatibleExtend.{u, v} g).obj B) (Category.id_comp f)
  calc
    _ = (Q L).map t ≫ (Q L).map e :=
      congrArg₂ (fun p q => p ≫ q) (localizedExtendComp_hom_app (𝟙 K) f B) hmap
    _ = (Q L).map (t ≫ e) := ((Q L).map_comp t e).symm
    _ = (Q L).map (eqToHom h) := congrArg (fun p => (Q L).map p) (compatibleExtend_id_left f B)
    _ = _ := eqToHom_map (Q L) h

/-- The localized identity projection and tower comparison satisfy the left unit law. -/
theorem localizedExtend_id_left (f : K ⟶ L) (A : K.CompatibleAnalyticCategory.{u, v}) :
    (localizedExtendComp.{u, v} (𝟙 K) f).hom.app A ≫
      (localizedExtend.{u, v} f).map ((localizedExtendId.{u, v} K).hom.app A) =
      eqToHom (congrArg (fun e => (localizedExtend.{u, v} e).obj A) (Category.id_comp f)) := by
  obtain ⟨B, rfl⟩ := (localizedObjectEquiv (K := K.carrier)).surjective A
  exact localizedExtend_id_left_obj f B

/-- The localized identity projection and tower comparison satisfy the right unit law. -/
theorem localizedExtend_id_right (f : K ⟶ L) (A : K.CompatibleAnalyticCategory.{u, v}) :
    (localizedExtendComp.{u, v} f (𝟙 L)).hom.app A ≫
      (localizedExtendId.{u, v} L).hom.app ((localizedExtend f).obj A) =
      eqToHom (congrArg (fun e => (localizedExtend.{u, v} e).obj A) (Category.comp_id f)) := by
  obtain ⟨B, rfl⟩ := (localizedObjectEquiv (K := K.carrier)).surjective A
  change (localizedExtendComp f (𝟙 L)).hom.app ((Q K).obj B) ≫
      (localizedExtendId L).hom.app ((localizedExtend f).obj ((Q K).obj B)) = _
  let t := (compatibleExtendComp f (𝟙 L)).hom.app B
  let e := (compatibleExtendId L).app ((compatibleExtend f).obj B)
  let h := congrArg (fun g => (compatibleExtend.{u, v} g).obj B) (Category.comp_id f)
  calc
    _ = (Q L).map t ≫ (Q L).map e :=
      congrArg₂ (fun p q => p ≫ q) (localizedExtendComp_hom_app f (𝟙 L) B)
        (localizedExtendId_hom_app ((compatibleExtend f).obj B))
    _ = (Q L).map (t ≫ e) := ((Q L).map_comp t e).symm
    _ = (Q L).map (eqToHom h) := congrArg (fun p => (Q L).map p) (compatibleExtend_id_right f B)
    _ = _ := eqToHom_map (Q L) h

/-- The two tower comparisons for three field changes agree in the localization. -/
theorem localizedExtend_assoc (f : K ⟶ L) (g : L ⟶ M) (h : M ⟶ N)
    (A : K.CompatibleAnalyticCategory.{u, v}) :
    (localizedExtendComp.{u, v} (f ≫ g) h).hom.app A ≫
      (localizedExtend.{u, v} h).map ((localizedExtendComp.{u, v} f g).hom.app A) =
    eqToHom (congrArg (fun e => (localizedExtend.{u, v} e).obj A) (Category.assoc f g h)) ≫
      (localizedExtendComp.{u, v} f (g ≫ h)).hom.app A ≫
        (localizedExtendComp.{u, v} g h).hom.app ((localizedExtend.{u, v} f).obj A) := by
  obtain ⟨B, rfl⟩ := (localizedObjectEquiv (K := K.carrier)).surjective A
  change (localizedExtendComp (f ≫ g) h).hom.app ((Q K).obj B) ≫
      (localizedExtend h).map ((localizedExtendComp f g).hom.app ((Q K).obj B)) =
    eqToHom _ ≫ (localizedExtendComp f (g ≫ h)).hom.app ((Q K).obj B) ≫
      (localizedExtendComp g h).hom.app ((localizedExtend f).obj ((Q K).obj B))
  have hmap := (congrArg (fun p => (localizedExtend h).map p)
    (localizedExtendComp_hom_app f g B)).trans
      (localizedExtend_map h ((compatibleExtendComp f g).hom.app B))
  let t := (compatibleExtendComp (f ≫ g) h).hom.app B
  let e := (compatibleExtend h).map ((compatibleExtendComp f g).hom.app B)
  let a := (compatibleExtendComp f (g ≫ h)).hom.app B
  let b := (compatibleExtendComp g h).hom.app ((compatibleExtend f).obj B)
  let he := congrArg (fun p => (compatibleExtend.{u, v} p).obj B) (Category.assoc f g h)
  calc
    _ = (Q N).map t ≫ (Q N).map e :=
      congrArg₂ (fun p q => p ≫ q) (localizedExtendComp_hom_app (f ≫ g) h B) hmap
    _ = (Q N).map (t ≫ e) := ((Q N).map_comp t e).symm
    _ = (Q N).map (eqToHom he ≫ a ≫ b) :=
      congrArg (fun p => (Q N).map p) (compatibleExtend_assoc f g h B)
    _ = (Q N).map (eqToHom he) ≫ (Q N).map (a ≫ b) := (Q N).map_comp _ _
    _ = eqToHom _ ≫ (Q N).map a ≫ (Q N).map b :=
      congrArg₂ (fun p q => p ≫ q) (eqToHom_map (Q N) he) ((Q N).map_comp a b)
    _ = _ := congrArg (fun p => eqToHom _ ≫ p)
      (congrArg₂ (fun p q => p ≫ q) (localizedExtendComp_hom_app f (g ≫ h) B).symm
        (localizedExtendComp_hom_app g h ((compatibleExtend f).obj B)).symm)

end Langlands.Analytic.CompleteUltrametricField
