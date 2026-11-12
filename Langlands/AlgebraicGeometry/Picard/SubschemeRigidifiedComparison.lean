import Langlands.AlgebraicGeometry.Picard.QuotientActionLocality
import Langlands.AlgebraicGeometry.Picard.SubschemeRigidifiedDescent
import Langlands.AlgebraicGeometry.Picard.SubschemeRigidifiedLocal
import Langlands.AlgebraicGeometry.Picard.RelativeUnitGroupSchemes
import Langlands.AlgebraicGeometry.Picard.FieldEtaleFppfClassSheafStatement
import Langlands.AlgebraicGeometry.Picard.RelativePicardLocalRepresentatives

/-! # The etale-fppf comparison from a rigidifying finite subscheme -/

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.QuotientActionLocality.QuotientAction

open Langlands.AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} (D : QuotientAction S)

/-- If the action does not change the image under `forget : P ⟶ F`, `forget` is etale-locally
surjective and `forget ≫ toE = π`, then `toE` is etale-locally injective. -/
theorem isLocallyInjective_etale (hP : Presieve.IsSeparated (fppfTopology S) D.P)
    [Smooth D.q.hom.hom.left] [Surjective D.q.hom.hom.left]
    {F : (Over S)ᵒᵖ ⥤ Type (u + 1)} (forget : D.P ⟶ F) (toE : F ⟶ D.E)
    (fac : forget ≫ toE = D.π)
    (hact : ∀ {T : Over S} (h : T ⟶ D.H.X) (x : D.P.obj (op T)),
      forget.app (op T) (D.act h x) = forget.app (op T) x)
    [Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) forget] :
    Presheaf.IsLocallyInjective (Scheme.etaleTopology.over S) toE where
  equalizerSieve_mem {T} a b hab := by
    let J := Scheme.etaleTopology.over S
    have hR₀ : Presheaf.imageSieve forget a ⊓ Presheaf.imageSieve forget b ∈ J T.unop :=
      J.intersection_covering (Presheaf.imageSieve_mem J forget a)
        (Presheaf.imageSieve_mem J forget b)
    refine J.transitive hR₀ _ ?_
    rintro V h ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    have hxy : D.π.app (op V) x = D.π.app (op V) y := by
      rw [← fac, NatTrans.comp_app, ConcreteCategory.comp_apply,
        ConcreteCategory.comp_apply, hx, hy, NatTrans.naturality_apply,
        NatTrans.naturality_apply, hab]
    obtain ⟨R, hR, hRact⟩ := D.etale_locally_orbit hP x y hxy
    refine J.superset_covering ?_ hR
    intro W a ha
    obtain ⟨h', hh'⟩ := hRact a ha
    change F.map (a ≫ h).op _ = F.map (a ≫ h).op _
    rw [op_comp, Functor.map_comp_apply, Functor.map_comp_apply, ← hx, ← hy,
      ← NatTrans.naturality_apply, ← NatTrans.naturality_apply, hh', hact]

end Langlands.AlgebraicGeometry.Picard.QuotientActionLocality.QuotientAction

namespace Langlands.AlgebraicGeometry.Picard.SubschemeRigidification

open Langlands.AlgebraicGeometry.AlgebraicSpace QuotientActionLocality

section General

variable {S X Z : Scheme.{u}} (f : X ⟶ S) (g : Z ⟶ S) (z : Z ⟶ X) (hz : z ≫ f = g)
  (unique : ∀ (T : Over S) (L M : relative f g z hz T), Subsingleton (L ≅ M))

include unique in
/-- The presheaf of rigidified classes is separated for the slice fppf topology. -/
lemma classPresheaf_isSeparated_fppf :
    Presieve.IsSeparated (AlgebraicSpace.fppfTopology S) (classPresheaf f g z hz) := by
  apply QuotientActionLocality.isSeparated_fppf_of_zariski_of_affine
  · exact classPresheaf_isSeparated_zariski f g z hz unique
  · intro R R' φ hf hs s₀ fam x y hx hy
    have : Flat (Spec.map φ) := hf
    have : Surjective (Spec.map φ) := hs
    let m : Over.mk (Spec.map φ ≫ s₀) ⟶ Over.mk s₀ := Over.homMk (Spec.map φ)
    have : Flat m.left := hf
    have : Surjective m.left := hs
    have : QuasiCompact m.left := inferInstanceAs (QuasiCompact (Spec.map φ))
    have hxy := (hx m Presieve.singleton.mk).trans (hy m Presieve.singleton.mk).symm
    exact classes_flatSeparated f g z hz unique m x y hxy

/-- For finite `g`, forgetting rigidifications is etale-locally surjective; in fact every
ordinary class acquires a rigidification on an open neighbourhood of each point. -/
instance forgetClassNatTrans_isLocallySurjective [IsFinite g] :
    Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S)
      (forgetClassNatTrans f g z hz) := by
  constructor
  intro T s
  obtain ⟨L, rfl⟩ := RelativePicard.exists_representative f T s
  apply etale_mem_of_points
  intro t
  obtain ⟨W, incl, hincl, ht, q, hq⟩ := exists_open_rigidification f g z hz T L t
  have : IsOpenImmersion incl.left := hincl
  refine ⟨W, incl, ⟨q, ?_⟩, inferInstance, ht⟩
  change forgetClasses f g z hz W q = _
  rw [hq, RelativePicard.map_classOf]

end General

section Field

variable {k : Type u} [Field k] {X Z : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
  [IsProper f] (g : Z ⟶ Spec (CommRingCat.of k)) [IsFinite g] (z : Z ⟶ X) (hz : z ≫ f = g)

open RelativeUnitGroupSchemes

/-- Rigidified classes, with the action of the units of `Z` through the quotient `q`. -/
def quotientAction (Q : GroupScheme (Spec (CommRingCat.of k))) (q : fieldGroup g ⟶ Q)
    (hker : ∀ {T : Over (Spec (CommRingCat.of k))} (h : T ⟶ (fieldGroup g).X),
      h ≫ q.hom.hom = 1 ↔ fieldPointsEquiv g T h ∈
        (Units.map ((zRel f g z hz).app T).appTop.hom.toMonoidHom).range) :
    QuotientAction (Spec (CommRingCat.of k)) where
  P := classPresheaf f g z hz
  E := RelativePicard.classSheafPresheaf f
  π := forgetClassNatTrans f g z hz ≫ RelativePicard.toClassSheaf f
  H := fieldGroup g
  Q := Q
  q := q
  act {T} h x := actClasses f g z hz (fieldPointsEquiv g T h) x
  act_one x := by
    simp only [map_one]
    exact actClasses_one f g z hz x
  act_mul h h' x := by
    simp only [map_mul]
    exact actClasses_mul f g z hz _ _ x
  map_act {T T'} a h x := by
    change classesPullback f g z hz a _ = actClasses f g z hz _ (classesPullback f g z hz a x)
    rw [classesPullback_actClasses, pointsEquiv_comp]
    rfl
  π_act {T} h x := by
    change (RelativePicard.toClassSheaf f).app (op T)
        (forgetClasses f g z hz T (actClasses f g z hz _ x)) =
      (RelativePicard.toClassSheaf f).app (op T) (forgetClasses f g z hz T x)
    rw [forgetClasses_actClasses]
  act_eq_self_iff h x := by
    rw [actClasses_eq_self_iff, hker]
  locally_orbit {T} x y hxy := by
    refine ⟨_, Presheaf.equalizerSieve_mem (Scheme.fppfTopology.over _)
      (RelativePicard.toClassSheaf f) _ _ hxy, ?_⟩
    intro V a ha
    have h₁ : forgetClasses f g z hz V (classesPullback f g z hz a x) =
        forgetClasses f g z hz V (classesPullback f g z hz a y) := by
      have h₂ := ha
      change (RelativePicard.classPresheaf f).map a.op
          ((forgetClassNatTrans f g z hz).app (op T) x) =
        (RelativePicard.classPresheaf f).map a.op
          ((forgetClassNatTrans f g z hz).app (op T) y) at h₂
      rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply] at h₂
      exact h₂
    obtain ⟨r, hr⟩ := exists_eq_actClasses_of_forgetClasses_eq f g z hz _ _ h₁
    refine ⟨(fieldPointsEquiv g V).symm r, ?_⟩
    change classesPullback f g z hz a x =
      actClasses f g z hz (fieldPointsEquiv g V ((fieldPointsEquiv g V).symm r))
        (classesPullback f g z hz a y)
    rw [MulEquiv.apply_symm_apply]
    exact hr

/-- **The etale-fppf comparison from a rigidifying finite subscheme.** If `g : Z ⟶ Spec k` is
finite, `z : Z ⟶ X` lies over `k`, and pulling back global functions along every
`T ×_k Z ⟶ T ×_k X` is injective, then the etale sheafification of the relative Picard
classes of the proper `f` is an fppf sheaf. -/
theorem isSheaf_etaleClassSheafPresheaf_of_rigidifying
    (hinj : ∀ T, Function.Injective ((zRel f g z hz).app T).appTop) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of k)))
      (RelativePicard.etaleClassSheafPresheaf f) := by
  have unique := iso_subsingleton f g z hz hinj
  obtain ⟨Q, q, hQs, hQa, hfl, hsu, hlfp, haff, hsm, hker⟩ := exists_quotient f g z hz hinj
  let D := quotientAction f g z hz Q q hker
  have : Smooth D.Q.X.hom := hQs
  have : IsAffineHom D.Q.X.hom := hQa
  have : Flat D.q.hom.hom.left := hfl
  have : Surjective D.q.hom.hom.left := hsu
  have : LocallyOfFinitePresentation D.q.hom.hom.left := hlfp
  have : IsAffineHom D.q.hom.hom.left := haff
  have : Smooth D.q.hom.hom.left := hsm
  have hP : Presieve.IsSeparated (fppfTopology _) D.P :=
    classPresheaf_isSeparated_fppf f g z hz unique
  have hE : Presieve.IsSeparated (fppfTopology _) D.E :=
    ((_root_.CategoryTheory.isSheaf_iff_isSheaf_of_type _ _).mp
      (RelativePicard.classSheaf f).property).isSeparated
  have hπ : Presheaf.IsLocallySurjective (fppfTopology _) D.π := by
    have := Presheaf.isLocallySurjective_of_le
      (Sites.etaleTopologyOver_le_fppfTopologyOver (Spec (CommRingCat.of k)))
      (forgetClassNatTrans f g z hz) inferInstance
    change Presheaf.IsLocallySurjective _
      (forgetClassNatTrans f g z hz ≫ RelativePicard.toClassSheaf f)
    infer_instance
  have hsurj : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over _)
      (RelativePicard.toClassSheaf f) := by
    refine D.isLocallySurjective_etale hP hE (RelativePicard.toClassSheaf f) ?_ hπ
    intro U V m hm₁ hm₂ hm₃ _ p hp
    have : IsAffineHom m.left := hm₁
    have : Flat m.left := hm₂
    have : Surjective m.left := hm₃
    obtain ⟨y, hy⟩ := exists_descended_class f g z hz unique m p hp
    refine ⟨y, ?_⟩
    change (RelativePicard.classSheafPresheaf f).map m.op
        ((RelativePicard.toClassSheaf f).app (op V) y) =
      (RelativePicard.toClassSheaf f).app (op U)
        ((forgetClassNatTrans f g z hz).app (op U) p)
    rw [← NatTrans.naturality_apply, hy]
  have hinj' : Presheaf.IsLocallyInjective (Scheme.etaleTopology.over _)
      (RelativePicard.toClassSheaf f) :=
    D.isLocallyInjective_etale hP (forgetClassNatTrans f g z hz)
      (RelativePicard.toClassSheaf f) rfl
      (fun {T} h x ↦ forgetClasses_actClasses f g z hz _ x)
  have hη : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over _)
      (RelativePicard.toEtaleClassSheaf f) := by
    change Presheaf.IsLocallySurjective _ (toSheafify _ (RelativePicard.classPresheaf f))
    infer_instance
  have h₁ : Sheaf.IsLocallyInjective (RelativePicard.etaleToFppfClassSheaf f) :=
    Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac _
      (RelativePicard.toClassSheaf f) (RelativePicard.toEtaleClassSheaf_etaleToFppf f)
  have h₂ : Sheaf.IsLocallySurjective (RelativePicard.etaleToFppfClassSheaf f) :=
    Presheaf.isLocallySurjective_of_isLocallySurjective_fac _
      (RelativePicard.toEtaleClassSheaf_etaleToFppf f)
  exact (RelativePicard.etaleToFppfClassSheaf_isIso_iff f).mp
    ((Sheaf.isLocallyBijective_iff_isIso _).mp ⟨h₁, h₂⟩)

end Field

end Langlands.AlgebraicGeometry.Picard.SubschemeRigidification
