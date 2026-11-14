import Langlands.AlgebraicGeometry.Picard.TwoAxisClassMurreConditionsStatement
import Langlands.AlgebraicGeometry.Picard.TwoAxisClassProductBaseChange
import Langlands.AlgebraicGeometry.Picard.TwoAxisBundleNormalization
import Langlands.AlgebraicGeometry.Picard.NoetherianLineBundleSeesawProof
import Langlands.AlgebraicGeometry.NoetherianApproximation.LineBundleQuotientDescent
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_nonempty_iso_pullback_of_nonempty_iso_pullback_of_isDirectLimit
import Mathlib.CategoryTheory.Presentable.Directed
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-! # Proof of Murre's (F2) for the two-axis class presheaf -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Picard

namespace TwoAxisClassFilteredColimits

section DirectLimit

variable {R' : Type u} [CommRing R'] {α : Type u} [PartialOrder α] [IsDirected α (· ≤ ·)]
  [Nonempty α] (K : α ⥤ CommAlgCat.{u} R')

/-- The transition ring maps of a directed diagram of algebras. -/
abbrev transition (a b : α) (h : a ≤ b) : K.obj a →+* K.obj b :=
  ((K.map (homOfLE h)).hom : K.obj a →+* K.obj b)

instance directedSystem :
    DirectedSystem (fun a ↦ (K.obj a : Type u)) fun a b h ↦ ⇑(transition K a b h) where
  map_self a x := by
    have : homOfLE (le_refl a) = 𝟙 a := Subsingleton.elim _ _
    show (K.map (homOfLE (le_refl a))).hom x = x
    rw [this, K.map_id]; rfl
  map_map {a b c} hab hbc x := by
    have : homOfLE (hab.trans hbc) = homOfLE hab ≫ homOfLE hbc := Subsingleton.elim _ _
    show (K.map (homOfLE hbc)).hom ((K.map (homOfLE hab)).hom x) =
      (K.map (homOfLE (hab.trans hbc))).hom x
    rw [this, K.map_comp]; rfl

/-- The ring maps of a cocone over a directed diagram of algebras. -/
abbrev coconeMap (c : Cocone K) (a : α) : K.obj a →+* (c.pt : Type u) :=
  (c.ι.app a).hom.toRingHom

/-- The forgetful functor from commutative algebras to types preserves colimits of directed
diagrams. -/
theorem isColimit_forget_mapCocone {c : Cocone K} (hc : IsColimit c) :
    Nonempty (IsColimit ((forget (CommAlgCat.{u} R')).mapCocone c)) := by
  have : IsFiltered α := inferInstance
  have : IsConnected α := IsFiltered.isConnected α
  let E : CommAlgCat.{u} R' ⥤ Type u := (commAlgCatEquivUnder (CommRingCat.of R')).functor ⋙
    Under.forget _ ⋙ forget CommRingCat
  have hE : IsColimit (E.mapCocone c) := isColimitOfPreserves E hc
  exact ⟨hE⟩

/-- The colimit of a directed diagram of algebras is the direct limit of the underlying rings. -/
theorem isDirectLimit {c : Cocone K} (hc : IsColimit c) :
    IsDirectLimit (fun a b h ↦ ⇑(transition K a b h))
      fun a ↦ ⇑(coconeMap K c a) := by
  obtain ⟨hc'⟩ := isColimit_forget_mapCocone K hc
  refine ⟨fun x ↦ ?_, fun a b xa xb h ↦ ?_, fun a b h x ↦ ?_⟩
  · obtain ⟨a, y, hy⟩ := Types.jointly_surjective_of_isColimit hc'
      (show ((forget (CommAlgCat.{u} R')).mapCocone c).pt from x)
    exact ⟨a, y, hy⟩
  · obtain ⟨k, f, g, hfg⟩ := (Types.FilteredColimit.isColimit_eq_iff _ hc').1 h
    exact ⟨k, leOfHom f, leOfHom g, hfg⟩
  · exact congrArg (fun φ : K.obj a ⟶ c.pt ↦ φ.hom x) (c.w (homOfLE h))

end DirectLimit

section Classes

open Langlands.AbelianScheme TwoAxisFamily TwoAxisRigidifiedLineBundle UnramifiedFunctor
open NoetherianApproximation (nonempty_iso_pullback_of_fac)

variable {S : Scheme.{u}} (A : Langlands.AbelianScheme S) {R' : Type u} [CommRing R']
  (f : Spec (CommRingCat.of R') ⟶ S)

/-- Restriction along an algebra map followed by the structure map is the structure map. -/
lemma algHomOver_comp_algebraOverBase {C D : Type u} [CommRing C] [Algebra R' C] [CommRing D]
    [Algebra R' D] (φ : C →ₐ[R'] D) :
    algHomOver f φ ≫ algebraOverBase f C = algebraOverBase f D := by
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, algHomOver, algebraOverBase, Over.homMk_left]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, AlgHom.comp_algebraMap]

variable {α : Type u} [PartialOrder α] [IsDirected α (· ≤ ·)] [Nonempty α]
  (K : α ⥤ CommAlgCat.{u} R')

/-- Every class over the colimit of a directed diagram of algebras comes from a class over
some algebra of the diagram. -/
theorem exists_classesPullback_eq {c : Cocone K} (hc : IsColimit c)
    (x : Classes A (algebraOver f c.pt)) :
    ∃ (j : α) (y : Classes A (algebraOver f (K.obj j))),
      classesPullback A (algHomOver f (c.ι.app j).hom) y = x := by
  induction x using Quotient.inductionOn with | h L => ?_
  let U : Over S := Over.mk f
  obtain ⟨j, M₀, hM₀, hdesc⟩ :=
    NoetherianApproximation.exists_lineBundle_descent_of_isDirectLimit (A₀ := R')
      (transition K) (coconeMap K c) (isDirectLimit K hc)
      (fun i j h ↦ (K.map (homOfLE h)).hom.comp_algebraMap)
      (fun i ↦ (c.ι.app i).hom.comp_algebraMap)
      (mumfordProduct (abelian A U)).hom (productMap A (algebraOverBase f c.pt))
      (mumfordProduct (abelian A (algebraOver f c.pt))).hom
      (productMap_isPullback A (algebraOverBase f c.pt)) L.obj.carrier L.property
  let hj := algebraOverBase f (K.obj j)
  let h' := algHomOver f (c.ι.app j).hom
  let κ : (mumfordProduct (abelian A (algebraOver f (K.obj j)))).left ⟶
      pullback (mumfordProduct (abelian A U)).hom
        (Spec.map (CommRingCat.ofHom (algebraMap R' (K.obj j)))) :=
    pullback.lift (productMap A hj) (mumfordProduct _).hom (productMap_isPullback A hj).w
  obtain ⟨e₀⟩ := hdesc (productMap A h' ≫ κ)
    (by
      rw [Category.assoc, pullback.lift_fst, ← productMap_comp,
        algHomOver_comp_algebraOverBase]
      rfl)
    (by rw [Category.assoc, pullback.lift_snd]; exact (productMap_isPullback A h').w)
  let E : LineBundle (mumfordProduct (abelian A (algebraOver f (K.obj j)))).left :=
    (LineBundle.pullback κ).obj ⟨M₀, hM₀⟩
  let D : LineBundle (mumfordProduct (abelian A (algebraOver f c.pt))).left :=
    ⟨L.obj.carrier, L.property⟩
  let e : (Scheme.Modules.pullback (productMap A h')).obj E.obj ≅ D.obj :=
    (Scheme.Modules.pullbackComp (productMap A h') κ).app M₀ ≪≫ e₀
  let A' := abelian A (algebraOver f (K.obj j))
  refine ⟨j, ⟦ofLineBundle (LineBundle.twoAxisNormalizedBundle
      Langlands.Scheme.Modules.pullbackTensorComparisonIsIso A' E)
    (LineBundle.twoAxisNormalizedBundleRigidification
      Langlands.Scheme.Modules.pullbackTensorComparisonIsIso A' E)⟧, ?_⟩
  rw [classesPullback_mk]
  apply mk_eq_mk_of_carrierIso
  exact LineBundle.twoAxisNormalizedBundleRestrictionIso
    Langlands.Scheme.Modules.pullbackTensorComparisonIsIso A'
    (abelian A (algebraOver f c.pt)) (productMap A h') (carrierMap A h')
    (productMap_fst A h') (productMap_snd A h') (first_naturality A h') (second_naturality A h')
    E D e L.obj.rigidification.first.symm L.obj.rigidification.second.symm

/-- Two classes over an algebra of a directed diagram that agree over the colimit already agree
over some later algebra of the diagram. -/
theorem exists_classesPullback_eq_of_eq {c : Cocone K} (hc : IsColimit c) (i : α)
    (x y : Classes A (algebraOver f (K.obj i)))
    (hxy : classesPullback A (algHomOver f (c.ι.app i).hom) x =
      classesPullback A (algHomOver f (c.ι.app i).hom) y) :
    ∃ (j : α) (hij : i ≤ j), classesPullback A (algHomOver f (K.map (homOfLE hij)).hom) x =
      classesPullback A (algHomOver f (K.map (homOfLE hij)).hom) y := by
  induction x using Quotient.inductionOn with | h L => ?_
  induction y using Quotient.inductionOn with | h M => ?_
  rw [classesPullback_mk, classesPullback_mk] at hxy
  obtain ⟨E⟩ := nonempty_carrierIso_of_mk_eq_mk A hxy
  let fX := (mumfordProduct (abelian A (algebraOver f (K.obj i)))).hom
  let hi := algHomOver f (c.ι.app i).hom
  have hpb := productMap_isPullback A hi
  let θ := hpb.lift (pullback.fst fX (Spec.map (CommRingCat.ofHom (coconeMap K c i))))
    (pullback.snd fX (Spec.map (CommRingCat.ofHom (coconeMap K c i)))) pullback.condition
  have h₀ := nonempty_iso_pullback_of_fac θ (hpb.lift_fst _ _ _) ⟨E⟩
  obtain ⟨j, hij, ⟨E'⟩⟩ :=
    Scheme.Modules.exists_nonempty_iso_pullback_of_nonempty_iso_pullback_of_isDirectLimit
      (transition K) (coconeMap K c) (isDirectLimit K hc) i fX L.obj.carrier M.obj.carrier
      (isInvertible_of_isLocallyFreeRankOne L.property)
      (isInvertible_of_isLocallyFreeRankOne M.property) h₀
  let k := algHomOver f (K.map (homOfLE hij)).hom
  have hpbk := productMap_isPullback A k
  let κ : (mumfordProduct (abelian A (algebraOver f (K.obj j)))).left ⟶
      pullback fX (Spec.map (CommRingCat.ofHom (transition K i j hij))) :=
    pullback.lift (productMap A k) (mumfordProduct _).hom hpbk.w
  obtain ⟨E''⟩ := nonempty_iso_pullback_of_fac κ (pullback.lift_fst _ _ _) ⟨E'⟩
  refine ⟨j, hij, ?_⟩
  rw [classesPullback_mk, classesPullback_mk]
  exact mk_eq_mk_of_carrierIso A E''

omit [IsDirected α (· ≤ ·)] [Nonempty α] in
lemma mapCocone_ι_app_apply {c : Cocone K} (i : α) (x : Classes A (algebraOver f (K.obj i))) :
    ((algebraFunctor f ⋙ classPresheaf A).mapCocone c).ι.app i x =
      classesPullback A (algHomOver f (c.ι.app i).hom) x :=
  rfl

omit [IsDirected α (· ≤ ·)] [Nonempty α] in
lemma comp_map_apply {i j : α} (g : i ⟶ j) (x : Classes A (algebraOver f (K.obj i))) :
    (K ⋙ algebraFunctor f ⋙ classPresheaf A).map g x =
      classesPullback A (algHomOver f (K.map g).hom) x :=
  rfl

/-- For a directed diagram of algebras, the class presheaf sends the colimit cocone to a
colimit cocone of types. -/
def isColimitMapCocone {c : Cocone K} (hc : IsColimit c) :
    IsColimit ((algebraFunctor f ⋙ classPresheaf A).mapCocone c) :=
  Types.FilteredColimit.isColimitOf' _ _
    (fun x ↦ by
      obtain ⟨j, y, hy⟩ := exists_classesPullback_eq A f K hc x
      exact ⟨j, y, by rw [mapCocone_ι_app_apply, hy]⟩)
    (fun i x y hxy ↦ by
      rw [mapCocone_ι_app_apply, mapCocone_ι_app_apply] at hxy
      obtain ⟨j, hij, h⟩ := exists_classesPullback_eq_of_eq A f K hc i x y hxy
      refine ⟨j, homOfLE hij, ?_⟩
      rw [comp_map_apply, comp_map_apply]
      exact h)

end Classes

end TwoAxisClassFilteredColimits

open TwoAxisRigidifiedLineBundle UnramifiedFunctor TwoAxisClassFilteredColimits in
/-- Murre's condition (F2) holds for the two-axis class presheaf of every abelian scheme over the
spectrum of a noetherian ring. -/
theorem noetherianTwoAxisClassFilteredColimits :
    NoetherianTwoAxisClassFilteredColimitsStatement.{u} := by
  intro R _ _ A R' _ f _
  refine ⟨fun J _ _ ↦ ⟨fun {K} ↦ ⟨fun {c} hc ↦ ?_⟩⟩⟩
  obtain ⟨α, _, _, _, Φ, _⟩ := IsFiltered.exists_directed J
  have hc' : IsColimit (c.whisker Φ) := (Functor.Final.isColimitWhiskerEquiv Φ c).symm hc
  let G := algebraFunctor f ⋙ classPresheaf A
  have h₁ : IsColimit (G.mapCocone (c.whisker Φ)) := isColimitMapCocone A f (Φ ⋙ K) hc'
  have h₂ : IsColimit ((G.mapCocone c).whisker Φ) :=
    IsColimit.ofIsoColimit h₁ (Functor.mapCoconeWhisker G)
  exact ⟨Functor.Final.isColimitWhiskerEquiv Φ _ h₂⟩

end Langlands.AlgebraicGeometry.Picard
