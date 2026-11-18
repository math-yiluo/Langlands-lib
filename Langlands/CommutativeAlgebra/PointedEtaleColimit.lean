import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RingHom.Etale

/-! # Strict locality of pointed étale colimits -/

universe u

open CategoryTheory Limits Polynomial

namespace Langlands.CommutativeAlgebra.PointedEtaleColimit

variable {J : Type u} [SmallCategory J] {F : J ⥤ CommRingCat.{u}}
  {Ω : Type u} [Field Ω]

/-- Every étale extension of a stage with a compatible point in `Ω` maps,
preserving that point, to a later stage over the original one. -/
def Refines (point : F ⟶ (Functor.const J).obj (CommRingCat.of Ω)) : Prop :=
  ∀ (i : J) (B : CommRingCat.{u}) (f : F.obj i ⟶ B) (p : B ⟶ CommRingCat.of Ω),
    f.hom.Etale → f ≫ p = point.app i →
    ∃ (j : J) (g : i ⟶ j) (e : B ⟶ F.obj j),
      f ≫ e = F.map g ∧ e ≫ point.app j = p

variable {c : Cocone F} (hc : IsColimit c)
  (point : F ⟶ (Functor.const J).obj (CommRingCat.of Ω))

/-- The map from the colimit induced by the compatible points of the stages. -/
def fieldMap : c.pt ⟶ CommRingCat.of Ω := hc.desc (Cocone.mk _ point)

@[reassoc (attr := simp)]
theorem ι_fieldMap (i : J) : c.ι.app i ≫ fieldMap hc point = point.app i :=
  hc.fac (Cocone.mk _ point) i

private theorem extendToColimit (hr : Refines point) (i : J) (B : CommRingCat.{u})
    (f : F.obj i ⟶ B) (p : B ⟶ CommRingCat.of Ω)
    (hf : f.hom.Etale) (hp : f ≫ p = point.app i) :
    ∃ q : B ⟶ c.pt, f ≫ q = c.ι.app i ∧ q ≫ fieldMap hc point = p := by
  obtain ⟨j, g, e, he, he'⟩ := hr i B f p hf hp
  refine ⟨e ≫ c.ι.app j, ?_, ?_⟩
  · rw [← Category.assoc, he, c.w]
  · rwa [Category.assoc, ι_fieldMap]

variable [IsFiltered J]

private theorem isUnit_of_fieldMap_ne_zero (hr : Refines point) {y : c.pt}
    (hy : (fieldMap hc point).hom y ≠ 0) : IsUnit y := by
  obtain ⟨i, x, hx⟩ :=
    Types.jointly_surjective_of_isColimit (isColimitOfPreserves (forget CommRingCat) hc) y
  change (F.obj i : Type u) at x
  change (c.ι.app i).hom x = y at hx
  let φi : (F.obj i : Type u) →+* Ω := (point.app i).hom
  have hpoint : IsUnit (φi x) := by
    apply isUnit_iff_ne_zero.mpr
    change (point.app i).hom x ≠ (0 : Ω)
    rw [← ι_fieldMap hc point i]
    simpa only [CommRingCat.hom_comp, RingHom.comp_apply, hx] using hy
  let B := CommRingCat.of (Localization.Away x)
  let f : F.obj i ⟶ B := CommRingCat.ofHom (algebraMap (F.obj i) (Localization.Away x))
  let p : B ⟶ CommRingCat.of Ω :=
    CommRingCat.ofHom (IsLocalization.Away.lift (S := Localization.Away x) x hpoint)
  have hf : f.hom.Etale :=
    RingHom.etale_algebraMap.mpr (Algebra.Etale.of_isLocalizationAway x)
  have hp : f ≫ p = point.app i := by
    ext1
    exact IsLocalization.Away.lift_comp x hpoint
  obtain ⟨q, hq, _⟩ := extendToColimit hc point hr i B f p hf hp
  have hunit := (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away x) x).map q.hom
  change IsUnit ((f ≫ q).hom x) at hunit
  rwa [hq, hx] at hunit

theorem isLocalHom_fieldMap (hr : Refines point) : IsLocalHom (fieldMap hc point).hom :=
  ⟨fun _ h ↦ isUnit_of_fieldMap_ne_zero hc point hr h.ne_zero⟩

include hc in
theorem isLocalRing (hr : Refines point) : IsLocalRing c.pt := by
  let : Nontrivial c.pt := (fieldMap hc point).hom.domain_nontrivial
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x ↦ ?_
  by_cases hx : (fieldMap hc point).hom x = 0
  · exact Or.inr (isUnit_of_fieldMap_ne_zero hc point hr (by simp [hx]))
  · exact Or.inl (isUnit_of_fieldMap_ne_zero hc point hr hx)

theorem ker_fieldMap [IsLocalRing c.pt] (hr : Refines point) :
    RingHom.ker (fieldMap hc point).hom = IsLocalRing.maximalIdeal c.pt := by
  ext x
  rw [RingHom.mem_ker, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  exact ⟨fun hx hu ↦ (hu.map (fieldMap hc point).hom).ne_zero hx,
    fun h ↦ by_contradiction fun hx ↦ h (isUnit_of_fieldMap_ne_zero hc point hr hx)⟩

include hc in
private theorem descends_monic (f : c.pt[X]) (hf : f.Monic) :
    ∃ (i : J) (g : (F.obj i)[X]), g.map (c.ι.app i).hom = f ∧ g.Monic := by
  classical
  have hc' := isColimitOfPreserves (forget CommRingCat) hc
  choose i x hx using fun n : Fin (f.natDegree + 1) ↦
    Types.jointly_surjective_of_isColimit hc' (f.coeff n)
  obtain ⟨j, hj⟩ := IsFiltered.sup_objs_exists (Finset.univ.image i)
  have hmap (n : Fin (f.natDegree + 1)) : Nonempty (i n ⟶ j) :=
    hj (Finset.mem_image_of_mem i (Finset.mem_univ n))
  have hlift : f ∈ lifts (c.ι.app j).hom := (lifts_iff_coeff_lifts f).mpr fun n ↦ by
    by_cases hn : n < f.natDegree + 1
    · let k : Fin (f.natDegree + 1) := ⟨n, hn⟩
      let g := (hmap k).some
      exact ⟨(F.map g).hom (x k), (congr($(c.w g).hom (x k))).trans (hx k)⟩
    · exact ⟨0, (map_zero _).trans (coeff_eq_zero_of_natDegree_lt (by omega)).symm⟩
  obtain ⟨g, hg, _, hgm⟩ := lifts_and_natDegree_eq_and_monic hlift hf
  exact ⟨j, g, hg, hgm⟩

/-- A simple root of a monic polynomial over the colimit at the compatible
point in `Ω` lifts to a root in the colimit. -/
theorem exists_root_of_simple_root (hr : Refines point) (f : c.pt[X]) (hf : f.Monic)
    (a : Ω) (ha : f.eval₂ (fieldMap hc point).hom a = 0)
    (ha' : f.derivative.eval₂ (fieldMap hc point).hom a ≠ 0) :
    ∃ b : c.pt, f.IsRoot b ∧ (fieldMap hc point).hom b = a := by
  obtain ⟨i, g, hg, hgm⟩ := descends_monic hc f hf
  let φi : (F.obj i : Type u) →+* Ω := (point.app i).hom
  have hpoint : (fieldMap hc point).hom.comp (c.ι.app i).hom = φi :=
    congr($(ι_fieldMap hc point i).hom)
  have hroot : g.eval₂ φi a = 0 := by
    simpa only [← hg, eval₂_map, hpoint] using ha
  have hderiv : g.derivative.eval₂ φi a ≠ 0 := by
    simpa only [← hg, derivative_map, eval₂_map, hpoint] using ha'
  let P : StandardEtalePair (F.obj i) := ⟨g, hgm, g.derivative, ⟨1, 0, 1, by simp⟩⟩
  let B := CommRingCat.of P.Ring
  let e : F.obj i ⟶ B := CommRingCat.ofHom (algebraMap (F.obj i) P.Ring)
  let : Algebra (F.obj i) Ω := φi.toAlgebra
  have h : P.HasMap a := by
    change g.eval₂ φi a = 0 ∧ IsUnit (g.derivative.eval₂ φi a)
    exact ⟨hroot, isUnit_iff_ne_zero.mpr hderiv⟩
  let p : B ⟶ CommRingCat.of Ω := CommRingCat.ofHom (P.lift a h).toRingHom
  have he : e.hom.Etale := RingHom.etale_algebraMap.mpr inferInstance
  have hp : e ≫ p = point.app i := by
    ext1
    exact (P.lift a h).comp_algebraMap
  obtain ⟨q, hq, hqp⟩ := extendToColimit hc point hr i B e p he hp
  refine ⟨q.hom P.X, ?_, ?_⟩
  · have hX : g.eval₂ (algebraMap (F.obj i) P.Ring) P.X = 0 := P.hasMap_X.1
    have hcoeff : q.hom.comp (algebraMap (F.obj i) P.Ring) = (c.ι.app i).hom :=
      congr($(hq).hom)
    rw [IsRoot.def, ← hg, eval_map, ← hcoeff, ← hom_eval₂, hX, map_zero]
  · exact congr($(hqp).hom P.X).trans (P.lift_X a h)

include hc in
theorem henselianLocalRing (hr : Refines point) : HenselianLocalRing c.pt := by
  let : IsLocalRing c.pt := isLocalRing hc point hr
  refine { toIsLocalRing := inferInstance, is_henselian := ?_ }
  intro f hf a₀ h₀ h'
  have hker := ker_fieldMap hc point hr
  rw [← hker, RingHom.mem_ker] at h₀
  obtain ⟨a, ha, ha₀⟩ :=
    exists_root_of_simple_root hc point hr f hf ((fieldMap hc point).hom a₀)
      (by simpa only [eval₂_at_apply] using h₀)
      (by simpa only [eval₂_at_apply] using (h'.map (fieldMap hc point).hom).ne_zero)
  refine ⟨a, ha, ?_⟩
  rw [← hker, RingHom.mem_ker, map_sub, ha₀, sub_self]

include hc in
theorem isSepClosed_residueField [IsSepClosed Ω] [IsLocalRing c.pt] (hr : Refines point) :
    IsSepClosed (IsLocalRing.ResidueField c.pt) := by
  let : IsLocalHom (fieldMap hc point).hom := isLocalHom_fieldMap hc point hr
  let k := IsLocalRing.ResidueField c.pt
  let r : c.pt →+* k := IsLocalRing.residue c.pt
  let e : k →+* Ω := IsLocalRing.ResidueField.lift (fieldMap hc point).hom
  have he : e.comp r = (fieldMap hc point).hom :=
    IsLocalRing.ResidueField.lift_comp_residue _
  refine IsSepClosed.of_exists_root k fun p hp hirr hsep ↦ ?_
  have hlift : p ∈ lifts r := mem_lifts_of_surjective IsLocalRing.residue_surjective p
  obtain ⟨f, hf, _, hfm⟩ := lifts_and_degree_eq_and_monic hlift hp
  obtain ⟨a, ha⟩ := IsSepClosed.exists_root (p.map e)
    (by rw [hp.degree_map]; exact (degree_pos_of_irreducible hirr).ne') hsep.map
  have hroot : p.eval₂ e a = 0 := (eval_map e a).symm.trans ha
  have hderiv := hsep.eval₂_derivative_ne_zero e hroot
  obtain ⟨b, hb, _⟩ := exists_root_of_simple_root hc point hr f hfm a
    (by simpa only [← hf, eval₂_map, he] using hroot)
    (by simpa only [← hf, derivative_map, eval₂_map, he] using hderiv)
  refine ⟨r b, ?_⟩
  rw [← hf, eval_map, eval₂_at_apply, hb, map_zero]

end Langlands.CommutativeAlgebra.PointedEtaleColimit
