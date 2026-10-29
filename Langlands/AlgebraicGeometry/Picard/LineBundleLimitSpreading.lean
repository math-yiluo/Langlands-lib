import Langlands.AlgebraicGeometry.Picard.LineBundleDescent
import Mathlib.AlgebraicGeometry.AffineTransitionLimit

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.SchemeModule Langlands.SchemeModule.LineBundleDescent

/-- In a cofiltered category, finitely many properties, each satisfied by some object and each
stable under passing to the source of a morphism, are satisfied by a common object. -/
lemma exists_forall_of_isCofiltered {C : Type*} [Category C] [IsCofiltered C]
    {J : Type*} [Finite J] (P : J → C → Prop) (hP : ∀ j {X Y : C} (_ : X ⟶ Y), P j Y → P j X)
    (h : ∀ j, ∃ X, P j X) : ∃ X, ∀ j, P j X := by
  classical
  choose X hX using h
  cases nonempty_fintype J
  obtain ⟨S, hS⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image X)
  exact ⟨S, fun j ↦ hP j (hS (Finset.mem_image_of_mem X (Finset.mem_univ j))).some (hX j)⟩

lemma appLE_eq_of_eq {X Y : Scheme.{u}} {f g : X ⟶ Y}
    (h : f = g) (U : Y.Opens) (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U) :
    f.appLE U V e = g.appLE U V (h ▸ e) := by
  subst h
  rfl

lemma map_injective_of_le_of_le {Y : Scheme.{u}} (A : Y.Modules) {V W : Y.Opens} (h : W ≤ V)
    (h' : V ≤ W) : Function.Injective (A.presheaf.map (homOfLE h).op) := fun a b hab ↦ by
  have := congrArg (A.presheaf.map (homOfLE h').op) hab
  rwa [map_map_apply, map_map_apply, map_id_apply, map_id_apply] at this

variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)

lemma preimage_π_app_preimage_map {i j : I} (f : j ⟶ i) (V : (D.obj i).Opens) :
    c.π.app j ⁻¹ᵁ (D.map f ⁻¹ᵁ V) = c.π.app i ⁻¹ᵁ V :=
  congr($(c.w f) ⁻¹ᵁ V)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
open Scheme.Opens in
include hc in
/-- A section over the preimage of an affine open of a stage of a cofiltered limit comes from
some later stage. -/
lemma exists_appLE_eq_of_isAffineOpen [IsCofiltered I]
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)] {i : I} {V : (D.obj i).Opens}
    (hV : IsAffineOpen V) (r : Γ(c.pt, c.π.app i ⁻¹ᵁ V)) :
    ∃ (j : I) (f : j ⟶ i) (s : Γ(D.obj j, D.map f ⁻¹ᵁ V)),
      (c.π.app j).appLE (D.map f ⁻¹ᵁ V) (c.π.app i ⁻¹ᵁ V)
        (preimage_π_app_preimage_map D c f V).ge s = r := by
  have (j : _) : IsAffine ((opensDiagram D i V).op.obj j).unop := hV.preimage _
  have (j : _) : IsAffine ((opensDiagram D i V).obj j) := hV.preimage _
  obtain ⟨⟨j⟩, s, hs⟩ := (Types.jointly_surjective_of_isColimit (isColimitOfPreserves
    (Scheme.Γ ⋙ forget _) (isLimitOpensCone D c hc i V).op) ((c.π.app i ⁻¹ᵁ V).topIso.inv r))
  obtain ⟨s, rfl⟩ := (D.map j.hom ⁻¹ᵁ V).topIso.symm.commRingCatIsoToRingEquiv.surjective s
  have h : c.π.app j.left ⁻¹ᵁ D.map j.hom ⁻¹ᵁ V = c.π.app i ⁻¹ᵁ V := congr($(c.w j.hom) ⁻¹ᵁ V)
  have : r = (c.π.app j.left).appLE (D.map j.hom ⁻¹ᵁ V) (c.π.app i ⁻¹ᵁ V) h.ge s := by
    convert!
      show r = ((topIso _).inv ≫ ((opensCone D c i V).π.app j).appTop ≫ (topIso _).hom) s from
        (c.π.app i ⁻¹ᵁ V).topIso.commRingCatIsoToRingEquiv.symm_apply_eq.mp hs.symm using 3
    simp [Scheme.Hom.app_eq_appLE, Scheme.Hom.resLE_appLE]
  exact ⟨j.left, j.hom, s, this.symm⟩

include hc in
lemma exists_appLE_eq_of_isAffineOpen' [IsCofiltered I]
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)] {i : I} {V : (D.obj i).Opens}
    (hV : IsAffineOpen V) {W : c.pt.Opens} (hW : W = c.π.app i ⁻¹ᵁ V) (r : Γ(c.pt, W)) :
    ∃ (j : I) (f : j ⟶ i) (s : Γ(D.obj j, D.map f ⁻¹ᵁ V)),
      (c.π.app j).appLE (D.map f ⁻¹ᵁ V) W
        (hW.trans (preimage_π_app_preimage_map D c f V).symm).le s = r := by
  subst hW
  exact exists_appLE_eq_of_isAffineOpen D c hc hV r

include hc in
/-- Spreading of a line bundle with finitely many sections with affine covering loci along a
cofiltered limit of qcqs schemes with affine transition maps, provided every projection is
surjective and injective on sections. -/
theorem exists_lineBundle_of_isLimit [IsCofiltered I]
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, CompactSpace (D.obj i)]
    [∀ i, QuasiSeparatedSpace (D.obj i)]
    (hinj : ∀ i (V : (D.obj i).Opens), Function.Injective ((c.π.app i).app V))
    (hsurj : ∀ i, Function.Surjective (c.π.app i).base)
    (F : c.pt.Modules) {J : Type*} [Finite J] (t : J → GlobalSections F)
    (hcov : ∀ x, ∃ j, x ∈ trivializationOpen F (t j))
    (haff : ∀ j, IsAffineOpen (trivializationOpen F (t j))) :
    ∃ (i : I) (M : LineBundle (D.obj i)) (s : J → GlobalSections M.obj),
      (∀ x, ∃ j, x ∈ trivializationOpen M.obj (s j)) ∧
        ∀ j, IsAffineOpen (trivializationOpen M.obj (s j)) := by
  classical
  let U : J → c.pt.Opens := fun j ↦ trivializationOpen F (t j)
  have hUcov : IsOpenCover U := by
    refine top_le_iff.mp fun x _ ↦ ?_
    obtain ⟨j, hj⟩ := hcov x
    exact Opens.mem_iSup.mpr ⟨j, hj⟩
  obtain ⟨i, V, hVcov, hV⟩ :=
    Scheme.exists_isOpenCover_and_isAffine_of_finite D c hc U hUcov haff
  have htriv : ∀ l, TrivializesOn F (t l) (U l) := fun l ↦
    (maximalTrivialization c.pt F (t l) (U l)).mpr le_rfl
  have hg : ∀ k l, ∃ g : Γ(c.pt, U l), (sectionHom F (t l)).app (U l) g =
      F.presheaf.map (homOfLE (show U l ≤ ⊤ from le_top)).op (t k) := fun k l ↦
    ((trivializesOn_iff_bijective F (t l) (U l)).mp (htriv l) (U l) le_rfl).2 _
  choose g hg using hg
  have hUS : ∀ (S : Over i) l, U l = c.π.app S.left ⁻¹ᵁ (D.map S.hom ⁻¹ᵁ V l) := fun S l ↦
    (hV l).2.trans (preimage_π_app_preimage_map D c S.hom (V l)).symm
  let P : J × J → Over i → Prop := fun kl S ↦
    ∃ a : Γ(D.obj S.left, D.map S.hom ⁻¹ᵁ V kl.2),
      (c.π.app S.left).appLE (D.map S.hom ⁻¹ᵁ V kl.2) (U kl.2) (hUS S kl.2).le a = g kl.1 kl.2
  have hPmono : ∀ kl {S T : Over i} (f : S ⟶ T), P kl T → P kl S := by
    rintro ⟨k, l⟩ S T f ⟨a, ha⟩
    have hle : D.map S.hom ⁻¹ᵁ V l ≤ D.map f.left ⁻¹ᵁ (D.map T.hom ⁻¹ᵁ V l) := by
      rw [← Over.w f, Functor.map_comp]
      rfl
    refine ⟨(D.map f.left).appLE _ _ hle a, ?_⟩
    rw [← ha, ← ConcreteCategory.comp_apply, Scheme.Hom.appLE_comp_appLE,
      appLE_eq_of_eq (c.w f.left)]
  have hPex : ∀ kl, ∃ S, P kl S := by
    rintro ⟨k, l⟩
    obtain ⟨j, f, a, ha⟩ := exists_appLE_eq_of_isAffineOpen' D c hc (hV l).1 (hV l).2 (g k l)
    exact ⟨Over.mk f, a, ha⟩
  obtain ⟨S, hS⟩ := exists_forall_of_isCofiltered P hPmono hPex
  let π := c.π.app S.left
  let V' : J → (D.obj S.left).Opens := fun l ↦ D.map S.hom ⁻¹ᵁ V l
  have hU' : ∀ y : D.obj S.left, ∃ l, y ∈ V' l := fun y ↦ hVcov.exists_mem _
  have hloc : ∀ l, trivializationOpen F (t l) = π ⁻¹ᵁ V' l := hUS S
  have htrans : ∀ k l, ∃ a : Γ(D.obj S.left, V' l),
      (sectionHom F (t l)).app (π ⁻¹ᵁ V' l) (π.app (V' l) a) =
        F.presheaf.map (homOfLE (show π ⁻¹ᵁ V' l ≤ ⊤ from le_top)).op (t k) := by
    intro k l
    obtain ⟨a, ha⟩ := hS (k, l)
    refine ⟨a, map_injective_of_le_of_le F (hUS S l).le (hUS S l).ge ?_⟩
    refine (hom_app_map (sectionHom F (t l)) (hUS S l).le
      (show Γ(structureModule c.pt, _) from π.app (V' l) a)).symm.trans ?_
    refine Eq.trans ?_ (map_map_apply F _ _ (t k)).symm
    refine Eq.trans ?_ (hg k l)
    exact congrArg ((sectionHom F (t l)).app (U l)) ha
  obtain ⟨M, s, hs⟩ := exists_lineBundle_of_descent π (hinj _) (hsurj _) F V' hU' t hloc htrans
  refine ⟨S.left, M, s, fun x ↦ ?_, fun l ↦ ?_⟩
  · obtain ⟨l, hl⟩ := hU' x
    exact ⟨l, (hs l).ge hl⟩
  · rw [hs l]
    exact (hV l).1.preimage _

end Langlands.AlgebraicGeometry.Picard
