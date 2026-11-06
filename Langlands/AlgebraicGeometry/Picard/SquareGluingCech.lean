import Langlands.AlgebraicGeometry.Picard.SquareGluingLegs
import Langlands.AlgebraicGeometry.Picard.LineBundleOpenCoverGluing
import Langlands.AlgebraicGeometry.Modules.OpenCoverIsoGluing
import Langlands.AlgebraicGeometry.Modules.OpenCoverHomGluing
import Langlands.AlgebraicGeometry.Modules.LineBundleIsoDescentProof

/-! # Čech gluing of locally realized actual square gluing data -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.SquareGluingDescent

open CubeMap Langlands.Scheme.Modules

namespace CubeMap

variable {S T T' : Sq.{u}}

instance isOpenImmersion_fstC (c : CubeMap S T) (c' : CubeMap S T') [IsOpenImmersion c'.t] :
    IsOpenImmersion (fstC c c').t :=
  inferInstanceAs (IsOpenImmersion (pullback.fst c.t c'.t))

instance isOpenImmersion_sndC (c : CubeMap S T) (c' : CubeMap S T') [IsOpenImmersion c.t] :
    IsOpenImmersion (sndC c c').t :=
  inferInstanceAs (IsOpenImmersion (pullback.snd c.t c'.t))

instance isOpenImmersion_comp (c : CubeMap S T) (c' : CubeMap T T') [IsOpenImmersion c.t]
    [IsOpenImmersion c'.t] : IsOpenImmersion (comp c' c).t :=
  inferInstanceAs (IsOpenImmersion (c'.t ≫ c.t))

end CubeMap

/-- The actual comparison is full and faithful on the target square of every
cartesian cube whose total map is an open immersion. -/
def FFOnCart (S : Sq.{u}) : Prop :=
  ∀ (T : Sq.{u}) (c : CubeMap S T), c.Cart → IsOpenImmersion c.t → T.C.Full ∧ T.C.Faithful

namespace Cech

variable {S : Sq.{u}} {D : S.GD} {ι : Type u} {T : ι → Sq.{u}} (c : ∀ i, CubeMap S (T i))

section Geometry

section Covers

variable (cart : ∀ i, (c i).Cart) (hcov : ∀ x : S.X, ∃ i y, (c i).t y = x)
include cart hcov

lemma covers₁ (x : S.X₁) : ∃ i y, (c i).g₁ y = x := by
  obtain ⟨i, y, hy⟩ := hcov (S.j₁ x)
  obtain ⟨z, hz, -⟩ := isPullback_exists_preimage (cart i).1 x y hy.symm
  exact ⟨i, z, hz⟩

lemma covers₂ (x : S.X₂) : ∃ i y, (c i).g₂ y = x := by
  obtain ⟨i, y, hy⟩ := hcov (S.j₂ x)
  obtain ⟨z, hz, -⟩ := isPullback_exists_preimage (cart i).2.1 x y hy.symm
  exact ⟨i, z, hz⟩

lemma covers₀ (x : S.X₀) : ∃ i y, (c i).g₀ y = x := by
  obtain ⟨i, y, hy⟩ := covers₁ c cart hcov (S.i₁ x)
  obtain ⟨z, hz, -⟩ := isPullback_exists_preimage (cart i).2.2 x y hy.symm
  exact ⟨i, z, hz⟩

end Covers

/-- The first projection cube of the triple overlap. -/
abbrev A3 (i j k : ι) :
    CubeMap (PB (c i) (c j)) (PB (fstC (c i) (c j)) (fstC (c i) (c k))) :=
  fstC (fstC (c i) (c j)) (fstC (c i) (c k))

/-- The second projection cube of the triple overlap. -/
abbrev B3 (i j k : ι) :
    CubeMap (PB (c i) (c k)) (PB (fstC (c i) (c j)) (fstC (c i) (c k))) :=
  sndC (fstC (c i) (c j)) (fstC (c i) (c k))

lemma triple_eq (i j k : ι) :
    comp (comp (A3 c i j k) (sndC (c i) (c j))) (c j) =
      comp (comp (B3 c i j k) (sndC (c i) (c k))) (c k) :=
  (comp_assoc _ _ _).trans ((congrArg (comp (A3 c i j k)) (fstC_comp (c i) (c j)).symm).trans
    ((comp_assoc _ _ _).symm.trans
      ((congrArg (fun d ↦ comp d (c i))
          (fstC_comp (fstC (c i) (c j)) (fstC (c i) (c k)))).trans
        ((comp_assoc _ _ _).trans
          ((congrArg (comp (B3 c i j k)) (fstC_comp (c i) (c k))).trans
            (comp_assoc _ _ _).symm)))))

/-- The cube from the third pairwise overlap into the triple overlap. -/
abbrev Q3 (i j k : ι) :
    CubeMap (PB (c j) (c k)) (PB (fstC (c i) (c j)) (fstC (c i) (c k))) :=
  PB.lift (comp (A3 c i j k) (sndC (c i) (c j))) (comp (B3 c i j k) (sndC (c i) (c k)))
    (triple_eq c i j k)

end Geometry

variable [∀ i, IsOpenImmersion (c i).t] (cart : ∀ i, (c i).Cart)
  (hcov : ∀ x : S.X, ∃ i y, (c i).t y = x) (hff : FFOnCart S)
  {N : ∀ i, PicardGroupoid (T i).X} (ρ : ∀ i, (T i).C.obj (N i) ≅ (c i).R.obj D)

section Covers

/-- The open cover of the total scheme by the local total schemes. -/
def coverT : S.X.OpenCover :=
  Scheme.Cover.mkOfCovers (P := @IsOpenImmersion) ι (fun i ↦ (T i).X) (fun i ↦ (c i).t)
    hcov (fun _ ↦ inferInstance)

/-- The open cover of the first leg by the local first legs. -/
def cover₁ : S.X₁.OpenCover :=
  Scheme.Cover.mkOfCovers (P := @IsOpenImmersion) ι (fun i ↦ (T i).X₁) (fun i ↦ (c i).g₁)
    (covers₁ c cart hcov) (fun i ↦ (cart i).isOpenImmersion_g₁)

/-- The open cover of the second leg by the local second legs. -/
def cover₂ : S.X₂.OpenCover :=
  Scheme.Cover.mkOfCovers (P := @IsOpenImmersion) ι (fun i ↦ (T i).X₂) (fun i ↦ (c i).g₂)
    (covers₂ c cart hcov) (fun i ↦ (cart i).isOpenImmersion_g₂)

/-- The open cover of the corner by the local corners. -/
def cover₀ : S.X₀.OpenCover :=
  Scheme.Cover.mkOfCovers (P := @IsOpenImmersion) ι (fun i ↦ (T i).X₀) (fun i ↦ (c i).g₀)
    (covers₀ c cart hcov) (fun i ↦ (cart i).isOpenImmersion_g₀)

end Covers

section Transitions

include cart hff in
lemma ff_overlap (i j : ι) :
    (PB (c i) (c j)).C.Full ∧ (PB (c i) (c j)).C.Faithful :=
  hff _ (comp (fstC (c i) (c j)) (c i)) ((cart_fstC _ _ (cart j)).comp (cart i))
    inferInstance

/-- The transition on a pairwise overlap: the unique arrow respecting the two
pulled-back realizations. -/
def tau (i j : ι) :
    (P (fstC (c i) (c j)).t).obj (N i) ⟶ (P (sndC (c i) (c j)).t).obj (N j) :=
  haveI := (ff_overlap c cart hff i j).1
  (PB (c i) (c j)).C.preimage ((pb (c i) (fstC (c i) (c j)) (ρ i)).hom ≫
    eqToHom (congrArg (fun e ↦ e.R.obj D) (fstC_comp (c i) (c j))) ≫
      (pb (c j) (sndC (c i) (c j)) (ρ j)).inv)

lemma resp_tau (i j : ι) :
    Resp (tau c cart hff ρ i j) (pb (c i) (fstC (c i) (c j)) (ρ i))
      (pb (c j) (sndC (c i) (c j)) (ρ j)) := by
  have := (ff_overlap c cart hff i j).1
  refine ⟨fstC_comp _ _, ?_⟩
  rw [tau, Functor.map_preimage, Category.assoc, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

/-- The cocycle identity of the transitions in the actual Picard groupoid. -/
lemma cocycle_pic (i j k : ι) :
    (P (A3 c i j k).t).map (tau c cart hff ρ i j) ≫
        sqH (A3 c i j k).t (Q3 c i j k).t (sndC (c i) (c j)).t (fstC (c j) (c k)).t
          (comp_eq_t (PB.lift_fstC _ _ (triple_eq c i j k)).symm) (N j) ≫
        (P (Q3 c i j k).t).map (tau c cart hff ρ j k) ≫
        sqH (Q3 c i j k).t (B3 c i j k).t (sndC (c j) (c k)).t (sndC (c i) (c k)).t
          (comp_eq_t (PB.lift_sndC _ _ (triple_eq c i j k))) (N k) =
      sqH (A3 c i j k).t (B3 c i j k).t (fstC (c i) (c j)).t (fstC (c i) (c k)).t
          (comp_eq_t (fstC_comp _ _)) (N i) ≫
        (P (B3 c i j k).t).map (tau c cart hff ρ i k) := by
  have := (hff _ (comp (A3 c i j k) (comp (fstC (c i) (c j)) (c i)))
    ((cart_fstC _ _ (cart_fstC _ _ (cart k))).comp ((cart_fstC _ _ (cart j)).comp (cart i)))
    inferInstance).2
  exact Resp.unique
    (((resp_tau c cart hff ρ i j).along (A3 c i j k)).comp
      ((resp_sqH (c j) (sndC (c i) (c j)) (A3 c i j k) (fstC (c j) (c k)) (Q3 c i j k)
        (PB.lift_fstC _ _ (triple_eq c i j k)).symm
        (comp_eq_t (PB.lift_fstC _ _ (triple_eq c i j k)).symm) (ρ j)).comp
      (((resp_tau c cart hff ρ j k).along (Q3 c i j k)).comp
        (resp_sqH (c k) (sndC (c j) (c k)) (Q3 c i j k) (sndC (c i) (c k)) (B3 c i j k)
          (PB.lift_sndC _ _ (triple_eq c i j k))
          (comp_eq_t (PB.lift_sndC _ _ (triple_eq c i j k))) (ρ k)))))
    ((resp_sqH (c i) (fstC (c i) (c j)) (A3 c i j k) (fstC (c i) (c k)) (B3 c i j k)
        (fstC_comp _ _) (comp_eq_t (fstC_comp _ _)) (ρ i)).comp
      ((resp_tau c cart hff ρ i k).along (B3 c i j k)))

/-- The cocycle identity for the underlying modules, on the cube overlaps. -/
lemma cocycle_mod (i j k : ι) :
    (Scheme.Modules.pullback (A3 c i j k).t).map (mi (tau c cart hff ρ i j)).hom ≫
        (squarePullbackIso (fstC (c j) (c k)).t (A3 c i j k).t (Q3 c i j k).t
          (sndC (c i) (c j)).t (comp_eq_t (PB.lift_fstC _ _ (triple_eq c i j k)).symm)
          (N j).of.obj).hom ≫
        (Scheme.Modules.pullback (Q3 c i j k).t).map (mi (tau c cart hff ρ j k)).hom ≫
        (squarePullbackIso (sndC (c i) (c k)).t (Q3 c i j k).t (B3 c i j k).t
          (sndC (c j) (c k)).t (comp_eq_t (PB.lift_sndC _ _ (triple_eq c i j k)))
          (N k).of.obj).hom =
      (squarePullbackIso (fstC (c i) (c k)).t (A3 c i j k).t (B3 c i j k).t
          (fstC (c i) (c j)).t (comp_eq_t (fstC_comp _ _)) (N i).of.obj).hom ≫
        (Scheme.Modules.pullback (B3 c i j k).t).map (mi (tau c cart hff ρ i k)).hom := by
  rw [mi_hom, mi_hom, mi_hom, ← mh_sqH, ← mh_sqH, ← mh_sqH]
  exact congrArg mh (cocycle_pic c cart hff ρ i j k)

/-- The transitions as isomorphisms of underlying modules on the overlaps of the
cover. -/
def trans (i j : ι) :
    (Scheme.Modules.pullback (pullback.fst ((coverT c hcov).f i) ((coverT c hcov).f j))).obj
        (N i).of.obj ≅
      (Scheme.Modules.pullback (pullback.snd ((coverT c hcov).f i) ((coverT c hcov).f j))).obj
        (N j).of.obj :=
  mi (tau c cart hff ρ i j)

lemma cocycle :
    OpenCoverModuleGluing.CocycleCondition (coverT c hcov) (fun i ↦ (N i).of.obj)
      (trans c cart hcov hff ρ) :=
  fun i j k ↦ OpenCoverModuleGluing.CompEq4.of_eq (cocycle_mod c cart hff ρ i j k)

end Transitions

section Glue

/-- The actual line-bundle gluing data of the local realizations. -/
def gd : LineBundleGluingData (coverT c hcov) where
  bundle i := (N i).of
  transition := trans c cart hcov hff ρ
  cocycle := cocycle c cart hcov hff ρ

/-- The glued actual line bundle. -/
def glued : PicardGroupoid S.X := Core.mk (gd c cart hcov hff ρ).glue

/-- The identification of the glued bundle with a local bundle. -/
def sig (i : ι) : (P (c i).t).obj (glued c cart hcov hff ρ) ⟶ N i :=
  pic ((gd c cart hcov hff ρ).moduleIso i)

lemma sig_compat (i j : ι) :
    (P (fstC (c i) (c j)).t).map (sig c cart hcov hff ρ i) ≫ tau c cart hff ρ i j =
      sqH (fstC (c i) (c j)).t (sndC (c i) (c j)).t (c i).t (c j).t
          (comp_eq_t (fstC_comp _ _)) (glued c cart hcov hff ρ) ≫
        (P (sndC (c i) (c j)).t).map (sig c cart hcov hff ρ j) := by
  apply mh_injective
  simp only [mh_comp, mh_map, mh_sqH]
  exact (gd c cart hcov hff ρ).moduleIso_compatible i j

/-- The local arrow of restricted data induced by the glued bundle. -/
def Psi (i : ι) : (c i).R.obj (S.C.obj (glued c cart hcov hff ρ)) ⟶ (c i).R.obj D :=
  (cIi (c i) (glued c cart hcov hff ρ)).inv ≫ (T i).C.map (sig c cart hcov hff ρ i) ≫ (ρ i).hom

lemma Psi_compat (i j : ι) :
    pbH (c i) (fstC (c i) (c j)) (Psi c cart hcov hff ρ i) ≫
        eqToHom (congrArg (fun e ↦ e.R.obj D) (fstC_comp (c i) (c j))) =
      eqToHom (congrArg (fun e ↦ e.R.obj (S.C.obj (glued c cart hcov hff ρ)))
          (fstC_comp (c i) (c j))) ≫
        pbH (c j) (sndC (c i) (c j)) (Psi c cart hcov hff ρ j) :=
  legs_compat (c i) (c j) (ρ i) (ρ j) (sig c cart hcov hff ρ i) (sig c cart hcov hff ρ j)
    (tau c cart hff ρ i j) (resp_tau c cart hff ρ i j) (sig_compat c cart hcov hff ρ i j)

lemma exists_left : ∃ l : (S.C.obj (glued c cart hcov hff ρ)).left ≅ D.left,
    ∀ i, (P (c i).g₁).map l.hom = (Psi c cart hcov hff ρ i).left := by
  obtain ⟨E, hE, -⟩ := openCoverIsoGluing_of_homGluing OpenCoverHomGluing.openCoverHomGluing
    S.X₁ (cover₁ c cart hcov) (S.C.obj (glued c cart hcov hff ρ)).left.of.obj D.left.of.obj
    (fun i ↦ mi (Psi c cart hcov hff ρ i).left) (fun i j ↦ by
      have h := congrArg mh (leg_left _ _ (Psi_compat c cart hcov hff ρ i j))
      simp only [mh_comp, mh_map, mh_sqH] at h
      exact h)
  exact ⟨Core.isoMk (ObjectProperty.isoMk _ E), fun i ↦ mh_injective (hE i)⟩

lemma exists_right : ∃ r : (S.C.obj (glued c cart hcov hff ρ)).right ≅ D.right,
    ∀ i, (P (c i).g₂).map r.hom = (Psi c cart hcov hff ρ i).right := by
  obtain ⟨E, hE, -⟩ := openCoverIsoGluing_of_homGluing OpenCoverHomGluing.openCoverHomGluing
    S.X₂ (cover₂ c cart hcov) (S.C.obj (glued c cart hcov hff ρ)).right.of.obj D.right.of.obj
    (fun i ↦ mi (Psi c cart hcov hff ρ i).right) (fun i j ↦ by
      have h := congrArg mh (leg_right _ _ (Psi_compat c cart hcov hff ρ i j))
      simp only [mh_comp, mh_map, mh_sqH] at h
      exact h)
  exact ⟨Core.isoMk (ObjectProperty.isoMk _ E), fun i ↦ mh_injective (hE i)⟩

include cart hcov hff ρ in
/-- Local realizations on a cover by cartesian open cubes glue to a global
realization, provided the comparison is fully faithful on such cubes. -/
theorem exists_iso : ∃ L : PicardGroupoid S.X, Nonempty (S.C.obj L ≅ D) := by
  obtain ⟨l, hl⟩ := exists_left c cart hcov hff ρ
  obtain ⟨r, hr⟩ := exists_right c cart hcov hff ρ
  refine ⟨glued c cart hcov hff ρ, ⟨Comma.isoMk l r ?_⟩⟩
  apply mh_injective
  apply LineBundleIsoDescent.hom_ext_of_openCover (cover₀ c cart hcov)
  intro i
  exact congrArg mh (map_w (c i) (Psi c cart hcov hff ρ i) (hl i).symm (hr i).symm)

end Glue

end Cech

end Langlands.AlgebraicGeometry.Picard.SquareGluingDescent
