import Langlands.AlgebraicGeometry.Picard.CocycleLineBundleGauge
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isIso_of_isFrameOn_of_iSup_eq_top

/-! # Module sheaves with local frames as glued line bundles

Let `M` be a sheaf of modules on a scheme `X`, `T i` opens of `X`, and `e i` a section of `M`
over `T i` that is a frame there (`Scheme.Modules.IsFrameOn (e i) (T i)`: on every open
`W ≤ T i`, `r ↦ r • e i|W` is bijective). The transition functions of the frames are the units
`g i j` on `T i ⊓ T j` with `e j = g i j • e i` there (`IsTransition e g`); they form a unit
cocycle (`isCocycle_of_isTransition`), and `frameCocycle` constructs them from the frames.

Sending a section of `M` to its family of frame coefficients is a morphism
`toGlued : M ⟶ glued g`. When the `T i` cover `X` it is an isomorphism `frameIso`, which sends
`e i` to the local generator `genSec g i`.
-/

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.Picard.CocycleGluing

variable {X : Scheme.{u}} {M : X.Modules}

section Coeff

lemma mres_mres {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V) (x : Γ(M, U)) :
    M.presheaf.map (homOfLE h').op (M.presheaf.map (homOfLE h).op x) =
      M.presheaf.map (homOfLE (h'.trans h)).op x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

lemma mres_self {U : X.Opens} (h : U ≤ U) (x : Γ(M, U)) : M.presheaf.map (homOfLE h).op x = x := by
  have e : (homOfLE h).op = 𝟙 (op U) := rfl
  rw [e, CategoryTheory.Functor.map_id]
  rfl

variable {U : X.Opens} {s : Γ(M, U)} (hs : Scheme.Modules.IsFrameOn s U)

/-- The coefficient of a section over `W ≤ U` with respect to the restriction of the frame `s`:
the unique `r` with `r • s|W = x`. -/
noncomputable def frameCoeff {W : X.Opens} (hW : W ≤ U) (x : Γ(M, W)) : Γ(X, W) :=
  (Equiv.ofBijective _ (hs hW hW)).symm x

lemma frameCoeff_smul_frame {W : X.Opens} (hW : W ≤ U) (x : Γ(M, W)) :
    frameCoeff hs hW x • M.presheaf.map (homOfLE hW).op s = x :=
  (Equiv.ofBijective _ (hs hW hW)).apply_symm_apply x

lemma frameCoeff_eq {W : X.Opens} (hW : W ≤ U) {x : Γ(M, W)} {r : Γ(X, W)}
    (h : r • M.presheaf.map (homOfLE hW).op s = x) : frameCoeff hs hW x = r :=
  (hs hW hW).1 ((frameCoeff_smul_frame hs hW x).trans h.symm)

lemma frameCoeff_add {W : X.Opens} (hW : W ≤ U) (x y : Γ(M, W)) :
    frameCoeff hs hW (x + y) = frameCoeff hs hW x + frameCoeff hs hW y :=
  frameCoeff_eq hs hW (by rw [add_smul, frameCoeff_smul_frame, frameCoeff_smul_frame])

lemma frameCoeff_smul {W : X.Opens} (hW : W ≤ U) (r : Γ(X, W)) (x : Γ(M, W)) :
    frameCoeff hs hW (r • x) = r * frameCoeff hs hW x :=
  frameCoeff_eq hs hW (by rw [mul_smul, frameCoeff_smul_frame])

lemma frameCoeff_frame {W : X.Opens} (hW : W ≤ U) :
    frameCoeff hs hW (M.presheaf.map (homOfLE hW).op s) = 1 :=
  frameCoeff_eq hs hW (one_smul _ _)

/-- Frame coefficients commute with restriction. -/
lemma res_frameCoeff {W W' : X.Opens} (hW : W ≤ U) (h : W' ≤ W) (x : Γ(M, W)) :
    X.presheaf.map (homOfLE h).op (frameCoeff hs hW x) =
      frameCoeff hs (h.trans hW) (M.presheaf.map (homOfLE h).op x) :=
  (frameCoeff_eq hs (h.trans hW) (by
    rw [← mres_mres hW h, ← Scheme.Modules.map_smul, frameCoeff_smul_frame])).symm

/-- The coefficients of two frames with respect to each other are mutually inverse. -/
lemma frameCoeff_mul_frameCoeff {U' : X.Opens} {t : Γ(M, U')} (ht : Scheme.Modules.IsFrameOn t U')
    {W : X.Opens} (hW : W ≤ U) (hW' : W ≤ U') :
    frameCoeff hs hW (M.presheaf.map (homOfLE hW').op t) *
      frameCoeff ht hW' (M.presheaf.map (homOfLE hW).op s) = 1 := by
  have h : (frameCoeff hs hW (M.presheaf.map (homOfLE hW').op t) *
      frameCoeff ht hW' (M.presheaf.map (homOfLE hW).op s)) •
        M.presheaf.map (homOfLE hW').op t = M.presheaf.map (homOfLE hW').op t := by
    rw [mul_smul, frameCoeff_smul_frame, frameCoeff_smul_frame]
  rw [← frameCoeff_eq ht hW' h, frameCoeff_frame]

end Coeff

variable {ι : Type u} {T : ι → X.Opens}

section Transition

/-- The frames `e i` have transition functions `g`: `e j = g i j • e i` on `T i ⊓ T j`. -/
def IsTransition (e : ∀ i, Γ(M, T i)) (g : ∀ i j : ι, (Γ(X, T i ⊓ T j))ˣ) : Prop :=
  ∀ i j : ι, M.presheaf.map (homOfLE (inf_le_right : T i ⊓ T j ≤ T j)).op (e j) =
    (g i j : Γ(X, T i ⊓ T j)) • M.presheaf.map (homOfLE (inf_le_left : T i ⊓ T j ≤ T i)).op (e i)

variable {e : ∀ i, Γ(M, T i)} {g : ∀ i j : ι, (Γ(X, T i ⊓ T j))ˣ}

/-- The transition relation on any open inside `T i ⊓ T j`. -/
lemma IsTransition.res (htrans : IsTransition e g) {i j : ι} {V : X.Opens} (hi : V ≤ T i)
    (hj : V ≤ T j) :
    M.presheaf.map (homOfLE hj).op (e j) =
      X.presheaf.map (homOfLE (le_inf hi hj)).op (g i j : Γ(X, T i ⊓ T j)) •
        M.presheaf.map (homOfLE hi).op (e i) := by
  have h := congrArg (fun z ↦ M.presheaf.map (homOfLE (le_inf hi hj)).op z) (htrans i j)
  simp only [Scheme.Modules.map_smul, mres_mres] at h
  exact h

variable (he : ∀ i, Scheme.Modules.IsFrameOn (e i) (T i))
include he

/-- The transition functions of a family of frames form a unit cocycle. -/
lemma isCocycle_of_isTransition (htrans : IsTransition e g) : IsCocycle g := by
  intro i j k
  have hi : T i ⊓ T j ⊓ T k ≤ T i := inf_le_left.trans inf_le_left
  have hj : T i ⊓ T j ⊓ T k ≤ T j := inf_le_left.trans inf_le_right
  have hk : T i ⊓ T j ⊓ T k ≤ T k := inf_le_right
  have e1 := htrans.res hi hj
  have e2 := htrans.res hj hk
  have e3 := htrans.res hi hk
  rw [e1, smul_smul] at e2
  rw [mul_comm]
  exact (he i hi hi).1 (e2.symm.trans e3)

/-- The transition functions are determined by the frames. -/
lemma IsTransition.unique {g' : ∀ i j : ι, (Γ(X, T i ⊓ T j))ˣ} (htrans : IsTransition e g)
    (htrans' : IsTransition e g') : g = g' := by
  funext i j
  exact Units.ext ((he i inf_le_left inf_le_left).1 ((htrans i j).symm.trans (htrans' i j)))

omit he in
variable (e) in
/-- The transition functions of a family of frames: `frameCocycle he i j` is the unit on
`T i ⊓ T j` with `e j = frameCocycle he i j • e i` there. -/
noncomputable def frameCocycle (he : ∀ i, Scheme.Modules.IsFrameOn (e i) (T i)) (i j : ι) :
    (Γ(X, T i ⊓ T j))ˣ where
  val := frameCoeff (he i) inf_le_left
    (M.presheaf.map (homOfLE (inf_le_right : T i ⊓ T j ≤ T j)).op (e j))
  inv := frameCoeff (he j) inf_le_right
    (M.presheaf.map (homOfLE (inf_le_left : T i ⊓ T j ≤ T i)).op (e i))
  val_inv := frameCoeff_mul_frameCoeff (he i) (he j) inf_le_left inf_le_right
  inv_val := frameCoeff_mul_frameCoeff (he j) (he i) inf_le_right inf_le_left

lemma isTransition_frameCocycle : IsTransition e (frameCocycle e he) := fun i _ ↦
  (frameCoeff_smul_frame (he i) inf_le_left _).symm

end Transition

section Hom

variable {e : ∀ i, Γ(M, T i)} (he : ∀ i, Scheme.Modules.IsFrameOn (e i) (T i))

/-- The family of frame coefficients of a section `s` over `U`: its `i`-th member is the
coefficient of `s|(U ⊓ T i)` with respect to `e i`. -/
noncomputable def frameFam {U : X.Opens} (s : Γ(M, U)) : Fam T U :=
  fun i ↦ frameCoeff (he i) inf_le_right
    (M.presheaf.map (homOfLE (inf_le_left : U ⊓ T i ≤ U)).op s)

lemma frameFam_apply {U : X.Opens} (s : Γ(M, U)) (i : ι) :
    frameFam he s i = frameCoeff (he i) inf_le_right
      (M.presheaf.map (homOfLE (inf_le_left : U ⊓ T i ≤ U)).op s) :=
  rfl

lemma res_frameFam {U V : X.Opens} (s : Γ(M, U)) {i : ι} (hi : V ≤ U ⊓ T i) :
    X.presheaf.map (homOfLE hi).op (frameFam he s i) =
      frameCoeff (he i) (hi.trans inf_le_right)
        (M.presheaf.map (homOfLE (hi.trans inf_le_left)).op s) := by
  rw [frameFam_apply, res_frameCoeff, mres_mres]

lemma frameFam_add {U : X.Opens} (s s' : Γ(M, U)) :
    frameFam he (s + s') = frameFam he s + frameFam he s' := by
  funext i
  rw [frameFam_apply, map_add, frameCoeff_add]
  rfl

lemma frameFam_smul {U : X.Opens} (r : Γ(X, U)) (s : Γ(M, U)) :
    frameFam he (r • s) = r • frameFam he s := by
  funext i
  rw [frameFam_apply, Scheme.Modules.map_smul, frameCoeff_smul]
  rfl

lemma famRes_frameFam {U V : X.Opens} (h : V ≤ U) (s : Γ(M, U)) :
    famRes T h (frameFam he s) = frameFam he (M.presheaf.map (homOfLE h).op s) := by
  funext i
  rw [famRes_apply, frameFam_apply, frameFam_apply, res_frameCoeff, mres_mres, mres_mres]

variable {g : ∀ i j : ι, (Γ(X, T i ⊓ T j))ˣ} (htrans : IsTransition e g)
include htrans

/-- Frame coefficients satisfy the cocycle relation of the transition functions. -/
lemma compat_frameFam {U : X.Opens} (s : Γ(M, U)) : Compat g (frameFam he s) := by
  intro i j V hi hj
  rw [res_frameFam, res_frameFam]
  refine frameCoeff_eq (he i) _ ?_
  rw [mul_comm, mul_smul, ← htrans.res (hi.trans inf_le_right) (hj.trans inf_le_right),
    frameCoeff_smul_frame]

/-- The morphism `M ⟶ glued g` sending a section to its family of frame coefficients. -/
noncomputable def toGlued : M ⟶ glued g where
  val :=
    { app := fun U ↦ ModuleCat.ofHom (X := ↑(M.val.obj U)) (Y := ↑((glued g).val.obj U))
        { toFun := fun s ↦ mk g (frameFam he (s : Γ(M, U.unop))) (compat_frameFam he htrans s)
          map_add' := fun s s' ↦ Subtype.ext (frameFam_add he s s')
          map_smul' := fun r s ↦ Subtype.ext (frameFam_smul he r s) }
      naturality := by
        intro U V f
        ext s
        apply Subtype.ext
        exact (famRes_frameFam he (leOfHom f.unop) s).symm }

/-- Component formula: the `i`-th component of the image of `s` is the coefficient of
`s|(U ⊓ T i)` with respect to `e i`. -/
lemma comp_toGlued_app {U : X.Opens} (s : Γ(M, U)) (i : ι) :
    comp g ((toGlued he htrans).app U s) i =
      frameCoeff (he i) inf_le_right (M.presheaf.map (homOfLE (inf_le_left : U ⊓ T i ≤ U)).op s) :=
  rfl

/-- `toGlued` sends the restriction of the frame `e i` to the local generator `genSec g i`. -/
lemma toGlued_app_frame (hg : IsCocycle g) (i : ι) {V : X.Opens} (hV : V ≤ T i) :
    (toGlued he htrans).app V (M.presheaf.map (homOfLE hV).op (e i)) = genSec g hg i hV := by
  refine eq_of_comp g fun j ↦ ?_
  change frameCoeff (he j) inf_le_right (M.presheaf.map (homOfLE (inf_le_left : V ⊓ T j ≤ V)).op
    (M.presheaf.map (homOfLE hV).op (e i))) = gen g i hV j
  rw [mres_mres, gen_apply]
  exact frameCoeff_eq (he j) _ (htrans.res (inf_le_right : V ⊓ T j ≤ T j) (inf_le_left.trans hV)).symm

lemma toGlued_app_frame_self (hg : IsCocycle g) (i : ι) :
    (toGlued he htrans).app (T i) (e i) = genSec g hg i le_rfl := by
  rw [← toGlued_app_frame he htrans hg i le_rfl, mres_self]

/-- When the `T i` cover `X`, `toGlued` is an isomorphism. -/
lemma isIso_toGlued (hT : (⨆ i, T i) = ⊤) : IsIso (toGlued he htrans) :=
  Scheme.Modules.isIso_of_isFrameOn_of_iSup_eq_top (toGlued he htrans) T hT e
    (fun i ↦ genSec g (isCocycle_of_isTransition he htrans) i le_rfl) he
    (fun i W hWU _ ↦ by
      rw [map_genSec g _ i hWU le_rfl]
      exact smul_genSec_bijective g _ i _)
    (fun i ↦ toGlued_app_frame_self he htrans _ i)

/-- A sheaf of modules with frames `e i` on a cover `T` with transition functions `g` is
isomorphic to the line bundle glued from `g`. Its forward morphism is `toGlued`. -/
noncomputable def frameIso (hT : (⨆ i, T i) = ⊤) : M ≅ glued g :=
  @asIso _ _ _ _ (toGlued he htrans) (isIso_toGlued he htrans hT)

lemma frameIso_hom (hT : (⨆ i, T i) = ⊤) : (frameIso he htrans hT).hom = toGlued he htrans :=
  rfl

/-- Component formula for the frame isomorphism. -/
lemma comp_frameIso_hom_app (hT : (⨆ i, T i) = ⊤) {U : X.Opens} (s : Γ(M, U)) (i : ι) :
    comp g ((frameIso he htrans hT).hom.app U s) i =
      frameCoeff (he i) inf_le_right (M.presheaf.map (homOfLE (inf_le_left : U ⊓ T i ≤ U)).op s) :=
  rfl

/-- The frame isomorphism sends `e i|V` to `genSec g i` over `V ≤ T i`. -/
lemma frameIso_hom_app_frame (hT : (⨆ i, T i) = ⊤) (hg : IsCocycle g) (i : ι) {V : X.Opens}
    (hV : V ≤ T i) :
    (frameIso he htrans hT).hom.app V (M.presheaf.map (homOfLE hV).op (e i)) = genSec g hg i hV :=
  toGlued_app_frame he htrans hg i hV

/-- The inverse of the frame isomorphism sends `genSec g i` over `V ≤ T i` to `e i|V`. -/
lemma frameIso_inv_app_genSec (hT : (⨆ i, T i) = ⊤) (hg : IsCocycle g) (i : ι) {V : X.Opens}
    (hV : V ≤ T i) :
    (frameIso he htrans hT).inv.app V (genSec g hg i hV) = M.presheaf.map (homOfLE hV).op (e i) := by
  rw [← frameIso_hom_app_frame he htrans hT hg i hV]
  change ((frameIso he htrans hT).hom.app V ≫ (frameIso he htrans hT).inv.app V)
    (M.presheaf.map (homOfLE hV).op (e i)) = _
  rw [← Scheme.Modules.Hom.comp_app, Iso.hom_inv_id, Scheme.Modules.Hom.id_app]
  rfl

end Hom

/-- Over an open `V ≤ T i`, a section of the glued sheaf is its `i`-th component times the local
generator `genSec g i`. -/
lemma eq_comp_smul_genSec (g : ∀ i j : ι, (Γ(X, T i ⊓ T j))ˣ) (hg : IsCocycle g) (i : ι)
    {V : X.Opens} (hV : V ≤ T i) (m : Γ(glued g, V)) :
    m = X.presheaf.map (homOfLE (le_inf le_rfl hV : V ≤ V ⊓ T i)).op (comp g m i) •
      genSec g hg i hV := by
  refine eq_of_comp g fun j ↦ ?_
  have h := compat_of_mem g m j i (V ⊓ T j) le_rfl (le_inf inf_le_left (inf_le_left.trans hV))
  rw [res_self] at h
  change comp g m j = X.presheaf.map (homOfLE (inf_le_left : V ⊓ T j ≤ V)).op
      (X.presheaf.map (homOfLE (le_inf le_rfl hV : V ≤ V ⊓ T i)).op (comp g m i)) * gen g i hV j
  rw [res_res, gen_apply, mul_comm]
  exact h

/-- The inverse of the frame isomorphism over `V ≤ T i`: a section of the glued sheaf goes to
its `i`-th component times `e i|V`. -/
lemma frameIso_inv_app {e : ∀ i, Γ(M, T i)} (he : ∀ i, Scheme.Modules.IsFrameOn (e i) (T i))
    {g : ∀ i j : ι, (Γ(X, T i ⊓ T j))ˣ} (htrans : IsTransition e g) (hT : (⨆ i, T i) = ⊤)
    (i : ι) {V : X.Opens} (hV : V ≤ T i) (m : Γ(glued g, V)) :
    (frameIso he htrans hT).inv.app V m =
      X.presheaf.map (homOfLE (le_inf le_rfl hV : V ≤ V ⊓ T i)).op (comp g m i) •
        M.presheaf.map (homOfLE hV).op (e i) := by
  conv_lhs => rw [eq_comp_smul_genSec g (isCocycle_of_isTransition he htrans) i hV m]
  rw [Scheme.Modules.Hom.app_smul, frameIso_inv_app_genSec]

end Langlands.AlgebraicGeometry.Picard.CocycleGluing
