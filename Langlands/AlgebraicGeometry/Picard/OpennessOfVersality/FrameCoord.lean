import Langlands.AlgebraicGeometry.Picard.LineHom.TestCoordinates
import Langlands.AlgebraicGeometry.Modules.LineBundleFlatDescentStr
import Langlands.AlgebraicGeometry.Picard.DualNumberAffineFrames
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isIso_of_isFrameOn_of_iSup_eq_top

/-! # Frame coordinates of morphisms between pullbacks to a common scheme -/

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.OpennessOfVersality

open Langlands.Scheme.Modules.LineBundleFlatDescent Scheme.Modules

variable {Z Z' A B : Scheme.{u}}

lemma app_res {M N : Z.Modules} (φ : M ⟶ N) {V W : Z.Opens} (h : W ≤ V) (s : Γ(M, V)) :
    φ.app W (M.presheaf.map (homOfLE h).op s) = N.presheaf.map (homOfLE h).op (φ.app V s) := by
  have := (φ.mapPresheaf).naturality (homOfLE h).op
  exact congrFun (congrArg (fun f => (ConcreteCategory.hom f : Γ(M, V) → Γ(N, W))) this) s

lemma res_res (M : Z.Modules) {U V W : Z.Opens} (h : V ≤ U) (h' : W ≤ V) (x : Γ(M, U)) :
    M.presheaf.map (homOfLE h').op (M.presheaf.map (homOfLE h).op x) =
      M.presheaf.map (homOfLE (h'.trans h)).op x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

variable {C : A.Modules} {D : B.Modules}

/-- The morphism `φ : u^* C ⟶ v^* D` sends the pullback of `e` to `a` times the pullback of
`f`, on the open `W`. -/
def HasCoord {u : Z ⟶ A} {v : Z ⟶ B} (φ : (pullback u).obj C ⟶ (pullback v).obj D)
    {T : A.Opens} {T' : B.Opens} (e : Γ(C, T)) (f : Γ(D, T')) {W : Z.Opens}
    (hu : W ≤ u ⁻¹ᵁ T) (hv : W ≤ v ⁻¹ᵁ T') (a : Γ(Z, W)) : Prop :=
  φ.app W (((pullback u).obj C).presheaf.map (homOfLE hu).op (pullbackLocalSection u e)) =
    a • ((pullback v).obj D).presheaf.map (homOfLE hv).op (pullbackLocalSection v f)

lemma HasCoord.tr (k : Z' ⟶ Z) {u : Z ⟶ A} {v : Z ⟶ B} {u' : Z' ⟶ A} {v' : Z' ⟶ B}
    (hku : k ≫ u = u') (hkv : k ≫ v = v') {φ : (pullback u).obj C ⟶ (pullback v).obj D}
    {T : A.Opens} {T' : B.Opens} {e : Γ(C, T)} {f : Γ(D, T')} {W : Z.Opens}
    {hu : W ≤ u ⁻¹ᵁ T} {hv : W ≤ v ⁻¹ᵁ T'} {a : Γ(Z, W)} (h : HasCoord φ e f hu hv a)
    {W' : Z'.Opens} (hW : W' ≤ k ⁻¹ᵁ W) (hu' : W' ≤ u' ⁻¹ᵁ T) (hv' : W' ≤ v' ⁻¹ᵁ T') :
    HasCoord (Langlands.Scheme.Modules.LineBundleFlatDescent.tr k hku hkv φ) e f hu' hv'
      (k.appLE W W' hW a) := by
  subst hku hkv
  unfold HasCoord Langlands.Scheme.Modules.LineBundleFlatDescent.tr
  rw [compIso_rfl, compIso_rfl]
  simp only [Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply, Iso.app_inv, Iso.app_hom]
  have ha : ((Scheme.Modules.pullbackComp k u).inv.app C).app W'
      (((pullback (k ≫ u)).obj C).presheaf.map (homOfLE hu').op (pullbackLocalSection (k ≫ u) e)) =
      ((pullback k).obj ((pullback u).obj C)).presheaf.map (homOfLE hW).op
        (pullbackLocalSection k
          (((pullback u).obj C).presheaf.map (homOfLE hu).op (pullbackLocalSection u e))) := by
    rw [app_res]
    erw [LineHom.pullbackComp_inv_app_pullbackLocalSection k u e]
    rw [← map_homOfLE_pullbackLocalSection k hu (pullbackLocalSection u e), res_res]
    rfl
  erw [ha]
  rw [app_res, ← pullbackLocalSection_app, h, pullbackLocalSection_smul, Scheme.Modules.map_smul,
    Scheme.Modules.Hom.app_smul, ← map_homOfLE_pullbackLocalSection k hv (pullbackLocalSection v f),
    res_res, app_res]
  erw [Langlands.Scheme.Modules.sectionPullback_comp k v D T' f]
  rfl

lemma HasCoord.mono {u : Z ⟶ A} {v : Z ⟶ B} {φ : (pullback u).obj C ⟶ (pullback v).obj D}
    {T : A.Opens} {T' : B.Opens} {e : Γ(C, T)} {f : Γ(D, T')} {W : Z.Opens}
    {hu : W ≤ u ⁻¹ᵁ T} {hv : W ≤ v ⁻¹ᵁ T'} {a : Γ(Z, W)} (h : HasCoord φ e f hu hv a)
    {W' : Z.Opens} (hW : W' ≤ W) :
    HasCoord φ e f (hW.trans hu) (hW.trans hv) (Z.presheaf.map (homOfLE hW).op a) := by
  unfold HasCoord at h ⊢
  rw [← res_res _ hu hW, app_res, h, Scheme.Modules.map_smul, res_res]

lemma HasCoord.comp {E' : Scheme.{u}} {E : E'.Modules} {u : Z ⟶ A} {v : Z ⟶ B} {w : Z ⟶ E'}
    {φ : (pullback u).obj C ⟶ (pullback v).obj D} {ψ : (pullback v).obj D ⟶ (pullback w).obj E}
    {T : A.Opens} {T' : B.Opens} {T'' : E'.Opens} {e : Γ(C, T)} {f : Γ(D, T')} {g : Γ(E, T'')}
    {W : Z.Opens} {hu : W ≤ u ⁻¹ᵁ T} {hv : W ≤ v ⁻¹ᵁ T'} {hw : W ≤ w ⁻¹ᵁ T''} {a b : Γ(Z, W)}
    (h : HasCoord φ e f hu hv a) (h' : HasCoord ψ f g hv hw b) :
    HasCoord (φ ≫ ψ) e g hu hw (a * b) := by
  unfold HasCoord at h h' ⊢
  rw [Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply, h, Scheme.Modules.Hom.app_smul, h',
    mul_smul]

lemma HasCoord.unique {u : Z ⟶ A} {v : Z ⟶ B} {φ : (pullback u).obj C ⟶ (pullback v).obj D}
    {T : A.Opens} {T' : B.Opens} {e : Γ(C, T)} {f : Γ(D, T')} (hf : Scheme.Modules.IsFrameOn f T')
    {W : Z.Opens} {hu : W ≤ u ⁻¹ᵁ T} {hv : W ≤ v ⁻¹ᵁ T'} {a a' : Γ(Z, W)}
    (h : HasCoord φ e f hu hv a) (h' : HasCoord φ e f hu hv a') : a = a' :=
  (hf.pullbackLocalSection v).bijective hv hv |>.1 (h.symm.trans h')

lemma HasCoord.exists (u : Z ⟶ A) (v : Z ⟶ B) (φ : (pullback u).obj C ⟶ (pullback v).obj D)
    {T : A.Opens} {T' : B.Opens} (e : Γ(C, T)) {f : Γ(D, T')}
    (hf : Scheme.Modules.IsFrameOn f T') {W : Z.Opens} (hu : W ≤ u ⁻¹ᵁ T) (hv : W ≤ v ⁻¹ᵁ T') :
    ∃ a, HasCoord φ e f hu hv a := by
  obtain ⟨a, ha⟩ := ((hf.pullbackLocalSection v).bijective hv hv).2
    (φ.app W (((pullback u).obj C).presheaf.map (homOfLE hu).op (pullbackLocalSection u e)))
  exact ⟨a, ha.symm⟩

/-- Morphisms between module sheaves with frames on a common cover are determined by their
values on the frames. -/
lemma hom_ext_of_frames {Y : Scheme.{u}} {M N : Y.Modules} {ι : Type u} {T : ι → Y.Opens}
    (hT : (⨆ i, T i) = ⊤) {s : ∀ i, Γ(M, T i)} (hs : ∀ i, Scheme.Modules.IsFrameOn (s i) (T i))
    {t : ∀ i, Γ(N, T i)} (ht : ∀ i, Scheme.Modules.IsFrameOn (t i) (T i)) {φ ψ : M ⟶ N}
    (h : ∀ i, φ.app (T i) (s i) = ψ.app (T i) (s i)) : φ = ψ := by
  have hs' := CocycleGluing.isTransition_frameCocycle hs
  have ht' := CocycleGluing.isTransition_frameCocycle ht
  apply (LineHom.frameHomEquiv hs ht hs' ht' hT).injective
  apply Subtype.ext
  refine LineHom.frameHomEquiv_apply_eq hs ht hs' ht' hT φ _ fun i => ?_
  rw [h i]
  exact LineHom.frameHomEquiv_spec hs ht hs' ht' hT ψ i

/-- A gauge family of units between two families of frames gives an isomorphism sending each
frame of the source to the corresponding unit times the frame of the target. -/
lemma exists_iso_of_gauge {Y : Scheme.{u}} {P₁ P₂ : Y.Modules} {ι : Type u} {T : ι → Y.Opens}
    (hT : (⨆ i, T i) = ⊤) {s : ∀ i, Γ(P₁, T i)} (hs : ∀ i, Scheme.Modules.IsFrameOn (s i) (T i))
    {t : ∀ i, Γ(P₂, T i)} (ht : ∀ i, Scheme.Modules.IsFrameOn (t i) (T i))
    {α β : ∀ i j : ι, (Γ(Y, T i ⊓ T j))ˣ} (hα : CocycleGluing.IsTransition s α)
    (hβ : CocycleGluing.IsTransition t β) (a : ∀ i, Γ(Y, T i))
    (ha : CocycleGluing.IsGaugeFamily α β a) (hunit : ∀ i, IsUnit (a i)) :
    ∃ ψ : P₁ ≅ P₂, ∀ i, ψ.hom.app (T i) (s i) = a i • t i := by
  set ψhom := (LineHom.frameHomEquiv hs ht hα hβ hT).symm ⟨a, ha⟩ with hψhom
  have hspec : ∀ i, ψhom.app (T i) (s i) = a i • t i := fun i => by
    have := LineHom.frameHomEquiv_spec hs ht hα hβ hT ψhom i
    rwa [hψhom, Equiv.apply_symm_apply] at this
  haveI : IsIso ψhom := Scheme.Modules.isIso_of_isFrameOn_of_iSup_eq_top ψhom T hT s
    (fun i => a i • t i) hs
    (fun i => DualNumberThickening.isFrameOn_smul_unit (t i) (ht i) (hunit i).unit) hspec
  exact ⟨asIso ψhom, hspec⟩

/-- Two morphisms between pullbacks agree if they have the same coordinates on frames over a
cover, with the coordinates of the first obtained by transport. -/
lemma tr_eq_of_hasCoord {Z Z' A₁ B₁ : Scheme.{u}} {C : A₁.Modules} {D : B₁.Modules}
    (k : Z' ⟶ Z) {u : Z ⟶ A₁} {v : Z ⟶ B₁} {u' : Z' ⟶ A₁} {v' : Z' ⟶ B₁}
    (hku : k ≫ u = u') (hkv : k ≫ v = v') (ψ : (pullback u).obj C ⟶ (pullback v).obj D)
    (φ : (pullback u').obj C ⟶ (pullback v').obj D) {ι : Type u} (T : ι → A₁.Opens)
    (T' : ι → B₁.Opens) (e : ∀ i, Γ(C, T i)) (he : ∀ i, Scheme.Modules.IsFrameOn (e i) (T i))
    (fr : ∀ i, Γ(D, T' i)) (hfr : ∀ i, Scheme.Modules.IsFrameOn (fr i) (T' i))
    (W : ι → Z.Opens) (hu : ∀ i, W i ≤ u ⁻¹ᵁ T i) (hv : ∀ i, W i ≤ v ⁻¹ᵁ T' i)
    (a : ∀ i, Γ(Z, W i)) (hψ : ∀ i, HasCoord ψ (e i) (fr i) (hu i) (hv i) (a i))
    (W' : ι → Z'.Opens) (hW' : (⨆ i, W' i) = ⊤) (hWW : ∀ i, W' i ≤ k ⁻¹ᵁ W i)
    (hu' : ∀ i, W' i ≤ u' ⁻¹ᵁ T i) (hv' : ∀ i, W' i ≤ v' ⁻¹ᵁ T' i)
    (hφ : ∀ i, HasCoord φ (e i) (fr i) (hu' i) (hv' i) 1)
    (ha : ∀ i, (k.appLE (W i) (W' i) (hWW i)).hom (a i) = 1) :
    Langlands.Scheme.Modules.LineBundleFlatDescent.tr k hku hkv ψ = φ := by
  refine hom_ext_of_frames hW'
    (s := fun i => ((pullback u').obj C).presheaf.map (homOfLE (hu' i)).op
      (pullbackLocalSection u' (e i)))
    (fun i => (((he i).pullbackLocalSection u').map (homOfLE (hu' i))).mono (hu' i))
    (t := fun i => ((pullback v').obj D).presheaf.map (homOfLE (hv' i)).op
      (pullbackLocalSection v' (fr i)))
    (fun i => (((hfr i).pullbackLocalSection v').map (homOfLE (hv' i))).mono (hv' i))
    fun i => ?_
  have h2 := (hψ i).tr k hku hkv (hWW i) (hu' i) (hv' i)
  rw [ha i] at h2
  exact h2.trans (hφ i).symm

end Langlands.AlgebraicGeometry.Picard.OpennessOfVersality
