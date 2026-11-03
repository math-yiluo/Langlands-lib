import Langlands.AlgebraicGeometry.Picard.LineHom.FrameHom
import Langlands.AlgebraicGeometry.Picard.CocycleLineBundlePullback
import Langlands.AlgebraicGeometry.CoherentSheaves.IntrinsicModuleHomDescent
import Langlands.AlgebraicGeometry.SectionPullback
import Langlands.AlgebraicGeometry.Modules.PullbackTransport

/-! # Frame coordinates of morphisms between pulled-back line bundles

Let `L` and `M` be sheaves of modules on `X` with frames `e i` and `f i` on a common open cover
`T`, with transition functions `α` and `β`. For every morphism `q : Y ⟶ X`, the pulled-back
sections `pullbackLocalSection q (e i)` are frames of `q^* L` on the cover `q ⁻¹ᵁ T i`, with the
pulled-back transition functions. So morphisms `q^* L ⟶ q^* M` correspond to the gauge families
of `pullbackCocycle q α` and `pullbackCocycle q β`. Under a further pullback along `k`, the
coordinates of a transported morphism are the images of the coordinates under `k`. Finally, the
restriction maps of the relative Hom presheaf `intrinsicModuleHomPresheaf p L M` are such
transports.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.Picard.LineHom

open CocycleGluing Scheme.Modules

section PullbackFrames

variable {X Y : Scheme.{u}} (q : Y ⟶ X) {ι : Type u} {T : ι → X.Opens} {M : X.Modules}
  {e : ∀ i, Γ(M, T i)} {g : ∀ i j : ι, (Γ(X, T i ⊓ T j))ˣ}

/-- Pulled-back frames have the pulled-back transition functions. -/
lemma isTransition_pullback (htrans : IsTransition e g) :
    IsTransition (T := fun i ↦ q ⁻¹ᵁ T i) (fun i ↦ pullbackLocalSection q (e i))
      (pullbackCocycle q g) := by
  intro i j
  have h1 := map_homOfLE_pullbackLocalSection q (inf_le_right : T i ⊓ T j ≤ T j) (e j)
  have h2 := map_homOfLE_pullbackLocalSection q (inf_le_left : T i ⊓ T j ≤ T i) (e i)
  rw [htrans i j, pullbackLocalSection_smul, ← h2, Scheme.Hom.app_eq_appLE] at h1
  exact h1

/-- The preimages of a cover form a cover. -/
lemma iSup_preimage_eq_top (hT : (⨆ i, T i) = ⊤) : (⨆ i, q ⁻¹ᵁ T i) = ⊤ := by
  rw [← Scheme.Hom.preimage_iSup, hT, Scheme.Hom.preimage_top]

end PullbackFrames

section Coordinates

variable {X : Scheme.{u}} {ι : Type u} {T : ι → X.Opens} {L M : X.Modules}
  {e : ∀ i, Γ(L, T i)} {f : ∀ i, Γ(M, T i)}
  (he : ∀ i, Scheme.Modules.IsFrameOn (e i) (T i))
  (hf : ∀ i, Scheme.Modules.IsFrameOn (f i) (T i))
  {α β : ∀ i j : ι, (Γ(X, T i ⊓ T j))ˣ}
  (hα : IsTransition e α) (hβ : IsTransition f β) (hT : (⨆ i, T i) = ⊤)

/-- Morphisms between the pullbacks of `L` and `M` along `q` are the gauge families of the
pulled-back transition functions, through the pulled-back frames. -/
noncomputable def pullbackFrameHomEquiv {Y : Scheme.{u}} (q : Y ⟶ X) :
    ((Scheme.Modules.pullback q).obj L ⟶ (Scheme.Modules.pullback q).obj M) ≃
      {a : ∀ i, Γ(Y, q ⁻¹ᵁ T i) // IsGaugeFamily (pullbackCocycle q α) (pullbackCocycle q β) a} :=
  frameHomEquiv (fun i ↦ (he i).pullbackLocalSection q) (fun i ↦ (hf i).pullbackLocalSection q)
    (isTransition_pullback q hα) (isTransition_pullback q hβ) (iSup_preimage_eq_top q hT)

/-- The coordinates of `φ` satisfy `φ (q^* e i) = a i • q^* f i`. -/
lemma pullbackFrameHomEquiv_spec {Y : Scheme.{u}} (q : Y ⟶ X)
    (φ : (Scheme.Modules.pullback q).obj L ⟶ (Scheme.Modules.pullback q).obj M) (i : ι) :
    φ.app (q ⁻¹ᵁ T i) (pullbackLocalSection q (e i)) =
      (pullbackFrameHomEquiv he hf hα hβ hT q φ).1 i • pullbackLocalSection q (f i) :=
  frameHomEquiv_spec (fun i ↦ (he i).pullbackLocalSection q) (fun i ↦ (hf i).pullbackLocalSection q)
    (isTransition_pullback q hα) (isTransition_pullback q hβ) (iSup_preimage_eq_top q hT) φ i

/-- Pulling back sections along a composite agrees with pulling back twice. -/
lemma pullbackComp_inv_app_pullbackLocalSection {Y Y' : Scheme.{u}} (k : Y' ⟶ Y) (q : Y ⟶ X)
    {N : X.Modules} {U : X.Opens} (s : Γ(N, U)) :
    ((Scheme.Modules.pullbackComp k q).inv.app N).app ((k ≫ q) ⁻¹ᵁ U)
        (pullbackLocalSection (k ≫ q) s) =
      pullbackLocalSection k (pullbackLocalSection q s) := by
  have h := congrArg (((Scheme.Modules.pullbackComp k q).inv.app N).app ((k ≫ q) ⁻¹ᵁ U))
    (Langlands.Scheme.Modules.sectionPullback_comp k q N U s)
  refine h.symm.trans ?_
  change ((Scheme.Modules.pullbackComp k q).hom.app N ≫
      (Scheme.Modules.pullbackComp k q).inv.app N).app _ _ = _
  rw [Iso.hom_inv_id_app, Scheme.Modules.Hom.id_app]
  rfl

/-- The coordinates of a transported morphism are the images of the coordinates. -/
theorem pullbackFrameHomEquiv_transport {Y Y' : Scheme.{u}} (k : Y' ⟶ Y) (q : Y ⟶ X)
    (q' : Y' ⟶ X) (h : k ≫ q = q')
    (φ : (Scheme.Modules.pullback q).obj L ⟶ (Scheme.Modules.pullback q).obj M) (i : ι) :
    (pullbackFrameHomEquiv he hf hα hβ hT q' (Langlands.Scheme.Modules.transport k h h φ)).1 i =
      k.appLE (q ⁻¹ᵁ T i) (q' ⁻¹ᵁ T i) (by subst h; exact (Scheme.Hom.comp_preimage k q (T i)).le)
        ((pullbackFrameHomEquiv he hf hα hβ hT q φ).1 i) := by
  subst h
  refine congrFun (frameHomEquiv_apply_eq (fun i ↦ (he i).pullbackLocalSection (k ≫ q))
    (fun i ↦ (hf i).pullbackLocalSection (k ≫ q)) (isTransition_pullback (k ≫ q) hα)
    (isTransition_pullback (k ≫ q) hβ) (iSup_preimage_eq_top (k ≫ q) hT) _
    (fun i ↦ k.appLE (q ⁻¹ᵁ T i) ((k ≫ q) ⁻¹ᵁ T i) (Scheme.Hom.comp_preimage k q (T i)).le
      ((pullbackFrameHomEquiv he hf hα hβ hT q φ).1 i)) fun j ↦ ?_) i
  rw [Langlands.Scheme.Modules.transport, Langlands.Scheme.Modules.LineBundleFlatDescent.compIso_rfl,
    Langlands.Scheme.Modules.LineBundleFlatDescent.compIso_rfl]
  simp only [Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply, Iso.app_inv, Iso.app_hom]
  erw [pullbackComp_inv_app_pullbackLocalSection k q (e j)]
  change ((Scheme.Modules.pullbackComp k q).hom.app M).app ((k ≫ q) ⁻¹ᵁ T j)
      (((Scheme.Modules.pullback k).map φ).app (k ⁻¹ᵁ (q ⁻¹ᵁ T j))
        (Langlands.Scheme.Modules.sectionPullback k _ (q ⁻¹ᵁ T j)
          (pullbackLocalSection q (e j)))) = _
  rw [← Langlands.Scheme.Modules.sectionPullback_naturality]
  change ((Scheme.Modules.pullbackComp k q).hom.app M).app _
      (pullbackLocalSection k (φ.app (q ⁻¹ᵁ T j) (pullbackLocalSection q (e j)))) = _
  rw [pullbackFrameHomEquiv_spec he hf hα hβ hT q φ j, pullbackLocalSection_smul,
    Scheme.Modules.Hom.app_smul]
  have h1 := ConcreteCategory.congr_hom (Scheme.Hom.app_eq_appLE (f := k) (U := q ⁻¹ᵁ T j))
    ((pullbackFrameHomEquiv he hf hα hβ hT q φ).1 j)
  have h2 := Langlands.Scheme.Modules.sectionPullback_comp k q M (T j) (f j)
  erw [h1, h2]
  rfl

end Coordinates

section Presheaf

open CoherentSheaves

/-- The restriction maps of the Hom presheaf of the intrinsic module pseudofunctor are
transports along the underlying morphisms. -/
lemma presheafHom_map_eq_transport {Y : Scheme.{u}} (L M : Y.Modules) {U U' : Over Y}
    (k : U' ⟶ U)
    (φ : (Scheme.Modules.pullback U.hom).obj L ⟶ (Scheme.Modules.pullback U.hom).obj M) :
    (intrinsicModulePseudofunctor.presheafHom L M).map k.op φ =
      Langlands.Scheme.Modules.transport k.left (Over.w k) (Over.w k) φ := by
  change Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := intrinsicModulePseudofunctor) φ
      k.left U'.hom U'.hom (Over.w k) (Over.w k) = _
  rw [Pseudofunctor.LocallyDiscreteOpToCat.pullHom,
    IntrinsicModuleHomDescent.mapComp'_hom _ _ _ (Over.w k),
    IntrinsicModuleHomDescent.mapComp'_inv _ _ _ (Over.w k)]
  rfl

/-- The restriction maps of the relative Hom presheaf transport morphisms along the induced maps
of base changes. -/
lemma intrinsicModuleHomPresheaf_map_down {B Y : Scheme.{u}} (p : Y ⟶ B) (L M : Y.Modules)
    {T T' : Over B} (g : T' ⟶ T) (φ : (intrinsicModuleHomPresheaf p L M).obj (op T)) :
    ((intrinsicModuleHomPresheaf p L M).map g.op φ).down =
      Langlands.Scheme.Modules.transport ((Over.pullback p).map g).left
        (Over.w ((Over.pullback p).map g)) (Over.w ((Over.pullback p).map g)) φ.down :=
  presheafHom_map_eq_transport L M ((Over.pullback p).map g) φ.down

end Presheaf

end Langlands.AlgebraicGeometry.Picard.LineHom
