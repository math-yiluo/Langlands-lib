import Langlands.GroupScheme.AntiAffine
import Langlands.GroupScheme.SmoothFieldComponent
import Langlands.GroupScheme.FieldSeparatedProof
import Langlands.AlgebraicGeometry.FieldExtensionAffineDescentProof
import Langlands.AbelianScheme.KernelBaseChange
import Langlands.GroupScheme.Reductive.UnipotentKernelQuotient

/-! # Field base change of anti-affine groups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k L : Type u} [Field k] [Field L]
  {G H : GroupScheme (Spec (CommRingCat.of k))}

namespace IsAntiAffine

/-- Anti-affineness is preserved by an actual group-scheme isomorphism. -/
theorem of_iso (e : G ≅ H) (hG : IsAntiAffine G) : IsAntiAffine H := by
  have : IsIso G.X.hom.appTop := hG
  have : IsIso e.inv.hom.hom := (Grp.forget _).map_isIso e.inv
  have : IsIso e.inv.hom.hom.left := (Over.forget _).map_isIso e.inv.hom.hom
  have : IsIso e.inv.hom.hom.left.appTop := Scheme.Γ.map_isIso e.inv.hom.hom.left.op
  change IsIso H.X.hom.appTop
  rw [← e.inv.hom.hom.w, Scheme.Hom.comp_appTop]
  infer_instance

/-- Flat base change of global sections preserves anti-affineness for qcqs
field groups along every field homomorphism. -/
theorem baseChange [CompactSpace G.X.left] [QuasiSeparatedSpace G.X.left]
    (hG : IsAntiAffine G) (φ : k →+* L) :
    IsAntiAffine ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom φ))).obj G) := by
  let : Algebra k L := φ.toAlgebra
  have : IsIso G.X.hom.appTop := hG
  have hpo := isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat G.X.hom L
  have : IsIso ((Scheme.ΓSpecIso (CommRingCat.of L)).inv ≫
      (pullback.snd G.X.hom (Spec.map (CommRingCat.ofHom (algebraMap k L)))).appTop) :=
    hpo.isIso_inl_of_isIso
  change IsIso (pullback.snd G.X.hom (Spec.map (CommRingCat.ofHom φ))).appTop
  exact (isIso_comp_left_iff (Scheme.ΓSpecIso (CommRingCat.of L)).inv _).mp this

/-- In the smooth connected case the qcqs hypotheses are consequences. -/
theorem baseChange_of_smooth_connected [Smooth G.X.hom] [ConnectedSpace G.X.left]
    (hG : IsAntiAffine G) (φ : k →+* L) :
    IsAntiAffine ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom φ))).obj G) := by
  have : QuasiCompact G.X.hom :=
    quasiCompact_of_smooth_connected G
  have : IsSeparated G.X.hom := fieldSeparated k G
  have : CompactSpace G.X.left := QuasiCompact.compactSpace_of_compactSpace G.X.hom
  have : QuasiSeparatedSpace G.X.left := quasiSeparatedSpace_of_quasiSeparated G.X.hom
  exact hG.baseChange φ

end IsAntiAffine

/-- A smooth connected field group remains connected after every field extension. -/
theorem connectedSpace_baseChange_of_smooth_connected
    [Smooth G.X.hom] [ConnectedSpace G.X.left]
    (b : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of k)) :
    ConnectedSpace ((GroupScheme.baseChange b).obj G).X.left := by
  have : QuasiCompact G.X.hom := quasiCompact_of_smooth_connected G
  exact G.connectedSpace_baseChange_of_connected b

namespace IsAffinization

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The specified affinization homomorphism remains an affinization after every
field extension, provided its source is qcqs. -/
theorem baseChange {Q : GroupScheme (Spec (CommRingCat.of k))} {q : G ⟶ Q}
    [CompactSpace G.X.left] [QuasiSeparatedSpace G.X.left]
    (hq : IsAffinization q) (φ : k →+* L) :
    IsAffinization ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom φ))).map q) := by
  let : Algebra k L := φ.toAlgebra
  let b := Spec.map (CommRingCat.ofHom (algebraMap k L))
  let B := GroupScheme.baseChange b
  have : IsAffine Q.X.left := hq.isAffine
  have : IsIso q.hom.hom.left.appTop := hq.isIso_appTop
  have : IsAffine (B.obj Q).X.left :=
    inferInstanceAs (IsAffine (pullback Q.X.hom b))
  refine ⟨inferInstance, ?_⟩
  have hG := isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat G.X.hom L
  have hQ := isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat Q.X.hom L
  have htop :
      ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ Q.X.hom.appTop) ≫
        q.hom.hom.left.appTop =
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ G.X.hom.appTop := by
    rw [Category.assoc, ← Scheme.Hom.comp_appTop, Over.w]
  have hright :
      ((Scheme.ΓSpecIso (CommRingCat.of L)).inv ≫
        (pullback.snd Q.X.hom b).appTop) ≫ (B.map q).hom.hom.left.appTop =
      (Scheme.ΓSpecIso (CommRingCat.of L)).inv ≫
        (pullback.snd G.X.hom b).appTop := by
    rw [Category.assoc, ← Scheme.Hom.comp_appTop]
    congr 1
    exact congrArg Scheme.Hom.appTop (B.map q).hom.hom.w
  have hnat :
      (pullback.fst Q.X.hom b).appTop ≫ (B.map q).hom.hom.left.appTop =
      q.hom.hom.left.appTop ≫ (pullback.fst G.X.hom b).appTop := by
    rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop]
    congr 1
    change ((Over.pullback b).map q.hom.hom).left ≫ pullback.fst Q.X.hom b =
      pullback.fst G.X.hom b ≫ q.hom.hom.left
    simp only [Over.pullback_map_left, pullback.lift_fst]
  have houter : IsPushout (CommRingCat.ofHom (algebraMap k L))
      (((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ Q.X.hom.appTop) ≫
        q.hom.hom.left.appTop)
      (((Scheme.ΓSpecIso (CommRingCat.of L)).inv ≫
        (pullback.snd Q.X.hom b).appTop) ≫ (B.map q).hom.hom.left.appTop)
      (pullback.fst G.X.hom b).appTop := by
    rw [htop, hright]
    exact hG
  exact (houter.of_top hnat hQ).isIso_inl_of_isIso

end IsAffinization

namespace AntiAffineQuotient

variable (A : AntiAffineQuotient G)

/-- A supplied anti-affine quotient has an actual smooth connected unipotent kernel. -/
theorem hasSmoothConnectedUnipotentKernel :
    HasSmoothConnectedUnipotentKernel A.projection :=
  ⟨A.smooth_kernel, A.connectedSpace_kernel, A.antiAffine_kernel.isUnipotent⟩

/-- Anti-affineness of the actual kernel persists under every field extension. -/
theorem antiAffine_kernel_baseChange (φ : k →+* L) :
    IsAntiAffine (kernel
      ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom φ))).map A.projection)) := by
  have : Smooth (kernel A.projection).X.hom := A.smooth_kernel
  have : ConnectedSpace (kernel A.projection).X.left := A.connectedSpace_kernel
  exact IsAntiAffine.of_iso
    (kernelBaseChangeIso (Spec.map (CommRingCat.ofHom φ)) A.projection)
    (A.antiAffine_kernel.baseChange_of_smooth_connected φ)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A supplied canonical anti-affine quotient commutes with every field extension.
Its group and projection are the actual base changes of the supplied data. -/
def baseChange (φ : k →+* L) :
    AntiAffineQuotient
      ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom φ))).obj G) := by
  let b := Spec.map (CommRingCat.ofHom φ)
  let B := GroupScheme.baseChange b
  have : IsAffine A.group.X.left := A.isAffinization.isAffine
  have : QuasiCompact A.projection.hom.hom.left := A.quasiCompact_projection
  have : CompactSpace G.X.left :=
    QuasiCompact.compactSpace_of_compactSpace A.projection.hom.hom.left
  have : IsSeparated G.X.hom := fieldSeparated k G
  have : QuasiSeparatedSpace G.X.left := quasiSeparatedSpace_of_quasiSeparated G.X.hom
  have : Smooth A.group.X.hom := A.smooth
  have : ConnectedSpace A.group.X.left := A.connectedSpace
  have : Smooth (kernel A.projection).X.hom := A.smooth_kernel
  have : ConnectedSpace (kernel A.projection).X.left := A.connectedSpace_kernel
  have : Smooth (B.obj (kernel A.projection)).X.hom :=
    inferInstanceAs (Smooth (pullback.snd (kernel A.projection).X.hom b))
  have : ConnectedSpace (B.obj (kernel A.projection)).X.left :=
    connectedSpace_baseChange_of_smooth_connected b
  let e : (kernel (B.map A.projection)).X ≅ (B.obj (kernel A.projection)).X :=
    (Grp.forget (Over (Spec (CommRingCat.of L)))).mapIso
      (kernelBaseChangeIso b A.projection).symm
  have : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
  refine
    { group := B.obj A.group
      projection := B.map A.projection
      isAffinization := A.isAffinization.baseChange φ
      smooth := inferInstanceAs (Smooth (pullback.snd A.group.X.hom b))
      connectedSpace := connectedSpace_baseChange_of_smooth_connected b
      smooth_projection := MorphismProperty.overPullbackMap (P := @Smooth)
        b A.projection.hom.hom A.smooth_projection
      surjective_projection := MorphismProperty.overPullbackMap (P := @Surjective)
        b A.projection.hom.hom A.surjective_projection
      quasiCompact_projection := MorphismProperty.overPullbackMap (P := @QuasiCompact)
        b A.projection.hom.hom A.quasiCompact_projection
      smooth_kernel := ?_
      connectedSpace_kernel := ?_
      antiAffine_kernel := A.antiAffine_kernel_baseChange φ }
  · rw [← e.hom.w]
    infer_instance
  · exact (Scheme.homeoOfIso ((Over.forget _).mapIso e)).connectedSpace_iff.2
      ‹ConnectedSpace (B.obj (kernel A.projection)).X.left›

/-- The base-changed actual projection has a smooth connected unipotent kernel. -/
theorem hasSmoothConnectedUnipotentKernel_baseChange (φ : k →+* L) :
    HasSmoothConnectedUnipotentKernel
      ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom φ))).map A.projection) :=
  (A.baseChange φ).hasSmoothConnectedUnipotentKernel

end AntiAffineQuotient

end Langlands.GroupScheme
