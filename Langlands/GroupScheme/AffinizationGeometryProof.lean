import Langlands.GroupScheme.AffinizationFpqcComparison
import Langlands.GroupScheme.FiniteKernelRepresentation
import Langlands.GroupScheme.SmoothConnectedAffineImage
import Langlands.GroupScheme.GeneralLinearSmoothProof
import Langlands.GroupScheme.AffinizationGeometryStatement
import Langlands.GroupScheme.AntiAffineBaseChange
import Langlands.GroupScheme.DominantHomFlatProof
import Langlands.AlgebraicGeometry.Morphisms.FpqcFiniteDescent

/-! # Geometry of an actual supplied affinization -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

private theorem affinization_geometry_descend
    {k : Type u} [Field k]
    {G Q : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [ConnectedSpace G.X.left]
    (q : G ⟶ Q) (hq : IsAffinization q)
    (hQ : Smooth (((GroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))).obj Q).X.hom))
    (hf : Flat (((GroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))).map q).hom.hom.left))
    (hs : Surjective (((GroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))).map q).hom.hom.left)) :
    Smooth Q.X.hom ∧ ConnectedSpace Q.X.left ∧ Flat q.hom.hom.left ∧
      Surjective q.hom.hom.left ∧ QuasiCompact q.hom.hom.left := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))
  obtain ⟨hbs, hbf, hbq⟩ := fieldExtension_fpqc k (AlgebraicClosure k)
  have : Surjective b := hbs
  have : Flat b := hbf
  have : QuasiCompact b := hbq
  have hpb := DominantHomFlat.baseChange_isPullback b q
  have : Flat q.hom.hom.left := MorphismProperty.of_isPullback_of_descendsAlong
    (P := @Flat) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    hpb ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ hf
  have : Surjective q.hom.hom.left := MorphismProperty.of_isPullback_of_descendsAlong
    (P := @Surjective) (Q := @Surjective) hpb inferInstance hs
  have : Smooth Q.X.hom := MorphismProperty.of_pullback_snd_of_descendsAlong
    (P := @Smooth) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    ⟨⟨hbs, hbf⟩, hbq⟩ hQ
  have : ConnectedSpace Q.X.left :=
    q.hom.hom.left.surjective.connectedSpace q.hom.hom.left.continuous
  have : IsAffine Q.X.left := hq.isAffine
  have : QuasiCompact G.X.hom := quasiCompact_of_smooth_connected G
  have : QuasiCompact (q.hom.hom.left ≫ Q.X.hom) := by
    rw [Over.w q.hom.hom]
    infer_instance
  have : QuasiCompact q.hom.hom.left := QuasiCompact.of_comp _ Q.X.hom
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩


private theorem affinization_geometry_of_comparison
    {k : Type u} [Field k] [IsAlgClosed k]
    {G Q : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [ConnectedSpace G.X.left]
    (q : G ⟶ Q) (hq : IsAffinization q)
    (comparison : ∀ (H : GroupScheme (Spec (CommRingCat.of k))) (q0 : G ⟶ H),
      IsAffine H.X.left → Flat q0.hom.hom.left → Surjective q0.hom.hom.left →
      QuasiCompact q0.hom.hom.left → kernelι q0 ≫ q = 0 →
        ∃ e : H ≅ Q, q0 ≫ e.hom = q) :
    Smooth Q.X.hom ∧ ConnectedSpace Q.X.left ∧ Flat q.hom.hom.left ∧
      Surjective q.hom.hom.left ∧ QuasiCompact q.hom.hom.left := by
  have : IsAffine Q.X.left := hq.isAffine
  have : QuasiCompact G.X.hom := quasiCompact_of_smooth_connected G
  have : CompactSpace G.X.left := QuasiCompact.compactSpace_of_compactSpace G.X.hom
  have : IsLocallyNoetherian G.X.left := LocallyOfFiniteType.isLocallyNoetherian G.X.hom
  have : IsNoetherian G.X.left := ⟨⟩
  let R := kernelDetectingRepresentation q
  let A := GeneralLinear.groupScheme (Fin R.dimension) (CommRingCat.of k)
  have : Smooth A.X.hom := GeneralLinear.smoothStatement _ _
  have : IsAffineHom A.X.hom := GeneralLinear.isAffineHom_groupScheme _ _
  let D := smoothConnectedAffineImage (q ≫ R.hom)
  have : IsAffine D.group.X.left := D.affine
  have : Smooth D.group.X.hom := D.smooth
  have : Flat D.projection.hom.hom.left := D.flat
  have : Surjective D.projection.hom.hom.left := D.surjective
  have : QuasiCompact D.projection.hom.hom.left := D.quasiCompact
  have hk : kernelι D.projection ≫ q = 0 := by
    apply R.detects (kernel D.projection) (kernelι D.projection)
    have he : kernelι D.projection ≫ D.projection = 0 :=
      Grp.hom_ext _ _ (kernel_isPullback D.projection).w
    calc
      kernelι D.projection ≫ q ≫ R.hom =
          kernelι D.projection ≫ (D.projection ≫ D.inclusion) :=
        congrArg (fun f => kernelι D.projection ≫ f) D.comp.symm
      _ = (kernelι D.projection ≫ D.projection) ≫ D.inclusion :=
        (Category.assoc _ _ _).symm
      _ = 0 := by rw [he, zero_comp]
  obtain ⟨e, he⟩ := comparison D.group D.projection D.affine D.flat D.surjective
    D.quasiCompact hk
  have : IsIso e.hom.hom.hom.left :=
    (Over.forget _).map_isIso e.hom.hom.hom
  have : IsIso e.inv.hom.hom.left :=
    (Over.forget _).map_isIso e.inv.hom.hom
  have hqfac : q.hom.hom.left =
      D.projection.hom.hom.left ≫ e.hom.hom.hom.left := by
    exact congrArg (fun f => f.hom.hom.left) he.symm
  have : Flat q.hom.hom.left := by rw [hqfac]; infer_instance
  have : Surjective q.hom.hom.left := by rw [hqfac]; infer_instance
  have : QuasiCompact q.hom.hom.left := by rw [hqfac]; infer_instance
  have : Smooth Q.X.hom := by
    rw [← e.inv.hom.hom.w]
    infer_instance
  have : ConnectedSpace Q.X.left :=
    q.hom.hom.left.surjective.connectedSpace q.hom.hom.left.continuous
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩


private theorem affinization_geometry_arbitrary
    (hAlgClosed : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (G Q : GroupScheme (Spec (CommRingCat.of k))) (q : G ⟶ Q),
      Smooth G.X.hom → ConnectedSpace G.X.left → IsAffinization q →
        Smooth Q.X.hom ∧ ConnectedSpace Q.X.left ∧ Flat q.hom.hom.left ∧
          Surjective q.hom.hom.left ∧ QuasiCompact q.hom.hom.left) :
    AffinizationGeometryStatement.{u} := by
  intro k _ G Q q hG hGc hq
  have : Smooth G.X.hom := hG
  have : ConnectedSpace G.X.left := hGc
  have : QuasiCompact G.X.hom := quasiCompact_of_smooth_connected G
  have : IsSeparated G.X.hom := fieldSeparated k G
  have : CompactSpace G.X.left := QuasiCompact.compactSpace_of_compactSpace G.X.hom
  have : QuasiSeparatedSpace G.X.left := quasiSeparatedSpace_of_quasiSeparated G.X.hom
  let b := Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))
  let B := GroupScheme.baseChange b
  have : Smooth (B.obj G).X.hom :=
    inferInstanceAs (Smooth (pullback.snd G.X.hom b))
  have : ConnectedSpace (B.obj G).X.left :=
    connectedSpace_baseChange_of_smooth_connected b
  have hqK : IsAffinization (B.map q) := hq.baseChange (algebraMap k (AlgebraicClosure k))
  obtain ⟨hQ, _, hf, hs, _⟩ := hAlgClosed (AlgebraicClosure k) (B.obj G) (B.obj Q)
    (B.map q) inferInstance inferInstance hqK
  exact affinization_geometry_descend q hq hQ hf hs

/-- The supplied actual affinization of a smooth connected field group has
smooth connected target and faithfully flat quasi-compact projection. -/
theorem affinizationGeometry : AffinizationGeometryStatement.{u} := by
  apply affinization_geometry_arbitrary
  intro k _ _ G Q q hG hGc hq
  have : Smooth G.X.hom := hG
  have : ConnectedSpace G.X.left := hGc
  apply affinization_geometry_of_comparison q hq
  intro H q0 hHa hqf hqs hqq hk
  have : IsAffine H.X.left := hHa
  have : Flat q0.hom.hom.left := hqf
  have : Surjective q0.hom.hom.left := hqs
  have : QuasiCompact q0.hom.hom.left := hqq
  exact ⟨hq.fpqcComparisonIso q0 hk, hq.fpqcComparisonIso_fac q0 hk⟩

end Langlands.GroupScheme
