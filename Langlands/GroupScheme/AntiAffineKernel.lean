import Langlands.GroupScheme.AntiAffine
import Langlands.GroupScheme.KernelPair
import Langlands.GroupScheme.FieldSeparatedProof
import Langlands.AlgebraicGeometry.GlobalFunctionsFieldProof

/-! # The kernel of a flat affinization is anti-affine -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

private lemma isPushout_appTop_of_flat
    {X Y S T : Scheme.{u}} {f : T ⟶ S} {g : Y ⟶ X} {iX : X ⟶ S} {iY : Y ⟶ T}
    (H : IsPullback g iY iX f)
    [IsAffine S] [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace T] [QuasiSeparatedSpace T] [Flat f]
    (hiX : iX.appTop.hom.Flat) :
    IsPushout iX.appTop f.appTop g.appTop iY.appTop := by
  have h := isIso_pushoutSection_of_isCompact_of_flat_right_of_ringHomFlat H
    (US := ⊤) (UT := ⊤) (UX := ⊤) (UY := ⊤) (by simp) (by simp) (by simp)
    (isAffineOpen_top _) CompactSpace.isCompact_univ isQuasiSeparated_univ
    CompactSpace.isCompact_univ isQuasiSeparated_univ
    (by
      have he : iX.appTop = iX.appLE ⊤ ⊤ (by simp) := Scheme.Hom.app_eq_appLE iX
      rw [← he]
      exact hiX)
  convert (isIso_pushoutSection_iff ..).mp h using 1 <;>
    exact Scheme.Hom.app_eq_appLE _

variable {k : Type u} [Field k]
  {G Q : GroupScheme (Spec (CommRingCat.of k))}

/-- A flat affinization of a quasi-compact field group has anti-affine full scheme kernel. -/
theorem IsAffinization.antiAffine_kernel {q : G ⟶ Q}
    [CompactSpace G.X.left] [Flat q.hom.hom.left]
    (hq : IsAffinization q) : IsAntiAffine (kernel q) := by
  have : IsAffine Q.X.left := hq.isAffine
  have : IsIso q.hom.hom.left.appTop := hq.isIso_appTop
  have : IsSeparated G.X.hom := fieldSeparated k G
  have : IsSeparated Q.X.hom := fieldSeparated k Q
  have : IsSeparated (kernel q).X.hom := fieldSeparated k (kernel q)
  have : QuasiSeparatedSpace G.X.left := quasiSeparatedSpace_of_quasiSeparated G.X.hom
  have : QuasiSeparatedSpace (kernel q).X.left :=
    quasiSeparatedSpace_of_quasiSeparated (kernel q).X.hom
  have : CompactSpace (kernel q).X.left :=
    QuasiCompact.compactSpace_of_compactSpace (kernelι q).hom.hom.left
  have hpo := isPushout_appTop_of_flat
    (IsPullback.of_hasPullback q.hom.hom.left q.hom.hom.left)
    (RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso q.hom.hom.left.appTop))
  have : IsIso (pullback.fst q.hom.hom.left q.hom.hom.left).appTop :=
    hpo.isIso_inl_of_isIso
  have : IsIso (KernelPair.schemeIso q).hom.appTop :=
    Scheme.Γ.map_isIso (KernelPair.schemeIso q).hom.op
  have hfst : IsIso (fst G.X (kernel q).X).left.appTop := by
    rw [← KernelPair.schemeIso_hom_fst q, Scheme.Hom.comp_appTop]
    infer_instance
  have : IsIso (pullback.fst G.X.hom (kernel q).X.hom).appTop := hfst
  have : Flat G.X.hom := inferInstance
  let := ((Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.toMulEquiv.isField
    (Field.toIsField k)).toField
  have hflat : (kernel q).X.hom.appTop.hom.Flat := by
    algebraize [(kernel q).X.hom.appTop.hom]
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  have hprod := isPushout_appTop_of_flat
    ((IsPullback.of_hasPullback G.X.hom (kernel q).X.hom).flip) hflat
  have : Nonempty (⊤ : G.X.left.Opens) :=
    ⟨⟨η[G.X].left (Classical.choice (inferInstance : Nonempty (Spec (CommRingCat.of k)))),
      trivial⟩⟩
  have hfaith : G.X.hom.appTop.hom.FaithfullyFlat := by
    algebraize [G.X.hom.appTop.hom]
    exact RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance
  exact Langlands.AlgebraicGeometry.GlobalFunctionsFieldProof.isIso_of_isPushout_of_faithfullyFlat
    _ _ _ _ hprod hfaith

end Langlands.GroupScheme
