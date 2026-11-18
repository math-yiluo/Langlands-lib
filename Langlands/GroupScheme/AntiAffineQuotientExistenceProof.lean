import Langlands.GroupScheme.AntiAffineQuotientExistenceStatement
import Langlands.GroupScheme.AntiAffineQuotientAssembly
import Langlands.GroupScheme.FieldAffinization
import Langlands.GroupScheme.AffinizationGeometryProof
import Langlands.GroupScheme.AntiAffineSmoothConnectedProof

/-! # Existence of the canonical anti-affine quotient -/

noncomputable section
universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Every smooth connected field group admits its canonical affine quotient
with smooth connected anti-affine full scheme-theoretic kernel. -/
theorem antiAffineQuotientExistence : AntiAffineQuotientExistenceStatement.{u} := by
  intro k _ G hG hGc
  have : Smooth G.X.hom := hG
  have : ConnectedSpace G.X.left := hGc
  obtain ⟨Q, q, hq⟩ := FieldAffinization.exists_of_smooth_connected G
  obtain ⟨hQ, hQc, hqf, hqs, hqq⟩ :=
    affinizationGeometry k G Q q inferInstance inferInstance hq
  have : QuasiCompact G.X.hom := quasiCompact_of_smooth_connected G
  have : IsSeparated Q.X.hom := fieldSeparated k Q
  have : LocallyOfFiniteType (kernel q).X.hom := by
    rw [← (kernelι q).hom.hom.w]
    infer_instance
  have : QuasiCompact (kernel q).X.hom := by
    rw [← (kernelι q).hom.hom.w]
    infer_instance
  have : CompactSpace G.X.left :=
    QuasiCompact.compactSpace_of_compactSpace G.X.hom
  have hanti : IsAntiAffine (kernel q) := hq.antiAffine_kernel
  obtain ⟨hNs, hNc⟩ :=
    antiAffineSmoothConnected k (kernel q) inferInstance inferInstance hanti
  exact ⟨AntiAffineQuotient.ofFlatAffinization q hq⟩

end Langlands.GroupScheme
