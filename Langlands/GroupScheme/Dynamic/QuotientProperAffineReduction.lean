import Langlands.GroupScheme.Dynamic.AffineHomogeneousClosedProduct
import Langlands.GroupScheme.Dynamic.QuotientEmbeddingClosed
import Langlands.GroupScheme.Dynamic.GeneralLinearQuotientProper
import Langlands.GroupScheme.Reductive.LinearQuotientAffineReduction
import Langlands.GroupScheme.Dynamic.QuotientProperStatement

/-! # Supplied dynamic quotient properness from independent linear quotient affineness -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme

namespace Dynamic

section Comparison

variable {k : Type u} [Field k] [IsAlgClosed k]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  [Smooth G.X.hom] [Smooth H.X.hom] [IsAffine H.X.left]
  (f : G ⟶ H) (hf : IsClosedSubgroup f)
  (D : HomogeneousQuotientFromEmbedding.HomogeneousQuotient f) [IsAffine D.scheme.left]
  (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
  {Q R : Over (Spec (CommRingCat.of k))} (q : G.X ⟶ Q) (r : H.X ⟶ R)
  [Smooth q.left] [Surjective q.left] [QuasiCompact q.left]
  [Smooth r.left] [Surjective r.left] [QuasiCompact r.left]
  [QuasiCompact Q.hom] [LocallyOfFiniteType R.hom]
  (hq : ∀ (T : Over (Spec (CommRingCat.of k))) (a b : T ⟶ G.X),
    a ≫ q = b ≫ q ↔ a⁻¹ * b ∈ (parabolic χ).carrier T)
  (hr : ∀ (T : Over (Spec (CommRingCat.of k))) (a b : T ⟶ H.X),
    a ≫ r = b ≫ r ↔ a⁻¹ * b ∈ (parabolic (χ ≫ f)).carrier T)

/-- A supplied affine ambient homogeneous quotient gives the actual closed
comparison of the two supplied dynamic quotients, with its projection equation. -/
def suppliedClosedQuotientComparison_of_affine_homogeneous :
    {m : Q ⟶ R // IsClosedImmersion m.left ∧ q ≫ m = f.hom.hom ≫ r} := by
  let : IsClosedImmersion f.hom.hom.left := hf
  let : Mono f.hom.hom.left := inferInstance
  let : Mono f.hom.hom := Over.mono_of_mono_left _
  exact suppliedClosedQuotientComparison_of_product_closed f χ q r hq hr
    (Affine.parabolicHom (χ ≫ f)) (Affine.isRepresentedBy_parabolicHom (χ ≫ f)) hf
    (D.isClosed_range_product_parabolic χ)

end Comparison

end Dynamic

/-- Independent affineness of reductive linear homogeneous quotients suffices
for the unchanged all-universe supplied dynamic quotient properness statement. -/
theorem dynamicQuotientProper_of_reductiveLinearQuotientAffine
    (hA : ReductiveLinearQuotientAffineStatement.{u}) :
    DynamicQuotientProperStatement.{u} := by
  intro k _ _ G hG χ Q q hsep hft hqc hsm hsurj hqqc hq
  let := hsep
  let := hft
  let := hqc
  let := hsm
  let := hsurj
  let := hqqc
  let : Smooth G.X.hom := hG.smooth
  obtain ⟨N, ρ, hρ, D, hD⟩ :=
    exists_affine_linearQuotient_of_reductiveLinearQuotientAffine hA k G hG
  let H := GeneralLinear.groupScheme (Fin N) (CommRingCat.of k)
  let : Smooth H.X.hom := GeneralLinear.smoothStatement (Fin N) _
  let : IsAffine H.X.left := GeneralLinear.isAffine_groupScheme (Fin N) _
  let : IsAffineHom D.scheme.hom := hD
  let : IsAffine D.scheme.left := isAffine_of_isAffineHom D.scheme.hom
  let E := GeneralLinear.properDynamicQuotient k (χ ≫ ρ)
  let := E.smooth_projection
  let := E.surjective_projection
  let := E.quasiCompact_projection
  let := E.locallyOfFiniteType
  let : IsProper E.scheme.hom := GeneralLinear.isProper_properDynamicQuotient k (χ ≫ ρ)
  have hr : ∀ (T : Over (Spec (CommRingCat.of k))) (a b : T ⟶ H.X),
      a ≫ E.projection = b ≫ E.projection ↔
        a⁻¹ * b ∈ (Dynamic.parabolic (χ ≫ ρ)).carrier T := by
    intro T a b
    rw [E.fibers, (Dynamic.Affine.isRepresentedBy_parabolicHom (χ ≫ ρ)).2]
  let C := Dynamic.suppliedClosedQuotientComparison_of_affine_homogeneous ρ hρ D χ
    q E.projection hq hr
  let : IsClosedImmersion C.val.left := C.property.1
  rw [← Over.w C.val]
  infer_instance

end Langlands.GroupScheme
