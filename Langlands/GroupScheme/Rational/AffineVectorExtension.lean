import Langlands.GroupScheme.Rational.TorusVectorExtension
import Langlands.GroupScheme.Rational.VectorGroupSplit
import Langlands.GroupScheme.SplitUnipotentQuotientSection
import Langlands.GroupScheme.SplitUnipotentAffineTorsorProof

/-! # Sections of affine extensions by vector groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]
    {E V H : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom E.X.hom] [IsAffineHom H.X.hom]
    (n : V ⟶ E) [Mono n.hom.hom] (q : E ⟶ H)
    [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    (hn : SubgroupFunctor.range n = SubgroupFunctor.range (kernelι q))
    {d : ℕ}

include hn

/-- Every affine faithfully flat quotient of an affine group by a full vector
kernel has a section as a morphism of schemes over the original field. -/
theorem RelativeRoot.IsVectorGroupOfDimension.exists_quotientSection
    (hV : RelativeRoot.IsVectorGroupOfDimension V d) :
    ∃ s : H.X ⟶ E.X, s ≫ q.hom.hom = 𝟙 H.X := by
  let : IsAffineHom V.X.hom := hV.isAffineHom
  let : Smooth V.X.hom := hV.smooth
  let : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  have hqc : QuasiCompact (q.hom.hom.left ≫ H.X.hom) := by
    rw [Over.w q.hom.hom]
    infer_instance
  let : QuasiCompact (q.hom.hom.left ≫ H.X.hom) := hqc
  let : QuasiCompact q.hom.hom.left := QuasiCompact.of_comp _ H.X.hom
  have hfib : ∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ E.X),
      g ≫ q.hom.hom = h ≫ q.hom.hom ↔
        g⁻¹ * h ∈ (SubgroupFunctor.range n).carrier T := by
    intro T g h
    rw [hn, mem_range_kernelι_iff, MonObj.mul_comp, GrpObj.inv_comp]
    exact inv_mul_eq_one.symm
  exact HomogeneousQuotient.affine_section_of_split_unipotent_torsors E V n q.hom.hom
    hfib splitUnipotentAffineTorsorStatement hV.isSplitUnipotent

variable (e : ∀ T : Over (Spec (CommRingCat.of k)),
      (T ⟶ V.X) ≃* Multiplicative (Fin d → Γ(T.left, ⊤)))
    (he : RelativeRoot.IsLinearVectorCoordinates (VectorExtensionDescent.action n q hn) e)

include he

/-- An affine faithfully flat extension of an arbitrary torus by a full vector
kernel with linear ambient conjugation admits an actual group-scheme section. -/
theorem IsTorus.exists_affine_extensionSection (hH : IsTorus H) :
    ∃ σ : H ⟶ E, σ ≫ q = 𝟙 H := by
  have hV : RelativeRoot.IsVectorGroupOfDimension V d := ⟨e, he.1⟩
  let : IsAffineHom V.X.hom := hV.isAffineHom
  obtain ⟨s, hs⟩ := hV.exists_quotientSection n q hn
  exact hH.exists_extensionSection n q hn s hs e he

/-- A chosen group-scheme section of an affine faithfully flat torus extension
with a scalar-linear vector kernel. -/
def IsTorus.affineExtensionSection (hH : IsTorus H) : H ⟶ E :=
  Classical.choose (hH.exists_affine_extensionSection n q hn e he)

/-- The chosen homomorphism splits the original quotient. -/
theorem IsTorus.affineExtensionSection_comp (hH : IsTorus H) :
    hH.affineExtensionSection n q hn e he ≫ q = 𝟙 H :=
  Classical.choose_spec (hH.exists_affine_extensionSection n q hn e he)

end Langlands.GroupScheme
