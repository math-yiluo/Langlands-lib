import Langlands.GroupScheme.Rational.TorusAnisotropicPartStatement
import Langlands.GroupScheme.Rational.TorusAnisotropicKernel
import Langlands.GroupScheme.Rational.TorusSplitQuotientIsogeny
import Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof

/-! # The maximal anisotropic subtorus and the almost direct product -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

/-- Every actual field torus has its universal anisotropic subtorus, and
multiplication with every largest split subtorus is finite and surjective. -/
theorem torusAnisotropicPart : TorusAnisotropicPartStatement.{u} := by
  intro k _ T hT
  obtain ⟨E, hE, hA, hfin, hgal, hTE⟩ :=
    torusFiniteGaloisSplitting k T.toGrp hT
  let := hE
  let := hA
  have := hfin
  have := hgal
  let : Fintype (E ≃ₐ[k] E) := Fintype.ofFinite _
  have hTE : IsSplitTorus
      ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj T).toGrp := hTE
  obtain ⟨Q, q, hQ, hqi, hqr⟩ :=
    TorusAnisotropicPart.exists_splitQuotient k E T hTE
  have : IsAffineHom Q.toGrp.X.hom := hQ.isAffineHom
  have : IsSeparated Q.toGrp.X.hom := inferInstance
  refine ⟨CommGroupScheme.kernel q, kernelι (CommGroupScheme.groupHom q),
    ?_, ?_, ?_, ?_, ?_⟩
  · change IsClosedImmersion (kernelι (CommGroupScheme.groupHom q)).hom.hom.left
    infer_instance
  · exact ⟨E, inferInstance, inferInstance,
      TorusAnisotropicPart.isSplitTorus_kernel_baseChange k E q hTE hQ hqr⟩
  · exact TorusAnisotropicPart.isAnisotropic_kernel k E q hTE hqr
  · intro C c _ hC hCa
    exact TorusAnisotropicPart.factors_kernel_of_isAnisotropic k q hQ C c hC hCa
  · intro A a ha
    have : IsAffine T.X.left := SplittingAssembly.isAffine_of_isTorus T.toGrp hT
    have : IsAffineHom T.toGrp.X.hom := inferInstance
    have : Smooth T.toGrp.X.hom := hT.smooth
    have : LocallyOfFiniteType T.toGrp.X.hom := inferInstance
    exact TorusAnisotropicPart.invariantQuotient_splitPart_kernelMultiplication
      k E hT hTE (a := Additive.ofMul a) ha hQ ⟨hqi, hqr⟩

end Langlands.GroupScheme
