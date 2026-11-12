import Langlands.GroupScheme.Reductive.FiniteProducts
import Langlands.GroupScheme.AffineWeilEmbeddingProduct
import Langlands.GroupScheme.Reductive.FieldExtensionProof
import Langlands.GroupScheme.Reductive.SemisimpleFieldReflectionProof
import Langlands.GroupScheme.Dynamic.CentralizerReductiveTransport
import Mathlib.FieldTheory.Separable

/-! # Connected reductivity of finite separable affine Weil restriction -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

namespace AffineWeil

/-- The actual finite separable affine Weil restriction of a connected
reductive group is connected reductive. -/
theorem isConnectedReductive_restriction
    (k K : Type u) [Field k] [Field K] [Algebra k K] [FiniteDimensional k K]
    [Algebra.IsSeparable k K] (G : GroupScheme (Spec (CommRingCat.of K)))
    (hG : IsConnectedReductive G) :
    haveI := hG.isAffineHom
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    haveI := hG.smooth
    IsConnectedReductive (groupScheme k K G) := by
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : Smooth G.X.hom := hG.smooth
  let Ω := AlgebraicClosure k
  let A : (K →ₐ[k] Ω) → GroupScheme (Spec (CommRingCat.of Ω)) := fun τ =>
    (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom τ.toRingHom))).obj G
  have hA : ∀ τ, IsConnectedReductive (A τ) := by
    intro τ
    let : Algebra K Ω := τ.toRingHom.toAlgebra
    exact connectedReductiveFieldExtensionStatement K Ω G hG
  have hprod : IsConnectedReductive (GroupScheme.pi A) :=
    isConnectedReductive_pi_of_isAlgClosed A hA
  have hsplit : ∀ x : K, ((minpoly k x).map (algebraMap k Ω)).Splits :=
    fun _ => IsAlgClosed.splits _
  have hbase := hprod.of_iso (embeddingProductIso k K Ω hsplit G)
  exact IsConnectedReductive.of_fieldExtension hbase

end AffineWeil

end Langlands.GroupScheme
