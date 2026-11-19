import Langlands.GroupScheme.Torus.NagataReductionStatements
import Langlands.GroupScheme.Reductive.LinearlyReductiveFieldExtensionProof
import Langlands.GroupScheme.Torus.MultiplicativeTypeFiniteGaloisSplittingProof
import Langlands.GroupScheme.AffineLinearEmbeddingProof
import Langlands.GroupScheme.MatrixRepresentation.LinearlyReductiveFrobeniusKernel
import Langlands.GroupScheme.Torus.LinearlyReductiveReducedIdentity
import Langlands.GroupScheme.Torus.NagataConnectedReduction

/-! # The identity-component necessity in Nagata's theorem -/

universe u

open AlgebraicGeometry CategoryTheory

namespace Langlands.GroupScheme

/-- Over a field of nonzero characteristic, the actual identity component of
a linearly reductive affine group scheme of finite type is of multiplicative
type, without smoothness or reducedness hypotheses. -/
theorem nagataIdentityComponentNecessity :
    NagataIdentityComponentNecessityStatement.{u} := by
  intro k _ p _ hp G _ _ hG
  let K := AlgebraicClosure k
  let b := algebraBaseMap k K
  let GK := (GroupScheme.baseChange b).obj G
  let : LocallyOfFiniteType GK.X.hom :=
    inferInstanceAs (LocallyOfFiniteType (CategoryTheory.Limits.pullback.snd G.X.hom b))
  let : IsAffineHom GK.X.hom :=
    inferInstanceAs (IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b))
  have hp' := (CharP.char_is_prime_or_zero k p).resolve_right hp
  let : ExpChar K p := ExpChar.prime hp'
  have hGK : IsLinearlyReductive GK :=
    (LinearReductivity.linearlyReductiveFieldExtension k K G).mp hG
  have hcomp : IsMultiplicativeType (finiteTypeIdentityComponent GK) := by
    refine nagataConnectedFrobeniusReduction K p hp'.one_lt
      (linearlyReductiveReducedIdentity K p hp'.one_lt) ?_ GK hGK
    intro H _ _ hH
    obtain ⟨n, ρ, hρ⟩ := affineLinearEmbeddingStatement K H inferInstance inferInstance
    exact ⟨n, ρ, hρ, MatrixRepresentation.linearlyReductiveFrobeniusKernel
      K p hp'.one_lt H hH n ρ hρ⟩
  have hMT : IsMultiplicativeType
      ((GroupScheme.baseChange b).obj (finiteTypeIdentityComponent G)) :=
    IsMultiplicativeType.of_iso
      (IdentityComponent.FiniteType.baseChangeIso G (algebraMap k K)) hcomp
  obtain ⟨Λ, hΛ, hfg, ⟨e⟩⟩ :=
    MultiplicativeTypeSplitting.isFGDiagonalizable_of_isSepClosed _ hMT
  exact ⟨finiteTypeIdentityComponent G, finiteTypeIdentityComponentι G, inferInstance,
    IdentityComponent.FiniteType.range_finiteTypeIdentityComponentι G,
    ⟨K, inferInstance, inferInstance, Λ, hΛ, hfg, ⟨e⟩⟩⟩

end Langlands.GroupScheme
