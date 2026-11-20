import Langlands.BaseChange.CyclicNormFieldConjugacy
import Langlands.BaseChange.CyclicNormFieldExistence

/-! # The cyclic norm lemma for `GL_n` -/

namespace Langlands.BaseChange

universe u v

/-- The norm lemma of Henniart–Lemaire for finite reduced cyclic algebras. -/
theorem cyclicNormLemma : CyclicNormLemmaStatement.{u,v} := by
  apply cyclicNormLemma_of_field_exists.{u,v}
  intro F _ E _ _ σ l n h δ
  exact cyclicNormAssociated_of_field h δ

end Langlands.BaseChange
