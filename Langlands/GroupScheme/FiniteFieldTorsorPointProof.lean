import Langlands.GroupScheme.FiniteFieldTorsorPointStatement
import Langlands.GroupScheme.FiniteFieldTorsorPoint.LangGroupScheme
import Langlands.GroupScheme.FiniteFieldTorsorPoint.TorsorAction

/-! # Proof that torsors over finite fields have rational points -/

universe u

namespace Langlands.GroupScheme

/-- An actual fpqc torsor under a smooth connected affine group over a finite field
has a rational point: Lang's theorem for the group combined with the torsor
argument. -/
theorem finiteFieldTorsorPointStatement : FiniteFieldTorsorPointStatement.{u} := by
  intro k _ _ H _ _ hconn X _ hfl hs hqc hiso
  let := Fintype.ofFinite k
  exact FiniteFieldTorsorPoint.torsor_point_of_lang H X hfl hs hqc hiso
    (FiniteFieldTorsorPoint.exists_eq_inv_mul_frobenius H (AlgebraicClosure k))

end Langlands.GroupScheme
