import Langlands.GroupScheme.Rational.CommutativeVectorClassificationStatement
import Langlands.GroupScheme.Rational.CommutativeVectorSplitExtension
import Langlands.GroupScheme.Rational.CommutativeAdditiveExtension
import Langlands.GroupScheme.Unipotent.AlgebraicallyClosedSplit

/-! # Characteristic-zero classification of commutative unipotent groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

set_option backward.isDefEq.respectTransparency false

/-- In characteristic zero a commutative affine group with a split series of
length `n` has natural vector-group coordinates of dimension `n` on every test. -/
theorem HasSplitSeries.isVectorGroupOfDimension_of_commutative
    {k : Type u} [Field k] [CharZero k] {n : ℕ}
    {H : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom H.X.hom] [IsCommMonObj H.X]
    (h : HasSplitSeries n H) : IsVectorGroupOfDimension H n := by
  induction n generalizing H with
  | zero => exact h.isVectorGroupOfDimension_zero
  | succ n ih =>
    obtain ⟨K, V, j, q, hj, _, _, _, hq, hV, hK⟩ := h
    let : IsClosedImmersion j.hom.hom.left := hj
    let : Mono j.hom.hom := Over.mono_of_mono_left _
    let : IsAffineHom K.X.hom := hj.isAffineHom
    let : IsCommMonObj K.X := by
      apply (isCommMonObj_iff_isMulCommutative K.X).2
      intro T
      refine ⟨⟨fun a b => ?_⟩⟩
      apply (cancel_mono j.hom.hom).1
      simp only [MonObj.mul_comp]
      exact mul_comm _ _
    have hKv : IsVectorGroupOfDimension K n := ih hK
    let : Flat q.hom.hom.left := hq.1
    let : Surjective q.hom.hom.left := hq.2.1
    obtain ⟨σ, hσ⟩ := CommutativeAdditiveExtension.exists_extensionSection
      j q hq.2.2.2.symm hKv hV
    exact CommutativeVectorSplitExtension.isVectorGroupOfDimension_of_section
      j q hq.2.2.2.symm σ hσ hKv hV

/-- The exact published characteristic-zero commutative-unipotent classification,
with one finite dimension and natural group equivalences on every scheme test. -/
theorem commutativeUnipotentVectorCharZero :
    CommutativeUnipotentVectorCharZeroStatement.{u} := by
  intro k _ _ _ G hsm haff hc hu
  let : Smooth G.X.hom := hsm
  let : IsAffineHom G.X.hom := haff
  obtain ⟨n, hn⟩ := Unipotent.algebraicallyClosedSplit k G.toGrp hc hu
  exact ⟨n, hn.isVectorGroupOfDimension_of_commutative⟩

end Langlands.GroupScheme.RelativeRoot
