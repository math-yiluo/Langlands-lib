import Langlands.Automorphic.WeakAutomorphicInductionArithmeticTransport
import Langlands.Global.AdelicFunctoriality.IdeleClassNormTransport
import Langlands.Global.Arithmetic.HarrisProposition48MackeyTransportStatement

/-! # Galois transport of the actual Mackey constituents -/

noncomputable section

universe uF uV

set_option autoImplicit false

namespace Langlands.Global.Harris

open AdelicFunctoriality Langlands.Automorphic

section

variable (Q : Proposition48Problem.{uF})
  (D : IntermediateField Q.E Q.L) (a τ : Q.L ≃ₐ[Q.E] Q.L) (σ : D ≃ₐ[Q.E] D)
  (hστ : ∀ x : D, (σ x : Q.L) = τ x)

private theorem map_conjugateField :
    (Q.conjugateField a).map τ.toAlgHom = Q.conjugateField (τ * a) := by
  ext x
  rw [IntermediateField.mem_map]
  change (∃ y, (∃ z, Q.conjugateEmbedding a z = y) ∧ τ y = x) ↔
    ∃ z, Q.conjugateEmbedding (τ * a) z = x
  constructor
  · rintro ⟨_, ⟨z, rfl⟩, h⟩
    exact ⟨z, h⟩
  · rintro ⟨z, rfl⟩
    exact ⟨Q.conjugateEmbedding a z, ⟨z, rfl⟩, rfl⟩

include hστ in
private theorem map_stepField : D.map τ.toAlgHom = D := by
  ext x
  rw [IntermediateField.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hστ ⟨y, hy⟩ ▸ (σ ⟨y, hy⟩).2
  · intro hx
    refine ⟨σ.symm ⟨x, hx⟩, (σ.symm ⟨x, hx⟩).2, ?_⟩
    exact (hστ _).symm.trans (congrArg Subtype.val (σ.apply_symm_apply _))

include hστ in
private theorem map_mackeyField :
    (Q.mackeyField D a).map τ.toAlgHom = Q.mackeyField D (τ * a) := by
  unfold Proposition48Problem.mackeyField
  rw [IntermediateField.map_sup, map_stepField Q D τ σ hστ, map_conjugateField Q a τ]

private def fieldImageEquiv {S T : IntermediateField Q.E Q.L}
    (h : S.map τ.toAlgHom = T) : S ≃+* T :=
  ((S.equivMap τ.toAlgHom).trans (IntermediateField.equivOfEq h)).toRingEquiv

private def conjugateFieldEquiv : Q.conjugateField a ≃+* Q.conjugateField (τ * a) :=
  fieldImageEquiv Q τ (map_conjugateField Q a τ)

private def mackeyFieldEquiv : Q.mackeyField D a ≃+* Q.mackeyField D (τ * a) :=
  fieldImageEquiv Q τ (map_mackeyField Q D a τ σ hστ)

private theorem comap_conjugateCharacter :
    HeckeCharacter.comap (conjugateFieldEquiv Q a τ) (Q.conjugateCharacter (τ * a)) =
      Q.conjugateCharacter a := by
  let j : Q.E' ≃+* Q.conjugateField a :=
    (Q.conjugateEmbedding a).equivFieldRange.toRingEquiv
  let j' : Q.E' ≃+* Q.conjugateField (τ * a) :=
    (Q.conjugateEmbedding (τ * a)).equivFieldRange.toRingEquiv
  let e := conjugateFieldEquiv Q a τ
  have hj : j.trans e = j' := by
    apply RingEquiv.ext
    intro x
    apply Subtype.ext
    rfl
  have h : e.trans j'.symm = j.symm := by
    apply RingEquiv.ext
    intro x
    apply j'.injective
    change j' (j'.symm (e x)) = j' (j.symm x)
    rw [j'.apply_symm_apply, ← hj, RingEquiv.trans_apply, j.apply_symm_apply]
  change HeckeCharacter.comap e (HeckeCharacter.comap j'.symm Q.ξ) =
    HeckeCharacter.comap j.symm Q.ξ
  rw [← HeckeCharacter.comap_trans, h]

private theorem comap_mackeyCharacter :
    HeckeCharacter.comap (mackeyFieldEquiv Q D a τ σ hστ) (Q.mackeyCharacter D (τ * a)) =
      Q.mackeyCharacter D a := by
  let A := Q.conjugateField a
  let A' := Q.conjugateField (τ * a)
  let C := Q.mackeyField D a
  let C' := Q.mackeyField D (τ * a)
  let : Algebra A C := (IntermediateField.inclusion (show A ≤ C from le_sup_right)).toAlgebra
  let : Algebra A' C' := (IntermediateField.inclusion (show A' ≤ C' from le_sup_right)).toAlgebra
  let e := conjugateFieldEquiv Q a τ
  let f := mackeyFieldEquiv Q D a τ σ hστ
  have he (x : A) : f (algebraMap A C x) = algebraMap A' C' (e x) := by
    apply Subtype.ext
    rfl
  apply DFunLike.ext
  intro x
  change Q.conjugateCharacter (τ * a) (ideleClassNorm (K := A') (ideleClassEquiv f x)) =
    Q.conjugateCharacter a (ideleClassNorm (K := A) x)
  rw [ideleClassNorm_equiv e f he]
  exact DFunLike.congr_fun (comap_conjugateCharacter Q a τ) _

end

/-- The Galois conjugate of the constituent for `a` is a constituent for `τ * a`
when `τ` restricts to `σ` on the step field. -/
theorem proposition48MackeyConstituentGaloisConjugate :
    Proposition48MackeyConstituentGaloisConjugateStatement.{uF, uV} := by
  intro Q D
  let : CompactSpace (AdeleQuotient D) := compactSpace_adeleQuotient D
  intro a τ σ hστ r c hc
  let C := Q.mackeyField D a
  let C' := Q.mackeyField D (τ * a)
  let : Algebra D C := (IntermediateField.inclusion (show D ≤ C from le_sup_left)).toAlgebra
  let : Algebra D C' := (IntermediateField.inclusion (show D ≤ C' from le_sup_left)).toAlgebra
  let f := mackeyFieldEquiv Q D a τ σ hστ
  have hf (x : D) : f (algebraMap D C x) = algebraMap D C' (σ x) := by
    apply Subtype.ext
    exact (hστ x).symm
  have hinv (x : D) : f.symm (algebraMap D C' x) = algebraMap D C (σ.symm x) := by
    apply f.injective
    rw [f.apply_symm_apply, hf, σ.apply_symm_apply]
  have hχ : HeckeCharacter.comap f.symm (Q.mackeyCharacter D a) = Q.mackeyCharacter D (τ * a) := by
    calc
      _ = HeckeCharacter.comap f.symm (HeckeCharacter.comap f (Q.mackeyCharacter D (τ * a))) :=
        congrArg (HeckeCharacter.comap f.symm) (comap_mackeyCharacter Q D a τ σ hστ).symm
      _ = _ := HeckeCharacter.comap_symm_comap f _
  change c.IsWeakAutomorphicInductionOf.{0, 0, uV} (Q.mackeyCharacter D a) at hc
  change (CuspidalOperatorRealization.IsoClass.arithmeticComap σ.toRingEquiv.symm c)
    |>.IsWeakAutomorphicInductionOf.{0, 0, uV} (Q.mackeyCharacter D (τ * a))
  rw [← hχ]
  exact hc.arithmeticComap σ.toRingEquiv.symm f.symm hinv

end Langlands.Global.Harris
