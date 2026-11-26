import Langlands.Automorphic.ConjugateContragredient
import Langlands.Automorphic.Contragredient
import Langlands.Automorphic.OperatorCMTransport
import Langlands.Automorphic.OperatorCMTransportClasses
import Langlands.Automorphic.OperatorArithmeticTransportClasses
import Langlands.Global.ArchimedeanLieTransport
import Langlands.Global.ArchimedeanGLTransport

/-!
# Conjugate self-duality from a contragredient CM image

For a CM field `F` and an actual automorphic realization `S` of `GL_n(𝔸_F)`, if the
CM image `S.complexConj` (the realization on the functions `f ∘ c`) realizes the
contragredient of `S`, then `S` is conjugate self-dual: composing the contragredient
pairing of `S.complexConj` with the CM image equivalence `S ≃ S.complexConj` gives a
pairing invariant under the conjugate-twisted operators whose partial map is a
bijection onto the contragredient functionals.

For cuspidal realizations this gives a class criterion: if `Sd` realizes the
contragredient of `S` and the class of `Sd.complexConj` is that of `S`, then the class
of `S` is conjugate self-dual. The file also identifies the arithmetic pullback of a
cuspidal realization along the CM involution with its CM image.
-/

noncomputable section

universe u

set_option autoImplicit false

namespace Langlands.Automorphic

open NumberField Langlands.Global Langlands.Global.CMConjugation
open Langlands.Global.AdelicFunctoriality

variable {F : Type u} [Field F] [NumberField F] [IsCMField F] {n : ℕ}

local instance conjugateSelfDualCriterionRationalGroup (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance conjugateSelfDualCriterionContinuousGroup (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance conjugateSelfDualCriterionFiniteSmoothGroup (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance conjugateSelfDualCriterionFormGroup (n : ℕ) :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance conjugateSelfDualCriterionStableGroup (n : ℕ) :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance conjugateSelfDualCriterionSpaceGroup (S : OperatorRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _

namespace OperatorRealization

/-- The CM involution of `F` is an involution. -/
private theorem fieldConj_trans : (fieldConj F).trans (fieldConj F) = RingEquiv.refl F :=
  RingEquiv.ext (IsCMField.complexConj_apply_apply F)

/-- Entrywise CM conjugation of the finite adelic group is an involution. -/
private theorem finiteConj_twice (d : FiniteAdelicGL F n) :
    finiteConj F n (finiteConj F n d) = d := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  simp only [finiteConj_apply]
  change ((finiteAdeleEquiv (fieldConj F)).trans (finiteAdeleEquiv (fieldConj F))) (d i j) = d i j
  rw [← finiteAdeleEquiv_trans, fieldConj_trans, finiteAdeleEquiv_refl, RingEquiv.refl_apply]

/-- CM conjugation of the standard compact subgroup at infinity is an involution. -/
private theorem compactConj_twice (k : standardInfiniteCompact F n) :
    compactConj F n (compactConj F n k) = k := by
  apply Subtype.ext
  apply Units.ext
  apply Matrix.ext
  intro i j
  simp only [compactConj_val, infiniteConj_apply]
  exact infiniteComplexConj_involutive (K := F) _

omit [NumberField F] [IsCMField F] in
/-- CM conjugation of the real Lie algebra at infinity is an involution. -/
private theorem lieConj_twice (X : ArchimedeanGL.RealLieAlgebra F n) :
    lieConj F n (lieConj F n X) = X := by
  apply (ArchimedeanGL.realLieAlgebraToMatrix F n).injective
  apply Matrix.ext
  intro i j
  simp only [lieConj_apply, mixedConj_apply, star_star, Prod.eta]

/-- The CM image equivalence intertwines the real Lie algebra action, twisted by the CM
conjugation of the Lie algebra. -/
theorem complexConjEquiv_lieAction (S : OperatorRealization F n)
    (X : ArchimedeanGL.RealLieAlgebra F n) (x : S.Space) :
    S.complexConj.lieAction X (S.complexConjEquiv x) =
      S.complexConjEquiv (S.lieAction (lieConj F n X) x) := by
  have h : ArchimedeanLieTransport.realLieEquiv n (fieldConj F) X = lieConj F n X := by
    apply (ArchimedeanGL.realLieAlgebraToMatrix F n).injective
    apply Matrix.ext
    intro i j
    rw [ArchimedeanLieTransport.realLieEquiv_entry, lieConj_apply]
    let y := ArchimedeanGL.realLieAlgebraToMatrix F n X i j
    simpa only [ArchimedeanGLTransport.mixedEquiv, RingEquiv.trans_apply,
      RingEquiv.apply_symm_apply, infiniteComplexConj] using
      mixedSpace_infiniteComplexConj F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm y)
  simpa only [OperatorRealization.lieAction, ArchimedeanLieTransport.envelopingEquiv_generator,
    ArchimedeanLieTransport.complexLieEquiv_complexify, h] using
    S.complexConjEquiv_differential
      (ArchimedeanGL.envelopingGenerator F n (ArchimedeanGL.complexify F n X)) x

set_option maxHeartbeats 1000000 in
/-- If the CM image of `S` realizes the contragredient of `S`, then `S` is conjugate
self-dual: the contragredient pairing `B` of `S.complexConj`, composed in its second
variable with the CM image equivalence `S ≃ S.complexConj`, is a conjugate-contragredient
pairing of `S`. -/
theorem isConjugateSelfDual_of_complexConj_isContragredientOf (S : OperatorRealization F n)
    (h : S.complexConj.IsContragredientOf S) : S.IsConjugateSelfDual := by
  let e := S.complexConjEquiv.toLinearEquiv
  obtain ⟨B, ⟨hf, hk, hLie⟩, hB, hinj, hsurj⟩ := h
  let C := B.compl₁₂ LinearMap.id e.toLinearMap
  have hflip (x : S.Space) : C.flip x = B.flip (e x) := rfl
  refine ⟨C, ⟨?_, ?_, ?_⟩, fun x => hB (e x), ?_, ?_⟩
  · intro d y x
    change B (S.finiteRepresentation (finiteConj F n d) y)
      (S.complexConjEquiv (S.finiteRepresentation d x)) = B y (S.complexConjEquiv x)
    simpa only [S.complexConjEquiv_finite, finiteConj_twice] using
      hf (finiteConj F n d) y (S.complexConjEquiv x)
  · intro k y x
    change B (S.compactRepresentation (compactConj F n k) y)
      (S.complexConjEquiv (S.compactRepresentation k x)) = B y (S.complexConjEquiv x)
    simpa only [S.complexConjEquiv_compact, compactConj_twice] using
      hk (compactConj F n k) y (S.complexConjEquiv x)
  · intro X y x
    change B (S.lieAction (lieConj F n X) y) (S.complexConjEquiv x) +
      B y (S.complexConjEquiv (S.lieAction X x)) = 0
    simpa only [complexConjEquiv_lieAction, lieConj_twice] using
      hLie (lieConj F n X) y (S.complexConjEquiv x)
  · intro x x' hx
    exact e.injective (hinj ((hflip x).symm.trans (hx.trans (hflip x'))))
  · intro l hl
    obtain ⟨x, hx⟩ := hsurj l hl
    exact ⟨e.symm x, (hflip _).trans ((congrArg B.flip (e.apply_symm_apply x)).trans hx)⟩

end OperatorRealization

namespace CuspidalOperatorRealization

variable [CompactSpace (AdeleQuotient F)] {r : ℕ}

/-- The arithmetic pullback of a cuspidal realization along the CM involution of `F` is
its CM image. -/
theorem arithmeticComap_fieldConj (S : CuspidalOperatorRealization F r) :
    S.arithmeticComap (fieldConj F) = S.complexConj := by
  have h : (S.arithmeticComap (fieldConj F)).realization = S.complexConj.realization := by
    change S.realization.arithmeticComap (fieldConj F) = S.realization.complexConj
    apply Subrepresentation.toSubmodule_injective
    rw [OperatorRealization.arithmeticComap_toSubmodule,
      OperatorRealization.complexConj_toSubmodule]
    rfl
  simpa only [CuspidalOperatorRealization.arithmeticComap,
    CuspidalOperatorRealization.complexConj, CuspidalOperatorRealization.mk.injEq] using h

/-- Class form of the arithmetic pullback along the CM involution. -/
theorem IsoClass.arithmeticComap_fieldConj (c : IsoClass F r) :
    IsoClass.arithmeticComap (fieldConj F) c = IsoClass.complexConj c := by
  obtain ⟨S, rfl⟩ := c.exists_representative
  rw [IsoClass.arithmeticComap_isoClass, IsoClass.complexConj_isoClass,
    CuspidalOperatorRealization.arithmeticComap_fieldConj S]

/-- Let `Sd` realize the contragredient of the cuspidal realization `S`. If the CM image
of `Sd` is equivalent to `S`, then the class of `S` is conjugate self-dual. -/
theorem isoClass_isConjugateSelfDual_of_isContragredientOf
    (S Sd : CuspidalOperatorRealization F r)
    (hSd : Sd.realization.IsContragredientOf S.realization)
    (h : Sd.complexConj.isoClass = S.isoClass) : S.isoClass.IsConjugateSelfDual := by
  have h' : Sd.isoClass = S.complexConj.isoClass := by
    simpa only [IsoClass.complexConj_isoClass, complexConj_complexConj] using
      congrArg IsoClass.complexConj h
  obtain ⟨e⟩ := (Sd.isoClass_eq_iff S.complexConj).mp h'
  exact S.isoClass_isConjugateSelfDual_iff.mpr
    (S.realization.isConjugateSelfDual_of_complexConj_isContragredientOf
      (hSd.of_equivalence_right e))

end CuspidalOperatorRealization

end Langlands.Automorphic
