import Langlands.Automorphic.Unramified.CuspidalWeakBaseChangeTwistStatement
import Langlands.Global.AdelicFunctoriality.LocalDegree
import Langlands.Global.Factors.RelativeWeilAssemblyCharacters

/-! # Norm-trivial determinant twists preserve attached weak base change

A Hecke character `χ` of `F` trivial on the idele-class norms from `E` satisfies
`χ_v(ϖ_v) ^ f_w = 1` at every finite place `w` of `E` above `v` with ramification
index one, where `ϖ_v` is the canonical uniformizer of the completion at `v` and `f_w`
is the residue degree. Hence the residue-degree power of the twisted Satake spectrum
at `v` equals the residue-degree power of the untwisted one, and the determinant twist
of `c` by `χ` has the same weak base change as `c`
(Arthur–Clozel 1989, III.1.1 and Lemma III.6.3).
-/

noncomputable section

universe uF uE uV uW

set_option autoImplicit false

namespace Langlands.Global.HeckeCharacter

open Langlands.Global.AdelicFunctoriality
open scoped NumberField

variable {F : Type uF} {E : Type uE} [Field F] [NumberField F] [Field E] [NumberField E]
  [Algebra F E]

/-- A Hecke character trivial on norms from `E` has uniformizer value of order dividing
the residue degree at every place `w` above `v` of ramification index one. The image of
the canonical uniformizer of `F_v` is a uniformizer of `E_w`, its local norm is the
`f_w`-th power of the uniformizer, and the idele supported at `w` has idele-class norm
supported at `v`. -/
theorem IsTrivialOnNorm.finiteUniformizerValue_pow_inertiaDeg {χ : HeckeCharacter F}
    (hχ : χ.IsTrivialOnNorm E) (v : FinitePlace F) (w : FinitePlacesAbove E v)
    (he : w.1.asIdeal.ramificationIdx (𝓞 F) = 1) :
    χ.finiteUniformizerValue v ^ w.1.asIdeal.inertiaDeg (𝓞 F) = 1 := by
  let uniformizer := (CompletionPadic.padicField v).canonicalTopologicalData.uniformizerUnit
  let upperUnit := Units.map (FiniteExtension.completionMap v w.1).toMonoidHom uniformizer
  have hnorm : FiniteExtension.localUnitNorm v w.1 upperUnit =
      uniformizer ^ w.1.asIdeal.inertiaDeg (𝓞 F) := by
    apply Units.ext
    rw [FiniteExtension.localUnitNorm_val]
    change FiniteExtension.localNorm v w.1
      (FiniteExtension.completionMap v w.1 (uniformizer : FiniteCompletion F v)) = _
    rw [FiniteExtension.localNorm_algebraMap, localDegree_eq, he, one_mul,
      Units.val_pow_eq_pow_val]
  have h := hχ (NumberField.IdeleClassGroup.ofAdicCompletion (𝓞 E) E w.1 upperUnit)
  rw [ideleClassNorm_ofAdicCompletion v w, hnorm] at h
  change χ.finiteComponent v (uniformizer ^ w.1.asIdeal.inertiaDeg (𝓞 F)) = 1 at h
  rw [map_pow] at h
  exact h

end Langlands.Global.HeckeCharacter

namespace Langlands.Automorphic.Unramified

open Langlands.Global Langlands.Unramified
open Langlands.Automorphic.CuspidalOperatorRealization

/-- A determinant twist by a Hecke character trivial on norms preserves an attached
weak base change (Arthur–Clozel 1989, Lemma III.6.3). The twisted lower class carries
the scaled spectral system with the finite determinant tail of `χ` added to its
exceptional set; at every retained place the residue-degree power removes the scaling. -/
theorem cuspidalWeakBaseChangeNormTwist :
    CuspidalWeakBaseChangeNormTwistStatement.{uF, uE, uV, uW} := by
  classical
  intro F E _ _ _ _ _ _ _ r c c' d χ hχ htwist hbase
  have horder := hχ.hasFiniteOrder E
  obtain rfl := (IsoClass.isFiniteOrderDeterminantTwist_iff_eq c c' χ horder).mp htwist
  obtain ⟨s, t, hs, ht, h⟩ := hbase
  let U := s.exceptional ∪ χ.finiteDeterminantTail (r + 1) horder
  refine ⟨(s.scale χ.finiteUniformizerValue).restrict U Finset.subset_union_left,
    t, hs.determinantTwist χ horder, ht, ?_⟩
  filter_upwards [h, U.eventually_cofinite_notMem] with v hv hvU
  obtain ⟨hs', ht', he, hspec⟩ := hv
  refine ⟨hvU, ht', he, fun w => ?_⟩
  rw [hspec w]
  change (s.eigenvalues v hs').power _ =
    (Eigenvalues.scale (χ.finiteUniformizerValue v) (s.eigenvalues v hs')).power _
  rw [Eigenvalues.power_scale, hχ.finiteUniformizerValue_pow_inertiaDeg v w (he w),
    Eigenvalues.scale_one]

end Langlands.Automorphic.Unramified
