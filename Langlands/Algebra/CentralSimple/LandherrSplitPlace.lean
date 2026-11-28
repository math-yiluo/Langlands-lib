import Langlands.Algebra.CentralSimple.LandherrQuadraticData
import Langlands.Global.Arithmetic.ChebotarevPrimeRealizationProof
import Langlands.Global.Arithmetic.KummerRadical
import Langlands.Global.AdelicFunctoriality.LocalDegree
import Mathlib.RingTheory.RamificationInertia.Ramification

/-! # Finite places of a number field at which a quadratic extension splits -/

noncomputable section

namespace Langlands.CentralSimple.Landherr

open NumberField IsDedekindDomain Langlands.Global.AdelicFunctoriality
open scoped Langlands.Global.AdelicFunctoriality.FiniteExtension

universe u

/-- An unramified prime whose arithmetic Frobenius is trivial has local degree one. -/
theorem localDegree_eq_one_of_identity_frobenius {K L : Type u} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (p : HeightOneSpectrum (𝓞 K)) (q : HeightOneSpectrum (𝓞 L))
    [q.asIdeal.LiesOver p.asIdeal] [Algebra.IsUnramifiedAt (𝓞 K) q.asIdeal]
    (hf : (RingOfIntegers.mapAlgHom (1 : L ≃ₐ[K] L)).IsArithFrobAt q.asIdeal) :
    Module.finrank (p.adicCompletion K) (q.adicCompletion L) = 1 := by
  classical
  let : Field (𝓞 K ⧸ p.asIdeal) := Ideal.Quotient.field _
  let : Field (𝓞 L ⧸ q.asIdeal) := Ideal.Quotient.field _
  let : Fintype (𝓞 K ⧸ p.asIdeal) := Fintype.ofFinite _
  let frob := FiniteField.frobeniusAlgHom (𝓞 K ⧸ p.asIdeal) (𝓞 L ⧸ q.asIdeal)
  have hfrob : frob = 1 := by
    ext x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hy := hf.mk_apply y
    rw [← q.asIdeal.over_def p.asIdeal, Nat.card_eq_fintype_card] at hy
    exact hy.symm
  rw [localDegree_eq, Ideal.ramificationIdx_eq_one, one_mul,
    Ideal.inertiaDeg_eq_of_isMaximal p.asIdeal q.asIdeal,
    ← FiniteField.orderOf_frobeniusAlgHom, show orderOf frob = 1 by rw [hfrob, orderOf_one]]

variable (F E : Type u) [Field F] [NumberField F] [Field E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E]

/-- Outside any finite set there is a finite place of `F` at which `d` is a square. -/
theorem exists_split_finitePlace (S : Finset (HeightOneSpectrum (𝓞 F))) :
    ∃ v : HeightOneSpectrum (𝓞 F), v ∉ S ∧
      IsSquare (algebraMap F (v.adicCompletion F) (skewSq F E)) := by
  have : FiniteDimensional F E :=
    .of_finrank_pos (by rw [Algebra.IsQuadraticExtension.finrank_eq_two F E]; decide)
  let _ : NumberField E := NumberField.of_module_finite F E
  obtain ⟨p, hp, q, hq, hu, hf⟩ := Global.chebotarevPrimeRealizationStatement F E 1 S
  have := hq
  have := hu
  have hdeg := localDegree_eq_one_of_identity_frobenius p q hf
  obtain ⟨c, hc⟩ := Global.Arithmetic.KummerRadical.exists_pow_eq_of_finrank_eq_one (p := 2)
    (β := skewRoot F E) (a := skewSq F E) (by rw [sq, algebraMap_skewSq]) p q hdeg
  exact ⟨p, hp, c, by rw [← hc, sq]⟩

end Langlands.CentralSimple.Landherr
