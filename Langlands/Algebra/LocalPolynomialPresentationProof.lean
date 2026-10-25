import Langlands.Algebra.LocalPolynomialPresentationStatement
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-! # A local polynomial presentation of an essentially finite type algebra -/

universe u v

namespace Langlands.Algebra

/-- An essentially finite type local algebra is a local quotient of a
finite-variable polynomial ring localized at a prime. -/
theorem localPolynomialPresentation :
    LocalPolynomialPresentationStatement.{u, v} := by
  classical
  intro R S _ _ _ _ _ _ h
  let := h
  let A := _root_.Algebra.EssFiniteType.subalgebra R S
  let M := _root_.Algebra.EssFiniteType.submonoid R S
  obtain ⟨n, g, hg⟩ :=
    _root_.Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
      (inferInstance : _root_.Algebra.FiniteType R A)
  let φ : MvPolynomial (Fin n) R →ₐ[R] S := A.val.comp g
  let q := (IsLocalRing.maximalIdeal S).comap φ.toRingHom
  have hq : q.IsPrime := Ideal.comap_isPrime φ.toRingHom _
  let := hq
  have hφ : ∀ y : q.primeCompl, IsUnit (φ y) := by
    intro y
    have hy : φ y ∉ IsLocalRing.maximalIdeal S := y.property
    simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] using hy
  let f : Localization.AtPrime q →ₐ[R] S := IsLocalization.liftAlgHom hφ
  have hf : Function.Surjective f := by
    change Function.Surjective (IsLocalization.lift hφ : Localization.AtPrime q →+* S)
    rw [IsLocalization.lift_surjective_iff]
    intro s
    obtain ⟨⟨a, t⟩, hs⟩ := IsLocalization.surj M s
    obtain ⟨a', ha'⟩ := hg a
    obtain ⟨t', ht'⟩ := hg (t : A)
    have ht : IsUnit (φ t') := by
      change IsUnit (A.val (g t'))
      rw [ht']
      exact t.property
    have htq : t' ∈ q.primeCompl := by
      change φ t' ∉ IsLocalRing.maximalIdeal S
      simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] using ht
    refine ⟨⟨a', ⟨t', htq⟩⟩, ?_⟩
    change s * A.val (g t') = A.val (g a')
    rw [ht', ha']
    exact hs
  have hlocal : IsLocalHom (algebraMap R (Localization.AtPrime q)) := by
    have hc : IsLocalHom (f.toRingHom.comp (algebraMap R (Localization.AtPrime q))) := by
      change IsLocalHom ((f : Localization.AtPrime q →+* S).comp _)
      rw [f.comp_algebraMap]
      infer_instance
    exact isLocalHom_of_comp _ f.toRingHom
  exact ⟨n, q, hq, f, hf, hlocal, IsLocalHom.of_surjective f.toRingHom hf⟩

end Langlands.Algebra
