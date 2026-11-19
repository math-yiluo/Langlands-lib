import Langlands.AlgebraicGeometry.FiniteEtale.AffineSplittingOfSections
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.Polynomial.Basic

/-! # Specialization of sections of a finite étale affine-space algebra -/

noncomputable section

universe u v

open Function MvPolynomial
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.FiniteEtale

attribute [local instance] MvPolynomial.algebraMvPolynomial

private theorem exists_specialization {k E : Type*} [Field k] [IsAlgClosed k]
    [Field E] [Algebra k E] (T : Subalgebra k E) (hT : T.FG) :
    Nonempty (T →ₐ[k] k) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal T
  let : Algebra.FiniteType k T := ⟨T.fg_top.mpr hT⟩
  let : Field (T ⧸ m) := Ideal.Quotient.field m
  let : Module.Finite k (T ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (T ⧸ m)
  exact ⟨(IsAlgClosed.lift : (T ⧸ m) →ₐ[k] k).comp (Ideal.Quotient.mkₐ k m)⟩

private theorem exists_section_of_section_over_extension {k E A : Type*}
    [Field k] [IsAlgClosed k] [Field E] [Algebra k E] {n : ℕ}
    [CommRing A] [Algebra (MvPolynomial (Fin n) k) A]
    [Algebra.FiniteType (MvPolynomial (Fin n) k) A]
    (φ : A →ₐ[MvPolynomial (Fin n) k] MvPolynomial (Fin n) E) (p : A → k)
    (hφ : ∀ a, constantCoeff (φ a) = algebraMap k E (p a)) :
    ∃ ψ : A →ₐ[MvPolynomial (Fin n) k] MvPolynomial (Fin n) k,
      ∀ a, constantCoeff (ψ a) = p a := by
  classical
  let R := MvPolynomial (Fin n) k
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := R) (A := A)
  let t := s.biUnion fun a => (φ a).coeffs
  let T := Algebra.adjoin k (t : Set E)
  let f : MvPolynomial (Fin n) T →ₐ[R] MvPolynomial (Fin n) E :=
    ⟨MvPolynomial.map T.val.toRingHom, fun r => by
      change MvPolynomial.map T.val.toRingHom (MvPolynomial.map (algebraMap k T) r) =
        MvPolynomial.map (algebraMap k E) r
      rw [MvPolynomial.map_map]
      exact congrArg (fun c : k →+* E => MvPolynomial.map c r) T.val.comp_algebraMap⟩
  have hf : Injective f := MvPolynomial.map_injective _ Subtype.val_injective
  have hrange (a : A) : φ a ∈ f.range := by
    suffices (⊤ : Subalgebra R A) ≤ f.range.comap φ from this Algebra.mem_top
    rw [← hs, Algebra.adjoin_le_iff]
    intro x hx
    change φ x ∈ Set.range (MvPolynomial.map T.val.toRingHom)
    refine MvPolynomial.mem_range_map_iff_coeffs_subset.mpr fun c hc => ?_
    refine ⟨⟨c, Algebra.subset_adjoin ?_⟩, rfl⟩
    exact Finset.mem_biUnion.mpr ⟨x, hx, hc⟩
  let e := AlgEquiv.ofInjective f hf
  let ψ : A →ₐ[R] MvPolynomial (Fin n) T := e.symm.toAlgHom.comp (φ.codRestrict f.range hrange)
  have hψ (a : A) : f (ψ a) = φ a :=
    congrArg Subtype.val (e.apply_symm_apply (φ.codRestrict f.range hrange a))
  obtain ⟨ρ⟩ := exists_specialization T ⟨t, rfl⟩
  let g : MvPolynomial (Fin n) T →ₐ[R] R :=
    ⟨MvPolynomial.map ρ.toRingHom, fun r => by
      change MvPolynomial.map ρ.toRingHom (MvPolynomial.map (algebraMap k T) r) = r
      rw [MvPolynomial.map_map]
      have hρ : ρ.toRingHom.comp (algebraMap k T) = RingHom.id k := ρ.comp_algebraMap
      exact (congrArg (fun c : k →+* k => MvPolynomial.map c r) hρ).trans
        (MvPolynomial.map_id r)⟩
  refine ⟨g.comp ψ, fun a => ?_⟩
  have hcoeff : constantCoeff (ψ a) = algebraMap k T (p a) := by
    apply Subtype.val_injective
    change T.val (constantCoeff (ψ a)) = algebraMap k E (p a)
    have he : MvPolynomial.map T.val.toRingHom (ψ a) = φ a := hψ a
    rw [← hφ a, ← he, constantCoeff_map]
    rfl
  change constantCoeff (MvPolynomial.map ρ.toRingHom (ψ a)) = p a
  rw [constantCoeff_map, hcoeff]
  exact ρ.commutes (p a)

set_option maxHeartbeats 400000 in
/-- Splitting descends along a coefficient-field extension of an algebraically closed field. -/
theorem exists_algEquiv_pi_of_split_extension {k A : Type u} {E : Type v}
    [Field k] [IsAlgClosed k] [Field E] [Algebra k E] {n : ℕ}
    [CommRing A] [Algebra (MvPolynomial (Fin n) k) A]
    [Algebra.Etale (MvPolynomial (Fin n) k) A] [Module.Finite (MvPolynomial (Fin n) k) A]
    (h : ∃ m : ℕ, Nonempty
      ((MvPolynomial (Fin n) E ⊗[MvPolynomial (Fin n) k] A) ≃ₐ[MvPolynomial (Fin n) E]
        (Fin m → MvPolynomial (Fin n) E))) :
    ∃ m : ℕ, Nonempty (A ≃ₐ[MvPolynomial (Fin n) k] (Fin m → MvPolynomial (Fin n) k)) := by
  let R := MvPolynomial (Fin n) k
  let S := MvPolynomial (Fin n) E
  let : Algebra R k := (constantCoeff (σ := Fin n) (R := k)).toAlgebra
  let : Algebra S E := (constantCoeff (σ := Fin n) (R := E)).toAlgebra
  let : Algebra R E := ((algebraMap k E).comp (constantCoeff (σ := Fin n))).toAlgebra
  let : IsScalarTower R S E := IsScalarTower.of_algebraMap_eq fun r =>
    (constantCoeff_map (algebraMap k E) r).symm
  obtain ⟨m, ⟨e⟩⟩ := h
  apply exists_algEquiv_pi_of_sections (K := k)
  intro p
  let p₀ : A →ₐ[R] E :=
    ⟨(algebraMap k E).comp p.toRingHom, fun r => congrArg (algebraMap k E) (p.commutes r)⟩
  let pE := AlgHom.liftEquiv R S A E p₀
  obtain ⟨φE, hφE⟩ := exists_section_of_algEquiv_pi e pE
  let φ : A →ₐ[R] S :=
    (φE.restrictScalars R).comp Algebra.TensorProduct.includeRight
  have hφ (a : A) : constantCoeff (φ a) = algebraMap k E (p a) := by
    have he := congrArg (AlgHom.liftEquiv R S A E).symm hφE
    exact DFunLike.congr_fun (he.trans ((AlgHom.liftEquiv R S A E).symm_apply_apply p₀)) a
  obtain ⟨ψ, hψ⟩ := exists_section_of_section_over_extension φ p hφ
  exact ⟨ψ, AlgHom.ext hψ⟩

end Langlands.AlgebraicGeometry.FiniteEtale
