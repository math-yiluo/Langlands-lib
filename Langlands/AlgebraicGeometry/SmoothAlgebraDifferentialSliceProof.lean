import Langlands.AlgebraicGeometry.SmoothAlgebraDifferentialSliceStatement
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.Smooth.StandardSmoothOfFree

/-! # Proof of the algebraic differential slicing criterion -/

noncomputable section

universe u v w t

namespace Langlands.AlgebraicGeometry

open Algebra TensorProduct

/-- Exactness identifies the differentials and first cotangent homology of a
quotient when its cotangent map is bijective. -/
theorem formallyEtale_of_cotangentComplex_bijective
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (P : Algebra.Extension.{w} R S) [Algebra.FormallySmooth R P.Ring]
    (h : Function.Bijective P.cotangentComplex) :
    Algebra.FormallyEtale R S := by
  have hzero : ∀ x : Ω[S⁄R], x = 0 := by
    intro x
    obtain ⟨y, rfl⟩ := P.toKaehler_surjective x
    exact (P.exact_cotangentComplex_toKaehler y).mpr (h.surjective y)
  exact ⟨⟨fun x y ↦ (hzero x).trans (hzero y).symm⟩,
    (P.cotangentComplex_injective_iff).mp h.injective⟩

/-- The finite kernel generators map to a basis, so the cotangent map is an
isomorphism and the quotient is etale. -/
theorem smoothAlgebraDifferentialSlice :
    SmoothAlgebraDifferentialSliceStatement.{u, v, w, t} := by
  intro R S _ _ _ P _ ι _ f hf b hb
  let v : ι → P.Cotangent := fun i ↦
    Algebra.Extension.Cotangent.mk ⟨f i, hf.le (Ideal.subset_span ⟨i, rfl⟩)⟩
  have hv : Submodule.span S (Set.range v) = ⊤ :=
    Algebra.Extension.Cotangent.span_eq_top_of_span_eq_ker f hf
  have hcomp : P.cotangentComplex ∘ v = b := by
    funext i
    exact (P.cotangentComplex_mk _).trans (hb i).symm
  have hbij : Function.Bijective P.cotangentComplex :=
    LinearMap.bijective_of_linearIndependent_of_span_eq_top hv
      (hcomp.symm ▸ b.linearIndependent) (hcomp.symm ▸ b.span_eq)
  have : Algebra.FormallyEtale R S :=
    formallyEtale_of_cotangentComplex_bijective P hbij
  have hfg : P.ker.FG := by
    rw [← hf]
    exact Submodule.fg_span (Set.finite_range f)
  have : Algebra.FinitePresentation R S :=
    Algebra.FinitePresentation.of_surjective (f := IsScalarTower.toAlgHom R P.Ring S)
      P.algebraMap_surjective hfg
  exact ⟨inferInstance, inferInstance⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- A prescribed differential basis at a prime extends, with the same
functions, to a principal open neighborhood. -/
theorem exists_notMem_basis_kaehlerDifferential
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.Smooth R S] (p : Ideal S) [p.IsPrime]
    {ι : Type t} (f : ι → S)
    (b : Module.Basis ι (Localization.AtPrime p) (Ω[Localization.AtPrime p⁄R]))
    (hb : ∀ i, b i =
      KaehlerDifferential.D R (Localization.AtPrime p)
        (algebraMap S (Localization.AtPrime p) (f i))) :
    ∃ (g : S), g ∉ p ∧
      ∃ (b' : Module.Basis ι (Localization.Away g) (Ω[Localization.Away g⁄R])),
        ∀ i, b' i = KaehlerDifferential.D R (Localization.Away g)
          (algebraMap S (Localization.Away g) (f i)) := by
  let e : (ι →₀ S) →ₗ[S] Ω[S⁄R] :=
    Finsupp.linearCombination S fun i ↦ KaehlerDifferential.D R S (f i)
  let l₁ : (ι →₀ S) →ₗ[S] (ι →₀ Localization.AtPrime p) :=
    Finsupp.mapRange.linearMap (Algebra.linearMap S (Localization.AtPrime p))
  let l₂ : Ω[S⁄R] →ₗ[S] Ω[Localization.AtPrime p⁄R] :=
    KaehlerDifferential.map R R S (Localization.AtPrime p)
  let eₚ : (ι →₀ Localization.AtPrime p) →ₗ[Localization.AtPrime p]
      Ω[Localization.AtPrime p⁄R] :=
    IsLocalizedModule.mapExtendScalars p.primeCompl l₁ l₂ (Localization.AtPrime p) e
  have heₚ : eₚ = b.repr.symm := by
    ext i
    trans IsLocalizedModule.map p.primeCompl l₁ l₂ e (l₁ (Finsupp.single i 1))
    · simp [eₚ, -IsLocalizedModule.map_apply, l₁]
    · simp [l₂, e, hb]
  have : Finite ι := Module.Finite.finite_basis b
  have hbij : Function.Bijective eₚ := heₚ ▸ b.repr.symm.bijective
  obtain ⟨g, hg, h⟩ := Module.FinitePresentation.exists_notMem_bijective e p l₁ l₂
    hbij
  let l₁' : (ι →₀ S) →ₗ[S] (ι →₀ Localization.Away g) :=
    Finsupp.mapRange.linearMap (Algebra.linearMap S _)
  let l₂' : Ω[S⁄R] →ₗ[S] Ω[Localization.Away g⁄R] :=
    KaehlerDifferential.map R R S (Localization.Away g)
  rw [← IsLocalizedModule.map_bijective_iff_localizedModuleMap_bijective l₁' l₂'] at h
  let e' : (ι →₀ Localization.Away g) →ₗ[Localization.Away g] Ω[Localization.Away g⁄R] :=
    IsLocalizedModule.mapExtendScalars (Submonoid.powers g) l₁' l₂' (Localization.Away g) e
  refine ⟨g, hg, Module.Basis.ofRepr (LinearEquiv.ofBijective e' h).symm, ?_⟩
  intro i
  change e' (Finsupp.single i 1) = _
  trans IsLocalizedModule.map (Submonoid.powers g) l₁' l₂' e (l₁' (Finsupp.single i 1))
  · simp [e', -IsLocalizedModule.map_apply, l₁']
  · simp [l₂', e]

/-- Quotienting a smooth algebra by a differential basis gives an etale
algebra. -/
theorem etale_quotient_span_of_basis_kaehlerDifferential
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.Smooth R S] {ι : Type t} [Finite ι] (f : ι → S)
    (b : Module.Basis ι S (Ω[S⁄R]))
    (hb : ∀ i, b i = KaehlerDifferential.D R S (f i)) :
    Algebra.Etale R (S ⧸ Ideal.span (Set.range f)) := by
  let I := Ideal.span (Set.range f)
  let P : Algebra.Extension R (S ⧸ I) :=
    { Ring := S
      σ := fun x ↦ (Ideal.Quotient.mk_surjective x).choose
      algebraMap_σ := fun x ↦ (Ideal.Quotient.mk_surjective x).choose_spec }
  have hker : Ideal.span (Set.range f) = P.ker := by
    exact Ideal.mk_ker.symm
  exact smoothAlgebraDifferentialSlice R (S ⧸ I) P ι f hker
    (b.baseChange (S ⧸ I)) (by intro i; simp [P, hb])

/-- A differential basis at a prime cuts out an etale quotient after
localizing away from an element outside that prime. -/
theorem exists_notMem_etale_quotient_span
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.Smooth R S] (p : Ideal S) [p.IsPrime]
    {ι : Type t} (f : ι → S)
    (b : Module.Basis ι (Localization.AtPrime p) (Ω[Localization.AtPrime p⁄R]))
    (hb : ∀ i, b i =
      KaehlerDifferential.D R (Localization.AtPrime p)
        (algebraMap S (Localization.AtPrime p) (f i))) :
    ∃ (g : S), g ∉ p ∧ Algebra.Etale R
      ((Localization.Away g) ⧸
        Ideal.span (Set.range (fun i ↦ algebraMap S (Localization.Away g) (f i)))) := by
  obtain ⟨g, hg, b', hb'⟩ := exists_notMem_basis_kaehlerDifferential p f b hb
  have : Finite ι := Module.Finite.finite_basis b
  have : Algebra.Smooth S (Localization.Away g) :=
    Algebra.Smooth.of_isLocalization_Away g
  have : Algebra.Smooth R (Localization.Away g) :=
    Algebra.Smooth.comp R S (Localization.Away g)
  exact ⟨g, hg, etale_quotient_span_of_basis_kaehlerDifferential _ b' hb'⟩

/-- Any family whose differentials generate at a prime contains finitely many
equations cutting out an etale quotient in a neighborhood. -/
theorem exists_notMem_etale_quotient_span_of_span
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.Smooth R S] (p : Ideal S) [p.IsPrime] (C : Set S)
    (hC : Submodule.span (Localization.AtPrime p)
      (Set.range (fun x : C ↦ KaehlerDifferential.D R (Localization.AtPrime p)
        (algebraMap S (Localization.AtPrime p) x))) = ⊤) :
    ∃ (ι : Type v) (_ : Finite ι) (f : ι → S), (∀ i, f i ∈ C) ∧
      ∃ (g : S), g ∉ p ∧ Algebra.Etale R
        ((Localization.Away g) ⧸
          Ideal.span (Set.range (fun i ↦ algebraMap S (Localization.Away g) (f i)))) := by
  obtain ⟨ι, a, b, hb⟩ := Module.exists_basis_of_span_of_flat _ hC
  have : Finite ι := Module.Finite.finite_basis b
  exact ⟨ι, inferInstance, (fun i ↦ (a i).1), (fun i ↦ (a i).2),
    exists_notMem_etale_quotient_span p _ b hb⟩

/-- Generation of the cotangent fiber suffices for choosing transverse
equations, by Nakayama's lemma. -/
theorem exists_notMem_etale_quotient_span_of_residue_span
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.Smooth R S] (p : Ideal S) [p.IsPrime] (C : Set S)
    (hC : Submodule.span (IsLocalRing.ResidueField (Localization.AtPrime p))
      (Set.range (fun x : C ↦
        (1 : IsLocalRing.ResidueField (Localization.AtPrime p)) ⊗ₜ[Localization.AtPrime p]
          KaehlerDifferential.D R (Localization.AtPrime p)
            (algebraMap S (Localization.AtPrime p) x))) = ⊤) :
    ∃ (ι : Type v) (_ : Finite ι) (f : ι → S), (∀ i, f i ∈ C) ∧
      ∃ (g : S), g ∉ p ∧ Algebra.Etale R
        ((Localization.Away g) ⧸
          Ideal.span (Set.range (fun i ↦ algebraMap S (Localization.Away g) (f i)))) := by
  apply exists_notMem_etale_quotient_span_of_span p C
  apply IsLocalRing.map_tensorProduct_mk_eq_top.mp
  rw [Submodule.map_span,
    ← Submodule.restrictScalars_span (Localization.AtPrime p)
      (IsLocalRing.ResidueField (Localization.AtPrime p)) Ideal.Quotient.mk_surjective,
    ← Set.range_comp]
  change (Submodule.span (IsLocalRing.ResidueField (Localization.AtPrime p))
    (Set.range (fun x : C ↦
      (1 : IsLocalRing.ResidueField (Localization.AtPrime p)) ⊗ₜ[Localization.AtPrime p]
        KaehlerDifferential.D R (Localization.AtPrime p)
          (algebraMap S (Localization.AtPrime p) x)))).restrictScalars _ = ⊤
  rw [hC, Submodule.restrictScalars_top]

end Langlands.AlgebraicGeometry
