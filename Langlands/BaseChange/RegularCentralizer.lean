import Langlands.BaseChange.GeneralLinearFiniteAlgebra
import Langlands.BaseChange.OrbitalIntegral
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.LinearAlgebra.Eigenspace.Zero

/-! Commutativity of regular semisimple matrix centralizers and descent under the cyclic norm. -/

noncomputable section

namespace Langlands.BaseChange

open Matrix _root_.Polynomial
open Langlands.JacquetLanglands

universe u v

private theorem commute_of_separable_charpoly_of_isAlgClosed {K : Type*} [Field K] [IsAlgClosed K]
    {n : ℕ} {A B C : Matrix (Fin n) (Fin n) K} (hA : A.charpoly.Separable)
    (hB : Commute A B) (hC : Commute A C) : Commute B C := by
  let toEnd : Matrix (Fin n) (Fin n) K ≃ₐ[K] Module.End K (Fin n → K) :=
    Matrix.toLinAlgEquiv'
  let a := toEnd A
  let b := toEnd B
  let c := toEnd C
  have hb : Commute a b := hB.map toEnd
  have hc : Commute a c := hC.map toEnd
  have hsep : a.charpoly.Separable := by
    change A.toLin'.charpoly.Separable
    rwa [Matrix.charpoly_toLin']
  have hs : a.IsSemisimple :=
    Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsep.squarefree a.aeval_self_charpoly
  apply toEnd.injective
  rw [map_mul, map_mul, ← LinearMap.eqLocus_eq_top, eq_top_iff, ← hs.iSup_eigenspace_eq_top]
  apply iSup_le
  intro eigenvalue
  have hdim : Module.finrank K (a.eigenspace eigenvalue) ≤ 1 :=
    (a.finrank_eigenspace_le eigenvalue).trans
      (rootMultiplicity_le_one_of_separable hsep eigenvalue)
  obtain ⟨v, hv⟩ := ((a.eigenspace eigenvalue).finrank_le_one_iff_isPrincipal.mp hdim).principal
  have hv' : v ∈ a.eigenspace eigenvalue := hv.symm ▸ Submodule.mem_span_singleton_self v
  have hvb : b v ∈ a.eigenspace eigenvalue :=
    Module.End.mapsTo_genEigenspace_of_comm hb eigenvalue 1 hv'
  have hvc : c v ∈ a.eigenspace eigenvalue :=
    Module.End.mapsTo_genEigenspace_of_comm hc eigenvalue 1 hv'
  rw [hv, Submodule.span_le]
  intro w hw
  have hw' : w = v := Set.mem_singleton_iff.mp hw
  subst w
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp (hv ▸ hvb)
  obtain ⟨s, hs'⟩ := Submodule.mem_span_singleton.mp (hv ▸ hvc)
  change b (c v) = c (b v)
  rw [← ht, ← hs', map_smul, map_smul, ← ht, ← hs', smul_smul, smul_smul, mul_comm s t]

private theorem commute_of_separable_charpoly {K : Type*} [Field K]
    {n : ℕ} {A B C : Matrix (Fin n) (Fin n) K} (hA : A.charpoly.Separable)
    (hB : Commute A B) (hC : Commute A C) : Commute B C := by
  let f := (algebraMap K (AlgebraicClosure K)).mapMatrix (m := Fin n)
  have hs : (f A).charpoly.Separable := by
    change (A.map (algebraMap K (AlgebraicClosure K))).charpoly.Separable
    rw [Matrix.charpoly_map]
    exact hA.map
  have h := commute_of_separable_charpoly_of_isAlgClosed hs (hB.map f) (hC.map f)
  change B * C = C * B
  ext i j
  apply (algebraMap K (AlgebraicClosure K)).injective
  exact congrArg (fun M : Matrix (Fin n) (Fin n) (AlgebraicClosure K) => M i j)
    (show f (B * C) = f (C * B) by rw [map_mul, map_mul, h.eq])

private theorem gl_commute_of_separable_charpoly {K : Type*} [Field K]
    {n : ℕ} {a b c : GeneralLinear n K} (ha : IsRegularSemisimple a)
    (hb : Commute b a) (hc : Commute c a) : Commute b c := by
  change b * c = c * b
  apply Units.ext
  exact (commute_of_separable_charpoly ha
    (hb.symm.map (Units.coeHom _)) (hc.symm.map (Units.coeHom _))).eq

/-- Ordinary centralizers of regular semisimple elements are commutative. -/
theorem glCentralizer_mul_comm {F : Type u} [Field F] {n : ℕ} {γ : GeneralLinear n F}
    (hγ : IsRegularSemisimple γ) (s t : glCentralizer γ) : s * t = t * s := by
  apply Subtype.ext
  have hs : Commute s.val γ := by
    change s.val * γ = γ * s.val
    simpa only [glCentralizer_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
      using s.property
  have ht : Commute t.val γ := by
    change t.val * γ = γ * t.val
    simpa only [glCentralizer_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
      using t.property
  exact (gl_commute_of_separable_charpoly hγ hs ht).eq

variable {F : Type u} [Field F] {E : Type v} [CommRing E] [Algebra F E] {n : ℕ}

/-- Commutativity persists after extension of coefficients to a finite reduced algebra. -/
theorem commute_of_commute_baseChange [Module.Finite F E] [IsReduced E]
    {γ : GeneralLinear n F} (hγ : IsRegularSemisimple γ)
    {b c : GeneralLinear n E} (hb : Commute b (baseChange F E n γ))
    (hc : Commute c (baseChange F E n γ)) : Commute b c := by
  let _ : IsArtinianRing E := IsArtinianRing.of_finite F E
  let e := generalLinearResidueEquiv E n
  change b * c = c * b
  apply e.injective
  rw [map_mul, map_mul]
  funext I
  let _ : Field (E ⧸ I.asIdeal) := Ideal.Quotient.field I.asIdeal
  let q := GeneralLinearGroup.map (n := Fin n) (Ideal.Quotient.mk I.asIdeal)
  have hq : IsRegularSemisimple (q (baseChange F E n γ)) := by
    change ((γ.val.map (algebraMap F E)).map (Ideal.Quotient.mk I.asIdeal)).charpoly.Separable
    rw [Matrix.charpoly_map, Matrix.charpoly_map]
    exact (show γ.val.charpoly.Separable from hγ).map.map
  exact (gl_commute_of_separable_charpoly hq (hb.map q) (hc.map q)).eq

end Langlands.BaseChange
