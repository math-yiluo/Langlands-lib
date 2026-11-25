/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.FieldTrace
public import WeilConjectures.AlgebraicGeometry.Sites.Hilbert90
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# Étale cohomology of a field is torsion in positive degrees

Let `K` be a field and `F` an abelian sheaf on the small étale site of `Spec K`. Every class
in `Hᵠ⁺¹(Spec K_ét, F)` has finite additive order.

## Main statements

- `AlgebraicGeometry.Scheme.exists_nsmul_eq_zero_sheafH_of_field`: every class in positive
  degree is killed by a positive integer.
- `AlgebraicGeometry.Scheme.isOfFinAddOrder_sheafH_of_field`: every class in positive degree
  has finite additive order.

## Implementation details

For `q = 0`, embed `F` into an injective sheaf `I` with quotient `Q`; a class `x ∈ H¹(F)` is
the image of a global section `s` of `Q` under the connecting homomorphism. The section `s`
lifts to `I` over `Spec L` for a finite separable extension `L / K`, so `x` dies under the unit
`F ⟶ f_* f^* F` of `f : Spec L ⟶ Spec K`. Composing with the trace
(`AlgebraicGeometry.Scheme.FieldTrace.unit_comp_trace`) shows `[L : K] • x = 0`. Higher degrees
follow by dimension shifting.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

open FieldTrace _root_.AlgebraicGeometry.Etale

variable (K : Type u) [Field K]

/-- Every class in `H¹(Spec K_ét, F)` is killed by a positive integer. -/
lemma exists_nsmul_eq_zero_sheafH_one_of_field
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (x : Sheaf.H F 1) : ∃ n : ℕ, 0 < n ∧ n • x = 0 := by
  let S := ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F)) (cokernel.condition _)
  have hS : S.ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance
  let hT := MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale (Spec (.of K))
  obtain ⟨y, rfl⟩ := Sheaf.H.δSucc_surjective hS 0 x
  have := (Sheaf.isLocallySurjective_iff_epi' (A := AddCommGrpCat.{u + 1}) S.g).2 hS.epi_g
  obtain ⟨L, _, _, _, g, t, ht⟩ := exists_etaleSpec_field_mem_of_mem_smallEtaleTopology _
    (Presheaf.imageSieve_mem (Spec (.of K)).smallEtaleTopology S.g.hom
      (Sheaf.H.equiv₀ S.X₃ hT y))
  have : Module.Finite K L := Algebra.FormallyUnramified.finite_of_free K L
  let adj := (localizationRestrictionLowerStarAdjunction AddCommGrpCat.{u + 1} (f K L)
    inferInstance)
  let G := localizationRestriction AddCommGrpCat.{u + 1} (f K L) inferInstance ⋙
    (f K L)_*[AddCommGrpCat.{u + 1}]
  let adjG : G ⊣ G :=
    adj.comp (lowerStarLocalizationRestrictionAdjunction AddCommGrpCat.{u + 1} (f K L))
  have : G.IsLeftAdjoint := adjG.isLeftAdjoint
  have : G.IsRightAdjoint := adjG.isRightAdjoint
  have hS' : (S.map G).ShortExact := hS.map_of_exact G
  let φ : S ⟶ S.map G :=
    { τ₁ := unit K L S.X₁
      τ₂ := unit K L S.X₂
      τ₃ := unit K L S.X₃
      comm₁₂ := (adj.unit.naturality S.f).symm
      comm₂₃ := (adj.unit.naturality S.g).symm }
  -- the global section `s` of `Q` lifts to `I` over `Spec K ×_K Spec L`
  let h : (MorphismProperty.Over.map ⊤ (inferInstance : AlgebraicGeometry.Etale (f K L))).obj
      ((f K L).Etale.obj (MorphismProperty.Over.mk ⊤ (𝟙 (Spec (.of K)))
        (MorphismProperty.id_mem @AlgebraicGeometry.Etale _))) ⟶ etaleSpec K L :=
    MorphismProperty.Over.homMk (pullback.snd _ _) rfl
  have hzero : Sheaf.H.map (unit K L S.X₁) 1 (Sheaf.H.δSucc hS 0 y) = 0 := by
    refine (Sheaf.H.map_δSucc hS hS' φ 0 y).trans ?_
    refine (Sheaf.H.exact_map_δSucc hS' 0 _).2 ⟨(Sheaf.H.equiv₀ _ hT).symm
      (S.X₂.obj.map h.op t), ?_⟩
    rw [Sheaf.H.equiv₀_symm_naturality, ← (Sheaf.H.equiv₀ S.X₃ hT).symm_apply_apply y,
      Sheaf.H.equiv₀_symm_naturality]
    congr 1
    change S.g.hom.app _ (S.X₂.obj.map h.op t) = (unit K L S.X₃).hom.app _ _
    rw [unit_app, NatTrans.naturality_apply, ht, ← ConcreteCategory.comp_apply,
      ← Functor.map_comp, ← op_comp, hT.hom_ext (h ≫ g) (counitMor K L _)]
    rfl
  refine ⟨Module.finrank K L, Module.finrank_pos, ?_⟩
  have e := unit_comp_trace K L S.X₁
  rw [natCast_zsmul] at e
  rw [← Sheaf.H.map_id_apply (Sheaf.H.δSucc hS 0 y), ← Sheaf.H.map_nsmul_apply, ← e,
    Sheaf.H.map_comp_apply, hzero, map_zero]

/-- **Étale cohomology of a field is torsion in positive degrees.** Every class in
`Hᵠ⁺¹(Spec K_ét, F)` is killed by a positive integer. -/
theorem exists_nsmul_eq_zero_sheafH_of_field (q : ℕ)
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (x : Sheaf.H F (q + 1)) : ∃ n : ℕ, 0 < n ∧ n • x = 0 := by
  induction q generalizing F with
  | zero => exact exists_nsmul_eq_zero_sheafH_one_of_field K F x
  | succ q ih =>
    let S := ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F))
      (cokernel.condition _)
    have hS : S.ShortExact :=
      ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance
    obtain ⟨y, rfl⟩ := Sheaf.H.δSucc_surjective hS (q + 1) x
    obtain ⟨n, hn, hy⟩ := ih S.X₃ y
    exact ⟨n, hn, by rw [← map_nsmul, hy, map_zero]⟩

/-- **Étale cohomology of a field is torsion in positive degrees.** Every class in
`Hᵠ⁺¹(Spec K_ét, F)` has finite additive order. -/
theorem isOfFinAddOrder_sheafH_of_field
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (x : Sheaf.H F (q + 1)) : IsOfFinAddOrder x :=
  isOfFinAddOrder_iff_nsmul_eq_zero.2 (exists_nsmul_eq_zero_sheafH_of_field K q F x)

end AlgebraicGeometry.Scheme
