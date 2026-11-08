import Langlands.ClassField.Global.IdeleLocalInjectivity
import Langlands.ClassField.Global.IdeleGaloisDescentProof

/-! # Single-place idele classes under the inclusion `C_K → C_L` and the Galois action

For a finite extension `L / K` of number fields and a finite place `p` of `K`, the inclusion
of the idele (class) with the single coordinate `a ∈ K_pˣ` is the product, over the places
`q` of `L` above `p`, of the idele (classes) with the single coordinate `a ∈ L_qˣ`. For a
family of relative automorphisms `σ i` of `E / F` such that `i ↦ σ i (w)` is a bijection onto
the places above `z`, the product of the `σ i`-conjugates of the `w`-coordinate class of `a`
is therefore the image of the `z`-coordinate class of `a` under `C_F → C_E`; left coset
representatives of the decomposition group of `w` form such a family.
-/

noncomputable section

universe u v

namespace Langlands.Global.AdelicFunctoriality

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField

variable {K : Type u} {L : Type v} [Field K] [Field L]
  [NumberField K] [NumberField L] [Algebra K L]

/-- The inclusion of a finite adele supported at the single place `p` is the product of
the finite adeles supported at the places above `p`, with coordinates the completed
embeddings. -/
theorem finiteAdeleInclusion_ofAdicCompletion (p : HeightOneSpectrum (𝓞 K))
    (x : p.adicCompletion K) :
    finiteAdeleInclusion (L := L) (FiniteAdeleRing.ofAdicCompletion K p x) =
      ∏ q : FinitePlacesAbove L p,
        FiniteAdeleRing.ofAdicCompletion L q.1 (FiniteExtension.completionMap p q.1 x) := by
  classical
  apply FiniteAdeleRing.ext
  intro q
  have hev (f : FinitePlacesAbove L p → FiniteAdeleRing (𝓞 L) L) :
      (∏ r, f r) q = ∏ r, f r q :=
    map_prod ({ toFun := fun z : FiniteAdeleRing (𝓞 L) L => z q
                map_one' := rfl
                map_mul' := fun _ _ => rfl } :
      FiniteAdeleRing (𝓞 L) L →* q.adicCompletion L) f _
  rw [finiteAdeleInclusion_apply, hev]
  change FiniteExtension.completionMap _ q (Pi.mulSingle p x (q.under (𝓞 K))) =
    ∏ r : FinitePlacesAbove L p, Pi.mulSingle r.1 (FiniteExtension.completionMap p r.1 x) q
  by_cases h : q.asIdeal.LiesOver p.asIdeal
  · have hp : q.under (𝓞 K) = p := finitePlacesAbove_under p ⟨q, h⟩
    subst hp
    rw [Pi.mulSingle_eq_same, Finset.prod_eq_single ⟨q, h⟩]
    · rw [Pi.mulSingle_eq_same]
    · intro r _ hr
      apply Pi.mulSingle_eq_of_ne
      intro hrq
      exact hr (Subtype.ext hrq.symm)
    · intro hq
      exact absurd (Finset.mem_univ _) hq
  · have hp : q.under (𝓞 K) ≠ p := by
      rintro rfl
      exact h (liesOver_under q)
    rw [Pi.mulSingle_eq_of_ne hp, map_one]
    refine (Finset.prod_eq_one fun r _ => Pi.mulSingle_eq_of_ne ?_ _).symm
    rintro rfl
    exact h r.2

/-- The inclusion of an idele with the single coordinate `a` at `p` is the product of the
ideles with the single coordinate `a` at the places above `p`. -/
theorem ideleInclusion_ofAdicCompletion (p : HeightOneSpectrum (𝓞 K))
    (a : (p.adicCompletion K)ˣ) :
    ideleInclusion (L := L) (IdeleGroup.ofAdicCompletion (𝓞 K) K p a) =
      ∏ q : FinitePlacesAbove L p, IdeleGroup.ofAdicCompletion (𝓞 L) L q.1
        (Units.map (FiniteExtension.completionMap p q.1).toMonoidHom a) := by
  have hfst (f : FinitePlacesAbove L p → AdeleRing (𝓞 L) L) :
      (∏ r, f r).1 = ∏ r, (f r).1 :=
    map_prod ({ toFun := fun x : AdeleRing (𝓞 L) L => x.1
                map_one' := rfl
                map_mul' := fun _ _ => rfl } : AdeleRing (𝓞 L) L →* InfiniteAdeleRing L) f _
  have hsnd (f : FinitePlacesAbove L p → AdeleRing (𝓞 L) L) :
      (∏ r, f r).2 = ∏ r, (f r).2 :=
    map_prod ({ toFun := fun x : AdeleRing (𝓞 L) L => x.2
                map_one' := rfl
                map_mul' := fun _ _ => rfl } :
      AdeleRing (𝓞 L) L →* FiniteAdeleRing (𝓞 L) L) f _
  apply Units.ext
  rw [ideleInclusion_val, Units.coe_prod]
  apply Prod.ext
  · rw [hfst]
    change infiniteAdeleMap (algebraMap K L) 1 =
      ∏ _q : FinitePlacesAbove L p, (1 : InfiniteAdeleRing L)
    rw [map_one, Finset.prod_const_one]
  · rw [hsnd]
    exact finiteAdeleInclusion_ofAdicCompletion p (a : p.adicCompletion K)

/-- The product, over the places `q` of `L` above `p`, of the idele classes with the single
coordinate `a ∈ L_qˣ` is the image under `C_K → C_L` of the idele class with the single
coordinate `a ∈ K_pˣ`. -/
theorem prod_ofAdicCompletion_eq_ideleClassInclusion (p : HeightOneSpectrum (𝓞 K))
    (a : (p.adicCompletion K)ˣ) :
    ∏ q : FinitePlacesAbove L p, IdeleClassGroup.ofAdicCompletion (𝓞 L) L q.1
        (Units.map (FiniteExtension.completionMap p q.1).toMonoidHom a) =
      ideleClassInclusion (IdeleClassGroup.ofAdicCompletion (𝓞 K) K p a) := by
  change ∏ q : FinitePlacesAbove L p,
      QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 L) L)
        (IdeleGroup.ofAdicCompletion (𝓞 L) L q.1
          (Units.map (FiniteExtension.completionMap p q.1).toMonoidHom a)) =
    QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 L) L)
      (ideleInclusion (IdeleGroup.ofAdicCompletion (𝓞 K) K p a))
  rw [← map_prod, ideleInclusion_ofAdicCompletion]

end Langlands.Global.AdelicFunctoriality

namespace Langlands.ClassField.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField
open Langlands.Global.AdelicFunctoriality

section Conjugates

variable {F : Type u} {E : Type v} [Field F] [NumberField F] [Field E] [NumberField E]
  [Algebra F E] (z : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
  [w.asIdeal.LiesOver z.asIdeal]

/-- If `finitePlaceEquiv σ q = w`, that is `q = σ(w)`, then `σ` moves the idele class with the
single coordinate `a ∈ E_wˣ` (for `a ∈ F_zˣ`) to the one with the single coordinate
`a ∈ E_qˣ`. -/
theorem relativeIdeleClassAut_ofAdicCompletion_completionMap (σ : E ≃ₐ[F] E)
    (q : HeightOneSpectrum (𝓞 E)) [q.asIdeal.LiesOver z.asIdeal]
    (h : finitePlaceEquiv σ.toRingEquiv q = w) (a : (z.adicCompletion F)ˣ) :
    relativeIdeleClassAut F E σ (IdeleClassGroup.ofAdicCompletion (𝓞 E) E w
        (Units.map (FiniteExtension.completionMap z w).toMonoidHom a)) =
      IdeleClassGroup.ofAdicCompletion (𝓞 E) E q
        (Units.map (FiniteExtension.completionMap z q).toMonoidHom a) := by
  subst h
  change ideleClassEquiv σ.toRingEquiv _ = _
  rw [ideleClassEquiv_ofAdicCompletion]
  congr 1
  apply Units.ext
  exact IdeleGaloisDescentProof.finiteCompletionEquiv_completionMap σ z q
    (a : z.adicCompletion F)

/-- For a finite family `σ` of relative automorphisms such that every place `q` above `z`
satisfies `finitePlaceEquiv (σ i) q = w` (that is `q = σ i (w)`) for exactly one `i`, the
product of the `σ i`-conjugates of the idele class with the single coordinate `a ∈ E_wˣ`
(for `a ∈ F_zˣ`) is the image under `C_F → C_E` of the idele class with the single
coordinate `a ∈ F_zˣ`. -/
theorem prod_relativeIdeleClassAut_ofAdicCompletion {ι : Type*} [Fintype ι]
    (σ : ι → E ≃ₐ[F] E)
    (hσ : ∀ q : HeightOneSpectrum (𝓞 E), q.asIdeal.LiesOver z.asIdeal →
      ∃! i, finitePlaceEquiv (σ i).toRingEquiv q = w)
    (a : (z.adicCompletion F)ˣ) :
    ∏ i, relativeIdeleClassAut F E (σ i) (IdeleClassGroup.ofAdicCompletion (𝓞 E) E w
        (Units.map (FiniteExtension.completionMap z w).toMonoidHom a)) =
      ideleClassInclusion (IdeleClassGroup.ofAdicCompletion (𝓞 F) F z a) := by
  have hlies : ∀ i,
      ((finitePlaceEquiv (σ i).toRingEquiv).symm w).asIdeal.LiesOver z.asIdeal := by
    intro i
    have h := liesOver_under (K := F) ((finitePlaceEquiv (σ i).toRingEquiv).symm w)
    rwa [← IdeleGaloisDescentProof.finitePlaceEquiv_under (σ i), Equiv.apply_symm_apply,
      finitePlacesAbove_under z ⟨w, inferInstance⟩] at h
  let f : ι → FinitePlacesAbove E z := fun i =>
    ⟨(finitePlaceEquiv (σ i).toRingEquiv).symm w, hlies i⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j hij
      have hq : (finitePlaceEquiv (σ i).toRingEquiv).symm w =
          (finitePlaceEquiv (σ j).toRingEquiv).symm w := congrArg Subtype.val hij
      obtain ⟨k, -, hk⟩ := hσ _ (hlies i)
      refine (hk i (Equiv.apply_symm_apply _ _)).trans (hk j ?_).symm
      show finitePlaceEquiv (σ j).toRingEquiv ((finitePlaceEquiv (σ i).toRingEquiv).symm w) = w
      rw [hq, Equiv.apply_symm_apply]
    · rintro ⟨q, hq⟩
      obtain ⟨i, hi, -⟩ := hσ q hq
      exact ⟨i, Subtype.ext ((Equiv.symm_apply_eq _).mpr hi.symm)⟩
  rw [← prod_ofAdicCompletion_eq_ideleClassInclusion]
  refine Fintype.prod_bijective f hf _ _ fun i => ?_
  have := hlies i
  exact relativeIdeleClassAut_ofAdicCompletion_completionMap z w (σ i) _
    (Equiv.apply_symm_apply _ _) a

end Conjugates

section Cosets

open scoped Langlands.Global.AdelicFunctoriality.FiniteExtension
open FundamentalClass

variable {F E : Type u} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [IsGalois F E] (z : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
  [w.asIdeal.LiesOver z.asIdeal]

/-- Left coset representatives `σ i` of the decomposition group `D_w`, the image of
`decompositionHom z w`, satisfy the place condition of
`prod_relativeIdeleClassAut_ofAdicCompletion`: every place `q` above `z` is `σ i (w)` for
exactly one `i`. -/
theorem existsUnique_finitePlaceEquiv_eq_of_coset {ι : Type*} (σ : ι → E ≃ₐ[F] E)
    (hσ : ∀ τ : E ≃ₐ[F] E, ∃! i, (σ i)⁻¹ * τ ∈ (decompositionHom z w).range)
    (q : HeightOneSpectrum (𝓞 E)) (hq : q.asIdeal.LiesOver z.asIdeal) :
    ∃! i, finitePlaceEquiv (σ i).toRingEquiv q = w := by
  have := hq
  obtain ⟨g, hg⟩ := exists_finitePlaceEquiv_eq z w q
  have hmul : ∀ x y : E ≃ₐ[F] E, finitePlaceEquiv (x * y).toRingEquiv w =
      finitePlaceEquiv y.toRingEquiv (finitePlaceEquiv x.toRingEquiv w) := by
    intro x y
    change finitePlaceEquiv (y.toRingEquiv.trans x.toRingEquiv) w = _
    rw [finitePlaceEquiv_trans]
    rfl
  have key : ∀ i, finitePlaceEquiv (σ i).toRingEquiv q = w ↔
      (σ i)⁻¹ * g⁻¹ ∈ (decompositionHom z w).range := by
    intro i
    rw [← mul_inv_rev, Subgroup.inv_mem_iff, mem_range_decompositionHom_iff, hmul, hg]
  obtain ⟨i, hi, huniq⟩ := hσ g⁻¹
  exact ⟨i, (key i).mpr hi, fun j hj => huniq j ((key j).mp hj)⟩

/-- The product of the conjugates of the idele class with the single coordinate `a ∈ E_wˣ`
(for `a ∈ F_zˣ`) by left coset representatives `σ i` of the decomposition group of `w` is the
image under `C_F → C_E` of the idele class with the single coordinate `a ∈ F_zˣ`. -/
theorem prod_relativeIdeleClassAut_ofAdicCompletion_of_coset {ι : Type*} [Fintype ι]
    (σ : ι → E ≃ₐ[F] E)
    (hσ : ∀ τ : E ≃ₐ[F] E, ∃! i, (σ i)⁻¹ * τ ∈ (decompositionHom z w).range)
    (a : (z.adicCompletion F)ˣ) :
    ∏ i, relativeIdeleClassAut F E (σ i) (IdeleClassGroup.ofAdicCompletion (𝓞 E) E w
        (Units.map (FiniteExtension.completionMap z w).toMonoidHom a)) =
      ideleClassInclusion (IdeleClassGroup.ofAdicCompletion (𝓞 F) F z a) :=
  prod_relativeIdeleClassAut_ofAdicCompletion z w σ
    (existsUnique_finitePlaceEquiv_eq_of_coset z w σ hσ) a

end Cosets

end Langlands.ClassField.Global
