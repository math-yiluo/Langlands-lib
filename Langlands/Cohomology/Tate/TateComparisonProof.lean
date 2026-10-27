import Langlands.Cohomology.Tate.PGroupTateVanishingProof
import Langlands.Cohomology.Tate.SylowTateVanishingProof
import Langlands.Cohomology.Tate.SubgroupShifts

/-!
# The comparison theorem for actual Tate cohomology

A morphism `f : D ⟶ E` is compared with the mapping-cone embedding
`D ⟶ E ⊞ coinduced D`. On every Sylow subgroup the cokernel has two consecutive vanishing
Tate groups, hence vanishes in every degree; Sylow detection then makes it acyclic for the
whole group, and the long exact sequence gives bijectivity.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Tate

namespace Comparison

set_option backward.isDefEq.respectTransparency false

variable {R G : Type u} [CommRing R] [Group G] [Fintype G]

/-- Actual Tate cohomology in a fixed degree is an additive functor. -/
abbrev tateCohomologyFunctorAdditive (n : ℤ) :
    (tateCohomologyFunctor (R := R) (G := G) n).Additive :=
  inferInstanceAs (tateComplexFunctor R G ⋙ HomologicalComplex.homologyFunctor _ _ n).Additive

attribute [local instance] tateCohomologyFunctorAdditive

/-- Exactness of actual Tate cohomology at the middle term of a short exact sequence. -/
lemma tate_exact₂ {S : ShortComplex (Rep.{u} R G)} (hS : S.ShortExact) (n : ℤ) :
    (ShortComplex.mk ((tateCohomologyFunctor n).map S.f) ((tateCohomologyFunctor n).map S.g)
      (by rw [← Functor.map_comp, S.zero, Functor.map_zero])).Exact :=
  (TateCohomology.map_tateComplexFunctor_shortExact hS).homology_exact₂ n

/-- The cokernel vanishes in degree `m` when the first map is surjective in degree `m` and
injective in degree `m + 1`. -/
lemma cokernel_isZero {S : ShortComplex (Rep.{u} R G)} (hS : S.ShortExact) (m : ℤ)
    (hepi : Epi ((tateCohomologyFunctor m).map S.f))
    (hmono : Mono ((tateCohomologyFunctor (m + 1)).map S.f)) :
    IsZero (tateCohomology S.X₃ m) := by
  have hg : (tateCohomologyFunctor m).map S.g = 0 := by
    rw [← cancel_epi ((tateCohomologyFunctor m).map S.f), ← Functor.map_comp, S.zero,
      Functor.map_zero, comp_zero]
  have hδ : TateCohomology.δ hS m = 0 := by
    rw [← cancel_mono ((tateCohomologyFunctor (m + 1)).map S.f), TateCohomology.δ_map,
      zero_comp]
  exact (TateCohomology.exact₃ hS m).isZero_X₂ hg hδ

/-- If the cokernel is acyclic, the first map is bijective on actual Tate cohomology. -/
lemma bijective_of_isZero {S : ShortComplex (Rep.{u} R G)} (hS : S.ShortExact)
    (h : ∀ n : ℤ, IsZero (tateCohomology S.X₃ n)) (n : ℤ) :
    Function.Bijective ((tateCohomologyFunctor n).map S.f) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨k, rfl⟩ : ∃ k : ℤ, n = k + 1 := ⟨n - 1, by ring⟩
    rw [← ModuleCat.mono_iff_injective]
    exact (TateCohomology.exact₁ hS k).mono_g ((h k).eq_of_src _ _)
  · rw [← ModuleCat.epi_iff_surjective]
    exact (tate_exact₂ hS n).epi_f ((h n).eq_of_tgt _ _)

/-- A projection with a section whose complementary idempotent factors through an acyclic
representation is invertible on actual Tate cohomology. -/
lemma isIso_map_of_split {X E I : Rep.{u} R G} (pr : X ⟶ E) (i : E ⟶ X) (s : X ⟶ I)
    (j : I ⟶ X) (hip : i ≫ pr = 𝟙 E) (hsum : pr ≫ i + s ≫ j = 𝟙 X) (n : ℤ)
    (hI : IsZero (tateCohomology I n)) : IsIso ((tateCohomologyFunctor n).map pr) := by
  refine ⟨(tateCohomologyFunctor n).map i, ?_, ?_⟩
  · have hs : (tateCohomologyFunctor n).map s = 0 := hI.eq_of_tgt _ _
    rw [← Functor.map_comp, eq_sub_of_add_eq hsum, Functor.map_sub, Functor.map_comp, hs,
      zero_comp, sub_zero, CategoryTheory.Functor.map_id]
  · rw [← Functor.map_comp, hip, CategoryTheory.Functor.map_id]

/-- Composing with a map that is invertible on Tate cohomology does not change surjectivity or
injectivity. -/
lemma surjective_injective_iff {D X E : Rep.{u} R G} (θ : D ⟶ X) (pr : X ⟶ E) (n : ℤ)
    [IsIso ((tateCohomologyFunctor n).map pr)] :
    (Function.Surjective ((tateCohomologyFunctor n).map (θ ≫ pr)) ↔
        Function.Surjective ((tateCohomologyFunctor n).map θ)) ∧
      (Function.Injective ((tateCohomologyFunctor n).map (θ ≫ pr)) ↔
        Function.Injective ((tateCohomologyFunctor n).map θ)) := by
  rw [← ModuleCat.epi_iff_surjective, ← ModuleCat.epi_iff_surjective,
    ← ModuleCat.mono_iff_injective, ← ModuleCat.mono_iff_injective, Functor.map_comp]
  exact ⟨epi_comp_iff_of_isIso _ _, mono_comp_iff_of_mono _ _⟩

end Comparison

open Comparison in
/-- The comparison theorem follows from Sylow detection and from the `p`-group vanishing
theorem. -/
theorem tateComparison_of (hP : PGroupTateVanishing.{u}) (hSyl : SylowTateVanishing.{u}) :
    TateComparison.{u} := by
  intro G _ _ D E f h n
  let I := coinduced D
  let θ : D ⟶ E ⊞ I := biprod.lift f (coinducedEmbedding D)
  have : Mono θ := by
    have : Mono (θ ≫ biprod.snd) := by
      rw [biprod.lift_snd]
      infer_instance
    exact mono_of_mono θ biprod.snd
  let S := ShortComplex.mk θ (cokernel.π θ) (cokernel.condition θ)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel θ }
  have hθ : θ ≫ biprod.fst = f := biprod.lift_fst _ _
  have hsum : (biprod.fst : E ⊞ I ⟶ E) ≫ biprod.inl + biprod.snd ≫ biprod.inr = 𝟙 _ :=
    biprod.total
  have hC : ∀ k : ℤ, IsZero (tateCohomology (cokernel θ) k) := by
    intro k
    refine hSyl IntegralScalar.{u} G (cokernel θ) k fun p hp P _ => ?_
    let F := Rep.resFunctor (k := IntegralScalar.{u}) P.1.subtype
    have hSP : (S.map F).ShortExact := hS.map_of_exact F
    have hθP : F.map θ ≫ F.map biprod.fst = F.map f := by rw [← Functor.map_comp, hθ]
    have hiso : ∀ m : ℤ,
        IsIso ((tateCohomologyFunctor m).map (F.map (biprod.fst : E ⊞ I ⟶ E))) :=
      fun m => isIso_map_of_split (F.map biprod.fst) (F.map biprod.inl) (F.map biprod.snd)
        (F.map biprod.inr)
        (by rw [← Functor.map_comp, biprod.inl_fst, CategoryTheory.Functor.map_id])
        (by rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_add, hsum,
          CategoryTheory.Functor.map_id]) m (restrictedCoinduced_tate_isZero P.1 D m)
    have hiff : ∀ m : ℤ,
        (Function.Surjective ((tateCohomologyFunctor m).map (F.map f)) ↔
          Function.Surjective ((tateCohomologyFunctor m).map (S.map F).f)) ∧
        (Function.Injective ((tateCohomologyFunctor m).map (F.map f)) ↔
          Function.Injective ((tateCohomologyFunctor m).map (S.map F).f)) := by
      intro m
      have := hiso m
      rw [← hθP]
      exact surjective_injective_iff (F.map θ) (F.map biprod.fst) m
    obtain ⟨m, hm₀, hm₁, hm₂⟩ := h p hp P
    have h₀ : IsZero (tateCohomology (Rep.res P.1.subtype (cokernel θ)) m) :=
      cokernel_isZero hSP m
        ((ModuleCat.epi_iff_surjective _).mpr ((hiff m).1.mp hm₀))
        ((ModuleCat.mono_iff_injective _).mpr ((hiff (m + 1)).2.mp hm₁.1))
    have h₁ : IsZero (tateCohomology (Rep.res P.1.subtype (cokernel θ)) (m + 1)) := by
      refine cokernel_isZero hSP (m + 1)
        ((ModuleCat.epi_iff_surjective _).mpr ((hiff (m + 1)).1.mp hm₁.2)) ?_
      rw [ModuleCat.mono_iff_injective, ← (hiff (m + 1 + 1)).2]
      rw [show m + 1 + 1 = m + 2 by ring]
      exact hm₂
    exact hP p hp P.1 P.isPGroup' (Rep.res P.1.subtype (cokernel θ)) m h₀ h₁ k
  have hiso : IsIso ((tateCohomologyFunctor n).map (biprod.fst : E ⊞ I ⟶ E)) :=
    isIso_map_of_split biprod.fst biprod.inl biprod.snd biprod.inr biprod.inl_fst hsum n
      (coinduced_tate_isZero D n)
  have hbij := bijective_of_isZero hS hC n
  have hiff := surjective_injective_iff θ (biprod.fst : E ⊞ I ⟶ E) n
  rw [hθ] at hiff
  exact ⟨hiff.2.mpr hbij.1, hiff.1.mpr hbij.2⟩

/-- Serre, *Local Fields*, IX §7, Theorem 12 (the case `B = ℤ`, for the whole group): a
morphism that is surjective, bijective and injective in three consecutive degrees on every
Sylow subgroup is bijective on actual Tate cohomology in every degree. -/
theorem tateComparison : TateComparison.{u} :=
  tateComparison_of pGroupTateVanishing sylowTateVanishing

end Langlands.Tate
