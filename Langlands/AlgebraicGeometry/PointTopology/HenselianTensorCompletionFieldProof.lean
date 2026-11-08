import Langlands.AlgebraicGeometry.PointTopology.HenselianValuedFieldPropertiesStatement
import Langlands.AlgebraicGeometry.PointTopology.HenselianEtalePointProof
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.RingTheory.AdjoinRoot

/-!
# For henselian `K`, the completion tensored with a finite separable extension is a field

If `K` is separably algebraically closed in a field `F`, a separable irreducible polynomial
over `K` stays irreducible over `F`: the coefficients of a monic factor over `F` are symmetric
functions of roots, which are separable over `K`. A henselian valued field is separably closed
in its completion `K̂` (the published `separableClosure_completion_eq_bot`). Hence, for a
primitive element of a finite separable extension `L`, `K̂ ⊗_K L` is `K̂[X]/(f)` with `f`
irreducible, a field.
-/

noncomputable section

universe u

open Polynomial
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.PointTopology

namespace HenselianTensorCompletion

variable {K F : Type u} [Field K] [Field F] [Algebra K F]

/-- A monic factor over `F` of a separable polynomial over `K` has its coefficients in `K`,
when `K` is separably closed in `F`. -/
theorem mem_lifts_of_dvd (hsep : separableClosure K F = ⊥) {f : K[X]} (hs : f.Separable)
    {g : F[X]} (hg : g.Monic) (hdvd : g ∣ f.map (algebraMap K F)) :
    g ∈ lifts (algebraMap K F) := by
  let Ω := AlgebraicClosure F
  let ι : F →ₐ[K] Ω := IsScalarTower.toAlgHom K F Ω
  have hsplit : (g.map (algebraMap F Ω)).Splits := IsAlgClosed.splits _
  have hprod := hsplit.eq_prod_roots_of_monic (hg.map _)
  -- every root of `g` in `Ω` is separable over `K`
  have hroot : ∀ β ∈ (g.map (algebraMap F Ω)).roots, β ∈ separableClosure K Ω := by
    intro β hβ
    have hg0 : g.map (algebraMap F Ω) ≠ 0 := (hg.map _).ne_zero
    have hβ' : (g.map (algebraMap F Ω)).IsRoot β := (mem_roots hg0).mp hβ
    have hfβ : aeval β f = 0 := by
      obtain ⟨q, hq⟩ := hdvd
      have : (f.map (algebraMap K F)).map (algebraMap F Ω) =
          g.map (algebraMap F Ω) * q.map (algebraMap F Ω) := by rw [hq, Polynomial.map_mul]
      rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq] at this
      rw [aeval_def, eval₂_eq_eval_map, this, eval_mul, hβ'.eq_zero, zero_mul]
    rw [mem_separableClosure_iff]
    exact hs.of_dvd (minpoly.dvd K β hfβ)
  -- hence `g` maps into polynomials over the separable closure of `K` in `Ω`
  have hlift : g.map (algebraMap F Ω) ∈ liftsRing (algebraMap (separableClosure K Ω) Ω) := by
    rw [hprod]
    refine Subring.multiset_prod_mem _ _ fun p hp => ?_
    obtain ⟨β, hβ, rfl⟩ := Multiset.mem_map.mp hp
    refine Subring.sub_mem _ ?_ ?_
    · rw [← lifts_iff_liftsRing]
      exact X_mem_lifts _
    · rw [← lifts_iff_liftsRing]
      exact C'_mem_lifts ⟨⟨β, hroot β hβ⟩, rfl⟩
  rw [← lifts_iff_liftsRing, lifts_iff_coeff_lifts] at hlift
  rw [lifts_iff_coeff_lifts]
  intro n
  obtain ⟨c, hc⟩ := hlift n
  have hmem : ι (g.coeff n) ∈ separableClosure K Ω := by
    rw [coeff_map] at hc
    change algebraMap F Ω (g.coeff n) ∈ separableClosure K Ω
    rw [← hc]
    exact c.2
  have hmem' : g.coeff n ∈ separableClosure K F := (map_mem_separableClosure_iff ι).mp hmem
  rw [hsep] at hmem'
  obtain ⟨a, ha⟩ := IntermediateField.mem_bot.mp hmem'
  exact ⟨a, ha⟩

/-- **Irreducibility is preserved** when `K` is separably closed in `F`. -/
theorem irreducible_map (hsep : separableClosure K F = ⊥) {f : K[X]} (hm : f.Monic)
    (hf : Irreducible f) (hs : f.Separable) : Irreducible (f.map (algebraMap K F)) := by
  have hm' : (f.map (algebraMap K F)).Monic := hm.map _
  rw [hm'.irreducible_iff_natDegree]
  refine ⟨fun h1 => ?_, fun g h hg hh hgh => ?_⟩
  · have := congrArg natDegree h1
    rw [natDegree_map, natDegree_one] at this
    exact hf.natDegree_pos.ne' this
  · obtain ⟨g₀, hg₀, hgdeg, hgm⟩ :=
      lifts_and_natDegree_eq_and_monic (mem_lifts_of_dvd hsep hs hg ⟨h, hgh.symm⟩) hg
    obtain ⟨h₀, hh₀, hhdeg, hhm⟩ :=
      lifts_and_natDegree_eq_and_monic
        (mem_lifts_of_dvd hsep hs hh ⟨g, by rw [← hgh, mul_comm]⟩) hh
    have hfac : g₀ * h₀ = f := by
      apply Polynomial.map_injective (algebraMap K F) (algebraMap K F).injective
      rw [Polynomial.map_mul, hg₀, hh₀, hgh]
    rcases hf.isUnit_or_isUnit hfac.symm with hu | hu
    · left
      rw [← hgdeg]
      exact natDegree_eq_zero_of_isUnit hu
    · right
      rw [← hhdeg]
      exact natDegree_eq_zero_of_isUnit hu

section Tensor

variable {L : Type u} [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]

/-- When `K` is separably closed in `F`, `F ⊗_K L` is a field for every finite separable `L`. -/
theorem isField_tensor (hsep : separableClosure K F = ⊥) : IsField (F ⊗[K] L) := by
  let pb := Field.powerBasisOfFiniteOfSeparable K L
  have hint : IsIntegral K pb.gen := pb.isIntegral_gen
  have hm : (minpoly K pb.gen).Monic := minpoly.monic hint
  have hirr : Irreducible (minpoly K pb.gen) := minpoly.irreducible hint
  have hs : (minpoly K pb.gen).Separable := Algebra.IsSeparable.isSeparable K pb.gen
  have hirr' := irreducible_map hsep hm hirr hs
  have : Fact (Irreducible ((minpoly K pb.gen).map (algebraMap K F))) := ⟨hirr'⟩
  have hroot : aeval (AdjoinRoot.root ((minpoly K pb.gen).map (algebraMap K F)))
      (minpoly K pb.gen) = 0 := by
    rw [← Polynomial.aeval_map_algebraMap F, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  let φL : L →ₐ[K] AdjoinRoot ((minpoly K pb.gen).map (algebraMap K F)) := pb.lift _ hroot
  let Φ : F ⊗[K] L →ₐ[F] AdjoinRoot ((minpoly K pb.gen).map (algebraMap K F)) :=
    Algebra.TensorProduct.lift (Algebra.ofId F _) φL (fun _ _ => Commute.all _ _)
  have hsurj : Function.Surjective Φ := by
    have hrange : Φ.range = ⊤ := by
      rw [eq_top_iff, ← AdjoinRoot.adjoinRoot_eq_top, Algebra.adjoin_le_iff,
        Set.singleton_subset_iff]
      refine ⟨1 ⊗ₜ pb.gen, ?_⟩
      simp [Φ, φL, PowerBasis.lift_gen]
    intro x
    have hx : x ∈ Φ.range := hrange ▸ Algebra.mem_top
    exact hx
  have := (AdjoinRoot.powerBasis hirr'.ne_zero).finite
  have hdim : Module.finrank F (F ⊗[K] L) =
      Module.finrank F (AdjoinRoot ((minpoly K pb.gen).map (algebraMap K F))) := by
    rw [Module.finrank_baseChange, (AdjoinRoot.powerBasis hirr'.ne_zero).finrank,
      AdjoinRoot.powerBasis_dim, natDegree_map, pb.finrank, pb.natDegree_minpoly]
  have hinj : Function.Injective Φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim (f := Φ.toLinearMap)).mpr hsurj
  exact MulEquiv.isField (Field.toIsField _) (AlgEquiv.ofBijective Φ ⟨hinj, hsurj⟩).toMulEquiv

end Tensor

end HenselianTensorCompletion

/-- **For henselian `K`, the completion tensored with a finite separable extension is a field
of the same degree** (Conrad, printed p.14). -/
theorem henselianTensorCompletionField : HenselianTensorCompletionFieldStatement.{u} := by
  intro K _ hK L _ _ _ _
  exact ⟨HenselianTensorCompletion.isField_tensor (separableClosure_completion_eq_bot K hK),
    Module.finrank_baseChange⟩

end Langlands.AlgebraicGeometry.PointTopology
