import Langlands.Representation.Jacquet.CompressionSeparationBound
import Langlands.Representation.Jacquet.SmallFixedVectorGenerator
import Langlands.Representation.Category.Subquotients
import Langlands.Representation.Classification.Cosocle
import Langlands.Representation.CompactCoefficient.SemisimplicityProof
import Langlands.Shimura.LevelHeckeAlgebraInvolution

/-! # Irreducible smooth representations separate natural endomorphisms of fixed vectors

For a compact open subgroup `K` of countable index, every maximal left ideal `I` of the
Hecke algebra `H = ℂ[G/K]^K` gives a maximal subrepresentation of the compact permutation
representation `ℂ[G/K]`: the vectors all of whose translates average into `I`. Since
an element of `H` lying in every maximal left ideal vanishes, a `K`-fixed vector of
`ℂ[G/K]` lying in every maximal subrepresentation vanishes. Quotients by maximal
subrepresentations are irreducible, so a natural endomorphism of `K`-fixed vectors that
vanishes on irreducible representations kills the identity-coset vector, hence vanishes.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open Langlands.Shimura.LevelHecke Langlands.Induction

universe uG uV

namespace Langlands.Jacquet

namespace FixedVectorSeparation

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (K : OpenSubgroup G) (hK : IsCompact (K : Set G))

/-- Averaging over `K`, as a linear map from the permutation module `ℂ[G/K]` to the
Hecke algebra of `K`. -/
def avg : (G ⧸ K.toSubgroup →₀ ℂ) →ₗ[ℂ] LevelHeckeAlgebra ℂ K.toSubgroup :=
  (LevelHeckeAlgebra.ofHeckeSpace K.toSubgroup).toLinearMap ∘ₗ
    (Compact.averageMap (permRep ℂ K.toSubgroup) (isSmooth_permutation K.toSubgroup K.isOpen)
      K hK).codRestrict (fixedVectors (permRep ℂ K.toSubgroup) K.toSubgroup)
      (Compact.averageMap_mem_fixedVectors _ _ K hK)

theorem coeffs_avg (v : G ⧸ K.toSubgroup →₀ ℂ) :
    LevelHeckeAlgebra.coeffs K (avg K hK v) =
      Compact.averageMap (permRep ℂ K.toSubgroup) (isSmooth_permutation K.toSubgroup K.isOpen)
        K hK v := rfl

/-- Averaging fixes the Hecke algebra. -/
theorem avg_coeffs (a : LevelHeckeAlgebra ℂ K.toSubgroup) :
    avg K hK (LevelHeckeAlgebra.coeffs K a) = a := by
  apply LevelHeckeAlgebra.ext_coeffs
  rw [coeffs_avg]
  exact Compact.averageMap_id _ _ K hK _
    (a : HeckeSpace ℂ K.toSubgroup K.toSubgroup).property

omit [IsTopologicalGroup G] in
theorem coeffs_one :
    LevelHeckeAlgebra.coeffs K (1 : LevelHeckeAlgebra ℂ K.toSubgroup) =
      Finsupp.single ((1 : G) : G ⧸ K.toSubgroup) 1 := rfl

omit [IsTopologicalGroup G] in
/-- The coefficients of a product, as the Frobenius map of the right factor. -/
theorem coeffs_mul_eq_frobenius (a b : LevelHeckeAlgebra ℂ K.toSubgroup) :
    LevelHeckeAlgebra.coeffs K (a * b) =
      frobenius (permRep ℂ K.toSubgroup) (b : HeckeSpace ℂ K.toSubgroup K.toSubgroup)
        (LevelHeckeAlgebra.coeffs K a) := rfl

/-- Averaging a translate of a Hecke algebra element is a left multiple of it. -/
theorem avg_translate (g : G) (i : LevelHeckeAlgebra ℂ K.toSubgroup) :
    avg K hK (permRep ℂ K.toSubgroup g (LevelHeckeAlgebra.coeffs K i)) =
      avg K hK (permRep ℂ K.toSubgroup g (LevelHeckeAlgebra.coeffs K 1)) * i := by
  apply LevelHeckeAlgebra.ext_coeffs
  set R := frobenius (permRep ℂ K.toSubgroup) (i : HeckeSpace ℂ K.toSubgroup K.toSubgroup)
  have hR : R (LevelHeckeAlgebra.coeffs K 1) = LevelHeckeAlgebra.coeffs K i :=
    frobenius_unitElement _ _
  rw [coeffs_mul_eq_frobenius, coeffs_avg, coeffs_avg, ← hR,
    ← R.isIntertwining _ _ g]
  have h := congrArg (fun f => f (permRep ℂ K.toSubgroup g (LevelHeckeAlgebra.coeffs K 1)))
    (Compact.averageMap_commute _ _ (isSmooth_permutation K.toSubgroup K.isOpen)
      (isSmooth_permutation K.toSubgroup K.isOpen) K hK R)
  exact h.symm

omit [IsTopologicalGroup G] in
/-- A subrepresentation of `ℂ[G/K]` containing `b` contains every left multiple `a * b`. -/
theorem coeffs_mul_mem (S : Subrepresentation (permRep ℂ K.toSubgroup))
    (a b : LevelHeckeAlgebra ℂ K.toSubgroup) (hb : LevelHeckeAlgebra.coeffs K b ∈ S) :
    LevelHeckeAlgebra.coeffs K (a * b) ∈ S := by
  change ((heckeAct (permRep ℂ K.toSubgroup) K.toSubgroup K.toSubgroup a b :
    HeckeSpace ℂ K.toSubgroup K.toSubgroup) : G ⧸ K.toSubgroup →₀ ℂ) ∈ S.toSubmodule
  rw [heckeAct_apply]
  exact Submodule.finsuppSum_mem _ _ _ _ fun q _ =>
    S.toSubmodule.smul_mem _ (S.apply_mem_toSubmodule _ hb)

omit [IsTopologicalGroup G] in
/-- The identity-coset vector generates the permutation representation `ℂ[G/K]`. -/
theorem unit_generates (S : Subrepresentation (permRep ℂ K.toSubgroup))
    (hS : Finsupp.single ((1 : G) : G ⧸ K.toSubgroup) (1 : ℂ) ∈ S) : S = ⊤ := by
  apply top_unique
  intro w hw
  clear hw
  induction w using Finsupp.induction_linear with
  | zero => exact S.toSubmodule.zero_mem
  | add a b ha hb => exact S.toSubmodule.add_mem ha hb
  | single q r =>
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
      have h := S.toSubmodule.smul_mem r (S.apply_mem_toSubmodule g hS)
      have he : (Finsupp.single (g : G ⧸ K.toSubgroup) r : G ⧸ K.toSubgroup →₀ ℂ) =
          r • permRep ℂ K.toSubgroup g (Finsupp.single ((1 : G) : G ⧸ K.toSubgroup) 1) := by
        rw [permutation_single, MulAction.Quotient.smul_mk, smul_eq_mul, mul_one,
          Finsupp.smul_single_one]
      change Finsupp.single (g : G ⧸ K.toSubgroup) r ∈ S.toSubmodule
      rw [he]
      exact h

/-- The subrepresentation of `ℂ[G/K]` attached to a left ideal `I` of the Hecke algebra:
the vectors all of whose translates average into `I`. -/
def idealSubrep
    (I : Submodule (LevelHeckeAlgebra ℂ K.toSubgroup) (LevelHeckeAlgebra ℂ K.toSubgroup)) :
    Subrepresentation (permRep ℂ K.toSubgroup) where
  toSubmodule :=
    { carrier := {v | ∀ g : G, avg K hK (permRep ℂ K.toSubgroup g v) ∈ I}
      add_mem' := fun {a b} ha hb g => by
        simp only [map_add]
        exact I.add_mem (ha g) (hb g)
      zero_mem' := fun g => by
        simp only [map_zero]
        exact I.zero_mem
      smul_mem' := fun c v hv g => by
        simp only [map_smul]
        exact I.smul_of_tower_mem c (hv g) }
  apply_mem_toSubmodule h v hv g := by
    rw [← Module.End.mul_apply, ← map_mul]
    exact hv (g * h)

theorem mem_idealSubrep
    (I : Submodule (LevelHeckeAlgebra ℂ K.toSubgroup) (LevelHeckeAlgebra ℂ K.toSubgroup))
    (v : G ⧸ K.toSubgroup →₀ ℂ) :
    v ∈ idealSubrep K hK I ↔ ∀ g : G, avg K hK (permRep ℂ K.toSubgroup g v) ∈ I := Iff.rfl

/-- The elements of `I` lie in the attached subrepresentation. -/
theorem coeffs_mem_idealSubrep
    (I : Submodule (LevelHeckeAlgebra ℂ K.toSubgroup) (LevelHeckeAlgebra ℂ K.toSubgroup))
    {i : LevelHeckeAlgebra ℂ K.toSubgroup} (hi : i ∈ I) :
    LevelHeckeAlgebra.coeffs K i ∈ idealSubrep K hK I := by
  intro g
  rw [avg_translate]
  exact I.smul_mem _ hi

/-- A maximal left ideal gives a maximal subrepresentation. -/
theorem isCoatom_idealSubrep
    (I : Submodule (LevelHeckeAlgebra ℂ K.toSubgroup) (LevelHeckeAlgebra ℂ K.toSubgroup))
    (hI : IsCoatom I) : IsCoatom (idealSubrep K hK I) := by
  refine ⟨fun htop => ?_, fun U hU => ?_⟩
  · have hmem : LevelHeckeAlgebra.coeffs K 1 ∈ idealSubrep K hK I := by
      rw [htop]; trivial
    have h1 := hmem 1
    rw [map_one, Module.End.one_apply, avg_coeffs] at h1
    exact hI.1 ((Ideal.eq_top_iff_one I).mpr h1)
  · obtain ⟨x, hxU, hx⟩ := SetLike.exists_of_lt hU
    rw [mem_idealSubrep] at hx
    push Not at hx
    obtain ⟨g, hg⟩ := hx
    set b := avg K hK (permRep ℂ K.toSubgroup g x) with hb_def
    have hbU : LevelHeckeAlgebra.coeffs K b ∈ U := by
      rw [hb_def, coeffs_avg]
      exact CompactCoefficientSemisimplicity.averageMap_mem _ _ K hK U
        (U.apply_mem_toSubmodule g hxU)
    have hsup : I ⊔ Submodule.span (LevelHeckeAlgebra ℂ K.toSubgroup) {b} = ⊤ := by
      refine hI.2 _ (lt_of_le_of_ne le_sup_left fun h => hg ?_)
      rw [h]
      exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self b)
    have h1 : (1 : LevelHeckeAlgebra ℂ K.toSubgroup) ∈
        I ⊔ Submodule.span (LevelHeckeAlgebra ℂ K.toSubgroup) {b} := by
      rw [hsup]; trivial
    obtain ⟨i, hi, z, hz, hiz⟩ := Submodule.mem_sup.mp h1
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
    apply unit_generates K U
    rw [← coeffs_one, ← hiz]
    change LevelHeckeAlgebra.coeffs K i + LevelHeckeAlgebra.coeffs K (c * b) ∈ U.toSubmodule
    exact U.toSubmodule.add_mem (le_of_lt hU (coeffs_mem_idealSubrep K hK I hi))
      (coeffs_mul_mem K U c b hbU)

include hK in
/-- A Hecke algebra element whose underlying vector lies in every maximal
subrepresentation of `ℂ[G/K]` vanishes. -/
theorem eq_zero_of_forall_mem_isCoatom_permRep [Countable (G ⧸ K.toSubgroup)]
    (x : LevelHeckeAlgebra ℂ K.toSubgroup)
    (hx : ∀ S : Subrepresentation (permRep ℂ K.toSubgroup), IsCoatom S →
      LevelHeckeAlgebra.coeffs K x ∈ S) : x = 0 := by
  refine LevelHeckeAlgebra.eq_zero_of_forall_mem_isCoatom hK x fun I hI => ?_
  have h := hx _ (isCoatom_idealSubrep K hK I hI) 1
  rwa [map_one, Module.End.one_apply, avg_coeffs] at h

end FixedVectorSeparation

open FixedVectorSeparation

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- For a compact open subgroup `K` of countable index, irreducible smooth representations
separate natural endomorphisms of `K`-fixed vectors. -/
theorem fixedVectorsSeparatedByIrreducibles (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    [Countable (G ⧸ K.toSubgroup)] :
    FixedVectorsSeparatedByIrreducibles.{uG, uV} K.toSubgroup := by
  intro T hnat hirr A
  let W := smallFixedVectorGenerator.{uG, uV} K
  let E := smallFixedVectorGeneratorEquiv.{uG, uV} K
  let w₀ := smallFixedVectorUnit.{uG, uV} K
  have hW : T W w₀ = 0 := by
    let x : LevelHeckeAlgebra ℂ K.toSubgroup :=
      (fixedVectorsEquiv E K.toSubgroup).symm (T W w₀)
    have hx : x = 0 := by
      refine eq_zero_of_forall_mem_isCoatom_permRep K hK x fun U hU => ?_
      let S : Subrepresentation W.representation :=
        { toSubmodule := U.toSubmodule.comap E.symm.toIntertwiningMap.toLinearMap
          apply_mem_toSubmodule := fun g v hv => by
            have h : E.symm.toIntertwiningMap (W.representation g v) =
                permRep ℂ K.toSubgroup g (E.symm.toIntertwiningMap v) :=
              E.symm.toIntertwiningMap.isIntertwining _ _ g v
            change E.symm.toIntertwiningMap (W.representation g v) ∈ U.toSubmodule
            rw [h]
            exact U.apply_mem_toSubmodule g hv }
      let Q := SmoothRep.quotient W S
      let q : (permRep ℂ K.toSubgroup).IntertwiningMap Q.representation :=
        (SmoothRep.hom (SmoothRep.mkQ W S)).comp E.toIntertwiningMap
      have hq : Function.Surjective q :=
        (SmoothRep.mkQ_surjective W S).comp E.toLinearEquiv.surjective
      have hker : q.ker = U := by
        refine Subrepresentation.toSubmodule_injective (Submodule.ext fun v => ?_)
        change (Submodule.Quotient.mk (E v) : W ⧸ S.toSubmodule) = 0 ↔ v ∈ U.toSubmodule
        rw [Submodule.Quotient.mk_eq_zero]
        change E.symm (E v) ∈ U.toSubmodule ↔ v ∈ U.toSubmodule
        rw [Representation.Equiv.symm_apply_apply]
      have hQ : Q.IsIrreducible :=
        (Classification.isIrreducible_iff_isCoatom_ker q hq).mpr (by rw [hker]; exact hU)
      have h0 := hnat W Q (SmoothRep.mkQ W S) w₀
      rw [hirr Q hQ, LinearMap.zero_apply] at h0
      have h0' : ((fixedVectorsMap (SmoothRep.hom (SmoothRep.mkQ W S)) K.toSubgroup (T W w₀) :
          fixedVectors Q.representation K.toSubgroup) : Q) = 0 := by
        rw [h0]; rfl
      change (Submodule.Quotient.mk ((T W w₀ : fixedVectors W.representation K.toSubgroup) : W) :
        W ⧸ S.toSubmodule) = 0 at h0'
      have hS : ((T W w₀ : fixedVectors W.representation K.toSubgroup) : W) ∈ S.toSubmodule :=
        (Submodule.Quotient.mk_eq_zero _).mp h0'
      exact hS
    have hx' := congrArg (fixedVectorsEquiv E K.toSubgroup) hx
    rw [map_zero] at hx'
    simpa [x] using hx'
  ext v
  let f : W ⟶ A := SmoothRep.ofHom (smallFixedVectorLift.{uG, uV, uV} K A.representation v)
  have hv : fixedVectorsMap (SmoothRep.hom f) K.toSubgroup w₀ = v :=
    Subtype.ext (smallFixedVectorLift_unit.{uG, uV, uV} K A.representation v)
  rw [LinearMap.zero_apply, ← hv, ← hnat W A f w₀, hW, map_zero]

end Langlands.Jacquet
