import Langlands.BruhatTits.Unipotent.CocharacterContraction
import Langlands.GroupScheme.Dynamic.LieProof
import Langlands.Representation.Exponents.PresentationConeContractionProof

/-! # Bounded conjugation of dynamic parabolic points

For a cocharacter `χ` of an affine group over a topological field, the
coordinates of `χ(t) x χ(t)⁻¹` are polynomials in `t` for every rational point
`x` of the dynamic parabolic `P_G(χ)`. Consequently, for a compact set `S` of
parameters, conjugation by `χ(t)` with `t ∈ S` is equicontinuous at the identity
on the rational points of `P_G(χ)`.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry Topology Filter
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.GroupScheme.AffineLine Langlands.GroupScheme.Dynamic
open Langlands.GroupScheme.Dynamic.AffineChart

namespace Langlands.BruhatTits.DynamicUnipotentContainment

section Points

variable {F : Type u} [Field F]
  {G : Langlands.GroupScheme (Spec (CommRingCat.of F))}
  (χ : (Langlands.GroupScheme.Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)

/-- The rational points of `P_G(χ)`. -/
abbrev parabolicPoints : Subgroup (RationalPoint F G.X) :=
  (parabolic χ).carrier (Over.mk (𝟙 (Spec (CommRingCat.of F))))

variable [IsAffine G.X.left]

theorem mem_parabolicPoints_iff (x : RationalPoint F G.X) :
    x ∈ parabolicPoints χ ↔
      ∀ b, ∀ n < 0, pointRing x ((coaction χ b).coeff n) = 0 :=
  Langlands.GroupScheme.DynamicLie.chart_mem_parabolic_iff χ x

/-- On parabolic points the coordinates of `χ(t) x χ(t)⁻¹` are the polynomial
coordinates `conjCoord`. -/
theorem pointRing_conj_apply_of_mem_parabolic (t : Fˣ) {x : RationalPoint F G.X}
    (hx : x ∈ parabolicPoints χ) (b : Γ(G.X.left, ⊤)) :
    pointRing (cocharPoint χ t * x * (cocharPoint χ t)⁻¹) b = conjCoord χ b t x := by
  have hneg := (mem_parabolicPoints_iff χ x).1 hx
  have hq : ∀ n < 0, (laurentCoeffMap (pointRing x) (coaction χ b)).coeff n = 0 :=
    fun n hn => by rw [GroupScheme.Corepresented.coeff_laurentCoeffMap]; exact hneg b n hn
  have hdeg : (LaurentPolynomial.trunc (laurentCoeffMap (pointRing x) (coaction χ b))).natDegree <
      degBound χ b + 1 := by
    refine Nat.lt_succ_of_le (Polynomial.natDegree_le_iff_coeff_eq_zero.2 fun N hN => ?_)
    rw [coeff_trunc, GroupScheme.Corepresented.coeff_laurentCoeffMap,
      coeff_eq_zero_of_degBound_lt χ b hN, map_zero]
  rw [pointRing_conj]
  change LaurentPolynomial.eval₂ (RingHom.id F) t
    (laurentCoeffMap (pointRing x) (coaction χ b)) = _
  rw [← toLaurent_trunc hq, LaurentPolynomial.eval₂_toLaurent,
    Polynomial.eval₂_id, Polynomial.eval_eq_sum_range' hdeg]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coeff_trunc, GroupScheme.Corepresented.coeff_laurentCoeffMap]

end Points

section Topology

variable {F : Type u} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  {G : Langlands.GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
  (χ : (Langlands.GroupScheme.Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)

local instance : TopologicalSpace (RationalPoint F G.X) := rationalPointTopology F G.X

omit [TopologicalSpace F] [IsTopologicalRing F] in
/-- The polynomial coordinates at the identity are those of the identity. -/
theorem conjCoord_one (b : Γ(G.X.left, ⊤)) (s : F) :
    conjCoord χ b s 1 = pointRing (1 : RationalPoint F G.X) b := by
  have h := pointRing_contraction χ (s, ⟨1, (unipotentPoints χ).one_mem⟩) b
  have h1 : contraction χ (s, ⟨1, (unipotentPoints χ).one_mem⟩) = 1 := by
    by_cases hs : s = 0
    · subst hs
      exact contraction_zero χ _
    · rw [contraction_of_ne_zero χ hs]
      simp
  rw [h1] at h
  exact h.symm

/-- **Equicontinuity on parabolic points.** For a compact set `S` of parameters,
every identity neighborhood `W` contains the conjugates `χ(t) y χ(t)⁻¹`, `t ∈ S`,
of all parabolic points `y` in a smaller identity neighborhood. -/
theorem exists_nhds_forall_conj_mem_of_parabolic (S : Set F) (hS : IsCompact S)
    (W : Set (RationalPoint F G.X)) (hW : W ∈ 𝓝 (1 : RationalPoint F G.X)) :
    ∃ W' ∈ 𝓝 (1 : RationalPoint F G.X), ∀ t : Fˣ, (t : F) ∈ S →
      ∀ y ∈ parabolicPoints χ, y ∈ W' →
        cocharPoint χ t * y * (cocharPoint χ t)⁻¹ ∈ W := by
  let c : RationalPoint F G.X → Γ(G.X.left, ⊤) → F := fun x b => pointRing x b
  have hind : IsInducing c :=
    Langlands.Aubert.General.RepresentedParabolic.ConeContraction.isInducing_pointRing (G := G)
  have hW' : W ∈ Filter.comap c (𝓝 (c 1)) := by
    rw [← hind.nhds_eq_comap]
    exact hW
  obtain ⟨V, hV, hVW⟩ := Filter.mem_comap.mp hW'
  have hV' : V ∈ Filter.pi fun b : Γ(G.X.left, ⊤) => 𝓝 (c 1 b) := by
    rw [← nhds_pi]
    exact hV
  obtain ⟨I, hI, tset, htset, hsub⟩ := Filter.mem_pi.mp hV'
  have hb : ∀ b ∈ I, ∀ᶠ y in 𝓝 (1 : RationalPoint F G.X), ∀ s ∈ S,
      conjCoord χ b s y ∈ tset b := by
    intro b _
    apply hS.eventually_forall_of_forall_eventually
    intro s _
    have hswap : Continuous fun z : RationalPoint F G.X × F => (z.2, z.1) :=
      continuous_snd.prodMk continuous_fst
    have hc := (continuous_conjCoord χ b).comp hswap
    have hmem : tset b ∈ 𝓝 (conjCoord χ b s (1 : RationalPoint F G.X)) := by
      rw [conjCoord_one χ b s]
      exact htset b
    exact (hc.continuousAt (x := ((1 : RationalPoint F G.X), s))).eventually_mem hmem
  have hall := (Filter.eventually_all_finite hI).mpr hb
  refine ⟨_, hall, fun t ht y hy hyW => hVW ?_⟩
  apply hsub
  intro b hbI
  change pointRing (cocharPoint χ t * y * (cocharPoint χ t)⁻¹) b ∈ tset b
  rw [pointRing_conj_apply_of_mem_parabolic χ t hy b]
  exact hyW b hbI t ht

end Topology

end Langlands.BruhatTits.DynamicUnipotentContainment
