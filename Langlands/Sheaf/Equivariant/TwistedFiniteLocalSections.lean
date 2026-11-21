import Langlands.Sheaf.Equivariant.LocalActionSmoothPart
import Langlands.Sheaf.Equivariant.TwistedOver

/-! # Finite-cover descent of discreteness for a supplied local lift -/

namespace Langlands.Sheaf.Equivariant.TwistedOver

open CategoryTheory Opposite

universe w v u uG

variable {C : Type u} [Category.{v} C] {P : MorphismProperty C} {X : C}
variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {ρ : G →* Aut X}

/-- Conjugation identifying the target group element with the source
group element along a twisted arrow between lifts. -/
def inverseTwistConjugation {U V : TwistedOver P ρ} (f : V ⟶ U) : G →* G :=
  (MulAut.conj (Hom.twist f)⁻¹).toMonoidHom

/-- For two lifts on the twisted site, restriction equivariance also supplies
local equivariance in the other direction. The twist of the arrow determines
the conjugacy between the two acting group elements. -/
theorem isLocallyEquivariant_of_isRestrictionEquivariant
    {U V : TwistedOver P ρ} {H H' : OpenSubgroup G}
    {a : (H : Subgroup G) →* (End U)ᵐᵒᵖ}
    {b : (H' : Subgroup G) →* (End V)ᵐᵒᵖ}
    (ha : IsLift a) (hb : IsLift b) {f : V ⟶ U}
    (hf : IsRestrictionEquivariant a b f) : IsLocallyEquivariant a b f := by
  intro K _
  obtain ⟨N, hNH', hN⟩ := hf H le_rfl
  let c := inverseTwistConjugation f
  have hc : Continuous c := IsTopologicalGroup.continuous_conj _
  refine ⟨H ⊓ (N ⊓ K).comap c hc, inf_le_left, fun h hh => ?_⟩
  have hch : c h ∈ N ⊓ K := (OpenSubgroup.mem_inf.mp hh).2
  let k : (H' : Subgroup G) := ⟨c h, hNH' (OpenSubgroup.mem_inf.mp hch).1⟩
  obtain ⟨j, -, he⟩ := hN k (OpenSubgroup.mem_inf.mp hch).1
  have ht := congrArg Hom.twist he
  rw [comp_twist, comp_twist, ha j, hb k] at ht
  have hk : (k : G) = (Hom.twist f)⁻¹ * h * Hom.twist f := by
    simp [k, c, inverseTwistConjugation]
  have hj : h = j := by simpa [hk, mul_assoc] using ht
  subst j
  exact ⟨k, (OpenSubgroup.mem_inf.mp hch).2, he⟩

/-- If the discrete sieve of a section contains a finite covering family,
then the section is discrete for any supplied admissible lift at its object. -/
theorem isDiscreteSection_of_finite_discreteSieve_cover {R : Type w} [CommRing R]
    {J : GrothendieckTopology (TwistedOver P ρ)} {L : LocalActionSystem (TwistedOver P ρ) G}
    [L.HasAdmissibleRefinements J] (hL : L.IsLiftSystem)
    {F : (TwistedOver P ρ)ᵒᵖ ⥤ ModuleCat.{w} R} (hF : Presheaf.IsSheaf J F)
    {U : TwistedOver P ρ} {H : OpenSubgroup G} {a : (H : Subgroup G) →* (End U)ᵐᵒᵖ}
    (ha : L.IsAdmissible U H a) (s : F.obj (op U))
    {n : ℕ} {V : Fin n → TwistedOver P ρ} {f : ∀ i, V i ⟶ U}
    (hf : ∀ i, L.discreteSieve F s (f i)) (hcov : Sieve.ofArrows V f ∈ J U) :
    IsDiscreteSection F a s := by
  choose W k p H' b hb hdisc hfac using hf
  have hle : Sieve.ofArrows V f ≤ Sieve.ofArrows W p := by
    rintro Z _ ⟨Y, l, _, ⟨i⟩, rfl⟩
    refine ⟨W i, l ≫ k i, p i, ⟨i⟩, ?_⟩
    rw [Category.assoc, hfac i]
  have hcov' := J.superset_covering hle hcov
  refine IsDiscreteSection.of_finite_family (fun i => ?_) hdisc ?_
  · exact isLocallyEquivariant_of_isRestrictionEquivariant (hL _ _ _ ha) (hL _ _ _ (hb i))
      (LocalActionSystem.HasAdmissibleRefinements.isRestrictionEquivariant
        (J := J) ha (hb i) (p i))
  · intro t t' htt'
    refine isSeparated_of_isSheaf hF hcov' ?_
    rintro Z _ ⟨Y, l, _, ⟨i⟩, rfl⟩
    rw [map_op_comp_apply, map_op_comp_apply, htt' i]

end Langlands.Sheaf.Equivariant.TwistedOver
