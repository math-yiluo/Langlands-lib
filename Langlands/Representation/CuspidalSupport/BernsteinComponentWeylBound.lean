import Langlands.Representation.CuspidalSupport.BernsteinComponentWeylGroup
import Langlands.Representation.CuspidalSupport.RationalNormKernelCentralFiniteIndex
import Langlands.Representation.CuspidalSupport.RationalPointCentralCharacter
import Langlands.Representation.Plancherel.TwistStabilizerComparison

/-! # A uniform bound on the orders of the Bernstein component groups -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport.ComponentWeyl

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G H : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom]

local instance : TopologicalSpace (GroupScheme.rationalPoints H) :=
  rationalPointTopology F H.X

/-- A twist stabilizing an irreducible representation is trivial on the point-group centre. -/
theorem mem_centralTrivial_of_twist_iso (hH : GroupScheme.IsConnectedReductive H)
    (ρ : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints H)) (hρ : ρ.IsIrreducible)
    {χ : UChar H} (hχ : Nonempty (rationalUnramifiedTwist H χ ρ ≅ ρ)) :
    χ ∈ centralTrivialUnramifiedCharacters (fun ψ => (rationalNormCharacters H ψ).toMul)
      (Subgroup.center (GroupScheme.rationalPoints H)) := by
  apply (mem_centralTrivialUnramifiedCharacters _ _ χ).2
  intro z
  let ω := rationalPointCentralCharacter F H hH ρ hρ
  obtain ⟨v, hv⟩ := Whittaker.MirabolicRigidity.exists_ne_zero_of_isIrreducible ρ.representation hρ
  obtain ⟨iso⟩ := hχ
  let e : ρ.representation.Equiv (rationalUnramifiedTwist H χ ρ).representation :=
    SmoothRep.equivOfIso iso.symm
  have hev : e v ≠ 0 := by
    intro he
    apply hv
    apply e.toLinearEquiv.injective
    change e.toLinearEquiv v = 0 at he
    simpa only [map_zero] using he
  have he := Representation.IntertwiningMap.isIntertwining ρ.representation
    (rationalUnramifiedTwist H χ ρ).representation e.toIntertwiningMap
    (z : GroupScheme.rationalPoints H) v
  change e (ρ.representation z v) = (χ.val z : ℂ) • ρ.representation z (e v) at he
  have hz := ω.property z
  rw [hz v, map_smul, hz (e v), smul_smul] at he
  have hscalar : (ω.val z : ℂ) = (χ.val z : ℂ) * (ω.val z : ℂ) :=
    smul_left_injective ℂ hev he
  apply Units.ext
  exact mul_right_cancel₀ (Units.ne_zero (ω.val z)) (by simpa using hscalar.symm)

private theorem weylGroup_card_le_of_stabilizer_le
    (j : H ⟶ G) (hj : Mono j.hom.hom)
    (ρ : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints H))
    {n : ℕ} (g : Fin n → GroupScheme.rationalPoints G)
    (hg : ∀ (w : GroupScheme.rationalPoints G) (φ : H ≅ H),
      φ.hom ≫ j = j ≫ (G.innerIso w).hom →
        ∃ (t : Fin n) (m : GroupScheme.rationalPoints H), w = g t * GroupScheme.rationalPoints.map j m)
    (C : Subgroup (UChar H)) [Finite C]
    (hC : ∀ χ, Nonempty (rationalUnramifiedTwist H χ ρ ≅ ρ) → χ ∈ C) :
    Finite (weylGroup j ρ) ∧ Nat.card (weylGroup j ρ) ≤ n * Nat.card C := by
  classical
  let S (t : Fin n) : Set (Equiv.Perm (UChar H)) :=
    {σ | ∃ c : RationalLeviConjugacy j j, ∃ χ ∈ twistSet ρ c.iso,
      σ = affinePerm c.iso χ ∧ ∃ m, c.point = g t * GroupScheme.rationalPoints.map j m}
  have hparam (t : Fin n) : ∃ f : C → Equiv.Perm (UChar H), S t ⊆ Set.range f := by
    rcases (S t).eq_empty_or_nonempty with h | ⟨_, c₀, χ₀, ⟨hχ₀⟩, _, m₀, hm₀⟩
    · exact ⟨fun _ => 1, h ▸ Set.empty_subset _⟩
    · refine ⟨fun a => affinePerm c₀.iso (a.val * χ₀), ?_⟩
      rintro σ ⟨c, χ, hχ, rfl, m, hm⟩
      have hpt : c.point = c₀.point * GroupScheme.rationalPoints.map j (m₀⁻¹ * m) := by
        rw [hm, hm₀, map_mul, map_inv, mul_assoc, mul_inv_cancel_left]
      obtain ⟨hset, hperm⟩ := twistSet_affinePerm_eq_of_point_eq j ρ hj c c₀ _ hpt
      obtain ⟨e⟩ := hset ▸ hχ
      have hη := hC (χ * χ₀⁻¹)
        ((twist_iso_twist_iff χ χ₀ ρ ρ).1 ⟨e ≪≫ hχ₀.symm⟩)
      refine ⟨⟨χ * χ₀⁻¹, hη⟩, ?_⟩
      change affinePerm c₀.iso ((χ * χ₀⁻¹) * χ₀) = affinePerm c.iso χ
      rw [inv_mul_cancel_right, hperm]
  choose f hf using hparam
  let imageOfLabel (p : Fin n × C) := f p.1 p.2
  have hcover (w : weylGroup j ρ) : ∃ p, imageOfLabel p = w.val := by
    obtain ⟨c, χ, hχ, heq⟩ := w.property
    obtain ⟨t, m, hm⟩ := hg c.point c.iso c.commutes.symm
    obtain ⟨a, ha⟩ := hf t (show w.val ∈ S t from ⟨c, χ, hχ, heq, m, hm⟩)
    exact ⟨(t, a), ha⟩
  let label (w : weylGroup j ρ) := (hcover w).choose
  have hlabel (w : weylGroup j ρ) : imageOfLabel (label w) = w.val := (hcover w).choose_spec
  have hinj : Function.Injective label := by
    intro w w' h
    exact Subtype.ext ((hlabel w).symm.trans ((congrArg imageOfLabel h).trans (hlabel w')))
  refine ⟨Finite.of_injective label hinj, ?_⟩
  simpa only [Nat.card_prod, Nat.card_fin] using Nat.card_le_card_of_injective label hinj

/-- If `n` points cover the normalizer of the embedded Levi modulo its rational points,
the order of every component group is at most `n` times the order of the fixed group of
unramified characters trivial on the centre of the Levi. -/
def RationalWeylGroupCardBoundStatement (j : H ⟶ G) {n : ℕ}
    (g : Fin n → GroupScheme.rationalPoints G) : Prop :=
  GroupScheme.IsConnectedReductive H →
  Mono j.hom.hom →
  (∀ (w : GroupScheme.rationalPoints G) (φ : H ≅ H),
    φ.hom ≫ j = j ≫ (G.innerIso w).hom →
      ∃ (t : Fin n) (m : GroupScheme.rationalPoints H), w = g t * GroupScheme.rationalPoints.map j m) →
  ∀ ρ : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints H), ρ.IsIrreducible →
    Finite (weylGroup j ρ) ∧ Nat.card (weylGroup j ρ) ≤ n * Nat.card
      (centralTrivialUnramifiedCharacters (fun ψ => (rationalNormCharacters H ψ).toMul)
        (Subgroup.center (GroupScheme.rationalPoints H)))

/-- The normalizer and the central character give a bound independent of the representation. -/
theorem rationalWeylGroup_card_le (j : H ⟶ G) {n : ℕ}
    (g : Fin n → GroupScheme.rationalPoints G) :
    RationalWeylGroupCardBoundStatement.{uF, uV} j g := by
  intro hH hj hg ρ hρ
  let ν := fun ψ => (rationalNormCharacters H ψ).toMul
  let Z := Subgroup.center (GroupScheme.rationalPoints H)
  have : (commonNormKernel ν ⊔ Z).FiniteIndex :=
    rationalCommonNormKernel_sup_center_finiteIndex F H hH
  have : Finite (centralTrivialUnramifiedCharacters ν Z) :=
    finite_centralTrivialUnramifiedCharacters ν Z
  exact weylGroup_card_le_of_stabilizer_le j hj ρ g hg (centralTrivialUnramifiedCharacters ν Z)
    (fun _ hχ => mem_centralTrivial_of_twist_iso hH ρ hρ hχ)

end Langlands.CuspidalSupport.ComponentWeyl
