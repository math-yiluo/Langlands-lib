import Langlands.GroupScheme.Reductive.InnerTitsObstruction
import Langlands.GroupScheme.Reductive.InnerFormStarForward
import Langlands.GroupScheme.Reductive.TitsAlgebraTransport
import Langlands.GroupScheme.Rational.SpecialLinearNumberedWeightTransport

/-! # Transport of the inner Tits obstruction under actual comparisons -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.GaloisPinningData

open MatrixRepresentation Langlands.Brauer

variable {k K : Type u} [Field k] [Field K] [Algebra k K] [IsGalois k K]
  {G H : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  [LocallyOfFiniteType G.X.hom] [LocallyOfFiniteType H.X.hom]
  (d : GaloisPinningData k K G) (d' : GaloisPinningData k K H)
  (hG : IsSimplyConnected G) (hH : IsSimplyConnected H)
  (hi : d.IsInnerStarAction) (hi' : d'.IsInnerStarAction)

local notation "p" => d.toSplitPinning
local notation "q" => d'.toSplitPinning
local notation "F" => GroupScheme.baseChange (algebraBaseMap k K)

local instance baseChangeAffine {J : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom J.X.hom] : IsAffineHom ((F).obj J).X.hom :=
  inferInstanceAs (IsAffineHom (Limits.pullback.snd J.X.hom (algebraBaseMap k K)))

omit [IsGalois k K] in
include hi in
/-- Vertex innerness passes to any supplied pinning on a group isomorphic over `k`. -/
theorem isInnerStarAction_of_groupIso (m : G ≅ H) : d'.IsInnerStarAction := by
  let E := (F).mapIso m
  have hE (σ : K ≃ₐ[k] K) :
      IsFppfInnerEquivalent E (Descent.pullIso (galoisBaseMap k K σ)
        (galoisBaseMap_over k K σ) (galoisBaseMap_over k K σ) E) := by
    have h : Descent.pullIso (galoisBaseMap k K σ)
        (galoisBaseMap_over k K σ) (galoisBaseMap_over k K σ) E = E := by
      apply Iso.ext
      exact Descent.pullHom_map _ _ _ _ m.hom
    rw [h]
    exact IsFppfInnerEquivalent.refl E
  obtain ⟨e, hb, h⟩ := InnerFormStarForward.exists_basedEquiv_of_innerEquivalent_pullIso d d' E hE
  intro σ v
  obtain ⟨a, rfl⟩ := (e.indexEquiv.subtypeEquiv hb).surjective v
  have he := congrArg (fun f : (p).rootDatum.Equiv (q).rootDatum => f.indexEquiv a.val) (h σ)
  change e.indexEquiv ((d.starAction σ).val.indexEquiv a.val) =
    (d'.starAction σ).val.indexEquiv (e.indexEquiv a.val) at he
  rw [hi σ a] at he
  exact he.symm

/-- The two obstructions agree under every based comparison arising from the
actual ground-field group isomorphism after a rational inner correction. -/
def InnerTitsObstructionTransportStatement (m : G ≅ H) : Prop :=
  ∀ (g : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ ((F).obj H).X)
    (t : (p).torus ≅ (q).torus) (e : (p).rootDatum.Equiv (q).rootDatum),
    (p).inclusion ≫ ((F).mapIso m ≪≫ ((F).obj H).innerIso g).hom =
      CommGroupScheme.groupHom t.hom ≫ (q).inclusion →
    (∀ χ, e.weightMap χ = characterLattice.congr t χ) →
    (∀ a, a ∈ (p).base.support ↔ e.indexEquiv a ∈ (q).base.support) →
    ∀ lam, d.innerTitsObstruction hG hi lam = d'.innerTitsObstruction hH hi' (e.weightEquiv lam)

/-- Restriction of the split highest-weight representation along the original
isomorphism preserves the Tits algebra, even when an inner correction is
needed to compare the chosen split pinnings. -/
theorem innerTitsObstructionTransport (m : G ≅ H) :
    d.InnerTitsObstructionTransportStatement d' hG hH hi hi' m := by
  intro g t e ht he hb
  have hdom (x : characterLattice (p).torus) (hx : (p).IsDominantWeight x) :
      d.innerTitsObstruction hG hi x = d'.innerTitsObstruction hH hi' (e.weightEquiv x) := by
    have hx' : (q).IsDominantWeight (e.weightEquiv x) :=
      (SplitPinning.isDominantWeight_weightMap_iff e hb x).mpr hx
    obtain ⟨n, ρ, hρ⟩ := (splitHighestWeightClassification K _ (q)).1 _ hx'
    let E := (F).mapIso m
    let ρ₀ := ρ.restrict E.hom
    have hρ₀ : (p).IsHighestWeight ρ₀ x := by
      apply (p).isHighestWeight_restrict_of_innerComp E g
      exact (SplitPinning.isHighestWeight_restrict_iso_iff (E ≪≫ _) t ht e he hb ρ x).mpr hρ
    rw [d.innerTitsObstruction_eq_classOf hG hi hρ₀,
      d'.innerTitsObstruction_eq_classOf hH hi' hρ]
    apply classOf_eq_of_algEquiv
    change titsAlgebra ρ₀ ≃ₐ[k] titsAlgebra ρ
    let hfix := d'.isStarFixedWeight_of_inner hH hi' (e.weightEquiv x)
    have := d'.nonempty_of_isHighestWeight hρ
    choose P hP hPu using fun σ => d'.exists_intertwiner_galoisTwist hρ hfix σ
    exact Subalgebra.equivOfEq _ _ (titsAlgebra_restrict_iso ρ hρ.1
      (SplitPinning.IsHighestWeight.intertwiner_eq_scalar (q) hρ) P hPu hP m)
  intro lam
  obtain ⟨a, b, ha, hb', _, _, heq⟩ :=
    d.exists_dominant_sub (d.corootSpan_eq_top_of_simplyConnected hG)
      (d.isStarFixedWeight_of_inner hG hi lam)
  simp only [heq, map_sub, hdom a ha, hdom b hb']

/-- Any actual group isomorphism aligns any two supplied inner pinnings after
base change and an inner correction, and the resulting weight map preserves
the obstruction. Taking the identity compares choices for the same group. -/
theorem exists_innerTitsObstruction_transport (m : G ≅ H) :
    ∃ (g : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ ((F).obj H).X)
      (t : (p).torus ≅ (q).torus) (e : (p).rootDatum.Equiv (q).rootDatum),
      (p).inclusion ≫ ((F).mapIso m ≪≫ ((F).obj H).innerIso g).hom =
        CommGroupScheme.groupHom t.hom ≫ (q).inclusion ∧
      (∀ χ, e.weightMap χ = characterLattice.congr t χ) ∧
      (∀ a, a ∈ (p).base.support ↔ e.indexEquiv a ∈ (q).base.support) ∧
      ∀ lam, d.innerTitsObstruction hG hi lam = d'.innerTitsObstruction hH hi' (e.weightEquiv lam) := by
  obtain ⟨g, t, e, ht, he, hb⟩ := (p).exists_inner_comp_based (q) ((F).mapIso m)
  exact ⟨g, t, e, ht, he, hb, d.innerTitsObstructionTransport d' hG hH hi hi' m g t e ht he hb⟩

end Langlands.GroupScheme.GaloisPinningData
