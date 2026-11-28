import Langlands.GroupScheme.Rational.GeometricBorelOppositeCocharacter
import Langlands.GroupScheme.Rational.MaximalSplitTorusCentralizer
import Langlands.GroupScheme.Rational.RankOneParabolicConjugacy
import Langlands.GroupScheme.Rational.RationalCocharacterRealization

/-! # Cocharacter conjugacy with respect to a field-defined Borel pair -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {G B : GroupScheme (Spec (CommRingCat.of k))}
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {b : B ⟶ G} {i : T.toGrp ⟶ G}

set_option backward.isDefEq.respectTransparency false in
private theorem eq_of_innerIso_comp_eq_of_mem_parabolic
    [IsSeparated G.X.hom] (ν₁ ν₂ : cocharacterLattice T)
    (g : GroupScheme.rationalPoints G)
    (hg : g ∈ (Dynamic.parabolic (CommGroupScheme.groupHom ν₂ ≫ i)).rationalPoints)
    (h : (CommGroupScheme.groupHom ν₁ ≫ i) ≫ (G.innerIso g).hom =
      CommGroupScheme.groupHom ν₂ ≫ i) :
    CommGroupScheme.groupHom ν₁ ≫ i = CommGroupScheme.groupHom ν₂ ≫ i := by
  let χ := CommGroupScheme.groupHom ν₂ ≫ i
  apply hom_ext_points
  intro V t
  let x := t ≫ (CommGroupScheme.groupHom ν₁ ≫ i).hom.hom
  let y := t ≫ χ.hom.hom
  let a : V ⟶ Over.mk (𝟙 (Spec (CommRingCat.of k))) := Over.homMk V.hom
  have hx : x ∈ (Dynamic.centralizer χ).carrier V := by
    apply range_le_centralizer_groupHom_comp i ν₂ V
    exact SubgroupFunctor.mem_range.mpr ⟨t ≫ (CommGroupScheme.groupHom ν₁).hom.hom,
      by simp only [x, Grp.comp_hom_hom, Category.assoc]⟩
  have hy : y ∈ (Dynamic.centralizer χ).carrier V := by
    apply range_le_centralizer_groupHom_comp i ν₂ V
    exact SubgroupFunctor.mem_range.mpr ⟨t ≫ (CommGroupScheme.groupHom ν₂).hom.hom,
      by simp only [y, χ, Grp.comp_hom_hom, Category.assoc]⟩
  let q : (Dynamic.parabolic χ).carrier V :=
    ⟨a ≫ g, (Dynamic.parabolic χ).comp_mem a hg⟩
  let intoP := Subgroup.inclusion (Dynamic.centralizer_le_parabolic χ V)
  have hc : q * intoP ⟨x, hx⟩ * q⁻¹ = intoP ⟨y, hy⟩ := by
    apply Subtype.ext
    change (a ≫ g) * x * (a ≫ g)⁻¹ = y
    rw [comp_eq_constantPoint a g]
    have ht := congrArg (fun f => t ≫ f.hom.hom) h
    rw [Grp.comp_hom_hom, ← Category.assoc, comp_innerIso_hom] at ht
    exact ht
  let π := Dynamic.limitHom χ V
  have hxy : π q * (⟨x, hx⟩ : (Dynamic.centralizer χ).carrier V) * (π q)⁻¹ = ⟨y, hy⟩ := by
    have hp := congrArg π hc
    simpa only [π, intoP, map_mul, map_inv, Dynamic.limitHom_inclusion] using hp
  have hcomm := (mem_torusCentralizer χ).mp
    (by rw [torusCentralizer_gm_eq_dynamicCentralizer]; exact (π q).2) V (𝟙 V) t
  rw [Category.id_comp] at hcomm
  change Commute (π q : V ⟶ G.X) y at hcomm
  have hxy' := congrArg Subtype.val hxy
  change (π q : V ⟶ G.X) * x * (π q : V ⟶ G.X)⁻¹ = y at hxy'
  change x = y
  calc
    x = (π q : V ⟶ G.X)⁻¹ * y * (π q : V ⟶ G.X) := by rw [← hxy']; group
    _ = y := by
      rw [hcomm.inv_left.eq]
      group

/-- A cocharacter class has a representative in a prescribed maximal torus
in a field-defined Borel whose dynamic parabolic contains that Borel. Such
a representative is unique among the cocharacters of the prescribed torus. -/
def BorelCocharacterConjugacyStatement : Prop :=
  ∀ (k : Type u) [Field k] {G B : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {b : B ⟶ G} {i : T.toGrp ⟶ G},
    IsConnectedReductive G → IsGeometricBorelSubgroup b → IsMaximalTorus i →
    ∀ f : T.toGrp ⟶ B, f ≫ b = i →
    (∀ χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G,
      ∃ (g : GroupScheme.rationalPoints G) (ζ : cocharacterLattice T),
        χ ≫ (G.innerIso g).hom = CommGroupScheme.groupHom ζ ≫ i ∧
        SubgroupFunctor.range b ≤ Dynamic.parabolic (CommGroupScheme.groupHom ζ ≫ i)) ∧
    ∀ (ν₁ ν₂ : cocharacterLattice T) (g : GroupScheme.rationalPoints G),
      SubgroupFunctor.range b ≤ Dynamic.parabolic (CommGroupScheme.groupHom ν₁ ≫ i) →
      SubgroupFunctor.range b ≤ Dynamic.parabolic (CommGroupScheme.groupHom ν₂ ≫ i) →
      (CommGroupScheme.groupHom ν₁ ≫ i) ≫ (G.innerIso g).hom =
        CommGroupScheme.groupHom ν₂ ≫ i → ν₁ = ν₂

set_option backward.isDefEq.respectTransparency false in
/-- Apply the rational chamber move in the maximal split subtorus, and compare
two such representatives by the parabolic limit map. -/
theorem borelCocharacterConjugacy : BorelCocharacterConjugacyStatement.{u} := by
  intro k _ G B T b i hG hb hi f hf
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth G.X.hom := hG.smooth
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨ν, hν, hcent, _⟩ := hb.exists_oppositeDynamicBorel hG hi f hf
  let χ₀ := CommGroupScheme.groupHom ν ≫ i
  obtain ⟨A, a, eta, ha, heta⟩ := cocharacterMaximalSplitTorus k G χ₀
  have hle : SubgroupFunctor.range a ≤ SubgroupFunctor.range i := by
    rw [← hcent, ← show CommGroupScheme.groupHom eta ≫ a =
      CommGroupScheme.groupHom ν ≫ i from heta]
    exact range_le_centralizer_groupHom_comp a eta
  let q := ha.isSplitSubtorus.factorInClosedSubgroup hi.2.1 hle
  have hqa : q.val ≫ i = a := q.property.2
  have hgen : IsGenericCocharacter a eta := by
    apply RationalCocharacter.isGenericCocharacter_of_centralizer_eq_torusCentralizer ha.1.1 a eta
    apply le_antisymm
    · rw [heta]
      change Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i) ≤ torusCentralizer a
      rw [hcent]
      exact range_le_torusCentralizer_of_factor a i q.val hqa
    · exact torusCentralizer_le_dynamicCentralizer a (CommGroupScheme.groupHom eta)
  have hB : SubgroupFunctor.range b = Dynamic.parabolic (CommGroupScheme.groupHom eta ≫ a) := by
    rw [heta]
    exact hν.2
  refine ⟨?_, ?_⟩
  · intro χ
    obtain ⟨g, ζ, hg, hdom⟩ := exists_innerIso_comp_eq_dominant_cocharacter hG ha hgen χ
    let νT : cocharacterLattice T := Additive.ofMul (CommGroupScheme.groupHom ζ ≫ q.val)
    have hνT : CommGroupScheme.groupHom νT ≫ i = CommGroupScheme.groupHom ζ ≫ a :=
      (Category.assoc _ _ _).trans (congrArg (CommGroupScheme.groupHom ζ ≫ ·) hqa)
    exact ⟨g, νT, hg.trans hνT.symm, by rw [hB, hνT]; exact hdom⟩
  · intro ν₁ ν₂ g h₁ h₂ hg
    let χ₁ := CommGroupScheme.groupHom ν₁ ≫ i
    let χ₂ := CommGroupScheme.groupHom ν₂ ≫ i
    let j := Dynamic.Affine.parabolicHom χ₂
    have hj := Dynamic.Affine.isClosedSubgroup_parabolicHom χ₂
    have hre : SubgroupFunctor.range j = Dynamic.parabolic χ₂ :=
      (Dynamic.Affine.isRepresentedBy_parabolicHom χ₂).2
    have hjP := isParabolicSubgroup_of_range_eq_dynamicParabolic hG j hj χ₂ hre
    have hc : Dynamic.parabolic χ₁ = (Dynamic.parabolic χ₂).comap (G.innerIso g).hom := by
      change χ₁ ≫ (G.innerIso g).hom = χ₂ at hg
      rw [← hg]
      exact Dynamic.parabolic_eq_comap_of_iso χ₁ (G.innerIso g)
    have hgP := mem_rationalPoints_of_minimalParabolic_le_comap hG a ha eta hgen j hjP
      (by rw [hre, ← hB]; exact h₂) g (by rw [hre, ← hB, ← hc]; exact h₁)
    rw [hre] at hgP
    have heq := eq_of_innerIso_comp_eq_of_mem_parabolic ν₁ ν₂ g hgP hg
    let : IsClosedImmersion i.hom.hom.left := hi.2.1
    let : Mono i := (Grp.forget _).mono_of_mono_map (f := i)
      (show Mono i.hom.hom from Over.mono_of_mono_left _)
    exact congrArg Additive.ofMul ((cancel_mono i).mp heq)

end Langlands.GroupScheme
