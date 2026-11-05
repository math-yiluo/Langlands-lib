import Langlands.GroupScheme.Rational.PointedCommutatorFamily
import Langlands.GroupScheme.Rational.UnipotentTorsionCenter

/-! # Power reduction retaining a supplied pointed family -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace PointedPowerFamily

variable {B : Scheme.{u}} {Z : GroupScheme B} [IsCommMonObj Z.X] {V : Over B}

/-- Apply the `q^n` power morphism to the supplied family. -/
def word (f : V ⟶ Z.X) (q n : ℕ) : V ⟶ Z.X :=
  f ≫ (multiplication Z (q ^ n : ℕ)).hom.hom

theorem word_zero (f : V ⟶ Z.X) (q : ℕ) : word f q 0 = f := by
  simp [word]

theorem word_succ (f : V ⟶ Z.X) (q n : ℕ) :
    word f q (n + 1) = word f q n ≫ (multiplication Z (q : ℤ)).hom.hom := by
  simp only [word, PowerImage.points_multiplication_nat, pow_succ, pow_mul]

/-- Every whole section killed by the original family remains killed. -/
theorem section_word {P : Over B} (s : P ⟶ V) (f : V ⟶ Z.X)
    (hs : s ≫ f = 1) (q n : ℕ) : s ≫ word f q n = 1 := by
  rw [word, ← Category.assoc, hs, MonObj.one_comp]

/-- The least vanishing power of a nontrivial family has a nontrivial
predecessor; the whole ambient group need not be the image of the family. -/
theorem exists_last_nontrivial_word (f : V ⟶ Z.X) (hf : f ≠ 1) (q : ℕ)
    (hq : ∃ r, HasUniformPowerExponent Z (q ^ r)) :
    ∃ n, word f q n ≠ 1 ∧ word f q (n + 1) = 1 := by
  classical
  have h : ∃ r, word f q r = 1 := by
    obtain ⟨r, hr⟩ := hq
    refine ⟨r, ?_⟩
    simpa only [word, PowerImage.points_multiplication_nat] using hr V f
  have hzero : word f q 0 ≠ 1 := by rwa [word_zero]
  have hpos : 0 < Nat.find h := by
    by_contra hn
    have hz : Nat.find h = 0 := by omega
    exact hzero (hz ▸ Nat.find_spec h)
  refine ⟨Nat.find h - 1, Nat.find_min h (by omega), ?_⟩
  have he : Nat.find h - 1 + 1 = Nat.find h := by omega
  rw [he]
  exact Nat.find_spec h

section Field

attribute [local instance] P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_geometricallyIntegral.S17A0.subsingleton_spec_field

variable {k : Type u} [Field k]
    {Z : GroupScheme (Spec (CommRingCat.of k))} [IsCommMonObj Z.X]
    {V : Over (Spec (CommRingCat.of k))}

/-- Generate the last nontrivial power of a pointed family. Its generated
subgroup is smooth, connected and killed by `q`, and its factor retains every
section killed by the original family. -/
theorem exists_torsion_generatedImage [Smooth Z.X.hom] [IsAffineHom Z.X.hom]
    (hV : ImageGeneration.FinitePowerGood _ V)
    (v₀ : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ V)
    (f : V ⟶ Z.X) (hf₀ : v₀ ≫ f = 1) (hf : f ≠ 1) (q : ℕ)
    (hq : ∃ r, HasUniformPowerExponent Z (q ^ r)) :
    ∃ (n : ℕ) (D : GeneratedImage (word f q n)),
      Smooth D.group.X.hom ∧ IsAffineHom D.group.X.hom ∧
      GeometricallyConnected D.group.X.hom ∧ ConnectedSpace D.group.X.left ∧
      SubgroupFunctor.range D.inclusion ≠ ⊥ ∧ word f q n ≠ 1 ∧
      HasUniformPowerExponent D.group q ∧
      ∀ {P : Over (Spec (CommRingCat.of k))} (s : P ⟶ V),
        s ≫ f = 1 → s ≫ D.factor = 1 := by
  obtain ⟨n, hn, hn'⟩ := exists_last_nontrivial_word f hf q hq
  have : GeometricallyReduced V.hom := hV.2.2.1
  have : GeometricallyIrreducible V.hom := hV.2.2.2
  have hInt : GeometricallyIntegral V.hom :=
    GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible _
  obtain ⟨D, hD⟩ := ImageGeneration.pointedImageGeneration k Z inferInstance inferInstance
    V hV.1 hV.2.1 hInt v₀ (word f q n) (section_word v₀ f hf₀ q n)
  have hnt : SubgroupFunctor.range D.inclusion ≠ ⊥ := by
    intro hz
    have hm : word f q n ∈ (SubgroupFunctor.range D.inclusion).carrier V :=
      SubgroupFunctor.mem_range.2 ⟨D.factor, D.factor_comp⟩
    rw [hz, SubgroupFunctor.bot_carrier, Subgroup.mem_bot] at hm
    exact hn hm
  have ht : HasUniformPowerExponent D.group q :=
    PowerImage.GeneratedImage.hasUniformPowerExponent D q (by
      rw [← word_succ]
      exact hn')
  have : GeometricallyConnected D.group.X.hom := hD.2.2.1
  refine ⟨n, D, hD.1, hD.2.1, hD.2.2.1,
    GeometricallyConnected.connectedSpace_of_subsingleton D.group.X.hom,
    hnt, hn, ht, ?_⟩
  intro P s hs
  let : Mono D.inclusion.hom.hom := D.represents.1
  apply (cancel_mono D.inclusion.hom.hom).1
  rw [Category.assoc, D.factor_comp, MonObj.one_comp]
  exact section_word s f hs q n

end Field

end PointedPowerFamily

section Unipotent

attribute [local instance] P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_geometricallyIntegral.S17A0.subsingleton_spec_field

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}

/-- From a nonconstant affine-line map in characteristic `p`, retain a
nontrivial family in an actual smooth connected commutative central subgroup
killed by `p`. Every original group parameter remains in the zero section. -/
theorem exists_pointed_torsion_central_family_of_not_hasConstantAffineLineMaps
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (p : ℕ) [Fact p.Prime] [CharP k p]
    (hU : IsUnipotent G) (hG : ¬ HasConstantAffineLineMaps G) :
    ∃ (n : ℕ) (W : CommGroupScheme (Spec (CommRingCat.of k)))
      (w : W.toGrp ⟶ G)
      (f : PointedCommutatorFamily.source G
        (AffineLine.scheme (Spec (CommRingCat.of k))) n ⟶ W.X),
      IsClosedSubgroup w ∧ Smooth W.X.hom ∧ IsAffineHom W.X.hom ∧
      GeometricallyConnected W.X.hom ∧ ConnectedSpace W.X.left ∧ IsCentral w ∧
      HasUniformPowerExponent W.toGrp p ∧ f ≠ 1 ∧
      PointedCommutatorFamily.basepointSection (G := G)
        (AffineLine.zeroSection _) n ≫ f = 1 := by
  obtain ⟨a, n, D, hs, ha, _hgc, hc, hcent, _hnt, hn, hsection⟩ :=
    PointedCommutatorFamily.exists_central_generatedImage_of_not_hasConstantAffineLineMaps
      hU hG
  let : IsClosedImmersion D.inclusion.hom.hom.left := D.closed
  let : Mono D.inclusion.hom.hom := D.represents.1
  let : Smooth D.group.X.hom := hs
  let : IsAffineHom D.group.X.hom := ha
  let : ConnectedSpace D.group.X.left := hc
  let : IsCommMonObj D.group.X := hcent.isCommMonObj
  have hf : D.factor ≠ 1 := by
    intro h
    apply hn
    rw [← D.factor_comp, h, MonObj.one_comp]
  have hgood := PointedCommutatorFamily.source_good (G := G)
    (ImageGeneration.finitePowerGood_of_geometricallyIntegral
      (AffineLine.scheme (Spec (CommRingCat.of k)))
      (by dsimp [AffineLine.scheme]; infer_instance)
      (by dsimp [AffineLine.scheme]; infer_instance)
      (by dsimp [AffineLine.scheme]; infer_instance)) n
  have hpoint : PointedCommutatorFamily.origin (G := G) (AffineLine.zeroSection _) n ≫
      D.factor = 1 := by
    apply (cancel_mono D.inclusion.hom.hom).1
    rw [Category.assoc, D.factor_comp, MonObj.one_comp]
    exact PointedCommutatorFamily.origin_word _ _
      (zeroSection_comp_affineLineDifference a) n
  obtain ⟨r, hr⟩ := exists_hasUniformPowerExponent_of_isUnipotent p hU
  obtain ⟨m, E, hEs, hEa, hEgc, hEc, _hEnt, hm, ht, hsections⟩ :=
    PointedPowerFamily.exists_torsion_generatedImage hgood
      (PointedCommutatorFamily.origin (G := G) (AffineLine.zeroSection _) n)
      D.factor hpoint hf p ⟨r, hr.of_mono D.inclusion⟩
  let w := E.inclusion ≫ D.inclusion
  have hw : IsClosedSubgroup w := by
    let : IsClosedImmersion E.inclusion.hom.hom.left := E.closed
    change IsClosedImmersion (E.inclusion.hom.hom.left ≫ D.inclusion.hom.hom.left)
    infer_instance
  let : IsClosedImmersion w.hom.hom.left := hw
  let : Mono w.hom.hom := Over.mono_of_mono_left _
  have hwcent : IsCentral w := hcent.comp E.inclusion
  refine ⟨n, hwcent.commGroupScheme, w, E.factor, hw, hEs, hEa, hEgc, hEc,
    hwcent, ht, ?_, hsections _ hsection⟩
  intro hz
  change E.factor = (1 : _ ⟶ E.group.X) at hz
  apply hm
  rw [← E.factor_comp, hz, MonObj.one_comp]

end Unipotent

end Langlands.GroupScheme
