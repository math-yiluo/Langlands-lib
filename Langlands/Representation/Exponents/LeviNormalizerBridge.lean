import Langlands.Representation.Plancherel.SplitComponentNormRigidity
import Langlands.GroupScheme.Rational.ParabolicLeviRealization
import Langlands.GroupScheme.Rational.ParabolicSplitComponentCocharacter
import Langlands.GroupScheme.Dynamic.GeometricUnipotentRadicalProof
import Langlands.GroupScheme.Torus.WeylImageFinite

/-! # Split components and the normalizers of represented centralizers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {A : CommGroupScheme (Spec (CommRingCat.of k))}
  {G M : GroupScheme (Spec (CommRingCat.of k))}

section Restriction

variable [IsAffineHom M.X.hom] {a : A.toGrp ⟶ M}

/-- The restriction to a split component is an actual automorphism. -/
def IsSplitComponent.automorphismRestrictionIso
    (ha : IsSplitComponent a) (φ : M ≅ M) : A ≅ A where
  hom := Additive.ofMul (ha.automorphismRestriction φ)
  inv := Additive.ofMul (ha.automorphismRestriction φ.symm)
  hom_inv_id := by
    apply congrArg Additive.ofMul
    let := ha.1.1.2.mono
    have : Mono a.hom.hom := Over.mono_of_mono_left _
    apply Grp.hom_ext
    apply (cancel_mono a.hom.hom).mp
    exact congrArg (fun f => f.hom.hom) (show
      (ha.automorphismRestriction φ ≫ ha.automorphismRestriction φ.symm) ≫ a =
        (𝟙 A.toGrp) ≫ a by
      rw [Category.assoc, ha.automorphismRestriction_comp,
        ← Category.assoc, ha.automorphismRestriction_comp, Category.assoc,
        Iso.symm_hom, Iso.hom_inv_id, Category.comp_id, Category.id_comp])
  inv_hom_id := by
    apply congrArg Additive.ofMul
    let := ha.1.1.2.mono
    have : Mono a.hom.hom := Over.mono_of_mono_left _
    apply Grp.hom_ext
    apply (cancel_mono a.hom.hom).mp
    exact congrArg (fun f => f.hom.hom) (show
      (ha.automorphismRestriction φ.symm ≫ ha.automorphismRestriction φ) ≫ a =
        (𝟙 A.toGrp) ≫ a by
      rw [Category.assoc, ha.automorphismRestriction_comp,
        ← Category.assoc, ha.automorphismRestriction_comp, Category.assoc,
        Iso.symm_hom, Iso.inv_hom_id, Category.comp_id, Category.id_comp])

/-- A normalizer of the ambient representative normalizes its split component. -/
theorem IsSplitComponent.isNormalizingPoint_of_normalizes
    (ha : IsSplitComponent a) {j : M ⟶ G}
    {w : rationalPoints G} {φ : M ≅ M}
    (hw : φ.hom ≫ j = j ≫ (G.innerIso w).hom) :
    IsNormalizingPoint (a ≫ j) w (ha.automorphismRestrictionIso φ) := by
  change (a ≫ j) ≫ (G.innerIso w).hom = ha.automorphismRestriction φ ≫ a ≫ j
  rw [Category.assoc, ← hw, ← Category.assoc, ← ha.automorphismRestriction_comp]
  exact Category.assoc _ _ _

end Restriction

section Centralizer

variable [IsAffineHom M.X.hom] {a : A.toGrp ⟶ M} {j : M ⟶ G}

/-- If a subgroup is the centralizer of one cocharacter, it is the centralizer
of its full split component. The equality is on every test scheme. -/
theorem IsSplitComponent.torusCentralizer_comp_eq_of_dynamicCentralizer
    (ha : IsSplitComponent a)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (hj : (Dynamic.centralizer χ).IsRepresentedBy j) :
    torusCentralizer (a ≫ j) = SubgroupFunctor.range j := by
  obtain ⟨ν, hν⟩ := ha.exists_cocharacter_factor_of_dynamicCentralizer χ hj
  apply le_antisymm
  · have hle := torusCentralizer_le_dynamicCentralizer (a ≫ j)
      (CommGroupScheme.groupHom ν)
    rw [hν, ← hj.2] at hle
    exact hle
  · intro V x hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    intro W q z
    have hc := (commute_of_mem_center (ha.1.2 W z) (q ≫ y)).symm
    have he := congrArg (fun t : W ⟶ M.X => t ≫ j.hom.hom) hc.eq
    apply (commute_iff_eq _ _).mpr
    simpa only [Grp.comp_hom_hom, MonObj.mul_comp, Category.assoc] using he

/-- Realize the centralizer of the split component of the specified rational
Levi, retaining only the rational parabolic classification input. -/
theorem IsSplitComponent.torusCentralizer_comp_eq_of_parabolicDynamic
    (hPD : ParabolicDynamicStatement.{u}) (hG : IsConnectedReductive G)
    {P : GroupScheme (Spec (CommRingCat.of k))}
    {p : P ⟶ G} (hp : IsParabolicSubgroup p)
    {l : M ⟶ P} (hl : IsRationalLeviSubgroup l) (ha : IsSplitComponent a) :
    torusCentralizer (a ≫ l ≫ p) = SubgroupFunctor.range (l ≫ p) := by
  obtain ⟨χ, -, hχ⟩ := DynamicLeviConjugacy.exists_cocharacter_parabolic_levi
    hPD dynamicGeometricUnipotentRadical hG hp hl
  let := (hl.isClosedSubgroup.comp hp.isClosedSubgroup).mono
  exact ha.torusCentralizer_comp_eq_of_dynamicCentralizer χ
    ⟨Over.mono_of_mono_left _, hχ⟩

end Centralizer

section Norm

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [IsAffineHom M.X.hom] {a : A.toGrp ⟶ M} {j : M ⟶ G}

/-- Norm preservation forces a normalizer into a represented split-component
centralizer. -/
theorem IsSplitComponent.mem_range_of_normalizes_of_norm
    (hM : IsConnectedReductive M) (ha : IsSplitComponent a)
    (hj : torusCentralizer (a ≫ j) = SubgroupFunctor.range j)
    {w : rationalPoints G} {φ : M ≅ M}
    (hw : φ.hom ≫ j = j ≫ (G.innerIso w).hom)
    (hnorm : ∀ x ∈ Subgroup.center (rationalPoints M), ∀ χ : rationalCharacters M,
      (Plancherel.rationalNormCharacters M χ).toMul (rationalPoints.map φ.hom x) =
        (Plancherel.rationalNormCharacters M χ).toMul x) :
    w ∈ (SubgroupFunctor.range j).carrier (Over.mk (𝟙 _)) := by
  rw [← hj, mem_torusCentralizer_base_iff]
  rw [Category.assoc, ← hw, ← Category.assoc,
    ha.comp_automorphism_eq_of_norm hM φ hnorm]

end Norm

end Langlands.GroupScheme
