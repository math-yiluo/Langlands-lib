import Langlands.GroupScheme.Dynamic.TripleParabolicIntersection
import Langlands.GroupScheme.Lie.PointTangent
import Langlands.GroupScheme.Lie.KernelTargetMaps
import Langlands.AlgebraicGeometry.TangentSmoothness
import Langlands.GroupScheme.SmoothProducts
import Langlands.GroupScheme.Rational.RelativeTitsNondegeneracy
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono

/-! # An open slice for three dynamic parabolics -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section WeightSplitting

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Every Lie vector is the sum of a vector in the span of the weight spaces satisfying a
predicate and one in the span of the others. -/
theorem exists_add_weightSpan_of_isSplitTorus (hT : IsSplitTorus T.toGrp) (t : T.toGrp ⟶ G)
    (p : characterLattice T → Prop) (x : Additive (lieKernel G k)) :
    ∃ a ∈ (⨆ (χ : characterLattice T) (_ : p χ), weightSpace t χ),
      ∃ b ∈ (⨆ (χ : characterLattice T) (_ : ¬ p χ), weightSpace t χ), a + b = x := by
  classical
  have htop := (isInternal_weightSpace_of_isSplitTorus k G T hT t).submodule_iSup_eq_top
  have hle : (⨆ χ, weightSpace t χ) ≤
      (⨆ (χ : characterLattice T) (_ : p χ), weightSpace t χ) ⊔
        ⨆ (χ : characterLattice T) (_ : ¬ p χ), weightSpace t χ := by
    refine iSup_le fun χ => ?_
    by_cases h : p χ
    · exact le_sup_of_le_left (le_iSup₂_of_le χ h le_rfl)
    · exact le_sup_of_le_right (le_iSup₂_of_le χ h le_rfl)
  have hx : x ∈ (⨆ (χ : characterLattice T) (_ : p χ), weightSpace t χ) ⊔
      ⨆ (χ : characterLattice T) (_ : ¬ p χ), weightSpace t χ := by
    apply hle
    rw [htop]
    exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hx
  exact ⟨a, ha, b, hb, hab⟩

omit [LocallyOfFiniteType G.X.hom] in
/-- A weight span is contained in another once every nonzero weight space of the first
index set has its character in the second index set. -/
theorem weightSpan_mono_of_ne_bot (t : T.toGrp ⟶ G) {p q : characterLattice T → Prop}
    (h : ∀ χ, p χ → weightSpace t χ ≠ ⊥ → q χ) :
    (⨆ (χ : characterLattice T) (_ : p χ), weightSpace t χ) ≤
      ⨆ (χ : characterLattice T) (_ : q χ), weightSpace t χ := by
  refine iSup₂_le fun χ hχ => ?_
  by_cases hb : weightSpace t χ = ⊥
  · rw [hb]
    exact bot_le
  · exact le_iSup₂_of_le χ (h χ hχ hb) le_rfl

/-- The infinitesimal slice decomposition for three cocharacters with zero sum, each root
negative at no more than one of them and vanishing at all three exactly when it vanishes at
the difference of the first two. -/
theorem exists_lie_slice_decomposition (hT : IsSplitTorus T.toGrp) (t : T.toGrp ⟶ G)
    (ν : Fin 3 → cocharacterLattice T)
    (hneg : ∀ α ∈ relativeRoots t, (∀ i, latticePairing T α (ν i) = 0) ∨
      ∃! i, latticePairing T α (ν i) < 0)
    (hzero : ∀ α ∈ relativeRoots t, latticePairing T α (ν 0 - ν 1) = 0 →
      ∀ i, latticePairing T α (ν i) = 0)
    (Z : Fin 3 → Additive (lieKernel G k)) :
    ∃ A ∈ (⨆ (χ : characterLattice T) (_ : 0 < latticePairing T χ (-(ν 0 - ν 1))),
        weightSpace t χ),
      ∃ B ∈ (⨆ (χ : characterLattice T) (_ : 0 < latticePairing T χ (ν 0 - ν 1)),
        weightSpace t χ),
        ∀ i, Z i - A - B ∈ nonnegativeWeightSpan t (ν i) := by
  classical
  let ν₀ := ν 0 - ν 1
  -- Roots are the nonzero characters with a nonzero weight space.
  have hroot (χ : characterLattice T) (hχ : χ ≠ 0) (hb : weightSpace t χ ≠ ⊥) :
      χ ∈ relativeRoots t := ⟨hχ, hb⟩
  -- Split each `Z i` into its nonnegative and negative parts for `ν i`.
  choose a ha b hb hab using fun i => exists_add_weightSpan_of_isSplitTorus hT t
    (fun χ => 0 ≤ latticePairing T χ (ν i)) (Z i)
  -- Negative parts of one cocharacter are nonnegative for the others.
  have hcross (i j : Fin 3) (hij : i ≠ j) :
      (⨆ (χ : characterLattice T) (_ : ¬ 0 ≤ latticePairing T χ (ν j)), weightSpace t χ) ≤
        nonnegativeWeightSpan t (ν i) := by
    refine weightSpan_mono_of_ne_bot t fun χ hχ hne => ?_
    have hχ0 : χ ≠ 0 := by
      rintro rfl
      simp at hχ
    rcases hneg χ (hroot χ hχ0 hne) with h | ⟨m, hm, huniq⟩
    · exact absurd (h j).ge hχ
    · have hjm : j = m := huniq j (lt_of_not_ge hχ)
      by_contra hi
      exact hij ((huniq i (lt_of_not_ge hi)).trans hjm.symm)
  -- The sum of the negative parts, split for `ν₀`.
  let X := b 0 + b 1 + b 2
  obtain ⟨xn, hxn, xr, hxr, hX⟩ := exists_add_weightSpan_of_isSplitTorus hT t
    (fun χ => latticePairing T χ ν₀ < 0) X
  obtain ⟨xp, hxp, x0, hx0, hxr'⟩ := exists_add_weightSpan_of_isSplitTorus hT t
    (fun χ => 0 < latticePairing T χ ν₀) xr
  have hxnU : xn ∈ (⨆ (χ : characterLattice T) (_ : 0 < latticePairing T χ (-ν₀)),
      weightSpace t χ) := by
    refine weightSpan_mono_of_ne_bot t (fun χ hχ _ => ?_) hxn
    simp only [map_neg]
    exact neg_pos.2 hχ
  have hx0' : x0 ∈ ⨆ χ ∈ ({χ | ¬ latticePairing T χ ν₀ < 0} ∩
      {χ | ¬ 0 < latticePairing T χ ν₀}), weightSpace t χ := by
    have hind := (isInternal_weightSpace_of_isSplitTorus k G T hT t).submodule_iSupIndep
    apply biSup_inf_biSup_le_of_iSupIndep hind
    refine ⟨?_, hx0⟩
    have hxpr : xp ∈ ⨆ χ ∈ {χ | ¬ latticePairing T χ ν₀ < 0}, weightSpace t χ :=
      weightSpan_mono_of_ne_bot t (fun χ hχ _ => not_lt.2 hχ.le) hxp
    have h := sub_mem hxr hxpr
    rwa [← hxr', add_sub_cancel_left] at h
  have hx0P (i : Fin 3) : x0 ∈ nonnegativeWeightSpan t (ν i) := by
    refine weightSpan_mono_of_ne_bot t (fun χ hχ hne => ?_) hx0'
    have hz : latticePairing T χ ν₀ = 0 := by
      have h1 : ¬ latticePairing T χ ν₀ < 0 := hχ.1
      have h2 : ¬ 0 < latticePairing T χ ν₀ := hχ.2
      omega
    by_cases hχ0 : χ = 0
    · subst hχ0
      simp
    · exact (hzero χ (hroot χ hχ0 hne) hz i).ge
  have hbmem (i j : Fin 3) (hij : i ≠ j) : b j ∈ nonnegativeWeightSpan t (ν i) :=
    hcross i j hij (hb j)
  have hXb (i : Fin 3) : X - b i ∈ nonnegativeWeightSpan t (ν i) := by
    fin_cases i
    · show X - b 0 ∈ nonnegativeWeightSpan t (ν 0)
      have : X - b 0 = b 1 + b 2 := by simp only [X]; abel
      rw [this]
      exact add_mem (hbmem 0 1 (by decide)) (hbmem 0 2 (by decide))
    · show X - b 1 ∈ nonnegativeWeightSpan t (ν 1)
      have : X - b 1 = b 0 + b 2 := by simp only [X]; abel
      rw [this]
      exact add_mem (hbmem 1 0 (by decide)) (hbmem 1 2 (by decide))
    · show X - b 2 ∈ nonnegativeWeightSpan t (ν 2)
      have : X - b 2 = b 0 + b 1 := by simp only [X]; abel
      rw [this]
      exact add_mem (hbmem 2 0 (by decide)) (hbmem 2 1 (by decide))
  refine ⟨xn, hxnU, xp, hxp, fun i => ?_⟩
  have hdecomp : Z i - xn - xp = a i - (X - b i) + x0 := by
    rw [← hab i, ← hX, ← hxr']
    abel
  rw [hdecomp]
  exact add_mem (sub_mem (ha i) (hXb i)) (hx0P i)

end WeightSplitting

section SliceMap

variable {k : Type u} [Field k] {G A B P₀ P₁ P₂ : GroupScheme (Spec (CommRingCat.of k))}
  (a : A ⟶ G) (b : B ⟶ G) (p₀ : P₀ ⟶ G) (p₁ : P₁ ⟶ G) (p₂ : P₂ ⟶ G)

/-- The source `A × B × P₀ × P₁ × P₂` of the slice map. -/
abbrev sliceSource (A B P₀ P₁ P₂ : GroupScheme (Spec (CommRingCat.of k))) :
    Over (Spec (CommRingCat.of k)) :=
  A.X ⊗ (B.X ⊗ (P₀.X ⊗ (P₁.X ⊗ P₂.X)))

/-- The cube `G × G × G`. -/
abbrev groupCube (G : GroupScheme (Spec (CommRingCat.of k))) : Over (Spec (CommRingCat.of k)) :=
  G.X ⊗ (G.X ⊗ G.X)

/-- The coordinate projections of the slice source. -/
def sliceA : sliceSource A B P₀ P₁ P₂ ⟶ A.X := fst _ _

/-- The second coordinate of the slice source. -/
def sliceB : sliceSource A B P₀ P₁ P₂ ⟶ B.X := snd _ _ ≫ fst _ _

/-- The third coordinate of the slice source. -/
def sliceP₀ : sliceSource A B P₀ P₁ P₂ ⟶ P₀.X := snd _ _ ≫ snd _ _ ≫ fst _ _

/-- The fourth coordinate of the slice source. -/
def sliceP₁ : sliceSource A B P₀ P₁ P₂ ⟶ P₁.X := snd _ _ ≫ snd _ _ ≫ snd _ _ ≫ fst _ _

/-- The fifth coordinate of the slice source. -/
def sliceP₂ : sliceSource A B P₀ P₁ P₂ ⟶ P₂.X := snd _ _ ≫ snd _ _ ≫ snd _ _ ≫ snd _ _

/-- The product of the first two coordinates of the slice source in `G`. -/
def sliceHead : sliceSource A B P₀ P₁ P₂ ⟶ G.X :=
  (sliceA ≫ a.hom.hom) * (sliceB ≫ b.hom.hom)

/-- The slice map `(x, y, z₀, z₁, z₂) ↦ (x y z₀, x y z₁, x y z₂)`. -/
def tripleSliceMap : sliceSource A B P₀ P₁ P₂ ⟶ groupCube G :=
  lift (sliceHead a b * (sliceP₀ ≫ p₀.hom.hom))
    (lift (sliceHead a b * (sliceP₁ ≫ p₁.hom.hom)) (sliceHead a b * (sliceP₂ ≫ p₂.hom.hom)))

/-- The identity point of the slice source. -/
def sliceIdentity : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ sliceSource A B P₀ P₁ P₂ :=
  lift 1 (lift 1 (lift 1 (lift 1 1)))

variable {T : Over (Spec (CommRingCat.of k))}

theorem comp_sliceHead (x : T ⟶ sliceSource A B P₀ P₁ P₂) :
    x ≫ sliceHead a b = ((x ≫ sliceA) ≫ a.hom.hom) * ((x ≫ sliceB) ≫ b.hom.hom) := by
  rw [sliceHead, MonObj.comp_mul, Category.assoc, Category.assoc]

theorem comp_tripleSliceMap_fst (x : T ⟶ sliceSource A B P₀ P₁ P₂) :
    x ≫ tripleSliceMap a b p₀ p₁ p₂ ≫ fst _ _ =
      (x ≫ sliceHead a b) * ((x ≫ sliceP₀) ≫ p₀.hom.hom) := by
  rw [tripleSliceMap, lift_fst, MonObj.comp_mul, Category.assoc]

theorem comp_tripleSliceMap_snd_fst (x : T ⟶ sliceSource A B P₀ P₁ P₂) :
    x ≫ tripleSliceMap a b p₀ p₁ p₂ ≫ snd _ _ ≫ fst _ _ =
      (x ≫ sliceHead a b) * ((x ≫ sliceP₁) ≫ p₁.hom.hom) := by
  rw [tripleSliceMap, lift_snd_assoc, lift_fst, MonObj.comp_mul, Category.assoc]

theorem comp_tripleSliceMap_snd_snd (x : T ⟶ sliceSource A B P₀ P₁ P₂) :
    x ≫ tripleSliceMap a b p₀ p₁ p₂ ≫ snd _ _ ≫ snd _ _ =
      (x ≫ sliceHead a b) * ((x ≫ sliceP₂) ≫ p₂.hom.hom) := by
  rw [tripleSliceMap, lift_snd_assoc, lift_snd, MonObj.comp_mul, Category.assoc]

/-- Points of the slice source are determined by their five coordinates. -/
theorem slice_hom_ext {x y : T ⟶ sliceSource A B P₀ P₁ P₂}
    (hA : x ≫ sliceA = y ≫ sliceA) (hB : x ≫ sliceB = y ≫ sliceB)
    (h₀ : x ≫ sliceP₀ = y ≫ sliceP₀) (h₁ : x ≫ sliceP₁ = y ≫ sliceP₁)
    (h₂ : x ≫ sliceP₂ = y ≫ sliceP₂) : x = y := by
  refine CartesianMonoidalCategory.hom_ext _ _ hA ?_
  refine CartesianMonoidalCategory.hom_ext _ _ (by simpa only [sliceB, Category.assoc] using hB) ?_
  refine CartesianMonoidalCategory.hom_ext _ _
    (by simpa only [sliceP₀, Category.assoc] using h₀) ?_
  refine CartesianMonoidalCategory.hom_ext _ _
    (by simpa only [sliceP₁, Category.assoc] using h₁) ?_
  simpa only [sliceP₂, Category.assoc] using h₂

theorem sliceIdentity_comp_sliceA :
    (sliceIdentity : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ sliceSource A B P₀ P₁ P₂) ≫
      sliceA = 1 := lift_fst _ _

theorem sliceIdentity_comp_tripleSliceMap :
    (sliceIdentity : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ sliceSource A B P₀ P₁ P₂) ≫
      tripleSliceMap a b p₀ p₁ p₂ = lift 1 (lift 1 1) := by
  have hB : (sliceIdentity : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶
      sliceSource A B P₀ P₁ P₂) ≫ sliceB = 1 := by
    simp only [sliceIdentity, sliceB, lift_snd_assoc, lift_fst]
  have h₀ : (sliceIdentity : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶
      sliceSource A B P₀ P₁ P₂) ≫ sliceP₀ = 1 := by
    simp only [sliceIdentity, sliceP₀, lift_snd_assoc, lift_fst]
  have h₁ : (sliceIdentity : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶
      sliceSource A B P₀ P₁ P₂) ≫ sliceP₁ = 1 := by
    simp only [sliceIdentity, sliceP₁, lift_snd_assoc, lift_fst]
  have h₂ : (sliceIdentity : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶
      sliceSource A B P₀ P₁ P₂) ≫ sliceP₂ = 1 := by
    simp only [sliceIdentity, sliceP₂, lift_snd_assoc, lift_snd]
  have hH : (sliceIdentity : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶
      sliceSource A B P₀ P₁ P₂) ≫ sliceHead a b = 1 := by
    rw [comp_sliceHead, sliceIdentity_comp_sliceA, hB, MonObj.one_comp, MonObj.one_comp,
      mul_one]
  refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
  · rw [Category.assoc, comp_tripleSliceMap_fst, hH, h₀, MonObj.one_comp, mul_one, lift_fst]
  refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
  · rw [Category.assoc, Category.assoc, comp_tripleSliceMap_snd_fst, hH, h₁, MonObj.one_comp,
      mul_one]
    simp only [Category.assoc, lift_snd_assoc, lift_fst]
  · rw [Category.assoc, Category.assoc, comp_tripleSliceMap_snd_snd, hH, h₂, MonObj.one_comp,
      mul_one]
    simp only [Category.assoc, lift_snd_assoc, lift_snd]

end SliceMap

section SliceMono

set_option maxHeartbeats 1000000

variable {k : Type u} [Field k] {G A B P₀ P₁ P₂ : GroupScheme (Spec (CommRingCat.of k))}
  (a : A ⟶ G) (b : B ⟶ G) (p₀ : P₀ ⟶ G) (p₁ : P₁ ⟶ G) (p₂ : P₂ ⟶ G)

private theorem inv_mul_eq_of_mul_eq {Γ : Type*} [Group Γ] {x y m m' : Γ}
    (e : x * m = y * m') : x⁻¹ * y = m * m'⁻¹ := by
  calc x⁻¹ * y = x⁻¹ * (y * m') * m'⁻¹ := by group
    _ = x⁻¹ * (x * m) * m'⁻¹ := by rw [e]
    _ = m * m'⁻¹ := by group

private theorem comp_mul_inv_comp {H : GroupScheme (Spec (CommRingCat.of k))}
    {T : Over (Spec (CommRingCat.of k))} (f : H ⟶ G) (w w' : T ⟶ H.X) :
    (w ≫ f.hom.hom) * (w' ≫ f.hom.hom)⁻¹ = (w * w'⁻¹) ≫ f.hom.hom := by
  rw [MonObj.mul_comp, GrpObj.inv_comp]

private theorem slice_component_cancel {H : GroupScheme (Spec (CommRingCat.of k))}
    {T : Over (Spec (CommRingCat.of k))} (f : H ⟶ G) [Mono f.hom.hom] {x y : T ⟶ G.X}
    {w w' : T ⟶ H.X} (e : x * (w ≫ f.hom.hom) = y * (w' ≫ f.hom.hom)) (hxy : x = y) :
    w = w' := by
  subst hxy
  exact (cancel_mono f.hom.hom).1 (mul_left_cancel e)

/-- The slice map is a monomorphism when the first two factors meet the intersection of the
last three only trivially, in the sense of the hypothesis. -/
theorem mono_tripleSliceMap [Mono a.hom.hom] [Mono b.hom.hom] [Mono p₀.hom.hom]
    [Mono p₁.hom.hom] [Mono p₂.hom.hom]
    (h : ∀ (T : Over (Spec (CommRingCat.of k))) (u u' : T ⟶ A.X) (v v' : T ⟶ B.X),
      ((u ≫ a.hom.hom) * (v ≫ b.hom.hom))⁻¹ * ((u' ≫ a.hom.hom) * (v' ≫ b.hom.hom)) ∈
        (SubgroupFunctor.range p₀ ⊓ SubgroupFunctor.range p₁ ⊓
          SubgroupFunctor.range p₂).carrier T →
      u = u' ∧ v = v') :
    Mono (tripleSliceMap a b p₀ p₁ p₂) := by
  constructor
  intro T x y hxy
  have e₀ : (x ≫ sliceHead a b) * ((x ≫ sliceP₀) ≫ p₀.hom.hom) =
      (y ≫ sliceHead a b) * ((y ≫ sliceP₀) ≫ p₀.hom.hom) := by
    rw [← comp_tripleSliceMap_fst, ← comp_tripleSliceMap_fst, ← Category.assoc, hxy,
      Category.assoc]
  have e₁ : (x ≫ sliceHead a b) * ((x ≫ sliceP₁) ≫ p₁.hom.hom) =
      (y ≫ sliceHead a b) * ((y ≫ sliceP₁) ≫ p₁.hom.hom) := by
    rw [← comp_tripleSliceMap_snd_fst, ← comp_tripleSliceMap_snd_fst, ← Category.assoc, hxy,
      Category.assoc]
  have e₂ : (x ≫ sliceHead a b) * ((x ≫ sliceP₂) ≫ p₂.hom.hom) =
      (y ≫ sliceHead a b) * ((y ≫ sliceP₂) ≫ p₂.hom.hom) := by
    rw [← comp_tripleSliceMap_snd_snd, ← comp_tripleSliceMap_snd_snd, ← Category.assoc, hxy,
      Category.assoc]
  have hmem : (x ≫ sliceHead a b)⁻¹ * (y ≫ sliceHead a b) ∈
      (SubgroupFunctor.range p₀ ⊓ SubgroupFunctor.range p₁ ⊓
        SubgroupFunctor.range p₂).carrier T := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [inv_mul_eq_of_mul_eq e₀, comp_mul_inv_comp]
      exact SubgroupFunctor.mem_range.2 ⟨_, rfl⟩
    · rw [inv_mul_eq_of_mul_eq e₁, comp_mul_inv_comp]
      exact SubgroupFunctor.mem_range.2 ⟨_, rfl⟩
    · rw [inv_mul_eq_of_mul_eq e₂, comp_mul_inv_comp]
      exact SubgroupFunctor.mem_range.2 ⟨_, rfl⟩
  rw [comp_sliceHead, comp_sliceHead] at hmem
  obtain ⟨hu, hv⟩ := h T _ _ _ _ hmem
  have hhead : x ≫ sliceHead a b = y ≫ sliceHead a b := by
    rw [comp_sliceHead, comp_sliceHead, hu, hv]
  exact slice_hom_ext hu hv (slice_component_cancel p₀ e₀ hhead)
    (slice_component_cancel p₁ e₁ hhead) (slice_component_cancel p₂ e₂ hhead)

end SliceMono

section SliceTangent

open Langlands.AlgebraicGeometry.Picard Langlands.AlgebraicGeometry.TangentSmoothness

set_option maxHeartbeats 1000000

variable {k : Type u} [Field k] {G A B P₀ P₁ P₂ : GroupScheme (Spec (CommRingCat.of k))}
  (a : A ⟶ G) (b : B ⟶ G) (p₀ : P₀ ⟶ G) (p₁ : P₁ ⟶ G) (p₂ : P₂ ⟶ G)

private theorem one_left_eq (H : GroupScheme (Spec (CommRingCat.of k))) :
    (Over.homMk (dualNumberAugmentation k) dualNumberAugmentation_comp_dualNumberProjection :
        Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶
          (algSpec (CommRingCat.of k)).obj
            (op (CommAlgCat.of (CommRingCat.of k) (DualNumber k)))) ≫
        ((Lie.kernelTangentEquiv H).symm ⟨_, (Lie.kernelTangentEquiv H 1).property⟩).val =
      1 := by
  apply Over.OverMorphism.ext
  exact (Lie.kernelTangentEquiv H 1).property.2

/-- An element of the Lie kernel restricts to the identity at the closed point. -/
private theorem aug_comp_lieKernel (H : GroupScheme (Spec (CommRingCat.of k)))
    (X : lieKernel H k) :
    (Over.homMk (dualNumberAugmentation k) dualNumberAugmentation_comp_dualNumberProjection :
        Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶
          (algSpec (CommRingCat.of k)).obj
            (op (CommAlgCat.of (CommRingCat.of k) (DualNumber k)))) ≫ X.val = 1 := by
  apply Over.OverMorphism.ext
  exact (Lie.kernelTangentEquiv H X).property.2

/-- The slice map is surjective on rational tangent vectors at the identity when the Lie
algebras of the five factors satisfy the infinitesimal slice condition. -/
theorem isTangentSurjectiveAt_tripleSliceMap
    (hLie : ∀ Z₀ Z₁ Z₂ : lieKernel G k, ∃ (α : lieKernel A k) (β : lieKernel B k)
      (γ₀ : lieKernel P₀ k) (γ₁ : lieKernel P₁ k) (γ₂ : lieKernel P₂ k),
      Lie.targetMap a k α * Lie.targetMap b k β * Lie.targetMap p₀ k γ₀ = Z₀ ∧
      Lie.targetMap a k α * Lie.targetMap b k β * Lie.targetMap p₁ k γ₁ = Z₁ ∧
      Lie.targetMap a k α * Lie.targetMap b k β * Lie.targetMap p₂ k γ₂ = Z₂) :
    IsTangentSurjectiveAt (sliceSource A B P₀ P₁ P₂).hom (groupCube G).hom
      (tripleSliceMap a b p₀ p₁ p₂).left
      (sliceIdentity : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶
        sliceSource A B P₀ P₁ P₂).left := by
  rintro t ⟨ht₁, ht₂⟩
  let D := (algSpec (CommRingCat.of k)).obj
    (op (CommAlgCat.of (CommRingCat.of k) (DualNumber k)))
  let tt : D ⟶ groupCube G := Over.homMk t ht₁
  let aug : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ D :=
    Over.homMk (dualNumberAugmentation k) dualNumberAugmentation_comp_dualNumberProjection
  have hbase : aug ≫ tt = sliceIdentity ≫ tripleSliceMap a b p₀ p₁ p₂ :=
    Over.OverMorphism.ext ht₂
  have hidA : (sliceIdentity : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶
      sliceSource A B P₀ P₁ P₂) ≫ sliceA = 1 := lift_fst _ _
  have hidB : (sliceIdentity : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶
      sliceSource A B P₀ P₁ P₂) ≫ sliceB = 1 := by
    simp only [sliceIdentity, sliceB, lift_snd_assoc, lift_fst]
  have hid₀ : (sliceIdentity : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶
      sliceSource A B P₀ P₁ P₂) ≫ sliceP₀ = 1 := by
    simp only [sliceIdentity, sliceP₀, lift_snd_assoc, lift_fst]
  have hid₁ : (sliceIdentity : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶
      sliceSource A B P₀ P₁ P₂) ≫ sliceP₁ = 1 := by
    simp only [sliceIdentity, sliceP₁, lift_snd_assoc, lift_fst]
  have hid₂ : (sliceIdentity : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶
      sliceSource A B P₀ P₁ P₂) ≫ sliceP₂ = 1 := by
    simp only [sliceIdentity, sliceP₂, lift_snd_assoc, lift_snd]
  have hidHead : (sliceIdentity : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶
      sliceSource A B P₀ P₁ P₂) ≫ sliceHead a b = 1 := by
    rw [comp_sliceHead, hidA, hidB, MonObj.one_comp, MonObj.one_comp, mul_one]
  -- The components of the tangent vector are Lie vectors of `G`.
  have hcomp (π : groupCube G ⟶ G.X)
      (hπ : (sliceIdentity : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶
        sliceSource A B P₀ P₁ P₂) ≫ tripleSliceMap a b p₀ p₁ p₂ ≫ π = 1) :
      IsTangentVectorAt G.X.hom (1 : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X).left
        (tt ≫ π).left := by
    refine ⟨Over.w (tt ≫ π), ?_⟩
    have h := congrArg (fun f => f ≫ π) hbase
    simp only [Category.assoc, hπ] at h
    exact congrArg CommaMorphism.left h
  have hπ₀ : (sliceIdentity : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶
      sliceSource A B P₀ P₁ P₂) ≫ tripleSliceMap a b p₀ p₁ p₂ ≫ fst _ _ = 1 := by
    rw [comp_tripleSliceMap_fst, hidHead, hid₀, MonObj.one_comp, mul_one]
  have hπ₁ : (sliceIdentity : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶
      sliceSource A B P₀ P₁ P₂) ≫ tripleSliceMap a b p₀ p₁ p₂ ≫ snd _ _ ≫ fst _ _ = 1 := by
    rw [comp_tripleSliceMap_snd_fst, hidHead, hid₁, MonObj.one_comp, mul_one]
  have hπ₂ : (sliceIdentity : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶
      sliceSource A B P₀ P₁ P₂) ≫ tripleSliceMap a b p₀ p₁ p₂ ≫ snd _ _ ≫ snd _ _ = 1 := by
    rw [comp_tripleSliceMap_snd_snd, hidHead, hid₂, MonObj.one_comp, mul_one]
  let Z₀ : lieKernel G k := (Lie.kernelTangentEquiv G).symm ⟨_, hcomp _ hπ₀⟩
  let Z₁ : lieKernel G k := (Lie.kernelTangentEquiv G).symm ⟨_, hcomp _ hπ₁⟩
  let Z₂ : lieKernel G k := (Lie.kernelTangentEquiv G).symm ⟨_, hcomp _ hπ₂⟩
  have hZ₀ : Z₀.val = tt ≫ fst _ _ := Over.OverMorphism.ext rfl
  have hZ₁ : Z₁.val = tt ≫ snd _ _ ≫ fst _ _ := Over.OverMorphism.ext rfl
  have hZ₂ : Z₂.val = tt ≫ snd _ _ ≫ snd _ _ := Over.OverMorphism.ext rfl
  obtain ⟨α, β, γ₀, γ₁, γ₂, h₀, h₁, h₂⟩ := hLie Z₀ Z₁ Z₂
  let sO : D ⟶ sliceSource A B P₀ P₁ P₂ :=
    lift α.val (lift β.val (lift γ₀.val (lift γ₁.val γ₂.val)))
  have hsA : sO ≫ sliceA = α.val := lift_fst _ _
  have hsB : sO ≫ sliceB = β.val := by simp only [sO, sliceB, lift_snd_assoc, lift_fst]
  have hs₀ : sO ≫ sliceP₀ = γ₀.val := by simp only [sO, sliceP₀, lift_snd_assoc, lift_fst]
  have hs₁ : sO ≫ sliceP₁ = γ₁.val := by simp only [sO, sliceP₁, lift_snd_assoc, lift_fst]
  have hs₂ : sO ≫ sliceP₂ = γ₂.val := by simp only [sO, sliceP₂, lift_snd_assoc, lift_snd]
  have hsHead : sO ≫ sliceHead a b = α.val ≫ a.hom.hom * β.val ≫ b.hom.hom := by
    rw [comp_sliceHead, hsA, hsB]
  have hbaseS : aug ≫ sO = sliceIdentity := by
    apply slice_hom_ext
    · rw [Category.assoc, hsA, hidA]; exact aug_comp_lieKernel A α
    · rw [Category.assoc, hsB, hidB]; exact aug_comp_lieKernel B β
    · rw [Category.assoc, hs₀, hid₀]; exact aug_comp_lieKernel P₀ γ₀
    · rw [Category.assoc, hs₁, hid₁]; exact aug_comp_lieKernel P₁ γ₁
    · rw [Category.assoc, hs₂, hid₂]; exact aug_comp_lieKernel P₂ γ₂
  have hmap : sO ≫ tripleSliceMap a b p₀ p₁ p₂ = tt := by
    refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
    · rw [Category.assoc, comp_tripleSliceMap_fst, hsHead, hs₀, ← hZ₀, ← h₀]
      rfl
    refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
    · rw [Category.assoc, Category.assoc, comp_tripleSliceMap_snd_fst, hsHead, hs₁,
        Category.assoc, ← hZ₁, ← h₁]
      rfl
    · rw [Category.assoc, Category.assoc, comp_tripleSliceMap_snd_snd, hsHead, hs₂,
        Category.assoc, ← hZ₂, ← h₂]
      rfl
  exact ⟨sO.left, ⟨Over.w sO, congrArg CommaMorphism.left hbaseS⟩,
    congrArg CommaMorphism.left hmap⟩

end SliceTangent

section SliceOpen

open Langlands.AlgebraicGeometry.Picard Langlands.AlgebraicGeometry.TangentSmoothness

variable {k : Type u} [Field k] {G A B P₀ P₁ P₂ : GroupScheme (Spec (CommRingCat.of k))}
  (a : A ⟶ G) (b : B ⟶ G) (p₀ : P₀ ⟶ G) (p₁ : P₁ ⟶ G) (p₂ : P₂ ⟶ G)

/-- A smooth slice source, a monomorphic slice map and tangent surjectivity at the identity
give an open neighborhood of the identity of `G × G × G` all of whose rational points lift to
rational points of the slice source. -/
theorem exists_open_rationalLift_of_mono_of_isTangentSurjectiveAt
    [Smooth (sliceSource A B P₀ P₁ P₂).hom] [LocallyOfFiniteType (groupCube G).hom]
    [Mono (tripleSliceMap a b p₀ p₁ p₂)]
    (htan : IsTangentSurjectiveAt (sliceSource A B P₀ P₁ P₂).hom (groupCube G).hom
      (tripleSliceMap a b p₀ p₁ p₂).left
      (sliceIdentity : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶
        sliceSource A B P₀ P₁ P₂).left) :
    ∃ U : (groupCube G).left.Opens,
      ((sliceIdentity : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶
          sliceSource A B P₀ P₁ P₂) ≫ tripleSliceMap a b p₀ p₁ p₂).left
          (IsLocalRing.closedPoint k) ∈ U ∧
        ∀ y : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ groupCube G,
          y.left (IsLocalRing.closedPoint k) ∈ U →
            ∃ x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ sliceSource A B P₀ P₁ P₂,
              x ≫ tripleSliceMap a b p₀ p₁ p₂ = y := by
  set f := (tripleSliceMap a b p₀ p₁ p₂).left with hfdef
  have hf : f ≫ (groupCube G).hom = (sliceSource A B P₀ P₁ P₂).hom :=
    Over.w (tripleSliceMap a b p₀ p₁ p₂)
  have hx : IsRationalPoint (sliceSource A B P₀ P₁ P₂).hom
      (sliceIdentity : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶
        sliceSource A B P₀ P₁ P₂).left := Over.w _
  have := locallyOfFinitePresentation_of_comp_eq f hf
  have hz := mem_smoothLocus_of_isTangentSurjectiveAt f hf hx htan
  have hsm : Smooth (f.smoothLocus.ι ≫ f) := by
    rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq,
      Scheme.Opens.ι_preimage_self]
  have : Mono f := inferInstanceAs (Mono (tripleSliceMap a b p₀ p₁ p₂).left)
  have : IsOpenImmersion (f.smoothLocus.ι ≫ f) :=
    IsOpenImmersion.of_flat_of_mono (f.smoothLocus.ι ≫ f)
  refine ⟨(f.smoothLocus.ι ≫ f).opensRange, ?_, fun y hy => ?_⟩
  · exact ⟨⟨_, hz⟩, rfl⟩
  · have hrange : Set.range y.left ⊆ Set.range (f.smoothLocus.ι ≫ f) := by
      rintro _ ⟨z, rfl⟩
      have hzc : z = IsLocalRing.closedPoint k :=
        Subsingleton.elim (α := PrimeSpectrum k) _ _
      rw [hzc]
      exact hy
    let l := IsOpenImmersion.lift (f.smoothLocus.ι ≫ f) y.left hrange
    have hl : l ≫ f.smoothLocus.ι ≫ f = y.left := by
      rw [← Category.assoc]
      exact IsOpenImmersion.lift_fac _ _ hrange
    have hover : (l ≫ f.smoothLocus.ι) ≫ (sliceSource A B P₀ P₁ P₂).hom =
        (Over.mk (𝟙 (Spec (CommRingCat.of k)))).hom := by
      rw [← hf, Category.assoc, ← Category.assoc f.smoothLocus.ι, ← Category.assoc, hl]
      exact Over.w y
    refine ⟨Over.homMk (l ≫ f.smoothLocus.ι) hover, ?_⟩
    apply Over.OverMorphism.ext
    change (l ≫ f.smoothLocus.ι) ≫ f = y.left
    rw [Category.assoc]
    exact hl

end SliceOpen

section TripleParabolicLift

set_option maxHeartbeats 1600000

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [Smooth G.X.hom] [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] [ConnectedSpace G.X.left]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}

private theorem inv_mul_eq_mul_mul_inv_of_eq {Γ : Type*} [Group Γ] {a b a' b' x : Γ}
    (hx : (a * b)⁻¹ * (a' * b') = x) : a⁻¹ * a' = b * x * b'⁻¹ := by
  subst hx
  group

/-- Three cocharacters of a split torus of a smooth connected affine group, with zero sum,
each root negative at no more than one of them and vanishing at all three exactly when it
vanishes at the difference of the first two. There is an open neighborhood of the identity in
`G × G × G` such that every rational point `(g₀, g₁, g₂)` in it has a rational point `h` of `G`
with `h⁻¹ gᵢ` in the dynamic parabolic of the `i`-th cocharacter for each `i`. -/
theorem exists_open_tripleParabolic_rationalLift (hT : IsSplitTorus T.toGrp) (t : T.toGrp ⟶ G)
    (ν : Fin 3 → cocharacterLattice T) (hsum : ν 0 + ν 1 + ν 2 = 0)
    (hneg : ∀ α ∈ relativeRoots t, (∀ i, latticePairing T α (ν i) = 0) ∨
      ∃! i, latticePairing T α (ν i) < 0)
    (hzero : ∀ α ∈ relativeRoots t, latticePairing T α (ν 0 - ν 1) = 0 →
      ∀ i, latticePairing T α (ν i) = 0) :
    ∃ U : (groupCube G).left.Opens,
      (lift 1 (lift 1 1) : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ groupCube G).left
          (IsLocalRing.closedPoint k) ∈ U ∧
        ∀ g : Fin 3 → (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X),
          (lift (g 0) (lift (g 1) (g 2)) :
              Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ groupCube G).left
            (IsLocalRing.closedPoint k) ∈ U →
          ∃ h : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X, ∀ i,
            h⁻¹ * g i ∈ (Dynamic.parabolic (CommGroupScheme.groupHom (ν i) ≫ t)).carrier _ := by
  have hGa : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  set ν₀ := ν 0 - ν 1 with hν₀
  let χm := CommGroupScheme.groupHom (-ν₀) ≫ t
  let χp := CommGroupScheme.groupHom ν₀ ≫ t
  let a := Dynamic.Affine.unipotentHom χm
  let b := Dynamic.Affine.unipotentHom χp
  let p₀ := Dynamic.Affine.parabolicHom (CommGroupScheme.groupHom (ν 0) ≫ t)
  let p₁ := Dynamic.Affine.parabolicHom (CommGroupScheme.groupHom (ν 1) ≫ t)
  let p₂ := Dynamic.Affine.parabolicHom (CommGroupScheme.groupHom (ν 2) ≫ t)
  have ha := Dynamic.Affine.isRepresentedBy_unipotentHom χm
  have hb := Dynamic.Affine.isRepresentedBy_unipotentHom χp
  have hp₀ := Dynamic.Affine.isRepresentedBy_parabolicHom (CommGroupScheme.groupHom (ν 0) ≫ t)
  have hp₁ := Dynamic.Affine.isRepresentedBy_parabolicHom (CommGroupScheme.groupHom (ν 1) ≫ t)
  have hp₂ := Dynamic.Affine.isRepresentedBy_parabolicHom (CommGroupScheme.groupHom (ν 2) ≫ t)
  have : Mono a.hom.hom := ha.1
  have : Mono b.hom.hom := hb.1
  have : Mono p₀.hom.hom := hp₀.1
  have : Mono p₁.hom.hom := hp₁.1
  have : Mono p₂.hom.hom := hp₂.1
  have hsA := (dynamicSmooth k G χm _ a).2.2 ha
  have hsB := (dynamicSmooth k G χp _ b).2.2 hb
  have hs₀ := (dynamicSmooth k G _ _ p₀).1 hp₀
  have hs₁ := (dynamicSmooth k G _ _ p₁).1 hp₁
  have hs₂ := (dynamicSmooth k G _ _ p₂).1 hp₂
  have : Smooth (sliceSource (Dynamic.Affine.unipotentScheme χm)
      (Dynamic.Affine.unipotentScheme χp)
      (Dynamic.Affine.parabolicScheme (CommGroupScheme.groupHom (ν 0) ≫ t))
      (Dynamic.Affine.parabolicScheme (CommGroupScheme.groupHom (ν 1) ≫ t))
      (Dynamic.Affine.parabolicScheme (CommGroupScheme.groupHom (ν 2) ≫ t))).hom :=
    smooth_tensor _ _ hsA (smooth_tensor _ _ hsB (smooth_tensor _ _ hs₀
      (smooth_tensor _ _ hs₁ hs₂)))
  have : Smooth (groupCube G).hom :=
    smooth_tensor _ _ inferInstance (smooth_tensor _ _ inferInstance inferInstance)
  -- The intersection of the three parabolics.
  have hint := parabolic_inf_parabolic_inf_parabolic_eq_centralizer hT t (ν 0) (ν 1) (ν 2) hsum
    (fun α hα h => ⟨hzero α hα h 0, hzero α hα h 1, hzero α hα h 2⟩)
  -- The slice map is a monomorphism.
  have : Mono (tripleSliceMap a b p₀ p₁ p₂) := by
    refine mono_tripleSliceMap a b p₀ p₁ p₂ fun T' u u' v v' hx => ?_
    set x := ((u ≫ a.hom.hom) * (v ≫ b.hom.hom))⁻¹ * ((u' ≫ a.hom.hom) * (v' ≫ b.hom.hom))
      with hxdef
    have hxZ : x ∈ (Dynamic.centralizer χp).carrier T' := by
      rw [← hint]
      obtain ⟨⟨h₀, h₁⟩, h₂⟩ := hx
      rw [hp₀.2] at h₀
      rw [hp₁.2] at h₁
      rw [hp₂.2] at h₂
      exact ⟨⟨h₀, h₁⟩, h₂⟩
    have hAU (w : T' ⟶ _) : w ≫ a.hom.hom ∈ (Dynamic.unipotent χm).carrier T' := by
      rw [← ha.2]; exact SubgroupFunctor.mem_range.2 ⟨w, rfl⟩
    have hBU (w : T' ⟶ _) : w ≫ b.hom.hom ∈ (Dynamic.unipotent χp).carrier T' := by
      rw [← hb.2]; exact SubgroupFunctor.mem_range.2 ⟨w, rfl⟩
    have hrel := inv_mul_eq_mul_mul_inv_of_eq hxdef.symm
    have hopp : (u ≫ a.hom.hom)⁻¹ * (u' ≫ a.hom.hom) = 1 := by
      have hU : (u ≫ a.hom.hom)⁻¹ * (u' ≫ a.hom.hom) ∈
          (Dynamic.unipotent (Dynamic.oppositeCocharacter χp)).carrier T' := by
        have h := mul_mem (inv_mem (hAU u)) (hAU u')
        have hχm : χm = Dynamic.oppositeCocharacter χp :=
          groupHom_neg_comp_eq_oppositeCocharacter t ν₀
        have heq : Dynamic.unipotent χm = Dynamic.unipotent (Dynamic.oppositeCocharacter χp) :=
          congrArg Dynamic.unipotent hχm
        rw [← heq]
        exact h
      have hP : (u ≫ a.hom.hom)⁻¹ * (u' ≫ a.hom.hom) ∈ (Dynamic.parabolic χp).carrier T' := by
        rw [hrel]
        exact mul_mem (mul_mem (Dynamic.unipotent_le_parabolic χp T' (hBU v))
          (Dynamic.centralizer_le_parabolic χp T' hxZ))
          (inv_mem (Dynamic.unipotent_le_parabolic χp T' (hBU v')))
      have hbot := Dynamic.opposite_unipotent_inf_parabolic χp
      have hmem : (u ≫ a.hom.hom)⁻¹ * (u' ≫ a.hom.hom) ∈
          (Dynamic.unipotent (Dynamic.oppositeCocharacter χp) ⊓
            Dynamic.parabolic χp).carrier T' := ⟨hU, hP⟩
      rw [hbot] at hmem
      exact hmem
    have hu : u ≫ a.hom.hom = u' ≫ a.hom.hom := inv_mul_eq_one.1 hopp
    have hxU : x ∈ (Dynamic.unipotent χp).carrier T' := by
      have h1 : (v ≫ b.hom.hom) * x * (v' ≫ b.hom.hom)⁻¹ = 1 := hrel.symm.trans hopp
      have hx' : x = (v ≫ b.hom.hom)⁻¹ * (v' ≫ b.hom.hom) := by
        rw [mul_inv_eq_one] at h1
        rw [← h1]
        group
      rw [hx']
      exact mul_mem (inv_mem (hBU v)) (hBU v')
    have hx1 : x = 1 := Dynamic.eq_one_of_mem_centralizer_of_mem_unipotent χp
      (fun _ _ _ _ hl hl' => hl.unique χp hl') hxZ hxU
    have hv : v ≫ b.hom.hom = v' ≫ b.hom.hom := by
      have h1 : ((u ≫ a.hom.hom) * (v ≫ b.hom.hom))⁻¹ *
          ((u' ≫ a.hom.hom) * (v' ≫ b.hom.hom)) = 1 := hxdef.symm.trans hx1
      have h2 := inv_mul_eq_one.1 h1
      rw [hu] at h2
      exact mul_left_cancel h2
    exact ⟨(cancel_mono a.hom.hom).1 hu, (cancel_mono b.hom.hom).1 hv⟩
  -- Tangent surjectivity.
  have htan := isTangentSurjectiveAt_tripleSliceMap a b p₀ p₁ p₂ (by
    intro Z₀ Z₁ Z₂
    let Z : Fin 3 → Additive (lieKernel G k) :=
      ![Additive.ofMul Z₀, Additive.ofMul Z₁, Additive.ofMul Z₂]
    obtain ⟨A', hA', B', hB', hY⟩ := exists_lie_slice_decomposition hT t ν hneg hzero Z
    have liftU {H : GroupScheme (Spec (CommRingCat.of k))} (j : H ⟶ G)
        {F : SubgroupFunctor G} (hj : F.IsRepresentedBy j) (X : lieKernel G k)
        (hX : X.val ∈ F.carrier _) : ∃ Y : lieKernel H k, Lie.targetMap j k Y = X := by
      have : Mono j.hom.hom := hj.1
      rw [← hj.2] at hX
      obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.1 hX
      refine ⟨⟨y, mem_lieKernel_of_comp j y ?_⟩, Subtype.ext hy⟩
      change Lie.reduction G (y ≫ j.hom.hom) = 1
      rw [hy]
      exact X.property
    obtain ⟨α, hα⟩ := liftU a ha (Additive.toMul A') (by
      rw [(dynamicLie k G χm _).2.2, iSup_nat_succ_weightSpace_cocharacter hT (-ν₀) t]
      exact hA')
    obtain ⟨β, hβ⟩ := liftU b hb (Additive.toMul B') (by
      rw [(dynamicLie k G χp _).2.2, iSup_nat_succ_weightSpace_cocharacter hT ν₀ t]
      exact hB')
    obtain ⟨γ₀, hγ₀⟩ := liftU p₀ hp₀ (Additive.toMul (Z 0 - A' - B'))
      ((mem_nonnegativeWeightSpan_iff_mem_parabolic hT t (ν 0) _).1 (hY 0))
    obtain ⟨γ₁, hγ₁⟩ := liftU p₁ hp₁ (Additive.toMul (Z 1 - A' - B'))
      ((mem_nonnegativeWeightSpan_iff_mem_parabolic hT t (ν 1) _).1 (hY 1))
    obtain ⟨γ₂, hγ₂⟩ := liftU p₂ hp₂ (Additive.toMul (Z 2 - A' - B'))
      ((mem_nonnegativeWeightSpan_iff_mem_parabolic hT t (ν 2) _).1 (hY 2))
    have key (i : Fin 3) : Additive.toMul A' * Additive.toMul B' *
        Additive.toMul (Z i - A' - B') = Additive.toMul (Z i) := by
      rw [← toMul_add, ← toMul_add]
      congr 1
      abel
    refine ⟨α, β, γ₀, γ₁, γ₂, ?_, ?_, ?_⟩
    · rw [hα, hβ, hγ₀, key 0]; rfl
    · rw [hα, hβ, hγ₁, key 1]; rfl
    · rw [hα, hβ, hγ₂, key 2]; rfl)
  obtain ⟨U, hU, hlift⟩ := exists_open_rationalLift_of_mono_of_isTangentSurjectiveAt
    a b p₀ p₁ p₂ htan
  refine ⟨U, by rwa [sliceIdentity_comp_tripleSliceMap] at hU, fun g hg => ?_⟩
  obtain ⟨x, hx⟩ := hlift _ hg
  refine ⟨x ≫ sliceHead a b, fun i => ?_⟩
  have hcomp₀ : g 0 = (x ≫ sliceHead a b) * ((x ≫ sliceP₀) ≫ p₀.hom.hom) := by
    rw [← comp_tripleSliceMap_fst, ← Category.assoc, hx, lift_fst]
  have hcomp₁ : g 1 = (x ≫ sliceHead a b) * ((x ≫ sliceP₁) ≫ p₁.hom.hom) := by
    rw [← comp_tripleSliceMap_snd_fst, ← Category.assoc, hx, lift_snd_assoc, lift_fst]
  have hcomp₂ : g 2 = (x ≫ sliceHead a b) * ((x ≫ sliceP₂) ≫ p₂.hom.hom) := by
    rw [← comp_tripleSliceMap_snd_snd, ← Category.assoc, hx, lift_snd_assoc, lift_snd]
  fin_cases i
  · show (x ≫ sliceHead a b)⁻¹ * g 0 ∈
      (Dynamic.parabolic (CommGroupScheme.groupHom (ν 0) ≫ t)).carrier _
    rw [hcomp₀, inv_mul_cancel_left, ← hp₀.2]
    exact SubgroupFunctor.mem_range.2 ⟨_, rfl⟩
  · show (x ≫ sliceHead a b)⁻¹ * g 1 ∈
      (Dynamic.parabolic (CommGroupScheme.groupHom (ν 1) ≫ t)).carrier _
    rw [hcomp₁, inv_mul_cancel_left, ← hp₁.2]
    exact SubgroupFunctor.mem_range.2 ⟨_, rfl⟩
  · show (x ≫ sliceHead a b)⁻¹ * g 2 ∈
      (Dynamic.parabolic (CommGroupScheme.groupHom (ν 2) ≫ t)).carrier _
    rw [hcomp₂, inv_mul_cancel_left, ← hp₂.2]
    exact SubgroupFunctor.mem_range.2 ⟨_, rfl⟩

end TripleParabolicLift

end Langlands.GroupScheme
