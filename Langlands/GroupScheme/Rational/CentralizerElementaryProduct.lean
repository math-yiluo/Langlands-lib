import Langlands.GroupScheme.Rational.DynamicCellTransporter
import Langlands.GroupScheme.Rational.DynamicElementarySubgroup
import Langlands.GroupScheme.Rational.LocalFieldDensity
import Langlands.GroupScheme.Reductive.RationalPointDensityProof

/-! # Rational points as centralizer points times the elementary subgroup -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace Dynamic

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}

/-- The cocharacter `t ↦ χ(t⁻¹)` used for the opposite open cell. -/
local notation "opp" χ =>
  CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫ χ

/-- The opposite-cell multiplication morphism `U_G(χ⁻¹) × P_G(χ) → G`, `(u, p) ↦ u * p`,
on the chosen closed affine models of `U_G(χ⁻¹)` and `P_G(χ)`. -/
abbrev oppositeCellMul [IsAffine G.X.left] (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) :
    (Affine.unipotentScheme (opp χ)).X ⊗ (Affine.parabolicScheme χ).X ⟶ G.X :=
  (fst _ _ ≫ (Affine.unipotentHom (opp χ)).hom.hom) * (snd _ _ ≫ (Affine.parabolicHom χ).hom.hom)

/-- For a smooth affine group, the opposite-cell multiplication morphism is an open immersion. -/
theorem isOpenImmersion_oppositeCellMul [Smooth G.X.hom] [IsAffineHom G.X.hom]
    [IsAffine G.X.left] (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) :
    IsOpenImmersion (oppositeCellMul χ).left :=
  oppositeCellStatement k G χ _ _ (Affine.unipotentHom (opp χ)) (Affine.parabolicHom χ)
    (Affine.isRepresentedBy_unipotentHom (opp χ)) (Affine.isRepresentedBy_parabolicHom χ)

/-- A rational point in the opposite open cell `U_G(χ⁻¹) × P_G(χ)` lies in
`N * z` for a rational point `z` of `Z_G(χ)`, when the normal subgroup `N`
contains the rational points of `U_G(χ)` and `U_G(χ⁻¹)`. -/
theorem exists_centralizer_of_mem_cell [Smooth G.X.hom] [IsAffineHom G.X.hom]
    [IsAffine G.X.left]
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) (N : Subgroup (rationalPoints G))
    (hU : (unipotent χ).rationalPoints ≤ N) (hU' : (unipotent (opp χ)).rationalPoints ≤ N)
    (c : rationalPoints G) (hc : Set.range c.left ⊆ Set.range (oppositeCellMul χ).left) :
    ∃ z ∈ (centralizer χ).rationalPoints, c * z⁻¹ ∈ N := by
  let iU := Affine.unipotentHom (opp χ)
  let iP := Affine.parabolicHom χ
  have hUrep := Affine.isRepresentedBy_unipotentHom (opp χ)
  have hPrep := Affine.isRepresentedBy_parabolicHom χ
  let m := oppositeCellMul χ
  have : IsOpenImmersion m.left := isOpenImmersion_oppositeCellMul χ
  let l := FiniteEtaleImage.liftOver m c hc
  have hl : l ≫ m = c := FiniteEtaleImage.liftOver_fac _ _ _
  let um : rationalPoints G := l ≫ fst _ _ ≫ iU.hom.hom
  let p : rationalPoints G := l ≫ snd _ _ ≫ iP.hom.hom
  have hcp : c = um * p := by
    rw [← hl, MonObj.comp_mul]
  have hum : um ∈ N := by
    apply hU'
    change um ∈ (unipotent (opp χ)).carrier _
    rw [← hUrep.2]
    exact ⟨l ≫ fst _ _, by
      change (l ≫ fst _ _) ≫ iU.hom.hom = l ≫ fst _ _ ≫ iU.hom.hom
      rw [Category.assoc]⟩
  have hp : p ∈ (parabolic χ).carrier _ := by
    rw [← hPrep.2]
    exact ⟨l ≫ snd _ _, by
      change (l ≫ snd _ _) ≫ iP.hom.hom = l ≫ snd _ _ ≫ iP.hom.hom
      rw [Category.assoc]⟩
  obtain ⟨z, hz⟩ := exists_hasLimit χ hp
  have hzc : z ∈ (centralizer χ).carrier _ := hz.mem_centralizer χ
  have hu : p * z⁻¹ ∈ (unipotent χ).carrier _ := by
    change HasLimit χ (p * z⁻¹) 1
    simpa only [mul_inv_cancel] using hz.mul χ ((hasLimit_of_mem_centralizer χ hzc).inv χ)
  refine ⟨z, hzc, ?_⟩
  rw [hcp, mul_assoc]
  exact N.mul_mem hum (hU hu)

/-- In a smooth connected group with dense rational points, every rational point `g` is
`c * (c⁻¹ * g)` with both factors in a given nonempty open set. -/
theorem exists_mem_open_inv_mul_mem_open [Smooth G.X.hom] [ConnectedSpace G.X.left]
    (hd : HasDenseRationalPoints k G.X) {O : Set G.X.left} (hO : IsOpen O) (hne : O.Nonempty)
    (g : rationalPoints G) :
    ∃ c : rationalPoints G, Set.range c.left ⊆ O ∧ Set.range (c⁻¹ * g).left ⊆ O := by
  have : IrreducibleSpace G.X.left := DynamicConnected.irreducibleSpace_of_smooth G
  let σ : G.X ⟶ G.X := (𝟙 G.X)⁻¹ * (toUnit G.X ≫ g)
  let σ' : G.X ⟶ G.X := (toUnit G.X ≫ g) * (𝟙 G.X)⁻¹
  have hσσ' : σ' ≫ σ = 𝟙 G.X := by
    simp only [σ, σ', MonObj.comp_mul, GrpObj.comp_inv, Category.comp_id, comp_toUnit_assoc,
      mul_inv_rev, inv_inv]
    group
  have hsurj : Function.Surjective σ.left := by
    intro x
    refine ⟨σ'.left x, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hσσ', Over.id_left]
    rfl
  have hO₂ : IsOpen (σ.left ⁻¹' O) := hO.preimage σ.left.continuous
  have hne₂ : (σ.left ⁻¹' O).Nonempty := by
    obtain ⟨x, hx⟩ := hne
    obtain ⟨w, rfl⟩ := hsurj x
    exact ⟨w, hx⟩
  obtain ⟨x, ⟨hxO, hxO₂⟩, hx⟩ := hd.inter_open_nonempty _ (hO.inter hO₂)
    (nonempty_preirreducible_inter hO hO₂ hne hne₂)
  obtain ⟨c, y, rfl⟩ := Set.mem_iUnion.mp hx
  have hcσ : c ≫ σ = c⁻¹ * g := by
    have h1 : c ≫ toUnit G.X = 𝟙 _ := toUnit_unique _ _
    simp only [σ, MonObj.comp_mul, GrpObj.comp_inv, Category.comp_id, ← Category.assoc, h1,
      Category.id_comp]
  refine ⟨c, ?_, ?_⟩
  · rintro _ ⟨y', rfl⟩
    rwa [Subsingleton.elim (α := PrimeSpectrum k) y' y]
  · rintro _ ⟨y', rfl⟩
    rw [← hcσ, Subsingleton.elim (α := PrimeSpectrum k) y' y, Over.comp_left, Scheme.Hom.comp_apply]
    exact hxO₂

/-- **Rational points modulo a normal subgroup containing opposite contracting points.**
Let `G` be a smooth connected affine group over a field `k` with Zariski dense rational
points, and `χ` a cocharacter of `G`. If a normal subgroup `N` of `G(k)` contains the rational
points of `U_G(χ)` and `U_G(χ⁻¹)`, then every rational point lies in `N * z` for some rational
point `z` of the centralizer `Z_G(χ)`. -/
theorem exists_centralizer_mul_inv_mem [Smooth G.X.hom] [IsAffineHom G.X.hom]
    [ConnectedSpace G.X.left] (hd : HasDenseRationalPoints k G.X)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) (N : Subgroup (rationalPoints G)) [N.Normal]
    (hU : (unipotent χ).rationalPoints ≤ N) (hU' : (unipotent (opp χ)).rationalPoints ≤ N)
    (g : rationalPoints G) :
    ∃ z ∈ (centralizer χ).rationalPoints, g * z⁻¹ ∈ N := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let m := oppositeCellMul χ
  have : IsOpenImmersion m.left := isOpenImmersion_oppositeCellMul χ
  have hne : (Set.range m.left).Nonempty :=
    ⟨_, ⟨(lift (1 : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ (Affine.unipotentScheme (opp χ)).X)
      (1 : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ (Affine.parabolicScheme χ).X)).left
        (IsLocalRing.closedPoint k), rfl⟩⟩
  obtain ⟨c, hc, hcg⟩ := exists_mem_open_inv_mul_mem_open hd m.left.isOpenEmbedding.isOpen_range
    hne g
  obtain ⟨z₁, hz₁, h₁⟩ := exists_centralizer_of_mem_cell χ N hU hU' c hc
  obtain ⟨z₂, hz₂, h₂⟩ := exists_centralizer_of_mem_cell χ N hU hU' (c⁻¹ * g) hcg
  refine ⟨z₁ * z₂, Subgroup.mul_mem _ hz₁ hz₂, ?_⟩
  have heq : g * (z₁ * z₂)⁻¹ = c * z₁⁻¹ * (z₁ * (c⁻¹ * g * z₂⁻¹) * z₁⁻¹) := by group
  rw [heq]
  exact N.mul_mem h₁ (Subgroup.Normal.conj_mem inferInstance _ h₂ z₁)

end Dynamic

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}

/-- **Rational points modulo the parabolic elementary subgroup.** For a connected reductive
group `G` over a field `k` with Zariski dense rational points and a cocharacter `χ` of `G`,
every rational point of `G` is `e * z` with `e` in the subgroup generated by the rational points
of all parabolic unipotent radicals and `z` a rational point of the centralizer `Z_G(χ)`. -/
theorem exists_parabolicElementarySubgroup_mul_centralizer (hG : IsConnectedReductive G)
    (hd : HasDenseRationalPoints k G.X) (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (g : rationalPoints G) :
    ∃ e ∈ parabolicElementarySubgroup G, ∃ z ∈ (Dynamic.centralizer χ).rationalPoints,
      g = e * z := by
  have := hG.smooth
  have := hG.isAffineHom
  have := hG.connectedSpace
  obtain ⟨z, hz, he⟩ := Dynamic.exists_centralizer_mul_inv_mem hd χ
    (parabolicElementarySubgroup G) (dynamicUnipotent_le_parabolicElementarySubgroup hG χ)
    (dynamicUnipotent_le_parabolicElementarySubgroup hG _) g
  exact ⟨g * z⁻¹, he, z, hz, by group⟩

/-- The centralizer of a cocharacter and the parabolic elementary subgroup generate the
rational points of a connected reductive group with Zariski dense rational points. -/
theorem centralizer_rationalPoints_sup_parabolicElementarySubgroup
    (hG : IsConnectedReductive G) (hd : HasDenseRationalPoints k G.X)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) :
    (Dynamic.centralizer χ).rationalPoints ⊔ parabolicElementarySubgroup G = ⊤ := by
  refine eq_top_iff.mpr fun g _ => ?_
  obtain ⟨e, he, z, hz, rfl⟩ := exists_parabolicElementarySubgroup_mul_centralizer hG hd χ g
  rw [sup_comm]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left he) (Subgroup.mem_sup_right hz)

/-- Over an infinite field, the centralizer of a cocharacter and the parabolic elementary
subgroup generate the rational points of a connected reductive group. -/
theorem centralizer_rationalPoints_sup_parabolicElementarySubgroup_of_infinite [Infinite k]
    (hG : IsConnectedReductive G) (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) :
    (Dynamic.centralizer χ).rationalPoints ⊔ parabolicElementarySubgroup G = ⊤ :=
  centralizer_rationalPoints_sup_parabolicElementarySubgroup hG
    (reductiveRationalPointDensity k G hG) χ

/-- Over a nonarchimedean local field, the centralizer of a cocharacter and the parabolic
elementary subgroup generate the rational points of a connected reductive group. -/
theorem centralizer_rationalPoints_sup_parabolicElementarySubgroup_of_localField
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} (hG : IsConnectedReductive G)
    (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) :
    (Dynamic.centralizer χ).rationalPoints ⊔ parabolicElementarySubgroup G = ⊤ := by
  have := hG.smooth
  have := hG.isAffineHom
  have := hG.connectedSpace
  exact centralizer_rationalPoints_sup_parabolicElementarySubgroup hG
    (hasDenseRationalPoints_of_localField F G) χ

end Langlands.GroupScheme
