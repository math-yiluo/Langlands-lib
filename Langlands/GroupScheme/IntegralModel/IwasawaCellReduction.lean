import Langlands.GroupScheme.IntegralModel.MaximalCompactStatement
import Langlands.GroupScheme.IntegralModel.LocalCompactPoints
import Langlands.AlgebraicGeometry.PointTopology.RepresentedSubgroup

/-! # Maximal compactness from opposite Iwasawa coverings and cell integrality -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology
open scoped ValuativeRel CategoryTheory.MonObj Pointwise

namespace Langlands.GroupScheme.IntegralModel

open Langlands.AlgebraicGeometry.PointTopology

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  (M : IntegralModel ↥𝒪[F] F G)

/-- Two closed subgroups `parabolic` and `oppositeParabolic` of the generic group, with
retractions onto a common subgroup `levi`, satisfying both Iwasawa coverings by the
original model image, maximality of the integral part of `levi` among compact subgroups
containing it, and integrality of the right factor of an integral product of elements of
the two retraction kernels. -/
structure IwasawaCellData where
  /-- The first subgroup. -/
  parabolic : GroupScheme (Spec (CommRingCat.of F))
  /-- The second subgroup. -/
  oppositeParabolic : GroupScheme (Spec (CommRingCat.of F))
  /-- The common retract. -/
  levi : GroupScheme (Spec (CommRingCat.of F))
  [parabolic_affine : IsAffineHom parabolic.X.hom]
  [oppositeParabolic_affine : IsAffineHom oppositeParabolic.X.hom]
  [levi_affine : IsAffineHom levi.X.hom]
  /-- The inclusion of the first subgroup into `G`. -/
  parabolicHom : parabolic ⟶ G
  /-- The inclusion of the second subgroup into `G`. -/
  oppositeParabolicHom : oppositeParabolic ⟶ G
  parabolicHom_closed : IsClosedImmersion parabolicHom.hom.hom.left
  oppositeParabolicHom_closed : IsClosedImmersion oppositeParabolicHom.hom.hom.left
  /-- The inclusion of the common retract into `G`. -/
  leviHom : levi ⟶ G
  /-- The common retract inside the first subgroup. -/
  leviSection : levi ⟶ parabolic
  /-- The common retract inside the second subgroup. -/
  oppositeLeviSection : levi ⟶ oppositeParabolic
  /-- The retraction of the first subgroup. -/
  leviProj : parabolic ⟶ levi
  /-- The retraction of the second subgroup. -/
  oppositeLeviProj : oppositeParabolic ⟶ levi
  leviSection_comp : leviSection ≫ parabolicHom = leviHom
  oppositeLeviSection_comp : oppositeLeviSection ≫ oppositeParabolicHom = leviHom
  leviSection_proj : leviSection ≫ leviProj = 𝟙 levi
  oppositeLeviSection_proj : oppositeLeviSection ≫ oppositeLeviProj = 𝟙 levi
  /-- `G(F) = P(F) · M(𝒪)`. -/
  iwasawa : Set.range (rationalPoints.map parabolicHom) *
    (M.integralPoints : Set (rationalPoints G)) = Set.univ
  /-- `G(F) = P⁻(F) · M(𝒪)`. -/
  oppositeIwasawa : Set.range (rationalPoints.map oppositeParabolicHom) *
    (M.integralPoints : Set (rationalPoints G)) = Set.univ
  /-- A compact subgroup of `Z(F)` containing every point that is integral in `G` consists
  of such points. -/
  levi_maximal :
    letI : IsAffine levi.X.left := isAffine_of_isAffineHom levi.X.hom
    letI : TopologicalSpace (rationalPoints levi) := rationalPointTopology F levi.X
    ∀ C : Subgroup (rationalPoints levi), IsCompact (C : Set (rationalPoints levi)) →
      M.integralPoints.comap (rationalPoints.map leviHom) ≤ C →
      C ≤ M.integralPoints.comap (rationalPoints.map leviHom)
  /-- If `v w` is integral, with `v` and `w` in the two retraction kernels, then `w` is
  integral. -/
  cell_integral : ∀ (v : rationalPoints oppositeParabolic) (w : rationalPoints parabolic),
    rationalPoints.map oppositeLeviProj v = 1 → rationalPoints.map leviProj w = 1 →
      rationalPoints.map oppositeParabolicHom v * rationalPoints.map parabolicHom w ∈
        M.integralPoints →
      rationalPoints.map parabolicHom w ∈ M.integralPoints

attribute [instance] IwasawaCellData.parabolic_affine IwasawaCellData.oppositeParabolic_affine
  IwasawaCellData.levi_affine

section Proof

variable [IsAffineHom G.X.hom]

private instance iwasawaGenericAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom

private instance iwasawaFieldHausdorff : T2Space F := by
  let := IsTopologicalAddGroup.rightUniformSpace F
  have := isUniformAddGroup_of_addCommGroup (G := F)
  infer_instance

local instance iwasawaGenericTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem rationalPoints_map_comp {H₁ H₂ H₃ : GroupScheme (Spec (CommRingCat.of F))}
    (f : H₁ ⟶ H₂) (g : H₂ ⟶ H₃) (x : rationalPoints H₁) :
    rationalPoints.map (f ≫ g) x = rationalPoints.map g (rationalPoints.map f x) := by
  simp only [rationalPoints.map_apply, Grp.comp_hom_hom, Category.assoc]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem rationalPoints_map_id {H : GroupScheme (Spec (CommRingCat.of F))}
    (x : rationalPoints H) : rationalPoints.map (𝟙 H) x = x := by
  simp only [rationalPoints.map_apply, Grp.id_hom_hom, Category.comp_id]

namespace IwasawaCellData

variable {M}

/-- The image under a retraction of the part of a compact subgroup lying in a closed
subgroup is compact. -/
private theorem isCompact_retract_image
    {P Z : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom P.X.hom]
    [IsAffineHom Z.X.hom] (i : P ⟶ G) (hi : IsClosedImmersion i.hom.hom.left)
    (p : P ⟶ Z) (L : Subgroup (rationalPoints G))
    (hL : IsCompact (L : Set (rationalPoints G))) :
    letI : IsAffine Z.X.left := isAffine_of_isAffineHom Z.X.hom
    letI : TopologicalSpace (rationalPoints Z) := rationalPointTopology F Z.X
    IsCompact (((L.comap (rationalPoints.map i)).map (rationalPoints.map p) :
      Subgroup (rationalPoints Z)) : Set (rationalPoints Z)) := by
  let : IsAffine P.X.left := isAffine_of_isAffineHom P.X.hom
  let : IsAffine Z.X.left := isAffine_of_isAffineHom Z.X.hom
  let : TopologicalSpace (rationalPoints P) := rationalPointTopology F P.X
  let : TopologicalSpace (rationalPoints Z) := rationalPointTopology F Z.X
  have : IsClosedImmersion i.hom.hom.left := hi
  have hemb : IsClosedEmbedding (rationalPoints.map i) :=
    isClosedEmbedding_rationalPointMap F i.hom.hom
  have hcont : Continuous (rationalPoints.map p) :=
    continuous_rationalPointMap F p.hom.hom
  have hpre : IsCompact ((rationalPoints.map i) ⁻¹' (L : Set (rationalPoints G))) :=
    hemb.isCompact_preimage hL
  simpa only [Subgroup.coe_map, Subgroup.coe_comap] using hpre.image hcont

/-- For a closed subgroup `P` with a retraction onto `Z`, a point of `P` lying in a compact
overgroup `L` of the model image has a factorization `k · w`, with `k` integral and `w` in
the retraction kernel and in `L`. -/
private theorem exists_kernel_factor
    {P Z : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom P.X.hom]
    [IsAffineHom Z.X.hom] (i : P ⟶ G) (hi : IsClosedImmersion i.hom.hom.left)
    (j : Z ⟶ G) (s : Z ⟶ P) (p : P ⟶ Z) (hsi : s ≫ i = j) (hsp : s ≫ p = 𝟙 Z)
    (hZ :
      letI : IsAffine Z.X.left := isAffine_of_isAffineHom Z.X.hom
      letI : TopologicalSpace (rationalPoints Z) := rationalPointTopology F Z.X
      ∀ C : Subgroup (rationalPoints Z), IsCompact (C : Set (rationalPoints Z)) →
        M.integralPoints.comap (rationalPoints.map j) ≤ C →
        C ≤ M.integralPoints.comap (rationalPoints.map j))
    (L : Subgroup (rationalPoints G)) (hL : IsCompact (L : Set (rationalPoints G)))
    (hML : M.integralPoints ≤ L) (b : rationalPoints P)
    (hb : rationalPoints.map i b ∈ L) :
    ∃ w : rationalPoints P, rationalPoints.map p w = 1 ∧ rationalPoints.map i w ∈ L ∧
      ∃ k ∈ M.integralPoints, rationalPoints.map i b = k * rationalPoints.map i w := by
  have hsec : ∀ z, rationalPoints.map p (rationalPoints.map s z) = z :=
    fun z => by rw [← rationalPoints_map_comp, hsp, rationalPoints_map_id]
  have hinc : ∀ z, rationalPoints.map i (rationalPoints.map s z) = rationalPoints.map j z :=
    fun z => by rw [← rationalPoints_map_comp, hsi]
  let t := rationalPoints.map p b
  have ht : rationalPoints.map j t ∈ M.integralPoints := by
    have hC := isCompact_retract_image i hi p L hL
    refine hZ _ hC ?_ ⟨b, hb, rfl⟩
    intro z hz
    refine ⟨rationalPoints.map s z, ?_, hsec z⟩
    show rationalPoints.map i (rationalPoints.map s z) ∈ L
    rw [hinc]
    exact hML hz
  refine ⟨(rationalPoints.map s t)⁻¹ * b, ?_, ?_, rationalPoints.map j t, ht, ?_⟩
  · rw [map_mul, map_inv, hsec]
    exact inv_mul_cancel t
  · rw [map_mul, map_inv, hinc]
    exact L.mul_mem (L.inv_mem (hML ht)) hb
  · rw [map_mul, map_inv, hinc, mul_inv_cancel_left]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] [IsAffineHom G.X.hom] in
/-- Every point lies in the integral image times the subgroup, with the subgroup factor on
the right. -/
private theorem exists_integral_mul
    {P : GroupScheme (Spec (CommRingCat.of F))} (i : P ⟶ G)
    (hcov : Set.range (rationalPoints.map i) *
      (M.integralPoints : Set (rationalPoints G)) = Set.univ)
    (g : rationalPoints G) :
    ∃ k ∈ M.integralPoints, ∃ b : rationalPoints P, g = k * rationalPoints.map i b := by
  have hg : g⁻¹ ∈ Set.range (rationalPoints.map i) *
      (M.integralPoints : Set (rationalPoints G)) := by
    rw [hcov]
    exact Set.mem_univ _
  obtain ⟨_, ⟨b, rfl⟩, k, hk, h⟩ := hg
  have h' : rationalPoints.map i b * k = g⁻¹ := h
  refine ⟨k⁻¹, M.integralPoints.inv_mem hk, b⁻¹, ?_⟩
  rw [map_inv, ← mul_inv_rev, h', inv_inv]

/-- Opposite Iwasawa coverings, maximality on the common retract and cell integrality
prove compactness and maximality of the original model image among compact subgroups. -/
theorem maximalCompact (D : IwasawaCellData M) :
    IsCompact (M.integralPoints : Set (rationalPoints G)) ∧
      ∀ L : Subgroup (rationalPoints G),
        IsCompact (L : Set (rationalPoints G)) → M.integralPoints ≤ L →
          L = M.integralPoints := by
  refine ⟨M.isCompact_integralPoints_localField, ?_⟩
  intro L hL hML
  apply le_antisymm ?_ hML
  intro l hl
  -- First Iwasawa covering and the first retraction.
  obtain ⟨k₁, hk₁, b, rfl⟩ := exists_integral_mul D.parabolicHom D.iwasawa l
  have hb : rationalPoints.map D.parabolicHom b ∈ L :=
    (L.mul_mem_cancel_left (hML hk₁)).mp hl
  obtain ⟨w, hw, hwL, k₂, hk₂, hbw⟩ :=
    exists_kernel_factor D.parabolicHom D.parabolicHom_closed D.leviHom D.leviSection
      D.leviProj D.leviSection_comp D.leviSection_proj D.levi_maximal L hL hML b hb
  -- Second Iwasawa covering applied to the kernel factor.
  obtain ⟨k₃, hk₃, c, hc⟩ :=
    exists_integral_mul D.oppositeParabolicHom D.oppositeIwasawa
      (rationalPoints.map D.parabolicHom w)
  have hcL : rationalPoints.map D.oppositeParabolicHom c ∈ L := by
    have : rationalPoints.map D.oppositeParabolicHom c =
        k₃⁻¹ * rationalPoints.map D.parabolicHom w := by
      rw [hc, inv_mul_cancel_left]
    rw [this]
    exact L.mul_mem (L.inv_mem (hML hk₃)) hwL
  obtain ⟨v, hv, -, k₄, hk₄, hcv⟩ :=
    exists_kernel_factor D.oppositeParabolicHom D.oppositeParabolicHom_closed D.leviHom
      D.oppositeLeviSection D.oppositeLeviProj D.oppositeLeviSection_comp
      D.oppositeLeviSection_proj D.levi_maximal L hL hML c hcL
  -- Cell integrality for `v · w⁻¹`.
  have hprod : rationalPoints.map D.oppositeParabolicHom v *
      rationalPoints.map D.parabolicHom w⁻¹ ∈ M.integralPoints := by
    have : rationalPoints.map D.oppositeParabolicHom v *
        rationalPoints.map D.parabolicHom w⁻¹ = (k₃ * k₄)⁻¹ := by
      rw [map_inv, mul_inv_eq_iff_eq_mul, mul_inv_rev, hc, hcv]
      group
    rw [this]
    exact M.integralPoints.inv_mem (M.integralPoints.mul_mem hk₃ hk₄)
  have hw' : rationalPoints.map D.leviProj w⁻¹ = 1 := by
    rw [map_inv, hw, inv_one]
  have hwK : rationalPoints.map D.parabolicHom w ∈ M.integralPoints := by
    have := D.cell_integral v w⁻¹ hv hw' hprod
    rw [map_inv] at this
    exact inv_mem_iff.mp this
  rw [hbw]
  exact M.integralPoints.mul_mem hk₁ (M.integralPoints.mul_mem hk₂ hwK)

end IwasawaCellData

end Proof

/-- An internal construction target: opposite Iwasawa cell data exist for every supplied
model with connected reductive full special fibre. No such datum is assumed. -/
def IwasawaCellDataStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (_hG : IsConnectedReductive G)
    (M : IntegralModel ↥𝒪[F] F G),
    IsConnectedReductive
      ((GroupScheme.baseChange (Spec.algebraMap ↥𝒪[F] 𝓀[F])).obj M.group) →
    Nonempty (IwasawaCellData M)

/-- Constructing opposite Iwasawa cell data would prove the exact published
maximal-compactness target, without any additional premise in that target. -/
theorem maximalCompactStatement_of_iwasawaCellData
    (h : IwasawaCellDataStatement.{u}) : MaximalCompactStatement.{u} := by
  intro F _ _ _ _ G hG M hspecial
  let : IsAffineHom G.X.hom := hG.isAffineHom
  obtain ⟨D⟩ := h F G hG M hspecial
  exact D.maximalCompact

end Langlands.GroupScheme.IntegralModel
