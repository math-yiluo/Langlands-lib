import Langlands.GroupScheme.Absolute.OppositeCellProof
import Langlands.GroupScheme.Dynamic.ParabolicProduct

/-! # Pulling opposite-cell factors back through a closed subgroup -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Dynamic

variable {k : Type u} [Field k]
  {H G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ H)
  (f : H ⟶ G) (hf : IsClosedSubgroup f)

local instance preimageSectionsAlgebra (T : Over (Spec (CommRingCat.of k))) :
    Algebra k Γ(T.left, ⊤) :=
  ((algΓ (CommRingCat.of k)).obj T).unop.algebra

include hf in
set_option backward.isDefEq.respectTransparency false in
/-- A closed subgroup containing the cocharacter contains both factors of any
opposite unipotent-parabolic decomposition of one of its points. -/
theorem exists_opposite_factors_of_isClosedSubgroup
    {T : Over (Spec (CommRingCat.of k))} (g : T ⟶ H.X) (m p : T ⟶ G.X)
    (hm : m ∈ (unipotent (CommGroupScheme.groupHom
      (Gm.powerHom _ (-1)) ≫ (χ ≫ f))).carrier T)
    (hp : p ∈ (parabolic (χ ≫ f)).carrier T)
    (hmp : m * p = g ≫ f.hom.hom) :
    ∃ (m₀ p₀ : T ⟶ H.X),
      m₀ ∈ (unipotent (CommGroupScheme.groupHom
        (Gm.powerHom _ (-1)) ≫ χ)).carrier T ∧
      p₀ ∈ (parabolic χ).carrier T ∧
      m₀ ≫ f.hom.hom = m ∧ p₀ ≫ f.hom.hom = p ∧ m₀ * p₀ = g := by
  obtain ⟨N, ρ, hρ⟩ := affineLinearEmbeddingStatement k G inferInstance inferInstance
  obtain ⟨a, e, he⟩ :=
    GeneralLinear.exists_innerIso_comp_eq_diagonalCocharacter k ((χ ≫ f) ≫ ρ)
  let conjIso := (GeneralLinear.groupScheme (Fin N) (CommRingCat.of k)).innerIso a
  let τ := ρ ≫ conjIso.hom
  let σ := f ≫ τ
  have : IsClosedImmersion f.hom.hom.left := hf
  have : Mono f.hom.hom := Over.mono_of_mono_left _
  have : IsClosedImmersion ρ.hom.hom.left := hρ
  have : IsIso conjIso.hom.hom.hom.left :=
    (inferInstance : IsIso ((Over.forget _).mapIso ((Grp.forget _).mapIso conjIso)).hom)
  have : IsClosedImmersion τ.hom.hom.left :=
    (inferInstance : IsClosedImmersion (ρ.hom.hom.left ≫ conjIso.hom.hom.hom.left))
  have : Mono τ.hom.hom := Over.mono_of_mono_left _
  have : IsClosedImmersion σ.hom.hom.left :=
    (inferInstance : IsClosedImmersion (f.hom.hom.left ≫ τ.hom.hom.left))
  have hχτ : (χ ≫ f) ≫ τ = GeneralLinear.diagonalCocharacter _ _ e := by
    simpa only [τ, Category.assoc] using he
  have hχσ : χ ≫ σ = GeneralLinear.diagonalCocharacter _ _ e := by
    simpa only [σ, Category.assoc] using hχτ
  have hmτ := unipotent_le_comap
    (CommGroupScheme.groupHom (Gm.powerHom _ (-1)) ≫ (χ ≫ f)) τ T hm
  rw [SubgroupFunctor.mem_comap, Category.assoc, hχτ,
    GeneralLinear.inv_comp_diagonalCocharacter,
    GeneralLinear.unipotent_diagonalCocharacter] at hmτ
  have hpτ := parabolic_le_comap (χ ≫ f) τ T hp
  rw [SubgroupFunctor.mem_comap, hχτ,
    GeneralLinear.parabolic_diagonalCocharacter] at hpτ
  have hz : GeneralLinear.pointsEquiv _ _ T (p ≫ τ.hom.hom) ∈
      GeneralLinear.zeroLocus Γ(T.left, ⊤) (embeddingIdeal σ) := by
    apply GeneralLinear.mem_zeroLocus_of_mul_mem e
      (ideal_le_embeddingIdeal (ρ := σ))
      (zeroLocusMulClosed_embeddingIdeal (ρ := σ))
      (one_mem_zeroLocus_embeddingIdeal (ρ := σ))
      (diagonalUnits_mem_zeroLocus_embeddingIdeal (ρ := σ) hχσ) hmτ hpτ
    rw [← map_mul, ← MonObj.mul_comp, hmp, Category.assoc, ← Grp.comp_hom_hom]
    exact pointsEquiv_comp_mem_zeroLocus (ρ := σ) g
  obtain ⟨p₀, hp₀⟩ := exists_comp_eq_of_mem_zeroLocus (ρ := σ)
    (p ≫ τ.hom.hom) hz
  have hp₀f : p₀ ≫ f.hom.hom = p := by
    apply (cancel_mono τ.hom.hom).mp
    simpa only [σ, Grp.comp_hom_hom, Category.assoc] using hp₀
  have hp₀P : p₀ ∈ (parabolic χ).carrier T := by
    rw [parabolic_eq_comap_of_isClosedSubgroup χ f hf, SubgroupFunctor.mem_comap, hp₀f]
    exact hp
  let m₀ := g * p₀⁻¹
  have hm₀f : m₀ ≫ f.hom.hom = m := by
    dsimp only [m₀]
    rw [MonObj.mul_comp, GrpObj.inv_comp, hp₀f, ← hmp, mul_inv_cancel_right]
  have hm₀U : m₀ ∈ (unipotent (CommGroupScheme.groupHom
      (Gm.powerHom _ (-1)) ≫ χ)).carrier T := by
    rw [unipotent_eq_comap_of_isClosedSubgroup _ f hf, SubgroupFunctor.mem_comap,
      Category.assoc, hm₀f]
    exact hm
  exact ⟨m₀, p₀, hm₀U, hp₀P, hm₀f, hp₀f, inv_mul_cancel_right _ _⟩

/-- The lifted opposite factors, together with their membership, image, and
product identities. -/
def oppositeFactorLift
    {T : Over (Spec (CommRingCat.of k))} (g : T ⟶ H.X) (m p : T ⟶ G.X)
    (hm : m ∈ (unipotent (CommGroupScheme.groupHom
      (Gm.powerHom _ (-1)) ≫ (χ ≫ f))).carrier T)
    (hp : p ∈ (parabolic (χ ≫ f)).carrier T)
    (hmp : m * p = g ≫ f.hom.hom) :
    {mp : (T ⟶ H.X) × (T ⟶ H.X) //
      mp.1 ∈ (unipotent (CommGroupScheme.groupHom
        (Gm.powerHom _ (-1)) ≫ χ)).carrier T ∧
      mp.2 ∈ (parabolic χ).carrier T ∧
      mp.1 ≫ f.hom.hom = m ∧ mp.2 ≫ f.hom.hom = p ∧ mp.1 * mp.2 = g} :=
  Classical.choice <| by
    obtain ⟨m₀, p₀, h⟩ := exists_opposite_factors_of_isClosedSubgroup χ f hf g m p hm hp hmp
    exact ⟨⟨(m₀, p₀), h⟩⟩

include hf in
/-- A closed subgroup containing the cocharacter contains each of the three
dynamic factors of any triple-cell decomposition of one of its points. -/
theorem exists_triple_factors_of_isClosedSubgroup
    {T : Over (Spec (CommRingCat.of k))} (g : T ⟶ H.X) (m z v : T ⟶ G.X)
    (hm : m ∈ (unipotent (CommGroupScheme.groupHom
      (Gm.powerHom _ (-1)) ≫ (χ ≫ f))).carrier T)
    (hz : z ∈ (centralizer (χ ≫ f)).carrier T)
    (hv : v ∈ (unipotent (χ ≫ f)).carrier T)
    (hmzv : m * (z * v) = g ≫ f.hom.hom) :
    ∃ (m₀ z₀ v₀ : T ⟶ H.X),
      m₀ ∈ (unipotent (CommGroupScheme.groupHom
        (Gm.powerHom _ (-1)) ≫ χ)).carrier T ∧
      z₀ ∈ (centralizer χ).carrier T ∧ v₀ ∈ (unipotent χ).carrier T ∧
      m₀ ≫ f.hom.hom = m ∧ z₀ ≫ f.hom.hom = z ∧
      v₀ ≫ f.hom.hom = v ∧ m₀ * (z₀ * v₀) = g := by
  have : IsClosedImmersion f.hom.hom.left := hf
  have : IsSeparated H.X.hom := by
    rw [← Over.w f.hom.hom]
    infer_instance
  have hp := (hasLimit_centralizer_mul_unipotent (χ ≫ f) hz hv).mem_parabolic (χ ≫ f)
  obtain ⟨m₀, p₀, hm₀, hp₀, hm₀f, hp₀f, hmp⟩ :=
    exists_opposite_factors_of_isClosedSubgroup χ f hf g m (z * v) hm hp hmzv
  let z₀ := limit χ ⟨p₀, hp₀⟩
  let v₀ := z₀⁻¹ * p₀
  have hz₀f : z₀ ≫ f.hom.hom = z := by
    have h := (hasLimit_limit χ ⟨p₀, hp₀⟩).comp_hom χ f
    rw [hp₀f] at h
    exact h.unique (χ ≫ f) (hasLimit_centralizer_mul_unipotent (χ ≫ f) hz hv)
  have hv₀f : v₀ ≫ f.hom.hom = v := by
    dsimp only [v₀]
    rw [MonObj.mul_comp, GrpObj.inv_comp, hz₀f, hp₀f, inv_mul_cancel_left]
  refine ⟨m₀, z₀, v₀, hm₀, limit_mem_centralizer χ ⟨p₀, hp₀⟩,
    inv_limit_mul_mem_unipotent χ ⟨p₀, hp₀⟩, hm₀f, hz₀f, hv₀f, ?_⟩
  dsimp only [v₀]
  rw [mul_inv_cancel_left, hmp]

end Langlands.GroupScheme.Dynamic
