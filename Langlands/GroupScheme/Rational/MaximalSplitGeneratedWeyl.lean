import Langlands.GroupScheme.Rational.MaximalSplitRankOneRelation
import Langlands.GroupScheme.Reductive.RootwiseWeylReductivity
import Langlands.GroupScheme.Torus.TransporterFunctoriality

/-! # Weyl transport of rootwise data -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme.MaximalSplitSubgroup

section Inversion

variable {K : Type u} [Field K] {T : CommGroupScheme (Spec (CommRingCat.of K))}
  {H : GroupScheme (Spec (CommRingCat.of K))}

/-- A *Weyl inversion* of a character `χ` of `T` inside `H`: a rational point `n` of `H`
normalizing `t` through an automorphism `σ` of `T` with `χ ∘ σ = -χ` that fixes every
cocharacter orthogonal to `χ`. -/
def HasWeylInversion (t : T.toGrp ⟶ H) (χ : characterLattice T) : Prop :=
  ∃ (σ : T ≅ T) (n : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ H.X),
    IsNormalizingPoint t n σ ∧ σ.hom ≫ χ = -χ ∧
      ∀ ξ : cocharacterLattice T, latticePairing T χ ξ = 0 → ξ ≫ σ.hom = ξ

/-- Precomposing a character with an endomorphism of `T` is postcomposing the cocharacter. -/
theorem latticePairing_comp (f : T ⟶ T) (χ : characterLattice T) (ξ : cocharacterLattice T) :
    latticePairing T (f ≫ χ) ξ = latticePairing T χ (ξ ≫ f) := by
  simp only [latticePairing, LinearMap.mk₂_apply, Category.assoc]

/-- Conjugating a Weyl inversion by a normalizing point gives a Weyl inversion of the
transported character. -/
theorem HasWeylInversion.transport {t : T.toGrp ⟶ H} {χ : characterLattice T}
    (h : HasWeylInversion t χ) {m : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ H.X} {τ : T ≅ T}
    (hm : IsNormalizingPoint t m τ) : HasWeylInversion t (τ.inv ≫ χ) := by
  obtain ⟨σ, n, hn, hσχ, hfix⟩ := h
  refine ⟨τ.symm ≪≫ σ ≪≫ τ, m * n * m⁻¹, (hm.mul hn).mul hm.inv, ?_, ?_⟩
  · simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc, hσχ,
      Preadditive.comp_neg]
  · intro ξ hξ
    have hξ' : latticePairing T χ (ξ ≫ τ.inv) = 0 := by
      rw [← latticePairing_comp]
      exact hξ
    simp only [Iso.trans_hom, Iso.symm_hom]
    rw [← Category.assoc ξ τ.inv (σ.hom ≫ τ.hom), ← Category.assoc (ξ ≫ τ.inv) σ.hom τ.hom,
      hfix _ hξ', Category.assoc, Iso.inv_hom_id,
      Category.comp_id]

/-- A normalizing point through the reflection `s_a` gives a Weyl inversion of `a`. -/
theorem hasWeylInversion_of_reflection {t : T.toGrp ⟶ H} {a : characterLattice T}
    {ν : cocharacterLattice T} (hpair : latticePairing T a ν = 2)
    {n : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ H.X}
    (hn : IsNormalizingPoint t n (latticeReflectionIso a ν hpair)) : HasWeylInversion t a := by
  refine ⟨latticeReflectionIso a ν hpair, n, hn, reflection_comp_root ν hpair, ?_⟩
  intro ξ hξ
  rw [cocharacter_comp_reflection hpair, hξ, zero_smul, sub_zero]

/-- The torus automorphism `σ` as an automorphism of the underlying group scheme. -/
def torusGrpIso (σ : T ≅ T) : T.toGrp ≅ T.toGrp where
  hom := CommGroupScheme.groupHom σ.hom
  inv := CommGroupScheme.groupHom σ.inv
  hom_inv_id := congrArg CommGroupScheme.groupHom σ.hom_inv_id
  inv_hom_id := congrArg CommGroupScheme.groupHom σ.inv_hom_id

/-- A Weyl inversion gives the rootwise Weyl datum of `RootwiseWeyl.isConnectedReductive_of_rootwiseWeyl`. -/
theorem HasWeylInversion.exists_transporter [IsAffineHom H.X.hom] {t : T.toGrp ⟶ H}
    {χ : characterLattice T} (h : HasWeylInversion t χ) :
    ∃ (c : T.toGrp ≅ T.toGrp) (n : Lie.AffinePoints H K),
      c.hom ≫ CommGroupScheme.groupHom χ = CommGroupScheme.groupHom (-χ) ∧
        (∀ ν : cocharacterLattice T, latticePairing T χ ν = 0 →
          CommGroupScheme.groupHom ν ≫ c.hom = CommGroupScheme.groupHom ν) ∧
        PointwiseSchemeAction.IsTransporter (c.hom ≫ t) t n := by
  obtain ⟨σ, n, hn, hσχ, hfix⟩ := h
  refine ⟨torusGrpIso σ, (Lie.affineSelfTestIso (CommRingCat.of K)).hom ≫ n,
    congrArg CommGroupScheme.groupHom hσχ, fun ν hν => congrArg CommGroupScheme.groupHom
      (hfix ν hν), ?_⟩
  exact hn.isTransporter.restrict _

end Inversion

section Transport

variable {K : Type u} [Field K] {T : CommGroupScheme (Spec (CommRingCat.of K))}
  {H : GroupScheme (Spec (CommRingCat.of K))}

/-- A character transported by a torus automorphism is zero only if it was. -/
theorem iso_inv_comp_ne_zero_iff (τ : T ≅ T) (χ : characterLattice T) :
    τ.inv ≫ χ ≠ 0 ↔ χ ≠ 0 := by
  refine not_congr ⟨fun h => ?_, fun h => by rw [h, Limits.comp_zero]⟩
  rw [← Iso.hom_inv_id_assoc τ χ, h, Limits.comp_zero]

variable [IsAffineHom H.X.hom] {t : T.toGrp ⟶ H}

/-- The adjoint action of a base point is injective. -/
theorem basePointAdjoint_injective (n : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ H.X) :
    Function.Injective (basePointAdjoint n) := by
  intro X Y hXY
  have := congrArg (basePointAdjoint n⁻¹) hXY
  change (basePointAdjoint n⁻¹ * basePointAdjoint n) X =
    (basePointAdjoint n⁻¹ * basePointAdjoint n) Y at this
  rwa [basePointAdjoint_inv_mul, Module.End.one_apply, Module.End.one_apply] at this

/-- A normalizing point permutes the roots. -/
theorem mem_roots_iff_of_isNormalizingPoint {n : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ H.X}
    {τ : T ≅ T} (hn : IsNormalizingPoint t n τ) (χ : characterLattice T) :
    τ.inv ≫ χ ∈ roots t ↔ χ ∈ roots t := by
  rw [mem_roots, mem_roots, iso_inv_comp_ne_zero_iff,
    Ne, Ne, weightSpace_eq_bot_iff_of_isNormalizingPoint hn χ]

/-- A normalizing point preserves the dimensions of weight spaces. -/
theorem finrank_weightSpace_of_isNormalizingPoint
    {n : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ H.X}
    {τ : T ≅ T} (hn : IsNormalizingPoint t n τ) (χ : characterLattice T) :
    Module.finrank K (weightSpace t (τ.inv ≫ χ)) = Module.finrank K (weightSpace t χ) := by
  rw [← hn.map_weightSpace χ]
  exact (Submodule.equivMapOfInjective _ (basePointAdjoint_injective n)
    (weightSpace t χ)).finrank_eq.symm

/-- The rootwise datum transported by Weyl points: `χ` is a root, its weight space is a
line, and it has a Weyl inversion. -/
def IsWeylLineRoot (t : T.toGrp ⟶ H) (χ : characterLattice T) : Prop :=
  χ ∈ roots t ∧ Module.finrank K (weightSpace t χ) = 1 ∧ HasWeylInversion t χ

/-- Normalizing points transport the rootwise datum. -/
theorem IsWeylLineRoot.transport {χ : characterLattice T} (h : IsWeylLineRoot t χ)
    {m : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ H.X} {τ : T ≅ T}
    (hm : IsNormalizingPoint t m τ) : IsWeylLineRoot t (τ.inv ≫ χ) :=
  ⟨(mem_roots_iff_of_isNormalizingPoint hm χ).mpr h.1,
    (finrank_weightSpace_of_isNormalizingPoint hm χ).trans h.2.1, h.2.2.transport hm⟩

/-- A normalizing point through the reflection `s_a` transports the rootwise datum from `χ`
to `χ - ⟨χ, ν⟩ a`. -/
theorem IsWeylLineRoot.reflection {χ : characterLattice T} (h : IsWeylLineRoot t χ)
    {a : characterLattice T} {ν : cocharacterLattice T} (hpair : latticePairing T a ν = 2)
    {n : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ H.X}
    (hn : IsNormalizingPoint t n (latticeReflectionIso a ν hpair)) :
    IsWeylLineRoot t (χ - latticePairing T χ ν • a) := by
  rw [← reflection_inv_comp_character hpair]
  exact h.transport hn

end Transport

end Langlands.GroupScheme.MaximalSplitSubgroup
