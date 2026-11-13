import Langlands.GroupScheme.Lie.RootOrbitCharacterDescent
import Langlands.GroupScheme.Torus.SplitPartCharacters
import Langlands.GroupScheme.GeometricComponentCanonicalIdentity

/-! # Galois-fixed characters vanishing on the largest split subtorus -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry Limits
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme

open Langlands.Plancherel.TorusNormKernel
open Langlands.GroupScheme.AffineCharacterFiniteGalois
open Langlands.GroupScheme.AffineCharacterTowerDescent

namespace GaloisPointComparison

variable (k : Type u) [Field k]

/-- The self-pullback comparison is natural in the group scheme. -/
@[reassoc]
theorem selfBaseChangeIso_hom_naturality {H G : GroupScheme (Spec (CommRingCat.of k))}
    (g : H ⟶ G) :
    (GroupScheme.baseChange (baseMap k k)).map g ≫ (selfBaseChangeIso k G).hom =
      (selfBaseChangeIso k H).hom ≫ g := by
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  simp only [Grp.comp_hom_hom, Over.comp_left, selfBaseChangeIso_hom_left]
  exact pullback.lift_fst _ _ _

end GaloisPointComparison

variable {k : Type u} [Field k]

/-- The value of the zero character is one. -/
theorem valueE_zero {F E : Type u} [Field F] [Field E] [Algebra F E]
    {T : GroupScheme (Spec (CommRingCat.of F))} (D : Type u) [CommRing D] [Algebra F D]
    [Algebra E D] [IsScalarTower F E D] (y : T.affinePoints (CommAlgCat.of F D)) :
    valueE (0 : rationalCharacters (GaloisPointComparison.baseChanged F E T)) D y = 1 := by
  rw [valueE_apply, rationalCharacters.comp_zero, map_one]

/-- **Galois-fixed characters vanishing on the largest split subtorus.** Let `T` be a
torus over a field `k` and `f : S ⟶ T` the inclusion of its largest split subtorus. A
character of `T` over the separable closure that is fixed by every element of the
absolute Galois group and restricts to zero on `S` is zero. -/
theorem IsLargestSplitSubtorus.galoisFixed_character_eq_zero
    {T S : CommGroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom T.toGrp.X.hom] [LocallyOfFiniteType T.toGrp.X.hom]
    (hT : IsTorus T.toGrp) {f : S ⟶ T}
    (hf : IsLargestSplitSubtorus (CommGroupScheme.groupHom f))
    (ψ : characterLattice
      ((CommGroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj T))
    (hfix : ∀ σ : SeparableClosure k ≃ₐ[k] SeparableClosure k,
      characterLattice.galoisRepresentation k (SeparableClosure k) T σ ψ = ψ)
    (hres : (CommGroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).map f ≫ ψ =
      0) :
    ψ = 0 := by
  have : IsAffine T.toGrp.X.left := isAffine_of_isAffineHom T.toGrp.X.hom
  have : IsAffineHom S.toGrp.X.hom := by
    have : IsClosedImmersion (CommGroupScheme.groupHom f).hom.hom.left := hf.1.2
    rw [← Over.w (CommGroupScheme.groupHom f).hom.hom]
    infer_instance
  have : IsAffine S.toGrp.X.left := isAffine_of_isAffineHom S.toGrp.X.hom
  set L := SeparableClosure k
  -- the character over `L`, regarded as an actual rational character of `T_L`
  let ψ' := baseChangedCharacter k L T ψ
  have hψ' : ∀ σ : L ≃ₐ[k] L,
      tensorConj T.toGrp k L σ (tensorValue T.toGrp L ψ' : L ⊗[k] Coord T.toGrp) =
        tensorValue T.toGrp L ψ' := by
    intro σ
    rw [tensorConj_tensorValue_baseChangedCharacter]
    exact congrArg (fun χ => (tensorValue T.toGrp L (baseChangedCharacter k L T χ) :
      L ⊗[k] Coord T.toGrp)) (hfix (σ.restrictScalars k))
  -- descend it to a character of the self-base change `T_k`
  let χ := fixedDescend T.toGrp k L ψ' hψ'
  have hχres : characterRestrict
      ((GroupScheme.baseChange (GaloisPointComparison.baseMap k k)).map
        (CommGroupScheme.groupHom f)) χ = 0 := by
    have h := characterRestrict_fixedDescend T.toGrp k L ψ' hψ' (CommGroupScheme.groupHom f) 0
      (by
        rw [map_zero]
        exact congrArg (fun φ => Additive.ofMul (CommGroupScheme.groupHom φ)) hres)
    rw [h, map_zero]
  -- transport to an actual character of `T` and use the largest split subtorus
  let χ₀ := characterRestrict (GaloisPointComparison.selfBaseChangeIso k T.toGrp).inv χ
  have hχ₀ : χ₀ = 0 := by
    apply hf.characterRestrict_injective hT
    rw [map_zero]
    change characterRestrict (CommGroupScheme.groupHom f)
      (characterRestrict (GaloisPointComparison.selfBaseChangeIso k T.toGrp).inv χ) = 0
    rw [← AddMonoidHom.comp_apply, ← characterRestrict_comp]
    have hnat : CommGroupScheme.groupHom f ≫
        (GaloisPointComparison.selfBaseChangeIso k T.toGrp).inv =
      (GaloisPointComparison.selfBaseChangeIso k S.toGrp).inv ≫
        (GroupScheme.baseChange (GaloisPointComparison.baseMap k k)).map
          (CommGroupScheme.groupHom f) := by
      rw [Iso.comp_inv_eq, Category.assoc,
        GaloisPointComparison.selfBaseChangeIso_hom_naturality, Iso.inv_hom_id_assoc]
    rw [hnat, characterRestrict_comp, AddMonoidHom.comp_apply, hχres, map_zero]
  have hχ : χ = 0 := by
    have h :
        characterRestrict (GaloisPointComparison.selfBaseChangeIso k T.toGrp).hom χ₀ = χ := by
      change characterRestrict (GaloisPointComparison.selfBaseChangeIso k T.toGrp).hom
        (characterRestrict (GaloisPointComparison.selfBaseChangeIso k T.toGrp).inv χ) = χ
      rw [← AddMonoidHom.comp_apply, ← characterRestrict_comp, Iso.hom_inv_id,
        characterRestrict_id, AddMonoidHom.id_apply]
    rw [← h, hχ₀, map_zero]
  -- the values of `ψ'` over `L`-algebras are those of `χ = 0`
  have hψ'0 : ψ' = 0 := by
    apply ext_valueE (E := L)
    intro D _ _ _ _ y
    rw [← valueE_fixedDescend T.toGrp k L ψ' hψ' y]
    change valueE χ D y = _
    rw [hχ, valueE_zero, valueE_zero]
  exact hψ'0
