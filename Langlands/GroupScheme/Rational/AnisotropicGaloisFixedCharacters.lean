import Langlands.GroupScheme.Torus.LargestSplitGaloisFixed
import Langlands.GroupScheme.Rational.MaximalSplitTorusSubgroup
import Langlands.GroupScheme.Rational.TorusSplitPart

/-!
# Galois-fixed characters of a torus in an anisotropic group

Let `G` be an anisotropic affine group of locally finite type over a field `k`, and let
`i : T ⟶ G` be a closed subgroup that is a torus. For any Galois extension `L/k`, finite or
not, a character of `T_L` fixed by every `k`-automorphism of `L` is zero. The proof descends
the character to `k` and restricts it to the largest split subtorus of `T`, which is trivial
because `G` is anisotropic.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme

open Langlands.Plancherel.TorusNormKernel
open Langlands.GroupScheme.AffineCharacterFiniteGalois
open Langlands.GroupScheme.AffineCharacterTowerDescent

variable {k : Type u} [Field k]

/-- A commutative group scheme that becomes a split torus over some field extension is a
torus. -/
theorem isTorus_of_isSplitTorus_baseChange {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (K : Type u) [Field K] [Algebra k K]
    (h : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T).toGrp) :
    IsTorus T.toGrp :=
  ⟨K, inferInstance, inferInstance, h⟩

/-- **Galois-fixed characters in an anisotropic group.** Let `G` be an anisotropic affine group
of locally finite type over `k` and `i : T ⟶ G` a closed subgroup with `T` a torus. For a
Galois extension `L/k`, possibly infinite, every character of `T_L` fixed by all of
`L ≃ₐ[k] L` is zero. -/
theorem IsAnisotropic.galoisFixed_character_eq_zero
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (hG : IsAnisotropic G)
    {T : CommGroupScheme (Spec (CommRingCat.of k))} {i : T.toGrp ⟶ G}
    (hi : IsClosedSubgroup i) (hT : IsTorus T.toGrp)
    (L : Type u) [Field L] [Algebra k L] [IsGalois k L]
    (ψ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T))
    (hfix : ∀ σ : L ≃ₐ[k] L, characterLattice.galoisRepresentation k L T σ ψ = ψ) :
    ψ = 0 := by
  have : IsClosedImmersion i.hom.hom.left := hi
  have : IsAffineHom T.toGrp.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  have : LocallyOfFiniteType T.toGrp.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  have : IsAffine T.toGrp.X.left := isAffine_of_isAffineHom T.toGrp.X.hom
  obtain ⟨S, f, hf⟩ := exists_largestSplitSubtorus T
  -- characters of the largest split subtorus vanish, since it is a split subtorus of `G`
  have hSG : IsSplitSubtorus (f ≫ i) := hf.1.comp hi
  have hsub : Subsingleton (rationalCharacters S.toGrp) := by
    have := hG.subsingleton_hom_of_isSplitSubtorus hSG (Gm (Spec (CommRingCat.of k))).toGrp
    exact ⟨fun a b => Additive.toMul.injective (Subsingleton.elim _ _)⟩
  -- the character over `L`, regarded as an actual rational character of `T_L`
  let ψ' := baseChangedCharacter k L T ψ
  have hψ' : ∀ σ : L ≃ₐ[k] L,
      tensorConj T.toGrp k L σ (tensorValue T.toGrp L ψ' : L ⊗[k] Coord T.toGrp) =
        tensorValue T.toGrp L ψ' := by
    intro σ
    rw [tensorConj_tensorValue_baseChangedCharacter]
    exact congrArg (fun χ => (tensorValue T.toGrp L (baseChangedCharacter k L T χ) :
      L ⊗[k] Coord T.toGrp)) (hfix (σ.restrictScalars k))
  -- descend it to a character of the self-base change `T_k`, then to `T`
  let χ := fixedDescend T.toGrp k L ψ' hψ'
  let χ₀ := characterRestrict (GaloisPointComparison.selfBaseChangeIso k T.toGrp).inv χ
  have hχ₀ : χ₀ = 0 := by
    apply hf.characterRestrict_injective hT
    exact Subsingleton.elim _ _
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

end Langlands.GroupScheme
