import Langlands.GroupScheme.Rational.RootFiniteness
import Langlands.GroupScheme.Reductive.SplitSemisimpleRootSpanNecessity
import Langlands.GroupScheme.Reductive.RootDatumExistence
import Langlands.GroupScheme.Torus.FiniteGaloisCharacterDescent

/-! # From fixed actual roots to a split maximal torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open Langlands.LinearAlgebra.RationalSpan

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

section CharacterRigidity

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- In a semisimple group, an integral character endomorphism fixing every
actual root of a split closed torus with root datum fixes every character. -/
theorem IsSemisimple.character_eq_of_fixed_roots
    (hG : IsSemisimple G) (hT : IsSplitTorus T.toGrp)
    {i : T.toGrp ⟶ G} (hi : IsClosedSubgroup i) {J : Type*}
    {P : RootDatum J (characterLattice T) (cocharacterLattice T)} (hP : IsRootDatumOf i P)
    (f : characterLattice T →ₗ[ℤ] characterLattice T)
    (hf : ∀ α ∈ roots i, f α = α) (χ : characterLattice T) : f χ = χ := by
  classical
  have : Finite (characterLattice T ⧸ P.rootSpan ℤ) :=
    hG.finite_quotient_rootSpan hT hi hP
  have : IsAddTorsionFree (ℚ ⊗[ℤ] characterLattice T) :=
    IsAddTorsionFree.of_module_rat _
  have : IsAddTorsionFree (characterLattice T) :=
    hT.character_toRat_injective.isAddTorsionFree toRat
  have hspan : P.rootSpan ℤ ≤ (f - LinearMap.id).ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨α, rfl⟩
    change f (P.root α) - P.root α = 0
    apply sub_eq_zero.mpr
    apply hf
    rw [← hP.2.1]
    exact Set.mem_range_self α
  obtain ⟨n, hn, hnχ⟩ :=
    (isOfFinAddOrder_of_finite ((P.rootSpan ℤ).mkQ χ)).exists_nsmul_eq_zero
  have hmem : n • χ ∈ P.rootSpan ℤ := by
    apply (Submodule.Quotient.mk_eq_zero (P.rootSpan ℤ)).mp
    change (P.rootSpan ℤ).mkQ (n • χ) = 0
    rw [map_nsmul]
    exact hnχ
  have heq : f (n • χ) = n • χ := sub_eq_zero.mp (hspan hmem)
  apply IsAddTorsionFree.nsmul_right_injective hn.ne'
  simpa only [map_nsmul] using heq

/-- The root datum needed for character rigidity exists for a split maximal
torus; no chosen root datum remains in this corollary. -/
theorem IsSemisimple.character_eq_of_fixed_maximalTorus_roots
    (hG : IsSemisimple G) (hT : IsSplitTorus T.toGrp)
    (i : T.toGrp ⟶ G) (hi : IsMaximalTorus i)
    (f : characterLattice T →ₗ[ℤ] characterLattice T)
    (hf : ∀ α ∈ roots i, f α = α) (χ : characterLattice T) : f χ = χ := by
  obtain ⟨J, _, P, hP, _⟩ := rootDatumExistence k G hG.isConnectedReductive T hT i hi
  exact hG.character_eq_of_fixed_roots hT hi.2.1 hP f hf χ

end CharacterRigidity

section GaloisSplitting

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
  {T S : CommGroupScheme (Spec (CommRingCat.of k))}

local notation "b" => algebraBaseMap k L
local notation "T_L" => Functor.obj (CommGroupScheme.baseChange b) T
local notation "S_L" => Functor.obj (CommGroupScheme.baseChange b) S

variable [FiniteDimensional k L] [IsGalois k L]

/-- If all characters of the split base change of `T` are fixed, a supplied
isomorphism to the base change of a split torus descends to an isomorphism over
the original field. -/
def IsSplitTorus.descendIsoOfFixedCharacters
    (hT : IsSplitTorus (T_L).toGrp) (hS : IsSplitTorus S.toGrp)
    (hfix : ∀ (σ : L ≃ₐ[k] L) (χ : characterLattice T_L),
      characterLattice.galoisRepresentation k L T σ χ = χ)
    (e : T_L ≅ S_L) : T ≅ S := by
  have he : ∀ (σ : L ≃ₐ[k] L) (χ : characterLattice S_L),
      (characterLattice.congr e).symm (characterLattice.galoisRepresentation k L S σ χ) =
        characterLattice.galoisRepresentation k L T σ ((characterLattice.congr e).symm χ) := by
    intro σ χ
    rw [hfix]
    obtain ⟨χ₀, rfl⟩ := (hS.characterLattice_baseChange_bijective b S).2 χ
    rw [characterLattice.galoisRepresentation_baseChange]
  exact (hT.exists_iso_of_equivariant_characterEquiv (hS.baseChange b)
    (characterLattice.congr e).symm he).choose

/-- A torus split by a finite Galois extension is already split if every
character of its split base change is fixed by all coefficient automorphisms. -/
theorem IsSplitTorus.of_galoisFixedCharacters
    (hT : IsSplitTorus (T_L).toGrp)
    (hfix : ∀ (σ : L ≃ₐ[k] L) (χ : characterLattice T_L),
      characterLattice.galoisRepresentation k L T σ χ = χ) : IsSplitTorus T.toGrp := by
  classical
  obtain ⟨I, hI, ⟨e⟩⟩ := hT
  let S₀ := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I
  have hS₀ : IsSplitTorus S₀.toGrp := isSplitTorus_splitTorus I
  let eL : T_L ≅ (CommGroupScheme.baseChange b).obj S₀ :=
    CommGroupScheme.isoOfGroupIso (e ≪≫ (splitTorus.baseChangeIso b I).symm)
  let a := (show IsSplitTorus (T_L).toGrp from ⟨I, hI, ⟨e⟩⟩).descendIsoOfFixedCharacters
    hS₀ hfix eL
  let aG : T.toGrp ≅ S₀.toGrp :=
    ⟨CommGroupScheme.groupHom a.hom, CommGroupScheme.groupHom a.inv,
      congrArg CommGroupScheme.groupHom a.hom_inv_id,
      congrArg CommGroupScheme.groupHom a.inv_hom_id⟩
  exact IsSplitTorus.of_iso aG hS₀

variable {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local notation "G_L" => Functor.obj (GroupScheme.baseChange b) G
local notation "j_L" => CategoryTheory.Functor.map (GroupScheme.baseChange b)

local instance : IsAffineHom (G_L).X.hom :=
  MorphismProperty.baseChange_obj (P := @IsAffineHom) b G.X inferInstance

/-- For a maximal torus in a semisimple base change, fixedness of every actual
root under every coefficient automorphism implies splitting over the original
field. -/
theorem isSplitTorus_of_galoisFixed_roots
    (hG : IsSemisimple G_L) (j : T.toGrp ⟶ G)
    (hj : IsMaximalTorus (T := T_L) (G := G_L) (j_L j))
    (hT : IsSplitTorus (T_L).toGrp)
    (hfix : ∀ (σ : L ≃ₐ[k] L) (β : roots (T := T_L) (G := G_L) (j_L j)),
      characterLattice.galoisRepresentation k L T σ β.val = β.val) :
    IsSplitTorus T.toGrp := by
  apply hT.of_galoisFixedCharacters
  intro σ χ
  apply hG.character_eq_of_fixed_maximalTorus_roots hT (j_L j) hj
    (characterLattice.galoisRepresentation k L T σ)
  intro α hα
  exact hfix σ ⟨α, hα⟩

end GaloisSplitting

end Langlands.GroupScheme
