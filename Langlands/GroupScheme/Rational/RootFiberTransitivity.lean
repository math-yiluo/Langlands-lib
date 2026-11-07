import Langlands.GroupScheme.Reductive.RootDatumOrbitSums
import Langlands.GroupScheme.Reductive.RootDatumGaloisCoroots
import Langlands.GroupScheme.Rational.RootGaloisOrbits
import Langlands.GroupScheme.Rational.RootFiniteness
import Langlands.GroupScheme.Torus.SplitPartCharacterTrace
import Langlands.GroupScheme.Torus.SplitLatticeBaseChange
import Langlands.GroupScheme.Rational.TorusCentralizerRationalModel
import Langlands.GroupScheme.Rational.StandardLeviStandardFamiliesProof
import Langlands.GroupScheme.Rational.CentralRootRestriction
import Langlands.GroupScheme.Rational.GenericTorusCocharacter
import Langlands.GroupScheme.Rational.MaximalSplitTorusSubgroup
import Langlands.GroupScheme.Rational.TorusSplitPart
import Langlands.GroupScheme.Dynamic.LieProof
import Langlands.GroupScheme.SubgroupBaseChange

/-! # Relative-root restriction fibers are single Galois orbits -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.GroupScheme

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {S : CommGroupScheme (Spec (CommRingCat.of k))} (f : S ⟶ T)

local notation "b" => algebraBaseMap k L
local notation "T_L" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) T
local notation "f_L" => CategoryTheory.Functor.map (CommGroupScheme.baseChange b) f

section Characters

variable [Fintype (L ≃ₐ[k] L)]

/-- Characters with equal restriction to the extended largest split subtorus have
equal Galois orbit sums. -/
theorem IsLargestSplitSubtorus.galoisOrbitSum_eq_of_restrict_eq
    [FiniteDimensional k L] [IsGalois k L]
    [IsAffineHom T.toGrp.X.hom] [LocallyOfFiniteType T.toGrp.X.hom]
    (hf : IsLargestSplitSubtorus (CommGroupScheme.groupHom f)) (hT : IsTorus T.toGrp)
    {χ ψ : characterLattice T_L} (h : f_L ≫ χ = f_L ≫ ψ) :
    CharacterAveraging.galoisOrbitSum k L T χ = CharacterAveraging.galoisOrbitSum k L T ψ := by
  have hzero := hf.galoisOrbitSum_character_eq_zero L hT (χ - ψ)
    (by rw [Preadditive.comp_sub, h, sub_self])
  have hsub : CharacterAveraging.galoisOrbitSum k L T (χ - ψ) =
      CharacterAveraging.galoisOrbitSum k L T χ - CharacterAveraging.galoisOrbitSum k L T ψ := by
    simp only [CharacterAveraging.galoisOrbitSum, CocharacterAveraging.orbitSum, map_sub,
      Finset.sum_sub_distrib]
  rw [hsub, sub_eq_zero] at hzero
  exact hzero

/-- A character whose restriction to a split original torus is nonzero has a nonzero
Galois orbit sum. -/
theorem galoisOrbitSum_ne_zero_of_restrict_ne_zero (hS : IsSplitTorus S.toGrp)
    {χ : characterLattice T_L} (hχ : f_L ≫ χ ≠ 0) :
    CharacterAveraging.galoisOrbitSum k L T χ ≠ 0 := by
  obtain ⟨c, hc⟩ := (hS.characterLattice_baseChange_bijective b S).surjective (f_L ≫ χ)
  have : IsAddTorsionFree (ℚ ⊗[ℤ] characterLattice S) := IsAddTorsionFree.of_module_rat _
  have : IsAddTorsionFree (characterLattice S) :=
    hS.character_toRat_injective.isAddTorsionFree Langlands.LinearAlgebra.RationalSpan.toRat
  have hrestrict : f_L ≫ CharacterAveraging.galoisOrbitSum k L T χ =
      characterLattice.baseChange b S (Fintype.card (L ≃ₐ[k] L) • c) := by
    simp only [CharacterAveraging.galoisOrbitSum, CocharacterAveraging.orbitSum,
      Preadditive.comp_sum]
    rw [map_nsmul, ← Finset.card_univ, ← Finset.sum_const]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [← characterLattice.galoisRepresentation_precompose, ← hc,
      characterLattice.galoisRepresentation_baseChange]
  intro hsum
  rw [hsum, Limits.comp_zero] at hrestrict
  have hcard : Fintype.card (L ≃ₐ[k] L) • c = 0 :=
    (hS.characterLattice_baseChange_bijective b S).injective (by rw [← hrestrict, map_zero])
  have hc0 : c = 0 := (nsmul_eq_zero_iff_right Fintype.card_ne_zero).mp hcard
  apply hχ
  rw [← hc, hc0, map_zero]

end Characters

variable {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (j : T.toGrp ⟶ G)

local notation "j_L" => CategoryTheory.Functor.map (GroupScheme.baseChange b) j
local notation "G_L" => CategoryTheory.Functor.obj (GroupScheme.baseChange b) G

local instance : IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

attribute [local instance] rootsGaloisAction

/-- **Quasi-split fiber transitivity.** Let `f : S ⟶ T` be the largest split subtorus of
a torus `T ⊆ G` split by a finite Galois extension `L/k`. If no root of `T_L` restricts
to zero on `S_L`, then every nonempty root-restriction fiber is one Galois orbit. -/
theorem rootOrbit_eq_restrictionFiber
    [FiniteDimensional k L] [IsGalois k L] [LocallyOfFiniteType G.X.hom]
    [IsAffineHom T.toGrp.X.hom] [LocallyOfFiniteType T.toGrp.X.hom]
    (hS : IsSplitTorus S.toGrp) (hf : IsLargestSplitSubtorus (CommGroupScheme.groupHom f))
    (hT : IsSplitTorus (T_L).toGrp)
    (hj : IsClosedImmersion (j_L).hom.hom.left)
    {J : Type*} [Finite J]
    {P : RootDatum J (characterLattice T_L) (cocharacterLattice T_L)}
    (hP : IsRootDatumOf (T := T_L) j_L P)
    (hzero : ∀ β : roots (T := T_L) (G := G_L) j_L, f_L ≫ β.val ≠ 0)
    (a : characterLattice S) {β : roots (T := T_L) (G := G_L) j_L}
    (hβ : β ∈ rootRestrictionFiber k L j f a) :
    MulAction.orbit (L ≃ₐ[k] L) β = rootRestrictionFiber k L j f a := by
  classical
  have : Fintype (L ≃ₐ[k] L) := Fintype.ofFinite _
  have hTt : IsTorus T.toGrp := ⟨L, inferInstance, inferInstance, hT⟩
  let ρ := IsRootDatumOf.galoisRootDatumActionOfClosedSplitTorus k L j hT hj hP
  have hsum : ∀ m : J, P.rootOrbitSum ρ m =
      CharacterAveraging.galoisOrbitSum k L T (P.root m) := by
    intro m
    unfold RootPairing.rootOrbitSum CharacterAveraging.galoisOrbitSum
      CocharacterAveraging.orbitSum
    refine Finset.sum_congr rfl fun σ _ => ?_
    exact IsRootDatumOf.galoisRootIndexEquiv_root k L j hP σ m
  have hroot : ∀ m : J, P.root m ∈ roots (T := T_L) (G := G_L) j_L := fun m => by
    rw [← hP.2.1]
    exact ⟨m, rfl⟩
  refine (rootOrbit_subset_restrictionFiber k L j f a hβ).antisymm fun γ hγ => ?_
  obtain ⟨m, hm⟩ : β.val ∈ Set.range P.root := by
    rw [hP.2.1]
    exact β.property
  obtain ⟨n, hn⟩ : γ.val ∈ Set.range P.root := by
    rw [hP.2.1]
    exact γ.property
  have heq : P.rootOrbitSum ρ n = P.rootOrbitSum ρ m := by
    rw [hsum, hsum, hm, hn]
    refine IsLargestSplitSubtorus.galoisOrbitSum_eq_of_restrict_eq k L f hf hTt ?_
    exact hγ.trans hβ.symm
  have hne : ∀ m : J, P.rootOrbitSum ρ m ≠ 0 := by
    intro m
    rw [hsum]
    exact galoisOrbitSum_ne_zero_of_restrict_ne_zero k L f hS (hzero ⟨P.root m, hroot m⟩)
  obtain ⟨σ, hσ⟩ := P.exists_smul_eq_of_rootOrbitSum_eq ρ heq hne
  refine MulAction.mem_orbit_iff.mpr ⟨σ, Subtype.ext ?_⟩
  rw [rootsGaloisAction_coe, ← hm, ← hn, ← hσ]
  exact (IsRootDatumOf.galoisRootIndexEquiv_root k L j hP σ m).symm


/-- A torus that is its own full centralizer of `S` has no root vanishing on `S` after
base change: such a root would be a root of the identity of `T_L`. -/
theorem root_restrict_ne_zero_of_torusCentralizer
    [LocallyOfFiniteType G.X.hom]
    [IsAffineHom T.toGrp.X.hom] [LocallyOfFiniteType T.toGrp.X.hom]
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus (T_L).toGrp)
    (hcent : (torusCentralizer (CommGroupScheme.groupHom f ≫ j)).IsRepresentedBy j)
    (β : roots (T := T_L) (G := G_L) j_L) : f_L ≫ β.val ≠ 0 := by
  intro hβ
  let : LocallyOfFiniteType (G_L).X.hom :=
    MorphismProperty.baseChange_obj (P := @LocallyOfFiniteType) b G.X inferInstance
  let : IsAffineHom (T_L).toGrp.X.hom :=
    MorphismProperty.baseChange_obj (P := @IsAffineHom) b T.toGrp.X inferInstance
  let : LocallyOfFiniteType (T_L).toGrp.X.hom :=
    MorphismProperty.baseChange_obj (P := @LocallyOfFiniteType) b T.toGrp.X inferInstance
  let ζ : cocharacterLattice T :=
    centralizingCocharacter hS (CommGroupScheme.groupHom f ≫ j) ≫ f
  have hζ : Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ j) =
      torusCentralizer (CommGroupScheme.groupHom f ≫ j) := by
    change Dynamic.centralizer
      ((CommGroupScheme.groupHom (centralizingCocharacter hS (CommGroupScheme.groupHom f ≫ j)) ≫
        CommGroupScheme.groupHom f) ≫ j) = _
    rw [Category.assoc, centralizingCocharacter_spec]
  have hrep : (Dynamic.centralizer
      (CommGroupScheme.groupHom (cocharacterLattice.baseChange b T ζ) ≫ j_L)).IsRepresentedBy
        j_L := by
    rw [cocharacterLattice.groupHom_baseChange_dynamic, ← Dynamic.baseChangeCocharacter_comp,
      Dynamic.centralizer_baseChange, hζ]
    exact hcent.baseChange b
  have hroots := relativeRoots_centralizer_factor (T := T_L) (G := G_L) (L := (T_L).toGrp)
    dynamicLie j_L (𝟙 _) j_L (Category.id_comp _) (cocharacterLattice.baseChange b T ζ) hrep
  have hmem : β.val ∈ relativeRoots (𝟙 (T_L).toGrp) := by
    rw [hroots]
    refine ⟨β.property, ?_⟩
    rw [latticePairing_apply, cocharacterLattice.baseChange_comp, Category.assoc, hβ,
      Limits.comp_zero, map_zero]
  have hc : IsCentral (CommGroupScheme.groupHom (𝟙 T_L) ≫ 𝟙 (T_L).toGrp) := by
    change IsCentral (𝟙 (T_L).toGrp ≫ 𝟙 (T_L).toGrp)
    rw [Category.id_comp]
    exact isCentral_to_commGroupScheme _
  have hz := root_restrict_eq_zero_of_isCentral (𝟙 (T_L).toGrp) (𝟙 T_L) hT hc hmem
  exact (mem_relativeRoots.mp hmem).1 (by simpa using hz)

/-- **Quasi-split fiber transitivity, ambient form.** Let `f ≫ j` be a maximal split
torus of `G` whose full centralizer is the closed torus `j : T ⟶ G`, split by a finite
Galois extension `L/k`. Then every nonempty root-restriction fiber is one Galois orbit. -/
theorem rootOrbit_eq_restrictionFiber_of_torusCentralizer
    [FiniteDimensional k L] [IsGalois k L] [LocallyOfFiniteType G.X.hom]
    [IsAffineHom T.toGrp.X.hom] [LocallyOfFiniteType T.toGrp.X.hom]
    (hf : IsMaximalSplitTorus (CommGroupScheme.groupHom f ≫ j))
    (hjc : IsClosedSubgroup j)
    (hcent : (torusCentralizer (CommGroupScheme.groupHom f ≫ j)).IsRepresentedBy j)
    (hT : IsSplitTorus (T_L).toGrp)
    {J : Type*} [Finite J]
    {P : RootDatum J (characterLattice T_L) (cocharacterLattice T_L)}
    (hP : IsRootDatumOf (T := T_L) j_L P)
    (a : characterLattice S) {β : roots (T := T_L) (G := G_L) j_L}
    (hβ : β ∈ rootRestrictionFiber k L j f a) :
    MulAction.orbit (L ≃ₐ[k] L) β = rootRestrictionFiber k L j f a := by
  let : IsAffine T.X.left := isAffine_of_isAffineHom T.toGrp.X.hom
  exact rootOrbit_eq_restrictionFiber k L f j hf.1.1 (hf.of_comp hjc).isLargestSplitSubtorus hT
    (IsClosedSubgroup.baseChange b hjc) hP
    (root_restrict_ne_zero_of_torusCentralizer k L f j hf.1.1 hT hcent) a hβ

section Embeddings

variable [FiniteDimensional k L] [IsGalois k L]

/-- When a restriction fiber is one Galois orbit, its actual roots are the
`k`-embeddings into `L` of the stabilizer field of any one of them. -/
def rootRestrictionFiberEmbeddingEquiv (a : characterLattice S)
    (β : roots (T := T_L) (G := G_L) j_L)
    (horbit : MulAction.orbit (L ≃ₐ[k] L) β = rootRestrictionFiber k L j f a) :
    rootRestrictionFiber k L j f a ≃ (rootOrbitField k L j β →ₐ[k] L) :=
  (Equiv.subtypeEquivRight fun γ => Set.ext_iff.mp horbit γ).symm.trans
    (rootOrbitEmbeddingEquiv k L j β)

/-- Postcomposition of embeddings is ordinary Galois transport inside the fiber. -/
theorem rootRestrictionFiberEmbeddingEquiv_symm_comp (a : characterLattice S)
    (β : roots (T := T_L) (G := G_L) j_L)
    (horbit : MulAction.orbit (L ≃ₐ[k] L) β = rootRestrictionFiber k L j f a)
    (σ : L ≃ₐ[k] L) (τ : rootOrbitField k L j β →ₐ[k] L) :
    ((rootRestrictionFiberEmbeddingEquiv k L f j a β horbit).symm (σ.toAlgHom.comp τ) :
        roots (T := T_L) (G := G_L) j_L) =
      σ • ((rootRestrictionFiberEmbeddingEquiv k L f j a β horbit).symm τ :
        roots (T := T_L) (G := G_L) j_L) :=
  rootOrbitEmbeddingEquiv_symm_comp k L j β σ τ

/-- The chosen root corresponds to the inclusion of its stabilizer field. -/
theorem rootRestrictionFiberEmbeddingEquiv_symm_val (a : characterLattice S)
    (β : roots (T := T_L) (G := G_L) j_L)
    (horbit : MulAction.orbit (L ≃ₐ[k] L) β = rootRestrictionFiber k L j f a)
    (τ : rootOrbitField k L j β →ₐ[k] L) :
    ((rootRestrictionFiberEmbeddingEquiv k L f j a β horbit).symm τ :
        roots (T := T_L) (G := G_L) j_L) =
      ((rootOrbitEmbeddingEquiv k L j β).symm τ : roots (T := T_L) (G := G_L) j_L) :=
  rfl

end Embeddings

end Langlands.GroupScheme
