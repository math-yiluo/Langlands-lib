import Langlands.Algebra.FiniteGaloisOrbits
import Langlands.GroupScheme.Reductive.RootDatumGaloisRoots
import Langlands.GroupScheme.Rational.AbsoluteRootRestriction
import Langlands.GroupScheme.Torus.WeilRestrictionNormOneCharacters

/-! # Actual root Galois orbits and their stabilizer fields -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (j : T.toGrp ⟶ G)

local notation "b" => algebraBaseMap k L
local notation "j_L" => CategoryTheory.Functor.map (GroupScheme.baseChange b) j
local notation "T_L" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) T
local notation "G_L" => CategoryTheory.Functor.obj (GroupScheme.baseChange b) G

local instance : IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

/-- The ordinary character Galois action restricted to the actual root set. -/
@[instance_reducible]
def rootsGaloisAction : MulAction (L ≃ₐ[k] L) (roots (T := T_L) (G := G_L) j_L) where
  smul σ β := ⟨characterLattice.galoisRepresentation k L T σ β.val,
    (mem_roots_galois_iff k L j σ β.val).mpr β.property⟩
  one_smul β := by
    apply Subtype.ext
    exact LinearMap.congr_fun (map_one (characterLattice.galoisRepresentation k L T)) β.val
  mul_smul σ τ β := by
    apply Subtype.ext
    exact LinearMap.congr_fun (map_mul (characterLattice.galoisRepresentation k L T) σ τ) β.val

attribute [local instance] rootsGaloisAction

@[simp] theorem rootsGaloisAction_coe (σ : L ≃ₐ[k] L) (β : roots (T := T_L) (G := G_L) j_L) :
    (σ • β : roots (T := T_L) (G := G_L) j_L).val =
      characterLattice.galoisRepresentation k L T σ β.val := rfl

/-- The field attached to an actual root is the fixed field of its ordinary Galois stabilizer. -/
def rootOrbitField (β : roots (T := T_L) (G := G_L) j_L) : IntermediateField k L :=
  Langlands.Algebra.FiniteGaloisOrbits.stabilizerField k L β

/-- Its fixed-field condition uses the actual character Galois representation. -/
theorem mem_rootOrbitField_iff (β : roots (T := T_L) (G := G_L) j_L) (x : L) :
    x ∈ rootOrbitField k L j β ↔
      ∀ σ : L ≃ₐ[k] L,
        characterLattice.galoisRepresentation k L T σ β.val = β.val → σ x = x := by
  change x ∈ IntermediateField.fixedField _ ↔ _
  rw [IntermediateField.mem_fixedField_iff]
  simp only [MulAction.mem_stabilizer_iff, Subtype.ext_iff, rootsGaloisAction_coe]

section FiniteGalois

variable [FiniteDimensional k L] [IsGalois k L]

/-- The embeddings of the actual-root stabilizer field are exactly its actual Galois orbit. -/
def rootOrbitEmbeddingEquiv (β : roots (T := T_L) (G := G_L) j_L) :
    MulAction.orbit (L ≃ₐ[k] L) β ≃ (rootOrbitField k L j β →ₐ[k] L) :=
  Langlands.Algebra.FiniteGaloisOrbits.orbitEmbeddingEquiv k L β

/-- Postcomposition of field embeddings is ordinary Galois transport of the actual root. -/
theorem rootOrbitEmbeddingEquiv_symm_comp (β : roots (T := T_L) (G := G_L) j_L) (σ : L ≃ₐ[k] L)
    (τ : rootOrbitField k L j β →ₐ[k] L) :
    ((rootOrbitEmbeddingEquiv k L j β).symm (σ.toAlgHom.comp τ) : roots (T := T_L) (G := G_L) j_L) =
      σ • ((rootOrbitEmbeddingEquiv k L j β).symm τ : roots (T := T_L) (G := G_L) j_L) :=
  Langlands.Algebra.FiniteGaloisOrbits.orbitEmbeddingEquiv_symm_comp k L β σ τ

end FiniteGalois

section Restriction

variable {S : CommGroupScheme (Spec (CommRingCat.of k))} (f : S ⟶ T)

/-- The actual roots whose restriction equals a specified original character. -/
def rootRestrictionFiber (a : characterLattice S) : Set (roots (T := T_L) (G := G_L) j_L) :=
  {β | (CommGroupScheme.baseChange b).map f ≫ β.val =
    characterLattice.baseChange b S a}

/-- Each actual root-restriction fiber is stable under ordinary Galois transport. -/
theorem rootsGaloisAction_mem_restrictionFiber (a : characterLattice S)
    (σ : L ≃ₐ[k] L) {β : roots (T := T_L) (G := G_L) j_L}
    (hβ : β ∈ rootRestrictionFiber k L j f a) :
    σ • β ∈ rootRestrictionFiber k L j f a := by
  change (CommGroupScheme.baseChange b).map f ≫
    characterLattice.galoisRepresentation k L T σ β.val = _
  rw [← characterLattice.galoisRepresentation_precompose, hβ,
    characterLattice.galoisRepresentation_baseChange]

/-- Thus an actual Galois root orbit remains inside its relative-root restriction fiber. -/
theorem rootOrbit_subset_restrictionFiber (a : characterLattice S)
    {β : roots (T := T_L) (G := G_L) j_L} (hβ : β ∈ rootRestrictionFiber k L j f a) :
    MulAction.orbit (L ≃ₐ[k] L) β ⊆ rootRestrictionFiber k L j f a := by
  intro γ hγ
  obtain ⟨σ, rfl⟩ := MulAction.mem_orbit_iff.mp hγ
  exact rootsGaloisAction_mem_restrictionFiber k L j f a σ hβ

variable [LocallyOfFiniteType G.X.hom]

/-- A root for a split original torus has a nonempty actual restriction fiber in a
field over which the containing torus splits. This asserts no orbit transitivity. -/
theorem rootRestrictionFiber_nonempty (hS : IsSplitTorus S.toGrp)
    (hT : IsSplitTorus ((GroupScheme.baseChange b).obj T.toGrp))
    (a : roots (CommGroupScheme.groupHom f ≫ j)) :
    (rootRestrictionFiber k L j f a.val).Nonempty := by
  refine ⟨splittingFieldRootLift hS hT f j a, ?_⟩
  exact splittingFieldRootLift_restriction hS hT f j a

/-- In particular, one actual root orbit lies in the prescribed restriction fiber. -/
theorem exists_rootOrbit_in_restrictionFiber (hS : IsSplitTorus S.toGrp)
    (hT : IsSplitTorus ((GroupScheme.baseChange b).obj T.toGrp))
    (a : roots (CommGroupScheme.groupHom f ≫ j)) :
    ∃ β : roots (T := T_L) (G := G_L) j_L, β ∈ rootRestrictionFiber k L j f a.val ∧
      MulAction.orbit (L ≃ₐ[k] L) β ⊆ rootRestrictionFiber k L j f a.val := by
  obtain ⟨β, hβ⟩ := rootRestrictionFiber_nonempty k L j f hS hT a
  exact ⟨β, hβ, rootOrbit_subset_restrictionFiber k L j f a.val hβ⟩

end Restriction

end Langlands.GroupScheme
