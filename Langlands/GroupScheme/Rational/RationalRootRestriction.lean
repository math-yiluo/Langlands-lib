import Langlands.GroupScheme.Rational.QuasiSplitRootRestriction
import Langlands.GroupScheme.Rational.RootGaloisOrbits
import Langlands.GroupScheme.Rational.RootReflectionAssembly
import Langlands.LinearAlgebra.SymmetricRootPairingForm

/-! # Rational restriction on the actual root spans -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open Langlands.LinearAlgebra.RationalSpan

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
  {S T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}

local notation "b" => algebraBaseMap k L
local notation "S_L" => Functor.obj (CommGroupScheme.baseChange b) S
local notation "T_L" => Functor.obj (CommGroupScheme.baseChange b) T
local notation "G_L" => Functor.obj (GroupScheme.baseChange b) G
local notation "j_L" => CategoryTheory.Functor.map (GroupScheme.baseChange b)

namespace SplittingFieldRootRestriction

/-- Restrict characters over an extension and descend along the character
pullback equivalence of the original split torus. -/
def characterMap (hS : IsSplitTorus S.toGrp) (f : S ⟶ T) :
    characterLattice T_L →ₗ[ℤ] characterLattice S :=
  (characterLattice.baseChangeEquiv b S hS).symm.toIntLinearEquiv.toLinearMap.comp
    (characterLattice.precompose ((CommGroupScheme.baseChange b).map f)).toIntLinearMap

/-- The rational extension of actual character restriction and descent. -/
def rationalMap (hS : IsSplitTorus S.toGrp) (f : S ⟶ T) :
    (ℚ ⊗[ℤ] characterLattice T_L) →ₗ[ℚ] (ℚ ⊗[ℤ] characterLattice S) :=
  (characterMap (L := L) hS f).baseChange ℚ

@[simp]
theorem rationalMap_toRat (hS : IsSplitTorus S.toGrp) (f : S ⟶ T)
    (β : characterLattice T_L) :
    rationalMap hS f (toRat β) = toRat (characterMap hS f β) := rfl

end SplittingFieldRootRestriction

variable [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

local instance : IsAffineHom (G_L).X.hom :=
  MorphismProperty.baseChange_obj (P := @IsAffineHom) b G.X inferInstance

local instance : LocallyOfFiniteType (G_L).X.hom :=
  MorphismProperty.baseChange_obj (P := @LocallyOfFiniteType) b G.X inferInstance

namespace IsQuasiSplit

variable (hG : IsQuasiSplit G) (a : S.toGrp ⟶ G) (j : T.toGrp ⟶ G) (f : S ⟶ T)
  (ha : IsMaximalSplitTorus a) (hj : IsMaximalTorus j)
  (hf : CommGroupScheme.groupHom f ≫ j = a)
  (hTL : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T).toGrp)

open SplittingFieldRootRestriction RelativeRootSystem

include hG hj hf hTL

/-- The rational character map carries the actual absolute-root span into
the original relative-root span. -/
theorem rationalMap_rootSpan_le :
    (relativeRootSpan (T := T_L) (G := G_L) (j_L j)).map (rationalMap (L := L) ha.1.1 f) ≤
      relativeRootSpan a := by
  rw [relativeRootSpan, ratSpan, Submodule.map_span]
  apply Submodule.span_le.mpr
  rintro _ ⟨_, ⟨β, hβ, rfl⟩, rfl⟩
  rw [rationalMap_toRat]
  exact toRat_mem_ratSpan (hG.rootRestriction (L := L) a j f ha hj hf hTL ⟨β, hβ⟩).property

/-- Actual root restriction, extended linearly to the full rational root spans. -/
def rationalRootRestriction :
    relativeRootSpan (T := T_L) (G := G_L) (j_L j) →ₗ[ℚ] relativeRootSpan a :=
  ((rationalMap (L := L) ha.1.1 f).comp
    (relativeRootSpan (T := T_L) (G := G_L) (j_L j)).subtype).codRestrict
    (relativeRootSpan a) (fun x =>
      hG.rationalMap_rootSpan_le (L := L) a j f ha hj hf hTL ⟨x.val, x.property, rfl⟩)

/-- On an actual root vector the rational map is precisely total root restriction. -/
@[simp]
theorem rationalRootRestriction_rootVector
    (β : relativeRoots (T := T_L) (G := G_L) (j_L j)) :
    hG.rationalRootRestriction (L := L) a j f ha hj hf hTL (rootVector (T := T_L) (G := G_L) (j_L j) β) =
      rootVector a (hG.rootRestriction (L := L) a j f ha hj hf hTL β) :=
by
  apply Subtype.ext
  change rationalMap (L := L) ha.1.1 f (toRat β.val) =
    toRat (hG.rootRestriction (L := L) a j f ha hj hf hTL β).val
  rw [rationalMap_toRat]
  rfl

/-- Total surjectivity on actual roots implies surjectivity on their rational spans. -/
theorem rationalRootRestriction_surjective :
    Function.Surjective (hG.rationalRootRestriction (L := L) a j f ha hj hf hTL) := by
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [← span_range_rootVector a]
  apply Submodule.span_le.mpr
  rintro _ ⟨α, rfl⟩
  obtain ⟨β, hβ⟩ := hG.rootRestriction_surjective (L := L) a j f ha hj hf hTL α
  refine ⟨rootVector (T := T_L) (G := G_L) (j_L j) β, ?_⟩
  rw [hG.rationalRootRestriction_rootVector, hβ]

/-- Ordinary Galois transport leaves total relative-root restriction unchanged. -/
theorem rootRestriction_galois (σ : L ≃ₐ[k] L)
    (β : roots (T := T_L) (G := G_L) (j_L j)) :
    hG.rootRestriction (L := L) a j f ha hj hf hTL
      ⟨characterLattice.galoisRepresentation k L T σ β.val,
        (mem_roots_galois_iff k L j σ β.val).mpr β.property⟩ =
      hG.rootRestriction (L := L) a j f ha hj hf hTL β := by
  apply Subtype.ext
  apply (characterLattice.baseChangeEquiv b S ha.1.1).injective
  change characterLattice.baseChange b S _ = characterLattice.baseChange b S _
  calc
    _ = characterLattice.galoisRepresentation k L S σ
        (characterLattice.baseChange b S (hG.rootRestriction (L := L) a j f ha hj hf hTL β).val) := by
      rw [hG.rootRestriction_baseChange, hG.rootRestriction_baseChange,
        characterLattice.galoisRepresentation_precompose]
    _ = _ := characterLattice.galoisRepresentation_baseChange k L S σ _

/-- If supplied root systems have exactly the actual root images, source
irreducibility and symmetry of the full target pairing force injectivity of
actual rational restriction. -/
theorem rationalRootRestriction_injective_of_rootSystems
    {I J : Type*}
    (P : RootPairing I ℚ (relativeRootSpan a) (Module.Dual ℚ (relativeRootSpan a)))
    (Q : RootPairing J ℚ
      (relativeRootSpan (T := T_L) (G := G_L) (j_L j))
      (Module.Dual ℚ (relativeRootSpan (T := T_L) (G := G_L) (j_L j))))
    [P.IsRootSystem] [Q.IsRootSystem] [Q.IsIrreducible]
    (hP : Subtype.val '' Set.range P.root = toRat '' relativeRoots a)
    (hQ : Subtype.val '' Set.range Q.root =
      toRat '' relativeRoots (T := T_L) (G := G_L) (j_L j))
    (hs : ∀ i j, P.pairing i j = P.pairing j i) :
    Function.Injective (hG.rationalRootRestriction (L := L) a j f ha hj hf hTL) := by
  apply Langlands.LinearAlgebra.SymmetricRootPairingForm.injective_of_mapsTo_roots P hs Q
  rintro _ ⟨i, rfl⟩
  have hx : (Q.root i).val ∈ toRat '' relativeRoots (T := T_L) (G := G_L) (j_L j) := by
    rw [← hQ]
    exact ⟨Q.root i, Set.mem_range_self i, rfl⟩
  obtain ⟨β, hβ, hβeq⟩ := hx
  have heq : Q.root i = rootVector (T := T_L) (G := G_L) (j_L j) ⟨β, hβ⟩ :=
    Subtype.ext hβeq.symm
  rw [heq, hG.rationalRootRestriction_rootVector]
  have hy : toRat (hG.rootRestriction (L := L) a j f ha hj hf hTL ⟨β, hβ⟩).val ∈
      Subtype.val '' Set.range P.root := by
    rw [hP]
    exact ⟨_, (hG.rootRestriction (L := L) a j f ha hj hf hTL ⟨β, hβ⟩).property, rfl⟩
  obtain ⟨_, ⟨n, rfl⟩, hn⟩ := hy
  exact ⟨n, Subtype.ext hn⟩

/-- Injectivity on the rational root span detects equality of actual roots
because the containing torus is split over the extension. -/
theorem rootRestriction_injective_of_rationalRootRestriction
    (hinj : Function.Injective (hG.rationalRootRestriction (L := L) a j f ha hj hf hTL)) :
    Function.Injective (hG.rootRestriction (L := L) a j f ha hj hf hTL) := by
  intro β γ heq
  apply (rootEmbedding (T := T_L) (G := G_L) (j_L j) hTL).injective
  apply hinj
  change hG.rationalRootRestriction (L := L) a j f ha hj hf hTL
      (rootVector (T := T_L) (G := G_L) (j_L j) β) =
    hG.rationalRootRestriction (L := L) a j f ha hj hf hTL
      (rootVector (T := T_L) (G := G_L) (j_L j) γ)
  rw [hG.rationalRootRestriction_rootVector, hG.rationalRootRestriction_rootVector, heq]

/-- With injective actual rational restriction, the ordinary Galois action
fixes every actual root character over the splitting extension. -/
theorem root_galois_eq_self_of_rationalRootRestriction_injective
    (hinj : Function.Injective (hG.rationalRootRestriction (L := L) a j f ha hj hf hTL))
    (σ : L ≃ₐ[k] L) (β : roots (T := T_L) (G := G_L) (j_L j)) :
    characterLattice.galoisRepresentation k L T σ β.val = β.val := by
  exact congrArg Subtype.val
    (hG.rootRestriction_injective_of_rationalRootRestriction (L := L) a j f ha hj hf hTL hinj
      (hG.rootRestriction_galois (L := L) a j f ha hj hf hTL σ β))

end IsQuasiSplit

end Langlands.GroupScheme
