import Langlands.GroupScheme.Reductive.RootDatum
import Langlands.GroupScheme.Torus.MaximalTransport
import Mathlib.LinearAlgebra.RootSystem.Hom

/-! # Actual lattice maps of root-datum homomorphisms -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry

namespace Langlands

/-- An isomorphism of underlying group schemes is also an isomorphism in the
category of commutative group schemes. -/
theorem CommGroupScheme.isIso_of_groupHom_isIso {S : Scheme.{u}}
    {T T' : CommGroupScheme S} (t : T ⟶ T') [IsIso (CommGroupScheme.groupHom t)] :
    IsIso t := by
  refine ⟨⟨Additive.ofMul (inv (CommGroupScheme.groupHom t)), ?_, ?_⟩⟩
  · exact congrArg Additive.ofMul (IsIso.hom_inv_id (CommGroupScheme.groupHom t))
  · exact congrArg Additive.ofMul (IsIso.inv_hom_id (CommGroupScheme.groupHom t))

namespace GroupScheme

variable {k : Type u} [Field k]
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    {T T' : CommGroupScheme (Spec (CommRingCat.of k))}

/-- In a commuting square of torus embeddings over an ambient group isomorphism,
maximality of the source torus makes the torus map an isomorphism. -/
theorem IsMaximalTorus.isIso_factor_of_isIso {i : T.toGrp ⟶ G}
    (hi : IsMaximalTorus i) {j : T'.toGrp ⟶ H}
    (hT' : IsTorus T'.toGrp) (hj : IsClosedSubgroup j)
    (φ : G ⟶ H) [IsIso φ] (t : T ⟶ T')
    (ht : i ≫ φ = CommGroupScheme.groupHom t ≫ j) : IsIso t := by
  have : IsIso (CommGroupScheme.groupHom t) :=
    (hi.comp_iso (asIso φ)).2.2 T' j (CommGroupScheme.groupHom t) hT' hj ht.symm
  exact CommGroupScheme.isIso_of_groupHom_isIso t

namespace RootDatumHom

variable {J : Type v} {J' : Type w}
    {P : RootDatum J (characterLattice T) (cocharacterLattice T)}
    {Q : RootDatum J' (characterLattice T') (cocharacterLattice T')}

/-- If the weight map is actual character pullback, its transpose is actual
cocharacter postcomposition, provided both pairings are the actual lattice pairings. -/
theorem coweightMap_apply_of_weightMap
    (hP : P.toLinearMap = latticePairing T) (hQ : Q.toLinearMap = latticePairing T')
    (f : RootPairing.Hom P Q) (t : T' ⟶ T)
    (hf : ∀ χ : characterLattice T, f.weightMap χ = t ≫ χ)
    (ν : cocharacterLattice T') : f.coweightMap ν = ν ≫ t := by
  apply P.flip.toPerfPair.injective
  ext χ
  have h := LinearMap.congr_fun (f.weight_coweight_transpose_apply P Q ν) χ
  change Q.toLinearMap (f.weightMap χ) ν = P.toLinearMap χ (f.coweightMap ν) at h
  change P.toLinearMap χ (f.coweightMap ν) = P.toLinearMap χ (ν ≫ t)
  rw [← h, hQ, hP, hf]
  exact congrArg (gmEndEquiv k) (Category.assoc ν t χ).symm

/-- An isomorphism of tori induces an injective coweight map when its character
pullback is the weight map of the root-datum homomorphism. -/
theorem injective_coweightMap_of_isIso
    (hP : P.toLinearMap = latticePairing T) (hQ : Q.toLinearMap = latticePairing T')
    (f : RootPairing.Hom P Q) (t : T' ⟶ T) [IsIso t]
    (hf : ∀ χ : characterLattice T, f.weightMap χ = t ≫ χ) :
    Function.Injective f.coweightMap := by
  intro ν μ h
  rw [coweightMap_apply_of_weightMap hP hQ f t hf,
    coweightMap_apply_of_weightMap hP hQ f t hf] at h
  exact (cancel_mono t).1 h

/-- An isomorphism of tori induces a surjective coweight map in every root-datum
homomorphism whose weight map is actual character pullback. -/
theorem surjective_coweightMap_of_isIso
    (hP : P.toLinearMap = latticePairing T) (hQ : Q.toLinearMap = latticePairing T')
    (f : RootPairing.Hom P Q) (t : T' ⟶ T) [IsIso t]
    (hf : ∀ χ : characterLattice T, f.weightMap χ = t ≫ χ) :
    Function.Surjective f.coweightMap := by
  intro ν
  refine ⟨ν ≫ inv t, ?_⟩
  rw [coweightMap_apply_of_weightMap hP hQ f t hf, Category.assoc,
    IsIso.inv_hom_id, Category.comp_id]

/-- The integral coweight equivalence of a root-datum homomorphism whose weight
map is pullback along an isomorphism of the actual tori. Its forward map is
the given root-datum homomorphism's coweight map. -/
def coweightMapEquivOfIso
    (hP : P.toLinearMap = latticePairing T) (hQ : Q.toLinearMap = latticePairing T')
    (f : RootPairing.Hom P Q) (t : T' ⟶ T) [IsIso t]
    (hf : ∀ χ : characterLattice T, f.weightMap χ = t ≫ χ) :
    cocharacterLattice T' ≃ₗ[ℤ] cocharacterLattice T :=
  LinearEquiv.ofBijective f.coweightMap
    ⟨injective_coweightMap_of_isIso hP hQ f t hf,
      surjective_coweightMap_of_isIso hP hQ f t hf⟩

@[simp]
theorem coweightMapEquivOfIso_apply
    (hP : P.toLinearMap = latticePairing T) (hQ : Q.toLinearMap = latticePairing T')
    (f : RootPairing.Hom P Q) (t : T' ⟶ T) [IsIso t]
    (hf : ∀ χ : characterLattice T, f.weightMap χ = t ≫ χ)
    (ν : cocharacterLattice T') :
    coweightMapEquivOfIso hP hQ f t hf ν = f.coweightMap ν := rfl

end RootDatumHom

end GroupScheme
end Langlands
