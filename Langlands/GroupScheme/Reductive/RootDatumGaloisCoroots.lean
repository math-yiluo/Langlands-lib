import Langlands.GroupScheme.Reductive.RootDatumGaloisRoots
import Langlands.GroupScheme.Reductive.RootDatumBaseChangeProof
import Langlands.GroupScheme.Reductive.RootDatumCorootComparison
import Langlands.GroupScheme.CocharacterTransportNaturality
import Langlands.GroupScheme.Torus.WeylImageFinite
import Mathlib.LinearAlgebra.RootSystem.Hom

/-! # Ordinary Galois transport of actual root data and coroots -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u v

namespace Langlands.GroupScheme

section Descent

variable {B S : Scheme.{u}} (b : S ⟶ B) (a : S ⟶ S) (ha : a ≫ b = b)

/-- The canonical descent identification, with the commutative group structure. -/
def CommGroupScheme.descentBaseChangeIso (T : CommGroupScheme B) :
    (CommGroupScheme.baseChange a).obj ((CommGroupScheme.baseChange b).obj T) ≅
      (CommGroupScheme.baseChange b).obj T :=
  CommGroupScheme.isoOfGroupIso (Langlands.GroupScheme.descentBaseChangeIso b a ha T.toGrp)

variable {T : CommGroupScheme B} {G : GroupScheme B} (i : T.toGrp ⟶ G)

/-- A normalizing point remains realizable after canonical descent transport. -/
theorem IsNormalizingPoint.exists_descentTransport
    {n : Over.mk (𝟙 S) ⟶ ((GroupScheme.baseChange b).obj G).X}
    {τ : (CommGroupScheme.baseChange b).obj T ≅ (CommGroupScheme.baseChange b).obj T}
    (hn : IsNormalizingPoint (T := (CommGroupScheme.baseChange b).obj T)
      ((GroupScheme.baseChange b).map i) n τ) :
    ∃ n' : Over.mk (𝟙 S) ⟶ ((GroupScheme.baseChange b).obj G).X,
      IsNormalizingPoint (T := (CommGroupScheme.baseChange b).obj T)
        ((GroupScheme.baseChange b).map i) n'
        ((CommGroupScheme.descentBaseChangeIso b a ha T).symm ≪≫
          (CommGroupScheme.baseChange a).mapIso τ ≪≫
            CommGroupScheme.descentBaseChangeIso b a ha T) := by
  obtain ⟨n', hn'⟩ := hn.exists_baseChange a
  exact ⟨n' ≫ (descentBaseChangeIso b a ha G).hom.hom.hom,
    hn'.transport (CommGroupScheme.descentBaseChangeIso b a ha T)
      (descentBaseChangeIso b a ha G) (descentBaseChangeIso_naturality b a ha i)⟩

/-- Inverse precomposition intertwines the ordinary descent transport of characters. -/
theorem characterAut_descentTransport
    (τ : (CommGroupScheme.baseChange b).obj T ≅ (CommGroupScheme.baseChange b).obj T)
    (χ : characterLattice ((CommGroupScheme.baseChange b).obj T)) :
    characterAut
      ((CommGroupScheme.descentBaseChangeIso b a ha T).symm ≪≫
        (CommGroupScheme.baseChange a).mapIso τ ≪≫
          CommGroupScheme.descentBaseChangeIso b a ha T)
      (characterLattice.transport b a ha T χ) =
        characterLattice.transport b a ha T (characterAut τ χ) := by
  change ((CommGroupScheme.descentBaseChangeIso b a ha T).inv ≫
      (CommGroupScheme.baseChange a).map τ.inv ≫
        (CommGroupScheme.descentBaseChangeIso b a ha T).hom) ≫
    (CommGroupScheme.descentBaseChangeIso b a ha T).inv ≫
      (CommGroupScheme.baseChange a).map χ ≫ (Gm.commBaseChangeIso a).hom = _
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  change _ = (CommGroupScheme.descentBaseChangeIso b a ha T).inv ≫
    (CommGroupScheme.baseChange a).map (τ.inv ≫ χ) ≫ (Gm.commBaseChangeIso a).hom
  rw [Functor.map_comp, Category.assoc]

end Descent

section Galois

variable (k E : Type u) [Field k] [Field E] [Algebra k E]
    (T : CommGroupScheme (Spec (CommRingCat.of k)))
    {J : Type v}
    (P : RootDatum J
      (characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj T))
      (cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj T)))

/-- Transport a supplied root datum by the ordinary Galois lattice equivalences. -/
def galoisTransportRootDatum (σ : E ≃ₐ[k] E) :
    RootDatum J
      (characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj T))
      (cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj T)) :=
  P.map (Equiv.refl J) (characterLattice.galoisEquiv k E T σ)
    (cocharacterLattice.galoisEquiv k E T σ)

@[simp] theorem galoisTransportRootDatum_root (σ : E ≃ₐ[k] E) (j : J) :
    (galoisTransportRootDatum k E T P σ).root j =
      characterLattice.galoisRepresentation k E T σ (P.root j) := rfl

@[simp] theorem galoisTransportRootDatum_coroot (σ : E ≃ₐ[k] E) (j : J) :
    (galoisTransportRootDatum k E T P σ).coroot j =
      cocharacterLattice.galoisRepresentation k E T σ (P.coroot j) := rfl

@[simp] theorem galoisTransportRootDatum_pairing (σ : E ≃ₐ[k] E)
    (χ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj T))
    (ν : cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj T)) :
    (galoisTransportRootDatum k E T P σ).toLinearMap
      (characterLattice.galoisRepresentation k E T σ χ)
      (cocharacterLattice.galoisRepresentation k E T σ ν) = P.toLinearMap χ ν := by
  change P.toLinearMap
    ((characterLattice.galoisEquiv k E T σ).symm (characterLattice.galoisEquiv k E T σ χ))
    ((cocharacterLattice.galoisEquiv k E T σ).symm (cocharacterLattice.galoisEquiv k E T σ ν)) = _
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]

/-- Transported root reflections intertwine the ordinary character action. -/
theorem galoisTransportRootDatum_reflection (σ : E ≃ₐ[k] E) (j : J)
    (χ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj T)) :
    (galoisTransportRootDatum k E T P σ).reflection j
      (characterLattice.galoisRepresentation k E T σ χ) =
        characterLattice.galoisRepresentation k E T σ (P.reflection j χ) := by
  simp only [RootPairing.reflection_apply, RootPairing.coroot', LinearMap.flip_apply,
    galoisTransportRootDatum_root, galoisTransportRootDatum_coroot,
    galoisTransportRootDatum_pairing, map_sub, map_zsmul]

variable {T} {P}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (i : T.toGrp ⟶ G)

local instance galoisBaseChangeAffine :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k E)).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap k E))
  infer_instance

/-- Ordinary Galois transport preserves the actual-root-datum predicate. -/
theorem IsRootDatumOf.galoisTransport
    (hP : IsRootDatumOf (T := (CommGroupScheme.baseChange (algebraBaseMap k E)).obj T)
      ((GroupScheme.baseChange (algebraBaseMap k E)).map i) P)
    (σ : E ≃ₐ[k] E) :
    IsRootDatumOf ((GroupScheme.baseChange (algebraBaseMap k E)).map i)
      (galoisTransportRootDatum k E T P σ) := by
  refine ⟨?_, ?_, ?_⟩
  · ext χ ν
    obtain ⟨χ, rfl⟩ := (characterLattice.galoisEquiv k E T σ).surjective χ
    obtain ⟨ν, rfl⟩ := (cocharacterLattice.galoisEquiv k E T σ).surjective ν
    change (galoisTransportRootDatum k E T P σ).toLinearMap
      (characterLattice.galoisRepresentation k E T σ χ)
      (cocharacterLattice.galoisRepresentation k E T σ ν) = _
    rw [galoisTransportRootDatum_pairing, hP.1]
    exact (latticePairing_galoisRepresentation k E T σ χ ν).symm
  · apply Set.Subset.antisymm
    · rintro χ ⟨j, rfl⟩
      rw [galoisTransportRootDatum_root, mem_roots_galois_iff, ← hP.2.1]
      exact ⟨j, rfl⟩
    · intro χ hχ
      obtain ⟨ψ, hψ⟩ := (characterLattice.galoisEquiv k E T σ).surjective χ
      have hψroot : ψ ∈ roots ((GroupScheme.baseChange (algebraBaseMap k E)).map i) := by
        apply (mem_roots_galois_iff k E i σ ψ).mp
        exact hψ.symm ▸ hχ
      obtain ⟨j, hj⟩ := hP.2.1.symm ▸ hψroot
      refine ⟨j, ?_⟩
      rw [galoisTransportRootDatum_root, hj]
      exact hψ
  · intro j
    obtain ⟨n, τ, hn, hτ⟩ := hP.2.2 j
    obtain ⟨n', hn'⟩ := hn.exists_descentTransport (algebraBaseMap k E)
      (galoisBaseMap k E σ) (galoisBaseMap_over k E σ)
    refine ⟨n', _, hn', ?_⟩
    apply LinearEquiv.ext
    intro χ'
    obtain ⟨χ, rfl⟩ := (characterLattice.galoisEquiv k E T σ).surjective χ'
    change characterAut _ (characterLattice.galoisRepresentation k E T σ χ) =
      (galoisTransportRootDatum k E T P σ).reflection j
        (characterLattice.galoisRepresentation k E T σ χ)
    rw [galoisTransportRootDatum_reflection,
      characterLattice.galoisRepresentation_apply, characterAut_descentTransport, hτ]
    rfl

section FiniteWeylImage

variable [Mono ((GroupScheme.baseChange (algebraBaseMap k E)).map i).hom.hom.left]
    [Finite (weylImage (T := (CommGroupScheme.baseChange (algebraBaseMap k E)).obj T)
      ((GroupScheme.baseChange (algebraBaseMap k E)).map i))]

/-- The ordinary Galois index permutation transforms actual coroots as well as roots. -/
theorem IsRootDatumOf.galoisRootIndexEquiv_coroot
    (hP : IsRootDatumOf (T := (CommGroupScheme.baseChange (algebraBaseMap k E)).obj T)
      ((GroupScheme.baseChange (algebraBaseMap k E)).map i) P)
    (σ : E ≃ₐ[k] E) (j : J) :
    P.coroot (IsRootDatumOf.galoisRootIndexEquiv k E i hP σ j) =
      cocharacterLattice.galoisRepresentation k E T σ (P.coroot j) := by
  change P.coroot (IsRootDatumOf.galoisRootIndexEquiv k E i hP σ j) =
    (galoisTransportRootDatum k E T P σ).coroot j
  apply hP.coroot_eq_of_finite_weylImage _ (IsRootDatumOf.galoisTransport k E i hP σ)
  rw [galoisTransportRootDatum_root, IsRootDatumOf.galoisRootIndexEquiv_root]

/-- The actual ordinary Galois root-datum automorphism. The coweight map is
contravariant, so its field automorphism is inverted. -/
def IsRootDatumOf.galoisRootDatumAut
    (hP : IsRootDatumOf (T := (CommGroupScheme.baseChange (algebraBaseMap k E)).obj T)
      ((GroupScheme.baseChange (algebraBaseMap k E)).map i) P)
    (σ : E ≃ₐ[k] E) : RootPairing.Aut P where
  weightMap := characterLattice.galoisRepresentation k E T σ
  coweightMap := cocharacterLattice.galoisRepresentation k E T σ⁻¹
  indexEquiv := IsRootDatumOf.galoisRootIndexEquiv k E i hP σ
  weight_coweight_transpose := by
    ext ν χ
    change P.toLinearMap (characterLattice.galoisRepresentation k E T σ χ) ν =
      P.toLinearMap χ (cocharacterLattice.galoisRepresentation k E T σ⁻¹ ν)
    rw [hP.1]
    simpa only [inv_inv] using
      (latticePairing_galoisRepresentation_right k E T σ⁻¹ χ ν).symm
  root_weightMap := by
    funext j
    exact (IsRootDatumOf.galoisRootIndexEquiv_root k E i hP σ j).symm
  coroot_coweightMap := by
    funext j
    apply (cocharacterLattice.galoisEquiv k E T σ).injective
    change cocharacterLattice.galoisRepresentation k E T σ
        (cocharacterLattice.galoisRepresentation k E T σ⁻¹ (P.coroot j)) =
      cocharacterLattice.galoisRepresentation k E T σ
        (P.coroot ((IsRootDatumOf.galoisRootIndexEquiv k E i hP σ).symm j))
    rw [Representation.self_inv_apply,
      ← IsRootDatumOf.galoisRootIndexEquiv_coroot k E i hP σ,
      Equiv.apply_symm_apply]
  bijective_weightMap := (characterLattice.galoisEquiv k E T σ).bijective
  bijective_coweightMap := (cocharacterLattice.galoisEquiv k E T σ⁻¹).bijective

@[simp] theorem IsRootDatumOf.galoisRootDatumAut_weightMap
    (hP : IsRootDatumOf (T := (CommGroupScheme.baseChange (algebraBaseMap k E)).obj T)
      ((GroupScheme.baseChange (algebraBaseMap k E)).map i) P)
    (σ : E ≃ₐ[k] E) :
    (IsRootDatumOf.galoisRootDatumAut k E i hP σ).weightMap =
      characterLattice.galoisRepresentation k E T σ := rfl

@[simp] theorem IsRootDatumOf.galoisRootDatumAut_coweightMap
    (hP : IsRootDatumOf (T := (CommGroupScheme.baseChange (algebraBaseMap k E)).obj T)
      ((GroupScheme.baseChange (algebraBaseMap k E)).map i) P)
    (σ : E ≃ₐ[k] E) :
    (IsRootDatumOf.galoisRootDatumAut k E i hP σ).coweightMap =
      cocharacterLattice.galoisRepresentation k E T σ⁻¹ := rfl

@[simp] theorem IsRootDatumOf.galoisRootDatumAut_indexEquiv
    (hP : IsRootDatumOf (T := (CommGroupScheme.baseChange (algebraBaseMap k E)).obj T)
      ((GroupScheme.baseChange (algebraBaseMap k E)).map i) P)
    (σ : E ≃ₐ[k] E) :
    (IsRootDatumOf.galoisRootDatumAut k E i hP σ).indexEquiv =
      IsRootDatumOf.galoisRootIndexEquiv k E i hP σ := rfl

/-- The actual ordinary root-datum automorphisms satisfy the Galois group law. -/
def IsRootDatumOf.galoisRootDatumAction
    (hP : IsRootDatumOf (T := (CommGroupScheme.baseChange (algebraBaseMap k E)).obj T)
      ((GroupScheme.baseChange (algebraBaseMap k E)).map i) P) :
    (E ≃ₐ[k] E) →* RootPairing.Aut P where
  toFun := IsRootDatumOf.galoisRootDatumAut k E i hP
  map_one' := by
    ext x
    · change characterLattice.galoisRepresentation k E T 1 x = x
      rw [map_one]
      rfl
    · change cocharacterLattice.galoisRepresentation k E T (1 : E ≃ₐ[k] E)⁻¹ x = x
      rw [inv_one, map_one]
      rfl
    · exact congrArg (fun e : Equiv.Perm J => e x) (map_one
        (IsRootDatumOf.galoisRootIndexAction k E i hP))
  map_mul' σ τ := by
    ext x
    · change characterLattice.galoisRepresentation k E T (σ * τ) x =
        characterLattice.galoisRepresentation k E T σ
          (characterLattice.galoisRepresentation k E T τ x)
      rw [map_mul]
      rfl
    · change cocharacterLattice.galoisRepresentation k E T (σ * τ)⁻¹ x =
        cocharacterLattice.galoisRepresentation k E T τ⁻¹
          (cocharacterLattice.galoisRepresentation k E T σ⁻¹ x)
      rw [mul_inv_rev, map_mul]
      rfl
    · exact congrArg (fun e : Equiv.Perm J => e x) (map_mul
        (IsRootDatumOf.galoisRootIndexAction k E i hP) σ τ)

end FiniteWeylImage

section ClosedSplitTorus

variable [LocallyOfFiniteType G.X.hom]

local instance galoisBaseChangeFiniteType :
    LocallyOfFiniteType ((GroupScheme.baseChange (algebraBaseMap k E)).obj G).X.hom := by
  change LocallyOfFiniteType (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap k E))
  infer_instance

/-- Closed split tori in affine algebraic groups need no separate finite-Weyl-image premise. -/
def IsRootDatumOf.galoisRootDatumActionOfClosedSplitTorus
    (hT : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj T).toGrp)
    (hi : IsClosedImmersion ((GroupScheme.baseChange (algebraBaseMap k E)).map i).hom.hom.left)
    (hP : IsRootDatumOf (T := (CommGroupScheme.baseChange (algebraBaseMap k E)).obj T)
      ((GroupScheme.baseChange (algebraBaseMap k E)).map i) P) :
    (E ≃ₐ[k] E) →* RootPairing.Aut P := by
  haveI := hi
  haveI : Finite (weylImage (T := (CommGroupScheme.baseChange (algebraBaseMap k E)).obj T)
      ((GroupScheme.baseChange (algebraBaseMap k E)).map i)) :=
    splitTorusWeylImageFinite E _ _ hT _ hi
  exact IsRootDatumOf.galoisRootDatumAction k E i hP

/-- The closed-split specialization has exactly the ordinary character map. -/
@[simp] theorem IsRootDatumOf.galoisRootDatumActionOfClosedSplitTorus_weightMap
    (hT : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj T).toGrp)
    (hi : IsClosedImmersion ((GroupScheme.baseChange (algebraBaseMap k E)).map i).hom.hom.left)
    (hP : IsRootDatumOf (T := (CommGroupScheme.baseChange (algebraBaseMap k E)).obj T)
      ((GroupScheme.baseChange (algebraBaseMap k E)).map i) P)
    (σ : E ≃ₐ[k] E) :
    (IsRootDatumOf.galoisRootDatumActionOfClosedSplitTorus k E i hT hi hP σ).weightMap =
      characterLattice.galoisRepresentation k E T σ := rfl

/-- The closed-split specialization has exactly the contravariant ordinary cocharacter map. -/
@[simp] theorem IsRootDatumOf.galoisRootDatumActionOfClosedSplitTorus_coweightMap
    (hT : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj T).toGrp)
    (hi : IsClosedImmersion ((GroupScheme.baseChange (algebraBaseMap k E)).map i).hom.hom.left)
    (hP : IsRootDatumOf (T := (CommGroupScheme.baseChange (algebraBaseMap k E)).obj T)
      ((GroupScheme.baseChange (algebraBaseMap k E)).map i) P)
    (σ : E ≃ₐ[k] E) :
    (IsRootDatumOf.galoisRootDatumActionOfClosedSplitTorus k E i hT hi hP σ).coweightMap =
      cocharacterLattice.galoisRepresentation k E T σ⁻¹ := rfl

/-- The closed-split specialization retains the ordinary actual-root index action. -/
@[simp] theorem IsRootDatumOf.galoisRootDatumActionOfClosedSplitTorus_indexEquiv
    (hT : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj T).toGrp)
    (hi : IsClosedImmersion ((GroupScheme.baseChange (algebraBaseMap k E)).map i).hom.hom.left)
    (hP : IsRootDatumOf (T := (CommGroupScheme.baseChange (algebraBaseMap k E)).obj T)
      ((GroupScheme.baseChange (algebraBaseMap k E)).map i) P)
    (σ : E ≃ₐ[k] E) :
    (IsRootDatumOf.galoisRootDatumActionOfClosedSplitTorus k E i hT hi hP σ).indexEquiv =
      IsRootDatumOf.galoisRootIndexEquiv k E i hP σ := rfl

end ClosedSplitTorus

end Galois

end Langlands.GroupScheme
