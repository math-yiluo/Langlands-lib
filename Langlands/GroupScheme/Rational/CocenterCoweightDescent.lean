import Langlands.GroupScheme.Rational.LeviCocenterRootModelStatement
import Langlands.GroupScheme.Reductive.RootDatumGaloisCoroots
import Langlands.GroupScheme.Reductive.RootDatumWeylComparison
import Langlands.LinearAlgebra.RootDatumCoweightFace

/-! # Actual cocenter descent from an ordinary Galois-fixed coweight -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Finiteness of the actual normalizer image implies finiteness of the
abstract Weyl group of every supplied actual root datum. -/
theorem IsRootDatumOf.finite_abstractWeylGroup
    {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {i : T.toGrp ⟶ G} [IsAffineHom G.X.hom] [Mono i.hom.hom.left]
    {J : Type*} {P : RootDatum J (characterLattice T) (cocharacterLattice T)}
    (hP : IsRootDatumOf i P) [Finite (weylImage i)] : Finite P.weylGroup := by
  let f : P.weylGroup → weylImage i := fun w =>
    ⟨RootPairing.Equiv.weightHom P w.val,
      hP.abstractWeylImage_le ⟨w.val, w.property, rfl⟩⟩
  apply Finite.of_injective f
  intro a b hab
  apply Subtype.ext
  exact RootPairing.Equiv.weightHom_injective P (congrArg Subtype.val hab)

section Descent

variable (k E : Type u) [Field k] [Field E] [Algebra k E]
    {T Q : CommGroupScheme (Spec (CommRingCat.of k))}
    (g : T ⟶ Q)
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (i : T.toGrp ⟶ G)
    {J : Type u} [Finite J]
    (P : RootDatum J
      (characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj T))
      (cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj T)))
    [P.IsReduced]

local instance descentBaseChangeAffine :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k E)).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap k E))
  infer_instance

local instance descentBaseChangeFiniteType :
    LocallyOfFiniteType ((GroupScheme.baseChange (algebraBaseMap k E)).obj G).X.hom := by
  change LocallyOfFiniteType
    (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap k E))
  infer_instance

/-- Choose a genuine root base whose simple zero-root subset gives actual
cocenter descent data. The geometric inputs are an ordinary Galois-fixed
coweight and the exact actual character image as its zero-coroot annihilator. -/
noncomputable def coweightCocenterRootDescent
    (hT : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj T).toGrp)
    (hi : IsClosedImmersion ((GroupScheme.baseChange (algebraBaseMap k E)).map i).hom.hom.left)
    (hP : IsRootDatumOf (T := (CommGroupScheme.baseChange (algebraBaseMap k E)).obj T)
      ((GroupScheme.baseChange (algebraBaseMap k E)).map i) P)
    (ν : cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj T))
    (hν : ∀ σ : E ≃ₐ[k] E, cocharacterLattice.galoisRepresentation k E T σ ν = ν)
    (hf : Function.Injective (characterLattice.baseChangePullback k E g))
    (hrange : ∀ x, x ∈ (characterLattice.baseChangePullback k E g).range ↔
      ∀ j, P.root' j ν = 0 → P.toLinearMap x (P.coroot j) = 0) :
    {B : P.Base // CocenterRootDescentData k E g P B
      {j : B.support | P.root' j ν = 0}} := by
  classical
  letI := Fintype.ofFinite J
  haveI := hi
  haveI : Finite (weylImage (T := (CommGroupScheme.baseChange (algebraBaseMap k E)).obj T)
      ((GroupScheme.baseChange (algebraBaseMap k E)).map i)) :=
    splitTorusWeylImageFinite E _ _ hT _ hi
  haveI : Finite P.weylGroup := hP.finite_abstractWeylGroup
  let C := LinearAlgebra.RootDatumCoweightFace.coweightFace P ν
  let δ := IsRootDatumOf.galoisRootDatumActionOfClosedSplitTorus k E i hT hi hP
  have hδ (σ : E ≃ₐ[k] E) : (δ σ).coweightEquiv ν = ν := by
    change cocharacterLattice.galoisRepresentation k E T σ⁻¹ ν = ν
    exact hν σ⁻¹
  let D (σ : E ≃ₐ[k] E) := C.correction (δ σ) (hδ σ)
  have hweight (σ : E ≃ₐ[k] E) (x) :
      (δ σ).weightEquiv x = characterLattice.galoisRepresentation k E T σ x := rfl
  have hcoweight (σ : E ≃ₐ[k] E) (y) :
      (δ σ).coweightEquiv.symm y =
        cocharacterLattice.galoisRepresentation k E T σ y := by
    apply (δ σ).coweightEquiv.injective
    rw [LinearEquiv.apply_symm_apply]
    change y = cocharacterLattice.galoisRepresentation k E T σ⁻¹
      (cocharacterLattice.galoisRepresentation k E T σ y)
    exact (Representation.inv_self_apply _ σ y).symm
  refine ⟨C.base, hf, ?_, ?_⟩
  · intro x
    rw [hrange, C.annihilator_iff]
    constructor
    · intro hx j hj
      exact hx j j.property hj
    · intro hx j hj hz
      exact hx ⟨j, hj⟩ hz
  · refine ⟨(fun σ => (D σ).weyl.val.weightEquiv.toLinearMap),
      (fun σ => (D σ).weyl.val.coweightEquiv.symm.toLinearMap),
      (fun σ => (D σ).perm), ?_, ?_, ?_, ?_⟩
    · intro σ x
      apply (D σ).fixed
      exact (hrange _).mp (LinearMap.mem_range_self _ x)
    · intro σ x y
      simpa only [LinearEquiv.coe_coe, hweight, hcoweight] using (D σ).pairing x y
    · intro σ j
      simpa only [LinearEquiv.coe_coe, hcoweight] using (D σ).coroot j
    · intro σ j
      exact (D σ).zero_iff j

end Descent

end Langlands.GroupScheme
