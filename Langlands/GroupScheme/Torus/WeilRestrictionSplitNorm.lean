import Langlands.GroupScheme.Torus.WeilRestrictionGaloisPoints
import Langlands.GroupScheme.Torus.UniversalPoint
import Langlands.GroupScheme.AffineWeilRestrictionTopology
import Langlands.GroupScheme.IntegralModel.SplitTorusBoundedPoints
import Langlands.Geometry.Building.KPZeroNormKernel

/-! # From `Res_{(I → L)/k} 𝔾ₘ` to the Weil restriction of a split `L`-torus

Let `L / k` be a finite field extension and `G` a group scheme over `L` with an isomorphism
`σ : G ≅ 𝔾ₘ^I` over `L`. This file builds a homomorphism of `k`-group schemes
`Res_{(I → L)/k} 𝔾ₘ ⟶ Res_{L/k} G`. On `T`-points it sends a unit `u` of `(I → L) ⊗[k] T` to
the point of `G` over `L ⊗[k] T` whose split coordinates are the coordinates of `u`. The file
computes the map on rational points and identifies the character-valuation kernel of `G(L)` in
split coordinates. -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj
open Langlands.Geometry.Building

namespace Langlands.GroupScheme.WeilGm

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

section SplitWeil

variable (k L : Type u) [Field k] [Field L] [Algebra k L] (I : Type u) [Fintype I]

/-- The `i`-th coordinate `(I → L) ⊗[k] T → L ⊗[k] T`. -/
def splitCoord (T : Type u) [CommRing T] [Algebra k T] (i : I) :
    (I → L) ⊗[k] T →ₐ[k] L ⊗[k] T :=
  Algebra.TensorProduct.map (Pi.evalAlgHom k (fun _ : I => L) i) (AlgHom.id k T)

omit [Fintype I] in
@[simp] theorem splitCoord_tmul (T : Type u) [CommRing T] [Algebra k T] (i : I)
    (b : I → L) (t : T) :
    splitCoord k L I T i (b ⊗ₜ t) = b i ⊗ₜ t :=
  rfl

omit [Fintype I] in
/-- The coordinates commute with change of the test algebra. -/
theorem splitCoord_naturality {T T' : Type u} [CommRing T] [Algebra k T] [CommRing T']
    [Algebra k T'] (f : T →ₐ[k] T') (i : I) (x : (I → L) ⊗[k] T) :
    splitCoord k L I T' i (Algebra.TensorProduct.lTensor (S := I → L) (I → L) f x) =
      Algebra.TensorProduct.lTensor (S := L) L f (splitCoord k L I T i x) := by
  induction x using TensorProduct.inductionOn with
  | tmul b t => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

omit [Fintype I] in
/-- At the tensor unit, the coordinates are the coordinates of `(I → L) ⊗[k] k ≃ (I → L)`. -/
theorem rid_splitCoord (i : I) (x : (I → L) ⊗[k] k) :
    Algebra.TensorProduct.rid k L L (splitCoord k L I k i x) =
      Algebra.TensorProduct.rid k (I → L) (I → L) x i := by
  induction x using TensorProduct.inductionOn with
  | tmul b t => simp
  | add x y hx hy => simp only [map_add, hx, hy, Pi.add_apply]

omit [Fintype I] in
/-- Change of coefficients on split-torus points acts on the unit coordinates. -/
theorem algSpec_map_comp_algebraPointsEquiv_symm [Finite I] {A B : Type u} [CommRing A]
    [Algebra L A] [CommRing B] [Algebra L B] (f : A →ₐ[L] B) (t : I → Aˣ) :
    (algSpec (CommRingCat.of L)).map (CommAlgCat.ofHom f).op ≫
        (splitTorus.algebraPointsEquiv (R := CommRingCat.of L) I A).symm t =
      (splitTorus.algebraPointsEquiv (R := CommRingCat.of L) I B).symm
        (fun i => Units.map f.toMonoidHom (t i)) := by
  apply (splitTorus.algebraPointsEquiv (R := CommRingCat.of L) I B).injective
  have h := splitTorus.algebraPointsEquiv_naturality (R := CommRingCat.of L) I f
    ((splitTorus.algebraPointsEquiv (R := CommRingCat.of L) I A).symm t)
  rw [Lie.affineMap_apply, MulEquiv.apply_symm_apply] at h
  rw [h, MulEquiv.apply_symm_apply]

variable (G : GroupScheme (Spec (CommRingCat.of L)))
  (σ : G ≅ splitTorus (Spec (CommRingCat.of L)) I)

/-- On `T`-points: the point of `G` over `L ⊗[k] T` with split coordinates the coordinates of
a unit of `(I → L) ⊗[k] T`. -/
def splitWeilPointHom (T : CommAlgCat.{u} (CommRingCat.of k)) :
    ((I → L) ⊗[CommRingCat.of k] T)ˣ →*
      G.affinePoints (CommAlgCat.of (CommRingCat.of L) (L ⊗[k] T)) :=
  ((splitTorus (Spec (CommRingCat.of L)) I).affinePointsTarget σ.inv
      (CommAlgCat.of (CommRingCat.of L) (L ⊗[k] T))).comp
    ((splitTorus.algebraPointsEquiv (R := CommRingCat.of L) I (L ⊗[k] T)).symm.toMonoidHom.comp
      (MonoidHom.pi fun i => Units.map (splitCoord k L I T i).toMonoidHom))

theorem splitWeilPointHom_apply (T : CommAlgCat.{u} (CommRingCat.of k))
    (w : ((I → L) ⊗[CommRingCat.of k] T)ˣ) :
    splitWeilPointHom k L I G σ T w =
      (splitTorus.algebraPointsEquiv (R := CommRingCat.of L) I (L ⊗[k] T)).symm
          (fun i => Units.map (splitCoord k L I T i).toMonoidHom w) ≫ σ.inv.hom.hom :=
  rfl

theorem splitWeilPointHom_naturality {T T' : CommAlgCat.{u} (CommRingCat.of k)} (g : T ⟶ T')
    (w : ((I → L) ⊗[CommRingCat.of k] T)ˣ) :
    G.affinePointMap (CommAlgCat.ofHom (Algebra.TensorProduct.lTensor (S := L) L g.hom))
        (splitWeilPointHom k L I G σ T w) =
      splitWeilPointHom k L I G σ T'
        (Units.map (Algebra.TensorProduct.lTensor (S := I → L) (I → L) g.hom :
          (I → L) ⊗[CommRingCat.of k] T →* (I → L) ⊗[CommRingCat.of k] T') w) := by
  rw [splitWeilPointHom_apply, splitWeilPointHom_apply, affinePointMap_apply,
    ← Category.assoc]
  refine congrArg (· ≫ σ.inv.hom.hom) ?_
  apply (splitTorus.algebraPointsEquiv (R := CommRingCat.of L) I (L ⊗[k] T')).injective
  rw [MulEquiv.apply_symm_apply]
  have h := splitTorus.algebraPointsEquiv_naturality (R := CommRingCat.of L) I
    (Algebra.TensorProduct.lTensor (S := L) L g.hom)
    ((splitTorus.algebraPointsEquiv (R := CommRingCat.of L) I (L ⊗[k] T)).symm
      (fun i => Units.map (splitCoord k L I T i).toMonoidHom w))
  rw [Lie.affineMap_apply, MulEquiv.apply_symm_apply] at h
  rw [h]
  funext i
  apply Units.ext
  exact (splitCoord_naturality k L I g.hom i (w : (I → L) ⊗[k] T)).symm

/-- The point maps form a natural transformation of group-valued functors. -/
def splitWeilNat :
    functor (CommRingCat.of k) (I → L) ⟶ AffineWeil.pointFunctor k L G where
  app T := GrpCat.ofHom (splitWeilPointHom k L I G σ T)
  naturality T T' g := by
    ext w
    exact (splitWeilPointHom_naturality k L I G σ g w).symm

variable [FiniteDimensional k L] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

/-- The homomorphism `Res_{(I → L)/k} 𝔾ₘ ⟶ Res_{L/k} G` of `k`-group schemes. -/
def splitWeilHom :
    groupScheme (CommRingCat.of k) (I → L) ⟶ AffineWeil.groupScheme k L G :=
  Corepresented.groupSchemeMap (corepresentableBy (CommRingCat.of k) (I → L))
    (AffineWeil.corepresentableBy k L G) (splitWeilNat k L I G σ)

set_option maxRecDepth 20000 in
/-- On affine test algebras, the homomorphism is the point map `splitWeilPointHom`. -/
theorem splitWeilHom_affinePoints' (S : CommAlgCat.{u} (CommRingCat.of k))
    (x : (algSpec (CommRingCat.of k)).obj (op S) ⟶
      (groupScheme (CommRingCat.of k) (I → L)).X) :
    Corepresented.affinePointsEquiv (AffineWeil.pointFunctor k L G)
        (AffineWeil.corepresentableBy k L G) S (x ≫ (splitWeilHom k L I G σ).hom.hom) =
      (splitWeilNat k L I G σ).app S
        (Corepresented.affinePointsEquiv (functor (CommRingCat.of k) (I → L))
          (corepresentableBy (CommRingCat.of k) (I → L)) S x) :=
  Corepresented.groupSchemeMap_affinePoints _ _ _ x

set_option maxRecDepth 20000 in
/-- On affine test algebras, the homomorphism is the point map `splitWeilPointHom`. -/
theorem splitWeilHom_affinePoints (T : Type u) [CommRing T] [Algebra k T]
    (x : (groupScheme (CommRingCat.of k) (I → L)).affinePoints
      (CommAlgCat.of (CommRingCat.of k) T)) :
    AffineWeil.pointsEquiv k L G T
        ((groupScheme (CommRingCat.of k) (I → L)).affinePointsTarget (splitWeilHom k L I G σ)
          (CommAlgCat.of (CommRingCat.of k) T) x) =
      splitWeilPointHom k L I G σ (CommAlgCat.of (CommRingCat.of k) T)
        (affineUnitsEquiv (CommRingCat.of k) (I → L) (CommAlgCat.of (CommRingCat.of k) T) x) :=
  splitWeilHom_affinePoints' k L I G σ _ x

/-- On rational points, followed by the base-point comparison of the Weil restriction, the
homomorphism gives the point of `G(L)` whose split coordinates are the coordinates of the
corresponding unit of `I → L`. -/
theorem basePointsEquiv_splitWeilHom
    (y : rationalPoints (groupScheme (CommRingCat.of k) (I → L))) :
    AffineWeil.basePointsEquiv k L G
        (GaloisPointComparison.rationalCoeffEquiv k _
          (rationalPoints.map (splitWeilHom k L I G σ) y)) =
      (splitTorus.algebraPointsEquiv (R := CommRingCat.of L) I L).symm
          (fun i => Units.map (Pi.evalMonoidHom (fun _ : I => L) i)
            (rationalUnitsEquiv k (I → L) y)) ≫ σ.inv.hom.hom := by
  rw [GaloisPointComparison.rationalCoeffEquiv_map]
  unfold AffineWeil.basePointsEquiv
  rw [MulEquiv.trans_apply, splitWeilHom_affinePoints, AffineWeil.tensorUnitPointsEquiv_apply,
    affinePointMap_apply, splitWeilPointHom_apply, ← Category.assoc,
    algSpec_map_comp_algebraPointsEquiv_symm]
  refine congrArg (fun t => (splitTorus.algebraPointsEquiv (R := CommRingCat.of L) I L).symm t ≫
    σ.inv.hom.hom) ?_
  funext i
  apply Units.ext
  exact rid_splitCoord k L I i _

/-- The same computation, read back as a rational point of `G`: it is the image under `σ⁻¹` of
the split-torus point with the coordinates of the corresponding unit of `I → L`. -/
theorem rationalCoeffEquiv_symm_basePointsEquiv_splitWeilHom
    (y : rationalPoints (groupScheme (CommRingCat.of k) (I → L))) :
    (GaloisPointComparison.rationalCoeffEquiv L G).symm
        (AffineWeil.basePointsEquiv k L G
          (GaloisPointComparison.rationalCoeffEquiv k _
            (rationalPoints.map (splitWeilHom k L I G σ) y))) =
      rationalPoints.map σ.inv
        ((splitTorus.affinePointsEquiv I (𝟙 (Spec (CommRingCat.of L)))).symm
          (fun i => Units.map (Pi.evalMonoidHom (fun _ : I => L) i)
            (rationalUnitsEquiv k (I → L) y))) := by
  rw [basePointsEquiv_splitWeilHom, MulEquiv.symm_apply_eq,
    GaloisPointComparison.rationalCoeffEquiv_map, affinePointsTarget_apply,
    ← IntegralModel.SplitTorusClosure.rationalCoeffEquiv_symm_algebraPointsEquiv_symm,
    MulEquiv.apply_symm_apply]

end SplitWeil

section Kernel

variable {L : Type u} [Field L] {I : Type u} [Fintype I]
  {G : GroupScheme (Spec (CommRingCat.of L))} (σ : G ≅ splitTorus (Spec (CommRingCat.of L)) I)
  {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation L Γ₀)

/-- A point of `G(L)` lies in the character-valuation kernel exactly when its split
coordinates have valuation one. -/
theorem mem_characterValuationKernel_iff_of_iso (x : rationalPoints G) :
    x ∈ characterValuationKernel v G ↔
      ∀ i, v (splitTorus.affinePointsEquiv I (𝟙 (Spec (CommRingCat.of L)))
        (rationalPoints.map σ.hom x) i : L) = 1 := by
  rw [← mem_split_characterValuationKernel]
  constructor
  · intro hx
    exact map_characterValuationKernel_le v σ.hom ⟨x, hx, rfl⟩
  · intro hx
    have h := map_characterValuationKernel_le v σ.inv ⟨_, hx, rfl⟩
    change rationalPoints.map σ.hom x ≫ σ.inv.hom.hom ∈ _ at h
    rwa [rationalPoints.map_apply, Category.assoc, ← Grp.comp_hom_hom, σ.hom_inv_id,
      Grp.id_hom_hom, Category.comp_id] at h

/-- The image under `σ⁻¹` of the split-torus point with coordinates `t` lies in the
character-valuation kernel exactly when every coordinate has valuation one. -/
theorem map_inv_mem_characterValuationKernel_iff (t : I → Lˣ) :
    rationalPoints.map σ.inv
        ((splitTorus.affinePointsEquiv I (𝟙 (Spec (CommRingCat.of L)))).symm t) ∈
      characterValuationKernel v G ↔ ∀ i, v (t i : L) = 1 := by
  rw [mem_characterValuationKernel_iff_of_iso σ v]
  have h : rationalPoints.map σ.hom (rationalPoints.map σ.inv
      ((splitTorus.affinePointsEquiv I (𝟙 (Spec (CommRingCat.of L)))).symm t)) =
        (splitTorus.affinePointsEquiv I (𝟙 (Spec (CommRingCat.of L)))).symm t := by
    rw [rationalPoints.map_apply, rationalPoints.map_apply, Category.assoc,
      ← Grp.comp_hom_hom, σ.inv_hom_id, Grp.id_hom_hom, Category.comp_id]
  rw [h, MulEquiv.apply_symm_apply]

end Kernel

end Langlands.GroupScheme.WeilGm
