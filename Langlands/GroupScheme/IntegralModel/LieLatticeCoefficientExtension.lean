import Langlands.GroupScheme.IntegralModel.LieLattice
import Langlands.GroupScheme.IntegralModel.BaseChange
import Langlands.GroupScheme.IntegralModel.UnramifiedModelDescent

/-! # Base change of Lie algebras and of Lie lattices

For a field extension `L/K` and an affine group `G` over `K`, the coefficient change
`K[ε] → L[ε]` followed by the scheme-pullback comparison gives the base change map
`Lie(G) → Lie(G_L)` (`GenericLie.baseChangeMap`). For an integral model `𝒢` of `G` over a
domain `R` with fraction field `K`, and a commuting square of domains and fraction fields
`R → A`, `K → L`, the Lie map of the base-changed model `𝒢_A` sends the coefficient change of
`X ∈ Lie(𝒢)` to the base change of the image of `X` in `Lie(G)` (`lieMap_baseChangeMap`). Hence
the base change map carries the Lie lattice `Lie(𝒢)` into `Lie(𝒢_A)`
(`baseChangeMap_mem_lieLattice`), in particular, over a nonarchimedean local field `F`, the
Lie lattice of a model over `𝒪[F]` into the Lie lattice of its base change to the integers of
the maximal unramified extension (`baseChangeMap_mem_lieLattice_baseChangeUnramified`). No
smoothness is needed.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace GenericLie

variable (R : Type u) {K : Type u} [CommRing R] [Field K] [Algebra R K]
  (S L : Type u) [CommRing S] [Field L] [Algebra S L] [Algebra K L]
  (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffineHom G.X.hom]

/-- The base change `G_L` of an affine group is affine. -/
instance baseChange_isAffineHom :
    IsAffineHom ((GroupScheme.baseChange (Spec.algebraMap K L)).obj G).X.hom := by
  change IsAffineHom (pullback.snd G.X.hom (Spec.algebraMap K L))
  infer_instance

/-- The base change map `Lie(G) → Lie(G_L)` for a field extension `L/K`: an element of the
dual-number kernel `ker(G(K[ε]) → G(K))` is pushed to `G(L[ε])` by the coefficient change
`K[ε] → L[ε]` and regarded as a point of the scheme pullback `G_L` (`Lie.kernelFieldExtension`).
It is additive (and `K`-semilinear); the rings `R` and `S` only select the module structures of
the type synonyms. -/
def baseChangeMap :
    GenericLie R G →+ GenericLie S ((GroupScheme.baseChange (Spec.algebraMap K L)).obj G) where
  toFun X := (equiv S _).symm (Additive.ofMul (Lie.kernelFieldExtension (K := L) G
    (equiv R G X).toMul))
  map_zero' := by
    rw [LinearEquiv.map_zero]
    exact congrArg (equiv S _).symm (congrArg Additive.ofMul (MonoidHom.map_one _))
  map_add' X Y := by
    rw [LinearEquiv.map_add]
    exact congrArg (equiv S _).symm (congrArg Additive.ofMul (MonoidHom.map_mul _ _ _))

omit [CommRing R] [Algebra R K] [CommRing S] [Algebra S L] in
theorem baseChangeMap_apply (X : GenericLie R G) :
    baseChangeMap R S L G X = (equiv S _).symm (Additive.ofMul (Lie.kernelFieldExtension (K := L) G
      (equiv R G X).toMul)) := rfl

omit [CommRing R] [Algebra R K] [CommRing S] [Algebra S L] in
/-- The base change map is semilinear along `K → L`. -/
theorem baseChangeMap_smul (c : K) (X : GenericLie R G) :
    baseChangeMap R S L G (c • X) = algebraMap K L c • baseChangeMap R S L G X := by
  have h (x : Additive (lieKernel G K)) : Additive.ofMul (Lie.kernelFieldExtension (K := L) G
      x.toMul) = (Lie.kernelBaseChangeLinearEquiv K L G L).symm
        (lieKernelMapLinear G (Algebra.ofId K L) x) := rfl
  rw [baseChangeMap_apply, baseChangeMap_apply, LinearEquiv.map_smul, h, h,
    LinearMap.map_smulₛₗ, LinearEquiv.map_smul, LinearEquiv.map_smul]
  rfl

end GenericLie

namespace IntegralModel

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  {G : GroupScheme (Spec (CommRingCat.of K))} [IsAffineHom G.X.hom]
  (M : IntegralModel R K G)
  (A L : Type u) [CommRing A] [IsDomain A] [Field L]
  [Algebra R A] [Algebra A L] [IsFractionRing A L]
  [Algebra K L] [Algebra R L] [IsScalarTower R A L] [IsScalarTower R K L]

section Points

variable {B : Type u} [CommRing B] [Algebra L B] [Algebra K B] [Algebra A B] [Algebra R B]
  [IsScalarTower K L B] [IsScalarTower A L B] [IsScalarTower R K B] [IsScalarTower R A B]

omit [IsAffineHom G.X.hom] in
/-- On points with values in an `L`-algebra, the generic identification of the base-changed
model is compatible with that of `M`: both send a point of the generic fibre of `𝒢_A` to the
same point of `𝒢`. -/
theorem affineBaseChangeEquiv_baseChangeGenericIso
    (w : Lie.AffinePoints ((GroupScheme.baseChange (Spec.algebraMap A L)).obj
      ((GroupScheme.baseChange (Spec.algebraMap R A)).obj M.group)) B) :
    Lie.affineBaseChangeEquiv R K M.group B
        (Lie.affineBaseChangeEquiv K L G B (w ≫ (M.baseChange A L).genericIso.hom.hom.hom) ≫
          M.genericIso.inv.hom.hom) =
      Lie.affineBaseChangeEquiv R A M.group B
        (Lie.affineBaseChangeEquiv A L ((GroupScheme.baseChange (Spec.algebraMap R A)).obj M.group)
          B w) := by
  apply Over.OverMorphism.ext
  simp only [Lie.affineBaseChangeEquiv_left, Over.comp_left, Category.assoc]
  exact congrArg (fun f => w.left ≫ f) (M.baseChangeGenericIso_hom_fst A L)

omit [IsAffineHom G.X.hom] in
/-- A point of `G` with values in a `K`-algebra is determined by the corresponding point of the
integral model `M`. -/
theorem affinePoints_ext {C : Type u} [CommRing C] [Algebra K C] [Algebra R C]
    [IsScalarTower R K C] {x y : Lie.AffinePoints G C}
    (h : Lie.affineBaseChangeEquiv R K M.group C (x ≫ M.genericIso.inv.hom.hom) =
      Lie.affineBaseChangeEquiv R K M.group C (y ≫ M.genericIso.inv.hom.hom)) : x = y := by
  have h' := (Lie.affineBaseChangeEquiv R K M.group C).injective h
  have hi : M.genericIso.inv.hom.hom ≫ M.genericIso.hom.hom.hom = 𝟙 _ :=
    congrArg (fun f => f.hom.hom) M.genericIso.inv_hom_id
  calc x = (x ≫ M.genericIso.inv.hom.hom) ≫ M.genericIso.hom.hom.hom := by
        rw [Category.assoc, hi, Category.comp_id]
    _ = (y ≫ M.genericIso.inv.hom.hom) ≫ M.genericIso.hom.hom.hom := by rw [h']
    _ = y := by rw [Category.assoc, hi, Category.comp_id]

end Points

/-- **Lie maps and base change.** For `X ∈ Lie(𝒢)`, the Lie map of the base-changed model
`𝒢_A` sends the coefficient change of `X` along `R → A` to the base change, along `K → L`, of
the image `M.lieMap X ∈ Lie(G)`. -/
theorem lieMap_baseChangeMap (X : M.LieModule) :
    (M.baseChange A L).lieMap (Additive.ofMul (Lie.kernelFieldExtension (K := A) M.group X.toMul)) =
      GenericLie.baseChangeMap R A L G (M.lieMap X) := by
  have hR : Lie.kernelBaseChangeEquiv K L G L
      (Additive.toMul (GenericLie.baseChangeMap R A L G (M.lieMap X))) =
        lieKernelMap G (Algebra.ofId K L) (Additive.toMul (M.lieMap X)) := by
    rw [GenericLie.baseChangeMap_apply]
    exact (Lie.kernelBaseChangeEquiv K L G L).apply_symm_apply _
  apply Additive.toMul.injective
  apply (Lie.kernelBaseChangeEquiv K L G L).injective
  rw [hR]
  apply Subtype.ext
  apply M.affinePoints_ext
  change Lie.affineBaseChangeEquiv R K M.group (DualNumber L)
      (Lie.affineBaseChangeEquiv K L G (DualNumber L)
        ((Lie.affineBaseChangeEquiv A L
            ((GroupScheme.baseChange (Spec.algebraMap R A)).obj M.group) (DualNumber L)).symm
          (Lie.affineMap ((GroupScheme.baseChange (Spec.algebraMap R A)).obj M.group)
            (GeneralLinear.DualNumber.coefficientAlgMap (Algebra.ofId A L))
            ((Lie.affineBaseChangeEquiv R A M.group (DualNumber A)).symm
              (Lie.affineMap M.group
                (GeneralLinear.DualNumber.coefficientAlgMap (Algebra.ofId R A))
                X.toMul.val))) ≫ (M.baseChange A L).genericIso.hom.hom.hom) ≫
        M.genericIso.inv.hom.hom) =
    Lie.affineBaseChangeEquiv R K M.group (DualNumber L)
      (Lie.affineMap G (GeneralLinear.DualNumber.coefficientAlgMap (Algebra.ofId K L))
        ((Lie.affineBaseChangeEquiv R K M.group (DualNumber K)).symm
          (Lie.affineMap M.group
            (GeneralLinear.DualNumber.coefficientAlgMap (Algebra.ofId R K))
            X.toMul.val) ≫ M.genericIso.hom.hom.hom) ≫ M.genericIso.inv.hom.hom)
  have hi : M.genericIso.hom.hom.hom ≫ M.genericIso.inv.hom.hom = 𝟙 _ :=
    congrArg (fun f => f.hom.hom) M.genericIso.hom_inv_id
  rw [M.affineBaseChangeEquiv_baseChangeGenericIso A L, MulEquiv.apply_symm_apply,
    Lie.affineBaseChangeEquiv_naturality, MulEquiv.apply_symm_apply, ← Lie.affineMap_comp]
  have hG (z : Lie.AffinePoints M.genericFibre (DualNumber K)) :
      Lie.affineMap G (GeneralLinear.DualNumber.coefficientAlgMap (R := CommRingCat.of K)
          (Algebra.ofId K L)) (z ≫ M.genericIso.hom.hom.hom) ≫ M.genericIso.inv.hom.hom =
        Lie.affineMap M.genericFibre (GeneralLinear.DualNumber.coefficientAlgMap
          (R := CommRingCat.of K) (Algebra.ofId K L)) z := by
    rw [Lie.affineMap_apply, Lie.affineMap_apply, Category.assoc, Category.assoc, hi,
      Category.comp_id]
  rw [hG, Lie.affineBaseChangeEquiv_naturality, MulEquiv.apply_symm_apply,
    ← Lie.affineMap_comp]
  refine congrArg (fun φ => Lie.affineMap M.group φ X.toMul.val) ?_
  apply AlgHom.ext
  intro z
  apply TrivSqZeroExt.ext
  · change algebraMap A L (algebraMap R A z.fst) = algebraMap K L (algebraMap R K z.fst)
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  · change algebraMap A L (algebraMap R A z.snd) = algebraMap K L (algebraMap R K z.snd)
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]

/-- The base change map carries the Lie lattice of `M` into that of `M.baseChange A L`. -/
theorem baseChangeMap_mem_lieLattice {Y : GenericLie R G} (hY : Y ∈ M.lieLattice) :
    GenericLie.baseChangeMap R A L G Y ∈ (M.baseChange A L).lieLattice := by
  obtain ⟨X, rfl⟩ := hY
  exact ⟨_, M.lieMap_baseChangeMap A L X⟩

/-- The image of `Lie(𝒢)` under the base change map lies in `Lie(𝒢_A)`. -/
theorem map_baseChangeMap_lieLattice_le :
    M.lieLattice.toAddSubgroup.map (GenericLie.baseChangeMap R A L G) ≤
      (M.baseChange A L).lieLattice.toAddSubgroup := by
  rintro _ ⟨Y, hY, rfl⟩
  exact M.baseChangeMap_mem_lieLattice A L hY

end IntegralModel

namespace IntegralModel

open Langlands.LocalGalois.Separable
open scoped ValuativeRel

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom]

private local instance : Algebra ↥𝒪[F] (fixedFieldIntegers F) :=
  Valuation.HasExtension.instAlgebraInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

private local instance : IsScalarTower ↥𝒪[F] (fixedFieldIntegers F) (inertiaFixedField F) :=
  Valuation.HasExtension.instIsScalarTowerInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

/-- Over a nonarchimedean local field `F` with maximal unramified extension
`K = inertiaFixedField F`, the base change map `Lie(G) → Lie(G_K)` carries the Lie lattice of a
model `M` over `𝒪[F]` into the Lie lattice of its base change `M.baseChangeUnramified` to the
integers of `K`. -/
theorem baseChangeMap_mem_lieLattice_baseChangeUnramified (M : IntegralModel ↥𝒪[F] F G)
    {Y : GenericLie ↥𝒪[F] G} (hY : Y ∈ M.lieLattice) :
    GenericLie.baseChangeMap ↥𝒪[F] (fixedFieldIntegers F) (inertiaFixedField F) G Y ∈
      M.baseChangeUnramified.lieLattice :=
  M.baseChangeMap_mem_lieLattice (fixedFieldIntegers F) (inertiaFixedField F) hY

end IntegralModel

end Langlands.GroupScheme
