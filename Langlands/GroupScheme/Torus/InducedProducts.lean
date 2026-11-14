import Langlands.GroupScheme.Torus.CommonFiniteGaloisSplitting
import Langlands.GroupScheme.Torus.InducedBasisTransport
import Langlands.GroupScheme.Torus.Products
import Langlands.GroupScheme.Torus.WeilRestrictionNormOneCharacters
import Mathlib.LinearAlgebra.Basis.Prod

/-! # Binary products of actual induced tori -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.CommGroupScheme

variable {S : Scheme.{u}} (T U : CommGroupScheme S)

/-- The actual binary product, with its componentwise commutative group law. -/
def prod : CommGroupScheme S where
  toGrp := T.toGrp ⊗ U.toGrp
  comm := (isCommMonObj_iff_isMulCommutative _).2 fun V =>
    { is_comm := ⟨fun x y => (GroupScheme.productPointsEquiv T.toGrp U.toGrp V).injective
        (by rw [map_mul, map_mul, mul_comm])⟩ }

/-- First projection from the actual commutative product. -/
def prodFst : prod T U ⟶ T := Additive.ofMul (fst T.toGrp U.toGrp)

/-- Second projection from the actual commutative product. -/
def prodSnd : prod T U ⟶ U := Additive.ofMul (snd T.toGrp U.toGrp)

/-- First-factor inclusion into the actual commutative product. -/
def prodInl : T ⟶ prod T U := Additive.ofMul (lift (𝟙 T.toGrp) (1 : T.toGrp ⟶ U.toGrp))

/-- Second-factor inclusion into the actual commutative product. -/
def prodInr : U ⟶ prod T U := Additive.ofMul (lift (1 : U.toGrp ⟶ T.toGrp) (𝟙 U.toGrp))

@[simp] theorem prodInl_fst : prodInl T U ≫ prodFst T U = 𝟙 T :=
  congrArg Additive.ofMul (lift_fst _ _)

@[simp] theorem prodInl_snd : prodInl T U ≫ prodSnd T U = 0 :=
  congrArg Additive.ofMul (lift_snd _ _)

@[simp] theorem prodInr_fst : prodInr T U ≫ prodFst T U = 0 :=
  congrArg Additive.ofMul (lift_fst _ _)

@[simp] theorem prodInr_snd : prodInr T U ≫ prodSnd T U = 𝟙 U :=
  congrArg Additive.ofMul (lift_snd _ _)

/-- The two coordinate endomorphisms sum to the identity of the product. -/
theorem prod_decomposition :
    prodFst T U ≫ prodInl T U + prodSnd T U ≫ prodInr T U = 𝟙 (prod T U) := by
  apply GroupScheme.CommGroupScheme.hom_ext_points
  intro V x
  rw [GroupScheme.comp_groupHom_add]
  change _ = x ≫ 𝟙 _
  rw [Category.comp_id]
  apply (GroupScheme.productPointsEquiv T.toGrp U.toGrp V).injective
  simp only [map_mul]
  apply Prod.ext
  · change ((x ≫ (fst T.toGrp U.toGrp).hom.hom) ≫
        (lift (𝟙 T.toGrp) (1 : T.toGrp ⟶ U.toGrp)).hom.hom) ≫ fst T.X U.X *
      ((x ≫ (snd T.toGrp U.toGrp).hom.hom) ≫
        (lift (1 : U.toGrp ⟶ T.toGrp) (𝟙 U.toGrp)).hom.hom) ≫ fst T.X U.X = _
    simpa using (GroupScheme.productPointsEquiv_fst T.toGrp U.toGrp V x).symm
  · change ((x ≫ (fst T.toGrp U.toGrp).hom.hom) ≫
        (lift (𝟙 T.toGrp) (1 : T.toGrp ⟶ U.toGrp)).hom.hom) ≫ snd T.X U.X *
      ((x ≫ (snd T.toGrp U.toGrp).hom.hom) ≫
        (lift (1 : U.toGrp ⟶ T.toGrp) (𝟙 U.toGrp)).hom.hom) ≫ snd T.X U.X = _
    simpa using (GroupScheme.productPointsEquiv_snd T.toGrp U.toGrp V x).symm

end Langlands.CommGroupScheme

namespace Langlands.GroupScheme.characterLattice

variable {S S' : Scheme.{u}} (b : S' ⟶ S) (T U : CommGroupScheme S)

/-- The character lattice of the actual base-changed product is the product of the
character lattices of its factors. Restriction to the factor inclusions gives the
forward map; the inverse adds pullbacks along the two projections. -/
def baseChangeProdEquiv :
    characterLattice ((CommGroupScheme.baseChange b).obj (CommGroupScheme.prod T U)) ≃+
      characterLattice ((CommGroupScheme.baseChange b).obj T) ×
      characterLattice ((CommGroupScheme.baseChange b).obj U) where
  toFun χ := ((CommGroupScheme.baseChange b).map (CommGroupScheme.prodInl T U) ≫ χ,
    (CommGroupScheme.baseChange b).map (CommGroupScheme.prodInr T U) ≫ χ)
  invFun χ := (CommGroupScheme.baseChange b).map (CommGroupScheme.prodFst T U) ≫ χ.1 +
    (CommGroupScheme.baseChange b).map (CommGroupScheme.prodSnd T U) ≫ χ.2
  left_inv χ := by
    simp only [← Category.assoc, ← Preadditive.add_comp, ← Functor.map_comp,
      ← Functor.map_add, CommGroupScheme.prod_decomposition]
    rw [CategoryTheory.Functor.map_id, Category.id_comp]
  right_inv χ := by
    apply Prod.ext <;>
      simp [Preadditive.comp_add, ← Category.assoc, ← Functor.map_comp]
  map_add' χ ψ := by
    apply Prod.ext <;> simp [Preadditive.comp_add]

/-- On each coordinate the product-character equivalence respects Galois transport. -/
theorem baseChangeProdEquiv_galois
    (k L : Type u) [Field k] [Field L] [Algebra k L]
    (T U : CommGroupScheme (Spec (CommRingCat.of k))) (σ : L ≃ₐ[k] L)
    (χ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj
      (CommGroupScheme.prod T U))) :
    baseChangeProdEquiv (algebraBaseMap k L) T U
      (galoisRepresentation k L (CommGroupScheme.prod T U) σ χ) =
      (galoisRepresentation k L T σ
        (baseChangeProdEquiv (algebraBaseMap k L) T U χ).1,
       galoisRepresentation k L U σ
        (baseChangeProdEquiv (algebraBaseMap k L) T U χ).2) := by
  apply Prod.ext
  · exact (galoisRepresentation_precompose k L (CommGroupScheme.prodInl T U) σ χ).symm
  · exact (galoisRepresentation_precompose k L (CommGroupScheme.prodInr T U) σ χ).symm

end Langlands.GroupScheme.characterLattice

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {T U : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Inducedness is invariant under an isomorphism of the underlying group schemes. -/
theorem IsInducedTorus.of_iso (e : T.toGrp ≅ U.toGrp) (hU : IsInducedTorus U) :
    IsInducedTorus T := by
  obtain ⟨E, hEF, hEA, hEfin, hEgal, hE, I, b, hb⟩ := hU
  let : Field E := hEF
  let : Algebra k E := hEA
  let : FiniteDimensional k E := hEfin
  let : IsGalois k E := hEgal
  let c := CommGroupScheme.isoOfGroupIso e
  let cE := (CommGroupScheme.baseChange (algebraBaseMap k E)).mapIso c
  let a := (characterLattice.congr cE).symm
  refine ⟨E, hEF, hEA, hEfin, hEgal,
    IsSplitTorus.of_iso ((GroupScheme.baseChange (algebraBaseMap k E)).mapIso e) hE,
    I, b.map a.toIntLinearEquiv, ?_⟩
  intro σ i
  obtain ⟨j, hj⟩ := hb σ i
  refine ⟨j, ?_⟩
  change characterLattice.galoisRepresentation k E T σ
      ((CommGroupScheme.baseChange (algebraBaseMap k E)).map c.hom ≫ b i) =
    (CommGroupScheme.baseChange (algebraBaseMap k E)).map c.hom ≫ b j
  rw [characterLattice.galoisRepresentation_precompose, hj]

/-- The actual binary product of two induced tori is induced. The character
basis is the disjoint union of the factor bases over a common splitting field. -/
theorem IsInducedTorus.prod (hT : IsInducedTorus T) (hU : IsInducedTorus U) :
    IsInducedTorus (CommGroupScheme.prod T U) := by
  let d := hT.isTorus.commonFiniteGaloisSplitting hU.isTorus
  let L := d.carrier
  have hTL : IsSplitTorus (GaloisPointComparison.baseChanged k L T.toGrp) := d.split_left
  have hUL : IsSplitTorus (GaloisPointComparison.baseChanged k L U.toGrp) := d.split_right
  obtain ⟨I, hI, bT, hbT⟩ := hT.exists_permuted_basis L hTL
  obtain ⟨J, hJ, bU, hbU⟩ := hU.exists_permuted_basis L hUL
  let e := characterLattice.baseChangeProdEquiv (algebraBaseMap k L) T U
  let b := (bT.prod bU).map e.symm.toIntLinearEquiv
  have he (i : I ⊕ J) : e (b i) = (bT.prod bU) i := e.apply_symm_apply _
  refine ⟨L, inferInstance, inferInstance, inferInstance, inferInstance,
    IsSplitTorus.of_iso (baseChangeTensorIso _ T.toGrp U.toGrp) (hTL.tensor hUL),
    I ⊕ J, b, ?_⟩
  intro σ i
  cases i with
  | inl i =>
    obtain ⟨j, hj⟩ := hbT σ i
    refine ⟨Sum.inl j, e.injective ?_⟩
    rw [characterLattice.baseChangeProdEquiv_galois, he, he]
    apply Prod.ext
    · simpa only [Module.Basis.prod_apply_inl_fst] using hj
    · simp only [Module.Basis.prod_apply_inl_snd, map_zero]
  | inr i =>
    obtain ⟨j, hj⟩ := hbU σ i
    refine ⟨Sum.inr j, e.injective ?_⟩
    rw [characterLattice.baseChangeProdEquiv_galois, he, he]
    apply Prod.ext
    · simp only [Module.Basis.prod_apply_inr_fst, map_zero]
    · simpa only [Module.Basis.prod_apply_inr_snd] using hj

/-- Product closure in an arbitrary commutative realization of the same actual
binary product of underlying group schemes. -/
theorem IsInducedTorus.of_product_iso
    {P : CommGroupScheme (Spec (CommRingCat.of k))}
    (e : P.toGrp ≅ T.toGrp ⊗ U.toGrp)
    (hT : IsInducedTorus T) (hU : IsInducedTorus U) : IsInducedTorus P :=
  IsInducedTorus.of_iso e (hT.prod hU)

end Langlands.GroupScheme
