import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainBaseChange
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainCancellation
import Langlands.Geometry.Analytic.GeneralizedAffinoid.AffinoidCoproduct

/-! # Actual products of full affinoid domains -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.Domain

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : PresentedAffinoidAlgebra K}

/-- A product full domain in the actual affinoid coproduct is the intersection
of the two full inverse-image domains. -/
def product (U : Domain K A) (V : Domain K B) :
    Domain K (AffinoidCoproduct.algebra K A B) :=
  (pullback (AffinoidCoproduct.leftMap K A B) U).inter
    (pullback (AffinoidCoproduct.rightMap K A B) V)

@[simp]
theorem product_locus (U : Domain K A) (V : Domain K B) :
    (U.product V).locus =
      (BanachSpectrum.comap (AffinoidCoproduct.leftMap K A B).toBoundedRingHom ⁻¹'
        U.locus) ∩
      (BanachSpectrum.comap (AffinoidCoproduct.rightMap K A B).toBoundedRingHom ⁻¹'
        V.locus) := rfl

/-- The first original domain algebra maps by the two actual pushout legs. -/
def productLeftMap (U : Domain K A) (V : Domain K B) :
    BoundedAlgHom K U.algebra (U.product V).algebra :=
  ((pullback (AffinoidCoproduct.leftMap K A B) U).interLeft
    (pullback (AffinoidCoproduct.rightMap K A B) V)).restriction.comp
      (pullbackMap (AffinoidCoproduct.leftMap K A B) U)

/-- The second original domain algebra maps by the two actual pushout legs. -/
def productRightMap (U : Domain K A) (V : Domain K B) :
    BoundedAlgHom K V.algebra (U.product V).algebra :=
  ((pullback (AffinoidCoproduct.leftMap K A B) U).interRight
    (pullback (AffinoidCoproduct.rightMap K A B) V)).restriction.comp
      (pullbackMap (AffinoidCoproduct.rightMap K A B) V)

theorem productLeftMap_comp_baseMap (U : Domain K A) (V : Domain K B) :
    (U.productLeftMap V).comp U.baseMap =
      (U.product V).baseMap.comp (AffinoidCoproduct.leftMap K A B) := by
  let L := pullback (AffinoidCoproduct.leftMap K A B) U
  let R := pullback (AffinoidCoproduct.rightMap K A B) V
  have h₁ := congrArg (fun f : BoundedAlgHom K A L.algebra =>
    (L.interLeft R).restriction.comp f)
      (pullbackMap_comp_baseMap (AffinoidCoproduct.leftMap K A B) U)
  have h₂ := congrArg (fun f : BoundedAlgHom K (AffinoidCoproduct.algebra K A B)
    (L.inter R).algebra => f.comp (AffinoidCoproduct.leftMap K A B))
      (L.interLeft R).comp_baseMap
  exact h₁.trans h₂

theorem productRightMap_comp_baseMap (U : Domain K A) (V : Domain K B) :
    (U.productRightMap V).comp V.baseMap =
      (U.product V).baseMap.comp (AffinoidCoproduct.rightMap K A B) := by
  let L := pullback (AffinoidCoproduct.leftMap K A B) U
  let R := pullback (AffinoidCoproduct.rightMap K A B) V
  have h₁ := congrArg (fun f : BoundedAlgHom K B R.algebra =>
    (L.interRight R).restriction.comp f)
      (pullbackMap_comp_baseMap (AffinoidCoproduct.rightMap K A B) V)
  have h₂ := congrArg (fun f : BoundedAlgHom K (AffinoidCoproduct.algebra K A B)
    (L.inter R).algebra => f.comp (AffinoidCoproduct.rightMap K A B))
      (L.interRight R).comp_baseMap
  exact h₁.trans h₂

/-- The structural map into the actual coproduct of the unchanged domain algebras. -/
def productBaseMap (U : Domain K A) (V : Domain K B) :
    BoundedAlgHom K (AffinoidCoproduct.algebra K A B)
      (AffinoidCoproduct.algebra K U.algebra V.algebra) :=
  AffinoidCoproduct.lift K (AffinoidCoproduct.algebra K U.algebra V.algebra) A B
    ((AffinoidCoproduct.leftMap K U.algebra V.algebra).comp U.baseMap)
    ((AffinoidCoproduct.rightMap K U.algebra V.algebra).comp V.baseMap)

@[simp]
theorem productBaseMap_comp_leftMap (U : Domain K A) (V : Domain K B) :
    (U.productBaseMap V).comp (AffinoidCoproduct.leftMap K A B) =
      (AffinoidCoproduct.leftMap K U.algebra V.algebra).comp U.baseMap :=
  AffinoidCoproduct.lift_comp_leftMap _ _ _ _ _ _

@[simp]
theorem productBaseMap_comp_rightMap (U : Domain K A) (V : Domain K B) :
    (U.productBaseMap V).comp (AffinoidCoproduct.rightMap K A B) =
      (AffinoidCoproduct.rightMap K U.algebra V.algebra).comp V.baseMap :=
  AffinoidCoproduct.lift_comp_rightMap _ _ _ _ _ _

/-- Both original domain legs give the forward comparison to the inverse-image
intersection presentation. -/
def productCoproductMap (U : Domain K A) (V : Domain K B) :
    BoundedAlgHom K (AffinoidCoproduct.algebra K U.algebra V.algebra)
      (U.product V).algebra :=
  AffinoidCoproduct.lift K (U.product V).algebra U.algebra V.algebra
    (U.productLeftMap V) (U.productRightMap V)

@[simp]
theorem productCoproductMap_comp_leftMap (U : Domain K A) (V : Domain K B) :
    (U.productCoproductMap V).comp (AffinoidCoproduct.leftMap K U.algebra V.algebra) =
      U.productLeftMap V :=
  AffinoidCoproduct.lift_comp_leftMap _ _ _ _ _ _

@[simp]
theorem productCoproductMap_comp_rightMap (U : Domain K A) (V : Domain K B) :
    (U.productCoproductMap V).comp (AffinoidCoproduct.rightMap K U.algebra V.algebra) =
      U.productRightMap V :=
  AffinoidCoproduct.lift_comp_rightMap _ _ _ _ _ _

theorem productCoproductMap_comp_productBaseMap (U : Domain K A) (V : Domain K B) :
    (U.productCoproductMap V).comp (U.productBaseMap V) = (U.product V).baseMap := by
  apply AffinoidCoproduct.hom_ext K (U.product V).algebra A B
  · rw [BoundedAlgHom.comp_assoc, productBaseMap_comp_leftMap,
      ← BoundedAlgHom.comp_assoc, productCoproductMap_comp_leftMap,
      productLeftMap_comp_baseMap]
  · rw [BoundedAlgHom.comp_assoc, productBaseMap_comp_rightMap,
      ← BoundedAlgHom.comp_assoc, productCoproductMap_comp_rightMap,
      productRightMap_comp_baseMap]

/-- The actual coproduct structural map has spectrum image in the product locus. -/
theorem productBaseMap_hasImageIn (U : Domain K A) (V : Domain K B) :
    HasImageIn K (U.productBaseMap V) (U.product V).locus := by
  intro x
  constructor
  · change BanachSpectrum.comap
      ((U.productBaseMap V).comp (AffinoidCoproduct.leftMap K A B)).toBoundedRingHom x
        ∈ U.locus
    rw [productBaseMap_comp_leftMap]
    exact U.represents.hasImageIn
      (BanachSpectrum.comap (AffinoidCoproduct.leftMap K U.algebra V.algebra).toBoundedRingHom x)
  · change BanachSpectrum.comap
      ((U.productBaseMap V).comp (AffinoidCoproduct.rightMap K A B)).toBoundedRingHom x
        ∈ V.locus
    rw [productBaseMap_comp_rightMap]
    exact V.represents.hasImageIn
      (BanachSpectrum.comap (AffinoidCoproduct.rightMap K U.algebra V.algebra).toBoundedRingHom x)

/-- Full-domain representation constructs the bounded inverse comparison,
including for trivial coefficient valuations. -/
def productToCoproductMap (U : Domain K A) (V : Domain K B) :
    BoundedAlgHom K (U.product V).algebra
      (AffinoidCoproduct.algebra K U.algebra V.algebra) :=
  ((U.product V).represents.2.2 (AffinoidCoproduct.algebra K U.algebra V.algebra)
    (U.productBaseMap V) (U.productBaseMap_hasImageIn V)).choose

@[simp]
theorem productToCoproductMap_comp_baseMap (U : Domain K A) (V : Domain K B) :
    (U.productToCoproductMap V).comp (U.product V).baseMap = U.productBaseMap V :=
  ((U.product V).represents.2.2 (AffinoidCoproduct.algebra K U.algebra V.algebra)
    (U.productBaseMap V) (U.productBaseMap_hasImageIn V)).choose_spec.1

@[simp]
theorem productToCoproductMap_comp_productLeftMap (U : Domain K A) (V : Domain K B) :
    (U.productToCoproductMap V).comp (U.productLeftMap V) =
      AffinoidCoproduct.leftMap K U.algebra V.algebra := by
  apply U.represents.hom_ext (AffinoidCoproduct.algebra K U.algebra V.algebra)
  rw [BoundedAlgHom.comp_assoc, productLeftMap_comp_baseMap,
    ← BoundedAlgHom.comp_assoc, productToCoproductMap_comp_baseMap,
    productBaseMap_comp_leftMap]

@[simp]
theorem productToCoproductMap_comp_productRightMap (U : Domain K A) (V : Domain K B) :
    (U.productToCoproductMap V).comp (U.productRightMap V) =
      AffinoidCoproduct.rightMap K U.algebra V.algebra := by
  apply V.represents.hom_ext (AffinoidCoproduct.algebra K U.algebra V.algebra)
  rw [BoundedAlgHom.comp_assoc, productRightMap_comp_baseMap,
    ← BoundedAlgHom.comp_assoc, productToCoproductMap_comp_baseMap,
    productBaseMap_comp_rightMap]

theorem productToCoproductMap_comp_productCoproductMap (U : Domain K A) (V : Domain K B) :
    (U.productToCoproductMap V).comp (U.productCoproductMap V) =
      BoundedAlgHom.id K (AffinoidCoproduct.algebra K U.algebra V.algebra) := by
  apply AffinoidCoproduct.hom_ext K _ U.algebra V.algebra
  · rw [BoundedAlgHom.comp_assoc, productCoproductMap_comp_leftMap,
      productToCoproductMap_comp_productLeftMap, BoundedAlgHom.id_comp]
  · rw [BoundedAlgHom.comp_assoc, productCoproductMap_comp_rightMap,
      productToCoproductMap_comp_productRightMap, BoundedAlgHom.id_comp]

theorem productCoproductMap_comp_productToCoproductMap (U : Domain K A) (V : Domain K B) :
    (U.productCoproductMap V).comp (U.productToCoproductMap V) =
      BoundedAlgHom.id K (U.product V).algebra := by
  apply (U.product V).represents.hom_ext (U.product V).algebra
  rw [BoundedAlgHom.comp_assoc, productToCoproductMap_comp_baseMap,
    productCoproductMap_comp_productBaseMap, BoundedAlgHom.id_comp]

/-- The product domain algebra is boundedly equivalent to the actual coproduct
of the two unchanged input domain algebras; both bounds are constructed. -/
def productCoproductEquiv (U : Domain K A) (V : Domain K B) :
    BoundedAlgEquiv K (AffinoidCoproduct.algebra K U.algebra V.algebra)
      (U.product V).algebra :=
  BoundedAlgEquiv.ofHomInv (U.productCoproductMap V) (U.productToCoproductMap V)
    (fun x => congrArg (fun f : BoundedAlgHom K
      (AffinoidCoproduct.algebra K U.algebra V.algebra)
      (AffinoidCoproduct.algebra K U.algebra V.algebra) => f x)
        (U.productToCoproductMap_comp_productCoproductMap V))
    (fun x => congrArg (fun f : BoundedAlgHom K (U.product V).algebra
      (U.product V).algebra => f x)
        (U.productCoproductMap_comp_productToCoproductMap V))

/-- A pair of actual input inclusions yields the actual product inclusion. -/
def productRestriction {U U' : Domain K A} {V V' : Domain K B}
    (f : U ⟶ U') (g : V ⟶ V') : U.product V ⟶ U'.product V' :=
  inclusionOfSubset _ _ fun _ hx => ⟨f.subset hx.1, g.subset hx.2⟩

/-- The actual product restriction commutes with the first original algebra leg. -/
theorem productRestriction_comp_productLeftMap {U U' : Domain K A}
    {V V' : Domain K B} (f : U ⟶ U') (g : V ⟶ V') :
    (productRestriction f g).restriction.comp (U'.productLeftMap V') =
      (U.productLeftMap V).comp f.restriction := by
  apply U'.represents.hom_ext (U.product V).algebra
  rw [BoundedAlgHom.comp_assoc, productLeftMap_comp_baseMap,
    ← BoundedAlgHom.comp_assoc, (productRestriction f g).comp_baseMap,
    BoundedAlgHom.comp_assoc, f.comp_baseMap, productLeftMap_comp_baseMap]

/-- The actual product restriction commutes with the second original algebra leg. -/
theorem productRestriction_comp_productRightMap {U U' : Domain K A}
    {V V' : Domain K B} (f : U ⟶ U') (g : V ⟶ V') :
    (productRestriction f g).restriction.comp (U'.productRightMap V') =
      (U.productRightMap V).comp g.restriction := by
  apply V'.represents.hom_ext (U.product V).algebra
  rw [BoundedAlgHom.comp_assoc, productRightMap_comp_baseMap,
    ← BoundedAlgHom.comp_assoc, (productRestriction f g).comp_baseMap,
    BoundedAlgHom.comp_assoc, g.comp_baseMap, productRightMap_comp_baseMap]

end Langlands.Analytic.PresentedAffinoidAlgebra.Domain
