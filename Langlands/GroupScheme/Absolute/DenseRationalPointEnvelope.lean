import Langlands.AlgebraicGeometry.PointTopology.RationalPoints
import Langlands.GroupScheme.Absolute.SmoothRationalPointClosure
import Langlands.AlgebraicGeometry.PointTopology.DenseRationalFamily
import Langlands.GroupScheme.AffineLinearEmbeddingCorepresentedProof

/-! # Dense rational points in the schematic closure of a subgroup -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RationalPointClosure

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]

/-- The affine spectrum of the ground field is the base test scheme. -/
def baseTestIso :
    (algSpec (CommRingCat.of k)).obj (op (baseAlgebra k)) ≅
      Over.mk (𝟙 (Spec (CommRingCat.of k))) :=
  Langlands.AlgebraicGeometry.PointTopology.ringTestSelfIso k

/-- A separating family of rational evaluations is dense in the affine spectrum. -/
theorem dense_family_of_separating
    {B : CommAlgCat.{u} (CommRingCat.of k)} {J : Type*}
    (χ : J → (B ⟶ baseAlgebra k))
    (hχ : ∀ b : B, (∀ j, (χ j).hom b = 0) → b = 0) :
    Langlands.AlgebraicGeometry.PointTopology.HasDenseRationalPointFamily
      (fun j => baseTestIso.inv ≫ (algSpec (CommRingCat.of k)).map (χ j).op) := by
  let S : Set (PrimeSpectrum B) := Set.range (fun j => classifiedPoint (χ j))
  have hI : PrimeSpectrum.vanishingIdeal S = ⊥ := by
    apply le_antisymm
    · intro b hb
      change b = 0
      apply hχ
      intro j
      exact (mem_asIdeal_classifiedPoint (χ j) b).1
        ((PrimeSpectrum.mem_vanishingIdeal S b).1 hb _ ⟨j, rfl⟩)
    · exact bot_le
  have hS : Dense S := by
    rw [dense_iff_closure_eq, ← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, hI]
    exact PrimeSpectrum.zeroLocus_bot
  apply hS.mono
  rintro _ ⟨j, rfl⟩
  apply Set.mem_iUnion.mpr
  refine ⟨j, IsLocalRing.closedPoint k, ?_⟩
  rfl

variable {F : CommAlgCat.{u} (CommRingCat.of k) ⥤ GrpCat.{u}}
  {B : CommAlgCat.{u} (CommRingCat.of k)}
  (e : (F ⋙ forget GrpCat).CorepresentableBy B)
  (Γ : Subgroup (F.obj (baseAlgebra k)))

/-- The schematic closure of the specified rational subgroup. -/
abbrev envelope : GroupScheme (Spec (CommRingCat.of k)) :=
  Corepresented.cutGroupScheme (isCutOutBy_closureSubgroup e Γ)

/-- The original subgroup, considered as points in the cut subgroup functor. -/
def subgroupToCut :
    Γ →* (Corepresented.cutFunctor (isCutOutBy_closureSubgroup e Γ)).obj (baseAlgebra k) where
  toFun gamma := ⟨gamma.1, mem_cutSet_of_mem gamma.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The original rational subgroup lifts to affine points of its schematic closure. -/
def affineLift :
    Γ →* ((algSpec (CommRingCat.of k)).obj (op (baseAlgebra k)) ⟶ (envelope e Γ).X) :=
  (Corepresented.affinePointsEquiv _ (Corepresented.cutCorepresentableBy
    (isCutOutBy_closureSubgroup e Γ)) (baseAlgebra k)).symm.toMonoidHom.comp
      (subgroupToCut e Γ)

theorem affineLift_eq (gamma : Γ) :
    affineLift e Γ gamma =
      (algSpec (CommRingCat.of k)).map (lift gamma.1 (mem_cutSet_of_mem gamma.2)).op := by
  apply (Corepresented.affinePointsEquiv _ (Corepresented.cutCorepresentableBy
    (isCutOutBy_closureSubgroup e Γ)) (baseAlgebra k)).injective
  rw [Corepresented.affinePointsEquiv_map]
  change (Corepresented.affinePointsEquiv _ (Corepresented.cutCorepresentableBy
    (isCutOutBy_closureSubgroup e Γ)) (baseAlgebra k))
      ((Corepresented.affinePointsEquiv _ (Corepresented.cutCorepresentableBy
        (isCutOutBy_closureSubgroup e Γ)) (baseAlgebra k)).symm
          ((subgroupToCut e Γ) gamma)) = _
  rw [MulEquiv.apply_symm_apply]
  apply Subtype.ext
  change gamma.1 = e.homEquiv (Corepresented.quotientMap (vanishingIdeal e Γ) ≫
    lift gamma.1 (mem_cutSet_of_mem gamma.2))
  rw [quotientMap_comp_lift, Equiv.apply_symm_apply]

/-- The lifted subgroup as actual rational points over the base scheme. -/
def rationalLift :
    Γ →* (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ (envelope e Γ).X) :=
  ((envelope e Γ).points.map baseTestIso.inv.op).hom.comp (affineLift e Γ)

theorem rationalLift_eq (gamma : Γ) :
    rationalLift e Γ gamma = baseTestIso.inv ≫
      (algSpec (CommRingCat.of k)).map (lift gamma.1 (mem_cutSet_of_mem gamma.2)).op := by
  change baseTestIso.inv ≫ affineLift e Γ gamma = _
  exact congrArg (fun f => baseTestIso.inv ≫ f) (affineLift_eq e Γ gamma)

/-- The lifted original subgroup is dense in its schematic closure. -/
theorem dense_rationalLift :
    Langlands.AlgebraicGeometry.PointTopology.HasDenseRationalPointFamily (rationalLift e Γ) := by
  have h := dense_family_of_separating
    (fun gamma : Γ => lift (e := e) gamma.1 (mem_cutSet_of_mem gamma.2))
      (eq_zero_of_forall_lift (e := e) (Γ := Γ))
  have heq : (rationalLift e Γ : Γ → _) =
      fun gamma : Γ => baseTestIso.inv ≫ (algSpec (CommRingCat.of k)).map
        (lift (e := e) gamma.1 (mem_cutSet_of_mem gamma.2)).op :=
    funext (rationalLift_eq e Γ)
  rw [heq]
  exact h

/-- The schematic envelope is affine over the field. -/
instance isAffineHom_envelope : IsAffineHom (envelope e Γ).X.hom :=
  isAffineHom_of_isAffine (X := Spec (CommRingCat.of (quotient e Γ))) _

/-- The quotient defining the schematic envelope is reduced. -/
instance isReduced_envelope : IsReduced (envelope e Γ).X.left := by
  have : _root_.IsReduced (B ⧸ vanishingIdeal e Γ) := isReduced_quotient e Γ
  exact inferInstanceAs (IsReduced (Spec (CommRingCat.of (B ⧸ vanishingIdeal e Γ))))

/-- A closed schematic envelope of a finite-type group remains locally of finite type. -/
instance locallyOfFiniteType_envelope
    [LocallyOfFiniteType (Corepresented.groupScheme F e).X.hom] :
    LocallyOfFiniteType (envelope e Γ).X.hom := by
  rw [← Over.w (Corepresented.cutHom (isCutOutBy_closureSubgroup e Γ)).hom.hom]
  infer_instance

/-- The envelope inclusion returns each original point under the corepresentation. -/
theorem affineLift_factor (gamma : Γ) :
    Corepresented.affinePointsEquiv F e (baseAlgebra k)
      (affineLift e Γ gamma ≫
        (Corepresented.cutHom (isCutOutBy_closureSubgroup e Γ)).hom.hom) = gamma.1 := by
  rw [Corepresented.cutHom, Corepresented.groupSchemeMap_affinePoints]
  change ((Corepresented.affinePointsEquiv _ (Corepresented.cutCorepresentableBy
    (isCutOutBy_closureSubgroup e Γ)) (baseAlgebra k)) (affineLift e Γ gamma)).1 = _
  change ((Corepresented.affinePointsEquiv _ (Corepresented.cutCorepresentableBy
    (isCutOutBy_closureSubgroup e Γ)) (baseAlgebra k))
      ((Corepresented.affinePointsEquiv _ (Corepresented.cutCorepresentableBy
        (isCutOutBy_closureSubgroup e Γ)) (baseAlgebra k)).symm
          ((subgroupToCut e Γ) gamma))).1 = _
  rw [MulEquiv.apply_symm_apply]
  rfl

/-- Every rational subgroup of an affine finite-type group has a reduced affine
finite-type envelope with a dense lift of the original points. -/
theorem exists_dense_envelope
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (Delta : Subgroup (Langlands.AlgebraicGeometry.PointTopology.RationalPoint k G.X)) :
    ∃ (H : GroupScheme (Spec (CommRingCat.of k))),
      IsReduced H.X.left ∧ IsAffineHom H.X.hom ∧ LocallyOfFiniteType H.X.hom ∧
      ∃ (i : H ⟶ G)
        (alpha : Delta →* Langlands.AlgebraicGeometry.PointTopology.RationalPoint k H.X),
        Langlands.AlgebraicGeometry.PointTopology.HasDenseRationalPointFamily alpha ∧
          ∀ gamma, alpha gamma ≫ i.hom.hom = gamma.1 := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨⟨B⟩, ⟨j⟩⟩ := (essImage_algSpec (G := G.X)).mpr this
  let e := AffineLinearEmbedding.corepresentableBy G j
  let Delta' : Subgroup (G.affinePointFunctor.obj (baseAlgebra k)) :=
    Delta.map ((G.points.map baseTestIso.hom.op).hom)
  let toDelta : Delta →* Delta' :=
    { toFun := fun d => ⟨baseTestIso.hom ≫ d.1, ⟨d.1, d.2, rfl⟩⟩
      map_one' := Subtype.ext (MonObj.comp_one _)
      map_mul' := fun x y => Subtype.ext (MonObj.comp_mul _ _ _) }
  have hsurj : Function.Surjective toDelta := by
    intro y
    obtain ⟨d, hd, heq⟩ := y.2
    exact ⟨⟨d, hd⟩, Subtype.ext heq⟩
  let H := envelope e Delta'
  let i : H ⟶ G := Corepresented.cutHom (isCutOutBy_closureSubgroup e Delta') ≫
    (AffineLinearEmbedding.modelIso G j).hom
  have hmodel : LocallyOfFiniteType (Corepresented.groupScheme G.affinePointFunctor e).X.hom := by
    have : IsIso j.hom.left := inferInstanceAs (IsIso ((Over.forget _).map j.hom))
    change LocallyOfFiniteType ((algSpec (CommRingCat.of k)).obj (op B)).hom
    rw [← Over.w j.hom]
    infer_instance
  have hfin : LocallyOfFiniteType H.X.hom := locallyOfFiniteType_envelope e Delta'
  let alpha := (rationalLift e Delta').comp toDelta
  refine ⟨H, inferInstance, inferInstance, hfin, i, alpha, ?_, ?_⟩
  · apply (dense_rationalLift e Delta').mono
    intro x hx
    obtain ⟨y, z, hz⟩ := Set.mem_iUnion.mp hx
    obtain ⟨d, rfl⟩ := hsurj y
    exact Set.mem_iUnion.mpr ⟨d, z, hz⟩
  · intro d
    have hfac : affineLift e Delta' (toDelta d) ≫
        (Corepresented.cutHom (isCutOutBy_closureSubgroup e Delta')).hom.hom ≫
          j.hom = (toDelta d).1 := by
      have hc := AffineCorepresentation.affinePointsEquiv_eq G j (baseAlgebra k)
        (affineLift e Delta' (toDelta d) ≫
          (Corepresented.cutHom (isCutOutBy_closureSubgroup e Delta')).hom.hom)
      exact (Category.assoc _ _ _).symm.trans
        (hc.symm.trans (affineLift_factor e Delta' (toDelta d)))
    change (baseTestIso.inv ≫ affineLift e Delta' (toDelta d)) ≫
      ((Corepresented.cutHom (isCutOutBy_closureSubgroup e Delta')).hom.hom ≫
        (AffineLinearEmbedding.modelIso G j).hom.hom.hom) = d.1
    rw [modelIso_hom_hom_hom]
    simp only [Category.assoc]
    erw [hfac]
    change baseTestIso.inv ≫ (baseTestIso.hom ≫ d.1) = d.1
    simp

end Langlands.GroupScheme.RationalPointClosure
