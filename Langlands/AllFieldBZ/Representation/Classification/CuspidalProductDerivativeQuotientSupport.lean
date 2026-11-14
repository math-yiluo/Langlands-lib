import Langlands.AllFieldBZ.Representation.CuspidalSupport.CuspidalTensorProof
import Langlands.AllFieldBZ.Representation.CuspidalSupport.JacquetVanishingHelpers
import Langlands.AllFieldBZ.Representation.CuspidalSupport.LeviTensorFactorizationProof
import Langlands.AllFieldBZ.Representation.Derivative.PartialDerivativeJacquetComparisonProof
import Langlands.AllFieldBZ.Representation.Geometric.GeometricLemmaProof
import Langlands.AllFieldBZ.Representation.Parabolic.RefinedInductionTensorProof
import Langlands.AllFieldBZ.Representation.Tensor.FlattenedGLRefinement
import Langlands.Representation.Classification.CuspidalProductDerivativeQuotientSupport

/-!
# All-field port of `Langlands.Representation.Classification.CuspidalProductDerivativeQuotientSupport`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Classification.CuspidalProductDerivativeQuotientSupport` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
namespace Langlands.AllFieldBZ.Classification.CuspidalProductDerivativeQuotientSupport
open Langlands.Classification.CuspidalProductDerivativeQuotientSupport hiding castSupercuspidal cuspidalDatum_castSupercuspidal derivative_quotient_support exists_inner_factors exists_rankCast_map flattenedLeviProductEquiv_flattenedLeviEquiv_symm fullSourcePieceEquiv full_piece_quotient full_piece_support inducingEquiv innerFactor intersectionTransportEquivTo isCuspidalConstituent_of_rankCast isQuotient_first_block isSubquotient_cuspidalProductInduced jacquet_quotient_support normalizedRefinedInducedCongr supercuspidalProperty_cast
open CategoryTheory
open Langlands.GeneralLinear
open Langlands.Geometric hiding CorrectionSubgroupDiagonalHaarStatement GeometricLemmaTheorem PadicBruhatMatrixExistenceTheorem PadicBruhatWeylReflectionTheorem PadicGeometricLemmaTheorem PadicParabolicBruhatTheorem PadicParabolicOrbitJacquetComparison PadicParabolicSupportGradedTheorem PadicParabolicSupportJacquetComparison PadicStandardIntersectionsTheorem closedSubgroupOrbitOrdering_of_finiteOrbitOrdering correctionSubgroupDiagonalHaar geometricLemma_of_orderedCosets geometricLemma_of_supportGraded geometricPieceFunctor intersectionLeviHalfModulusBalance_sourceLevi intersectionLeviModulusBalance intersectionLeviModulusBalance_sourceLevi jacquetInductionFunctor leviModulus_of_diagonal padicBruhatMatrixExistence padicBruhatWeylReflection padicGeometricLemma padicParabolicBruhat padicParabolicOrbitJacquetComparison padicParabolicSupportGradedTheorem padicParabolicSupportJacquetComparison padicStandardIntersectionsTheorem parabolicInductionSupportFiltration parabolicJacquetImageSubfunctor parabolicJacquetSupportFiltration parabolicOrbitJacquetFunctor parabolicSupportGradedCompactSmoothIso refinedLeviModulus_of_diagonal supportCoinvariantsImageHom_injective supportCoinvariantsImageIso supportImageNatIso supportImageQuotientHom supportImageQuotientHom_bijective supportImageQuotientIso supportImageToQuotient supportImageToQuotient_ker supportImageToQuotient_on_support supportImageToQuotient_surjective
open Langlands.AllFieldBZ.Geometric
open Langlands.CuspidalSupport hiding AssociatedCuspidalInductionFactorsTheorem AssociatedCuspidalInductionHomTheorem AssociatedGeometricPieceEquivalenceTheorem AssociatedGeometricPieceVanishingTheorem AssociatedJacquetFiltrationTheorem CuspidalEmbeddingTheorem CuspidalInductionLengthTheorem GLCuspidalTensorAssociationStatement GLCuspidalTensorStatement MinimalNonzeroJacquetTheorem MinimalWeylTransportQuasicuspidalTheorem NonassociatedJacquetSubquotientsTheorem PadicAssociatedGeometricPiecesTheorem PadicLeviAdmissibleFactorizationStatement PadicLeviCuspidalFactorizationStatement PadicLeviTensorSupercuspidalReflectionStatement TotalConjugatingCountTheorem TwoBlockAssociatedCuspidalInductionFactorsTheorem associatedCuspidalInductionFactors_of_adjacent associatedCuspidalInductionFactors_of_length_lt_two associatedGeometricPieceEquivalence cuspidalDatum_eq_of_equiv factors_of_blockMap factors_step fullRefinedInductionEquiv fullRefinedJacquetEquiv geometricPieceFunctor_subsingleton_of_proper_source glCuspidalTensor glCuspidalTensorAssociation isIrreducible_normalizedParabolicInduced_singleBlock minimalNonzeroJacquet minimalWeylTransportQuasicuspidal nonassociatedJacquetSubquotients_rankZero normalizedRefinedInductionFunctor_subsingleton padicLeviAdmissibleFactorization padicLeviCuspidalFactorization padicLeviTensorSupercuspidalReflection refinedHalfModulus_eq_one_of_full refinedInverseHalfModulus_eq_one_of_full refinedModulus_eq_one_of_full totalConjugatingCount
open Langlands.AllFieldBZ.CuspidalSupport
universe uF uV uW uR uG uC vC

section Filtration
variable {R : Type uR} {G : Type uG} [CommRing R] [Monoid G]
  {C : Type uC} [Category.{vC} C]

end Filtration
section Geometry
variable {F : Type uF} [Field F] {n : ℕ} (B C : BlockShape n)

end Geometry
section Piece
variable {F : LocalFieldPackage.{uF}} (T : F.TopologicalData)

/-- Intersection transport of the restriction of a source Levi representation,
when the whole source Levi is conjugated onto a third Levi `D`, read through a
homomorphism from the target intersection to `D` compatible with the ambient
embeddings. -/
def intersectionTransportEquivTo {G : Type uF} [Field G] {n : ℕ}
    (B C D : BlockShape n) (w : Equiv.Perm (Fin n))
    (hw : ConjugatesLevi (F := G) B D w) (ψ : sourceLevi G C B w⁻¹ →* D.Levi G)
    (hψ : ∀ x, D.leviEmbedding G (ψ x) = C.leviEmbedding G x.val)
    {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ (sourceLevi G B C w) W) (ρ : Representation ℂ (B.Levi G) V)
    (e : σ.Equiv (ρ.comp (sourceLevi G B C w).subtype)) :
    (intersectionTransport G B C w σ).Equiv ((transport B D w hw ρ).comp ψ) := by
  have key : ∀ m : sourceLevi G C B w⁻¹,
      ((intersectionLeviConjugation G B C w).symm m).val =
        (leviConjugation B D w hw).symm (ψ m) := by
    intro m
    apply B.leviEmbedding_injective G
    rw [intersectionLeviConjugation_symm_embedding, leviConjugation_symm_embedding, hψ]
  refine Representation.Equiv.mk e.toLinearEquiv ?_
  intro m
  apply LinearMap.ext
  intro v
  have he := LinearMap.congr_fun
    (e.isIntertwining' ((intersectionLeviConjugation G B C w).symm m)) v
  change e (σ ((intersectionLeviConjugation G B C w).symm m) v) =
    ρ ((leviConjugation B D w hw).symm (ψ m)) (e v)
  change e (σ ((intersectionLeviConjugation G B C w).symm m) v) =
    ρ ((intersectionLeviConjugation G B C w).symm m).val (e v) at he
  rw [key] at he
  exact he

/-- An equivalence of representations of the refined Levi induces an equivalence of
their normalized refined inductions. -/
def normalizedRefinedInducedCongr {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)
    {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ (refinedLevi F.Carrier B S) V}
    {τ : Representation ℂ (refinedLevi F.Carrier B S) W} (E : σ.Equiv τ) :
    letI := T.topology
    letI := T.leviTopologicalGroup B
    (T.normalizedRefinedInduced B S σ).Equiv (T.normalizedRefinedInduced B S τ) := by
  let := T.topology
  let := T.leviTopologicalGroup B
  exact Representation.Equiv.mk
    (LinearEquiv.ofLinearMap
      (T.normalizedRefinedInducedMap B S E.toIntertwiningMap).toLinearMap
      (T.normalizedRefinedInducedMap B S E.symm.toIntertwiningMap).toLinearMap
      (by
        apply LinearMap.ext
        intro f
        apply Subtype.ext
        apply Subtype.ext
        funext x
        exact E.apply_symm_apply _)
      (by
        apply LinearMap.ext
        intro f
        apply Subtype.ext
        apply Subtype.ext
        funext x
        exact E.symm_apply_apply _))
    (T.normalizedRefinedInducedMap B S E.toIntertwiningMap).isIntertwining'

variable {n : ℕ} (B C : BlockShape n) (w : Equiv.Perm (Fin n))
  (S : BlockRefinement B) (R : BlockRefinement C)
  (hS : sourceLevi F.Carrier B C w = refinedLevi F.Carrier B S)
  (hR : sourceLevi F.Carrier C B w⁻¹ = refinedLevi F.Carrier C R)

set_option maxHeartbeats 1200000 in
/-- When the source refinement is the whole source Levi, the geometric piece is
the normalized refined induction of the whole source representation, transported
onto the flattened target refinement. -/
def fullSourcePieceEquiv (hfull : refinedLevi F.Carrier B S = ⊤)
    (hw : ConjugatesLevi (F := F.Carrier) B (C.flatten R) w) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier),
      ((Langlands.AllFieldBZ.Geometric.geometricPieceFunctor T B C w S R hS hR).obj A).ρ.Equiv
        (T.normalizedRefinedInduced C R
          ((transport B (C.flatten R) w hw A.representation).comp
            (flattenedLeviEquiv F.Carrier C R).symm.toMonoidHom)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro A
  let J := (T.normalizedRefinedJacquetFunctor B S).obj A
  have eJ : J.representation.Equiv
      (A.representation.comp (refinedLevi F.Carrier B S).subtype) :=
    Langlands.AllFieldBZ.CuspidalSupport.fullRefinedJacquetEquiv T B S hfull A.representation
  let J' := (subgroupEqualityFunctor _ _ hS.symm).obj J
  have eJ' : J'.representation.Equiv
      (A.representation.comp (sourceLevi F.Carrier B C w).subtype) :=
    subgroupEqualityEquiv _ _ hS.symm J A.representation eJ
  let e := flattenedLeviEquiv F.Carrier C R
  let ψ : sourceLevi F.Carrier C B w⁻¹ →* (C.flatten R).Levi F.Carrier :=
    e.symm.toMonoidHom.comp (MulEquiv.subgroupCongr hR).toMonoidHom
  have hψ : ∀ x, (C.flatten R).leviEmbedding F.Carrier (ψ x) =
      C.leviEmbedding F.Carrier x.val := by
    intro x
    exact flattenedLeviEquiv_symm_embedding F.Carrier C R (MulEquiv.subgroupCongr hR x)
  let τ := transport B (C.flatten R) w hw A.representation
  let Q := (intersectionTransportFunctor F.Carrier B C w).obj J'
  have eQ : Q.representation.Equiv (τ.comp ψ) :=
    intersectionTransportEquivTo B C (C.flatten R) w hw ψ hψ J'.representation
      A.representation eJ'
  let Q' := (subgroupEqualityFunctor _ _ hR).obj Q
  have eQ' : Q'.representation.Equiv (τ.comp e.symm.toMonoidHom) :=
    subgroupEqualityEquivOf _ _ hR Q τ e.symm.toMonoidHom eQ
  change (T.normalizedRefinedInduced C R Q'.representation).Equiv _
  exact normalizedRefinedInducedCongr T C R eQ'

end Piece
section Factors
variable {F : LocalFieldPackage.{uF}} (T : F.TopologicalData)

/-- Transporting the smooth object of a supercuspidal representation along an
equality of ranks gives a supercuspidal representation. -/
theorem supercuspidalProperty_cast {a b : ℕ} (h : a = b)
    (X : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := a)) :
    letI := T.topology
    supercuspidalProperty (F := F.Carrier) (n := b)
      (h ▸ X.obj : SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier)) := by
  subst h
  exact X.property

/-- A supercuspidal representation transported along an equality of ranks. -/
def castSupercuspidal {a b : ℕ} (h : a = b)
    (X : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := a)) :
    letI := T.topology
    SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := b) :=
  letI := T.topology
  ⟨(h ▸ X.obj : SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier)),
    supercuspidalProperty_cast T h X⟩

/-- The cuspidal datum of a rank-transported supercuspidal representation is the
cuspidal datum of the original one. -/
theorem cuspidalDatum_castSupercuspidal {a b : ℕ} (h : a = b) (ha : 0 < a) (hb : 0 < b)
    (X : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := a)) :
    letI := T.topology
    (⟨b, hb, (castSupercuspidal T h X).isoClass⟩ : LocalFieldPackage.TopologicalData.CuspidalDatum.{uV, uF} T) =
      ⟨a, ha, X.isoClass⟩ := by
  subst h
  rfl

variable {n : ℕ} (C : BlockShape n) (R : BlockRefinement C)

/-- The supercuspidal factor of a flattened block, read as a representation of its
inner block. -/
def innerFactor
    (X : letI := T.topology
      ∀ k : Fin (C.flatten R).length,
        SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (C.flatten R).size k))
    (i : Fin C.length) (j : Fin (R i).length) :
    letI := T.topology
    SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (R i).size j) :=
  castSupercuspidal T (C.flatten_size_flattenBlockEquiv R ⟨i, j⟩)
    (X (C.flattenBlockEquiv R ⟨i, j⟩))

/-- The flattened product coordinates of a refined Levi element are its block
coordinates. -/
theorem flattenedLeviProductEquiv_flattenedLeviEquiv_symm
    (m : refinedLevi F.Carrier C R) :
    flattenedLeviProductEquiv F.Carrier C R ((flattenedLeviEquiv F.Carrier C R).symm m) =
      (refinedLeviEquiv F.Carrier C R).symm m := by
  rw [flattenedLeviEquiv, MulEquiv.symm_trans_apply, MulEquiv.apply_symm_apply]

/-- A factorization in flattened product coordinates gives the inducing
representation of the refined induction tensor comparison. -/
def inducingEquiv {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {σ : Representation ℂ ((C.flatten R).Levi F.Carrier) V}
    {A : Parabolic.RefinedInductionTensor.Factors.{uF, uV} F T C R}
    (E : letI := T.topology
      σ.Equiv ((FiniteTensor.external fun i => (A i).representation).comp
        (flattenedLeviProductEquiv F.Carrier C R).toMonoidHom)) :
    Representation.Equiv (σ.comp (flattenedLeviEquiv F.Carrier C R).symm.toMonoidHom)
      (Parabolic.RefinedInductionTensor.inducingRepresentation F T C R A) :=
  Representation.Equiv.mk E.toLinearEquiv fun m => by
    let := T.topology
    have := E.isIntertwining' ((flattenedLeviEquiv F.Carrier C R).symm m)
    simpa only [Parabolic.RefinedInductionTensor.inducingRepresentation,
      MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      flattenedLeviProductEquiv_flattenedLeviEquiv_symm] using this

/-- An irreducible cuspidal representation of a flattened Levi is the block tensor of
supercuspidal representations of its blocks; regrouped over the coarse blocks, its
pullback to the refined Levi is the inducing representation of the inner external
tensor products. -/
theorem exists_inner_factors (hn : 0 < n) {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ ((C.flatten R).Levi F.Carrier) V) (hσ : σ.IsIrreducible)
    (hc : letI := T.topology; IsLeviCuspidal (C.flatten R) σ) :
    letI := T.topology
    ∃ X : ∀ k : Fin (C.flatten R).length,
        SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (C.flatten R).size k),
      Nonempty (σ.Equiv ((C.flatten R).blockTensor (fun k => (X k).obj.representation))) ∧
      Nonempty (Representation.Equiv (σ.comp (flattenedLeviEquiv F.Carrier C R).symm.toMonoidHom)
        (Parabolic.RefinedInductionTensor.inducingRepresentation F T C R
          (fun i => FiniteTensor.externalSmoothObject
            (fun j => (innerFactor T C R X i j).obj)))) := by
  let := T.topology
  obtain ⟨X, ⟨eX⟩⟩ := Langlands.AllFieldBZ.CuspidalSupport.padicLeviCuspidalFactorization.{uF, uV, uV} F T n hn (C.flatten R)
    (SmoothRep.of σ hc.1.1) hσ hc
  refine ⟨X, ⟨eX⟩, ⟨inducingEquiv T C R ?_⟩⟩
  exact eX.trans (FiniteTensor.flattenedTensorRegroupEquiv F T C R (fun k => (X k).obj))

end Factors
section TensorFactor
open Function
end TensorFactor
section Core
variable {F : LocalFieldPackage.{uF}} (T : F.TopologicalData)

/-- A nonzero map out of the external tensor product of the two induced blocks of a
refinement of `(a, b)`, equivariant for the first block, makes an irreducible
representation of `GL_a` a quotient of the first induced block. -/
theorem isQuotient_first_block {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (R : BlockRefinement (Shahidi.twoBlocks a b ha hb))
    (A : Parabolic.RefinedInductionTensor.Factors.{uF, uV} F T
      (Shahidi.twoBlocks a b ha hb) R)
    (τ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier))
    (hτ : letI := T.topology; τ.IsIrreducible)
    (ψ : letI := T.topology
      PiTensorProduct ℂ (Parabolic.RefinedInductionTensor.BlockFunctions F T
        (Shahidi.twoBlocks a b ha hb) R A) →ₗ[ℂ] τ)
    (hψ : ψ ≠ 0)
    (heq : letI := T.topology
      ∀ g x, ψ (FiniteTensor.external
        (Parabolic.RefinedInductionTensor.blockRepresentations F T
          (Shahidi.twoBlocks a b ha hb) R A)
        ((Shahidi.twoBlockLeviEquiv ha hb F.Carrier).symm (g, 1)) x) =
      τ.representation g (ψ x)) :
    letI := T.topology
    SmoothRep.IsQuotient τ ((T.normalizedParabolicInductionFunctor (R 0)).obj (A 0)) := by
  let := T.topology
  obtain ⟨χ, hχ, hχeq⟩ := exists_factor_map
    (Parabolic.RefinedInductionTensor.blockRepresentations F T
      (Shahidi.twoBlocks a b ha hb) R A) 0
    (fun g => (Shahidi.twoBlockLeviEquiv ha hb F.Carrier).symm (g, 1))
    (fun g j hj => by
      fin_cases j
      · exact (hj rfl).elim
      · rfl)
    τ.representation ψ hψ heq
  exact isQuotient_of_ne_zero (Q := τ) hτ χ hχ fun g v => hχeq g v

/-- In a geometric piece with full source refinement, a nonzero map equivariant for
the first block of `(a, b)` makes an irreducible representation of `GL_a` a quotient
of the first induced block of any factorization of the transported inducing
representation. -/
theorem full_piece_quotient {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (B : BlockShape (a + b)) (w : Equiv.Perm (Fin (a + b)))
    (S : BlockRefinement B) (R : BlockRefinement (Shahidi.twoBlocks a b ha hb))
    (hS : sourceLevi F.Carrier B (Shahidi.twoBlocks a b ha hb) w = refinedLevi F.Carrier B S)
    (hR : sourceLevi F.Carrier (Shahidi.twoBlocks a b ha hb) B w⁻¹ =
      refinedLevi F.Carrier (Shahidi.twoBlocks a b ha hb) R)
    (hfull : refinedLevi F.Carrier B S = ⊤)
    (hw : ConjugatesLevi (F := F.Carrier) B ((Shahidi.twoBlocks a b ha hb).flatten R) w)
    (P0 : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier))
    (A : Parabolic.RefinedInductionTensor.Factors.{uF, uV} F T
      (Shahidi.twoBlocks a b ha hb) R)
    (eI : letI := T.topology
      Representation.Equiv
      ((transport B ((Shahidi.twoBlocks a b ha hb).flatten R) w hw P0.representation).comp
        (flattenedLeviEquiv F.Carrier (Shahidi.twoBlocks a b ha hb) R).symm.toMonoidHom)
      (Parabolic.RefinedInductionTensor.inducingRepresentation F T
        (Shahidi.twoBlocks a b ha hb) R A))
    (τ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier))
    (hτ : letI := T.topology; τ.IsIrreducible)
    (ψ : letI := T.topology
      ((Langlands.AllFieldBZ.Geometric.geometricPieceFunctor T B (Shahidi.twoBlocks a b ha hb) w S R hS hR).obj P0) →ₗ[ℂ] τ)
    (hψ : ψ ≠ 0)
    (heq : letI := T.topology
      ∀ g v, ψ (((Langlands.AllFieldBZ.Geometric.geometricPieceFunctor T B (Shahidi.twoBlocks a b ha hb) w S R hS hR).obj
        P0).ρ ((Shahidi.twoBlockLeviEquiv ha hb F.Carrier).symm (g, 1)) v) =
      τ.representation g (ψ v)) :
    letI := T.topology
    SmoothRep.IsQuotient τ ((T.normalizedParabolicInductionFunctor (R 0)).obj (A 0)) := by
  let := T.topology
  let EP := fullSourcePieceEquiv T B _ w S R hS hR hfull hw P0
  let EF := normalizedRefinedInducedCongr T _ R eI
  obtain ⟨⟨ET, -⟩⟩ := Parabolic.refinedInductionTensor F T (a + b) _ R A
  obtain ⟨χ, hχ, hχeq⟩ := exists_map_of_equiv (EP.trans (EF.trans ET))
    (fun g => (Shahidi.twoBlockLeviEquiv ha hb F.Carrier).symm (g, 1)) τ.representation
    ψ hψ heq
  exact isQuotient_first_block T ha hb R A τ hτ χ hχ hχeq

open LocalFieldPackage.TopologicalData in
/-- The cuspidal product of a family of supercuspidal representations indexed by the
blocks of a shape is the normalized parabolic induction of their external tensor
product; so a quotient of the latter is a subquotient of the former. -/
theorem isSubquotient_cuspidalProductInduced {m : ℕ} (D : BlockShape m)
    (X : letI := T.topology
      ∀ j, SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := D.size j))
    (τ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier))
    (hq : letI := T.topology
      SmoothRep.IsQuotient τ ((T.normalizedParabolicInductionFunctor D).obj
        (FiniteTensor.externalSmoothObject fun j => (X j).obj))) :
    letI := T.topology
    SmoothRep.IsSubquotient τ (T.cuspidalProductInduced
      (fun j => (⟨D.size j, D.positive j, (X j).isoClass⟩ : Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.CuspidalDatum.{uV, uF} T))
      D.sum_eq X) := by
  let := T.topology
  obtain ⟨l, size, pos, sum⟩ := D
  exact hq.isSubquotient

open LocalFieldPackage.TopologicalData in
/-- In a geometric piece of the `(a, b)` Jacquet module of a supercuspidal product
with full source refinement, an irreducible representation of `GL_a` receiving a
nonzero first-block-equivariant map is a constituent of a product of a submultiset of
the supercuspidal data. -/
theorem full_piece_support {a b k : ℕ} (ha : 0 < a) (hb : 0 < b)
    (ρ : Fin k → Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.CuspidalDatum.{uV, uF} T) (h : ∑ i, (ρ i).rank = a + b)
    (A : letI := T.topology
      ∀ i, SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (ρ i).rank))
    (hA : ∀ i, (ρ i).IsRepresentedBy (A i))
    (τ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier))
    (hτ : letI := T.topology; τ.IsIrreducible)
    (w : Equiv.Perm (Fin (a + b))) (S : BlockRefinement (T.cuspidalShape ρ h))
    (R : BlockRefinement (Shahidi.twoBlocks a b ha hb))
    (hS : sourceLevi F.Carrier (T.cuspidalShape ρ h) (Shahidi.twoBlocks a b ha hb) w =
      refinedLevi F.Carrier (T.cuspidalShape ρ h) S)
    (hR : sourceLevi F.Carrier (Shahidi.twoBlocks a b ha hb) (T.cuspidalShape ρ h) w⁻¹ =
      refinedLevi F.Carrier (Shahidi.twoBlocks a b ha hb) R)
    (hfull : refinedLevi F.Carrier (T.cuspidalShape ρ h) S = ⊤)
    (ψ : letI := T.topology
      ((Langlands.AllFieldBZ.Geometric.geometricPieceFunctor T (T.cuspidalShape ρ h) (Shahidi.twoBlocks a b ha hb) w S R
        hS hR).obj (FiniteTensor.externalSmoothObject fun i => (A i).obj)) →ₗ[ℂ] τ)
    (hψ : ψ ≠ 0)
    (heq : letI := T.topology
      ∀ g v, ψ (((Langlands.AllFieldBZ.Geometric.geometricPieceFunctor T (T.cuspidalShape ρ h) (Shahidi.twoBlocks a b ha hb)
        w S R hS hR).obj (FiniteTensor.externalSmoothObject fun i => (A i).obj)).ρ
          ((Shahidi.twoBlockLeviEquiv ha hb F.Carrier).symm (g, 1)) v) =
        τ.representation g (ψ v)) :
    ∃ (l : ℕ) (ρ'' : Fin l → Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.CuspidalDatum.{uV, uF} T),
      T.IsCuspidalConstituent ρ'' τ ∧
      (List.ofFn ρ'' : Multiset (Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.CuspidalDatum.{uV, uF} T)) ≤ List.ofFn ρ := by
  classical
  let := T.topology
  have : IsTopologicalRing F.Carrier := by
    let := T.valuativeRel
    have := T.localField
    infer_instance
  have hn : 0 < a + b := by omega
  obtain ⟨hirr, hc⟩ := Langlands.AllFieldBZ.CuspidalSupport.glCuspidalTensor F T (a + b) hn (T.cuspidalShape ρ h) A
  have hsrc : sourceLevi F.Carrier (T.cuspidalShape ρ h) (Shahidi.twoBlocks a b ha hb) w = ⊤ :=
    hS.trans hfull
  have hw := conjugatesLevi_flatten_of_source_top (F := F.Carrier) (T.cuspidalShape ρ h)
    (Shahidi.twoBlocks a b ha hb) R w hsrc hR
  obtain ⟨X, ⟨eX⟩, ⟨eI⟩⟩ := exists_inner_factors T (Shahidi.twoBlocks a b ha hb) R hn
    (transport _ _ w hw (FiniteTensor.external fun i => (A i).obj.representation))
    ((isIrreducible_transport w hw _).mpr hirr)
    (isLeviCuspidal_transport_of_conjugatesLevi _ _ w hw _ hc)
  have hquot := full_piece_quotient T ha hb (T.cuspidalShape ρ h) w S R hS hR hfull hw
    (FiniteTensor.externalSmoothObject fun i => (A i).obj)
    (fun i => FiniteTensor.externalSmoothObject fun j =>
      (innerFactor T (Shahidi.twoBlocks a b ha hb) R X i j).obj)
    eI τ hτ ψ hψ heq
  let D := (Shahidi.twoBlocks a b ha hb).flatten R
  let ρ' : Fin D.length → Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.CuspidalDatum.{uV, uF} T :=
    fun j => ⟨D.size j, D.positive j, (X j).isoClass⟩
  have assoc : (List.ofFn ρ : Multiset (Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.CuspidalDatum.{uV, uF} T)) = List.ofFn ρ' :=
    Langlands.AllFieldBZ.CuspidalSupport.glCuspidalTensorAssociation F T (a + b) hn k D.length ρ ρ' h D.sum_eq A X hA
      (fun _ => rfl) ⟨w, hw, ⟨eX⟩⟩
  let ρ'' : Fin (R 0).length → Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.CuspidalDatum.{uV, uF} T := fun j =>
    ⟨(R 0).size j, (R 0).positive j,
      (innerFactor T (Shahidi.twoBlocks a b ha hb) R X 0 j).isoClass⟩
  refine ⟨(R 0).length, ρ'', ⟨(R 0).sum_eq,
    fun j => innerFactor T (Shahidi.twoBlocks a b ha hb) R X 0 j,
    fun _ => rfl, hτ,
    isSubquotient_cuspidalProductInduced T (R 0)
      (innerFactor T (Shahidi.twoBlocks a b ha hb) R X 0) τ hquot⟩, ?_⟩
  have hρ'' : ρ'' = ρ' ∘ fun j => (Shahidi.twoBlocks a b ha hb).flattenBlockEquiv R ⟨0, j⟩ := by
    funext j
    exact cuspidalDatum_castSupercuspidal T _ _ _ _
  rw [hρ'', assoc]
  exact ofFn_comp_le ρ' _ fun j j' hjj' => by
    have := ((Shahidi.twoBlocks a b ha hb).flattenBlockEquiv R).injective hjj'
    simpa using this

open LocalFieldPackage.TopologicalData in
/-- An irreducible representation of `GL_a` receiving a nonzero map from the
`(a, b)` Jacquet module of a supercuspidal product, equivariant for the first block,
is a constituent of a product of a submultiset of the supercuspidal data. -/
theorem jacquet_quotient_support {a b k : ℕ} (ha : 0 < a) (hb : 0 < b)
    (ρ : Fin k → Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.CuspidalDatum.{uV, uF} T) (h : ∑ i, (ρ i).rank = a + b)
    (A : letI := T.topology
      ∀ i, SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (ρ i).rank))
    (hA : ∀ i, (ρ i).IsRepresentedBy (A i))
    (τ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier))
    (hτ : letI := T.topology; τ.IsIrreducible)
    (φ : letI := T.topology
      ((T.normalizedJacquetFunctor (Shahidi.twoBlocks a b ha hb)).obj
        (T.cuspidalProductInduced ρ h A)) →ₗ[ℂ] τ)
    (hφ : φ ≠ 0)
    (heq : letI := T.topology
      ∀ g v, φ (((T.normalizedJacquetFunctor (Shahidi.twoBlocks a b ha hb)).obj
        (T.cuspidalProductInduced ρ h A)).representation
          ((Shahidi.twoBlockLeviEquiv ha hb F.Carrier).symm (g, 1)) v) =
        τ.representation g (φ v)) :
    ∃ (l : ℕ) (ρ'' : Fin l → Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.CuspidalDatum.{uV, uF} T),
      T.IsCuspidalConstituent ρ'' τ ∧
      (List.ofFn ρ'' : Multiset (Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.CuspidalDatum.{uV, uF} T)) ≤ List.ofFn ρ := by
  let := T.topology
  have hn : 0 < a + b := by omega
  obtain ⟨-, hc⟩ := Langlands.AllFieldBZ.CuspidalSupport.glCuspidalTensor F T (a + b) hn (T.cuspidalShape ρ h) A
  obtain ⟨S, R, hS, hR, m, e, perm, s, hs⟩ := Geometric.padicGeometricLemma.{uF, uV} F T
    (a + b) hn (T.cuspidalShape ρ h) (Shahidi.twoBlocks a b ha hb)
  obtain ⟨i, ψ, hψ, hψeq⟩ := exists_graded_map s
    (FiniteTensor.externalSmoothObject fun i => (A i).obj)
    (fun g => (Shahidi.twoBlockLeviEquiv ha hb F.Carrier).symm (g, 1))
    τ.representation φ hφ heq
  obtain ⟨E⟩ := hs i
  let P := (Langlands.AllFieldBZ.Geometric.geometricPieceFunctor T (T.cuspidalShape ρ h) (Shahidi.twoBlocks a b ha hb)
    (e (perm i)).val (S (e (perm i))) (R (e (perm i))) (hS (e (perm i))).2.1
    (hR (e (perm i))).2.1).obj (FiniteTensor.externalSmoothObject fun i => (A i).obj)
  have E' : (s.graded i).obj (FiniteTensor.externalSmoothObject fun i => (A i).obj) ≅ P :=
    E.app _
  obtain ⟨ψ', hψ', hψ'eq⟩ := exists_map_of_iso E'
    (fun g => (Shahidi.twoBlockLeviEquiv ha hb F.Carrier).symm (g, 1))
    τ.representation ψ hψ hψeq
  by_cases hP : refinedParabolic F.Carrier (T.cuspidalShape ρ h) (S (e (perm i))) = ⊤
  · exact full_piece_support T ha hb ρ h A hA τ hτ (e (perm i)).val (S (e (perm i)))
      (R (e (perm i))) (hS (e (perm i))).2.1 (hR (e (perm i))).2.1
      (refinedLevi_eq_top_of_refinedParabolic_eq_top _ _ hP) ψ' hψ' hψ'eq
  · exfalso
    have hsub := Langlands.AllFieldBZ.CuspidalSupport.geometricPieceFunctor_subsingleton_of_proper_source F T _ _ (e (perm i)).val
      (S (e (perm i))) (R (e (perm i))) (hS (e (perm i))).2.1 (hR (e (perm i))).2.1 _ hc.2 hP
    exact hψ' (LinearMap.ext fun v => by
      rw [@Subsingleton.elim _ hsub v 0, map_zero, LinearMap.zero_apply])

end Core
section Derivative
variable {F : LocalFieldPackage.{uF}} (T : F.TopologicalData)

/-- A nonzero equivariant map onto an irreducible representation survives a rank
cast, together with irreducibility. -/
theorem exists_rankCast_map {m m' : ℕ} (h : m = m')
    (X : letI := T.topology; SmoothRep.{0, uF, uW} ℂ (GeneralLinear m F.Carrier))
    (τ : letI := T.topology; SmoothRep.{0, uF, uW} ℂ (GeneralLinear m F.Carrier))
    (hτ : letI := T.topology; τ.IsIrreducible)
    (χ : letI := T.topology; X →ₗ[ℂ] τ) (hχ : χ ≠ 0)
    (heq : letI := T.topology
      ∀ g v, χ (X.representation g v) = τ.representation g (χ v)) :
    letI := T.topology
    ((Derivative.generalLinearRankCast.{uF, uW} T h).obj τ).IsIrreducible ∧
    ∃ χ' : (Derivative.generalLinearRankCast.{uF, uW} T h).obj X →ₗ[ℂ]
        (Derivative.generalLinearRankCast.{uF, uW} T h).obj τ,
      χ' ≠ 0 ∧ ∀ g v,
        χ' (((Derivative.generalLinearRankCast.{uF, uW} T h).obj X).representation g v) =
          ((Derivative.generalLinearRankCast.{uF, uW} T h).obj τ).representation g (χ' v) := by
  subst h
  exact ⟨hτ, χ, hχ, heq⟩

open LocalFieldPackage.TopologicalData in
/-- Cuspidal constituency is unchanged by a rank cast. -/
theorem isCuspidalConstituent_of_rankCast {m m' : ℕ} (h : m = m') {l : ℕ}
    (ρ'' : Fin l → Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.CuspidalDatum.{uV, uF} T)
    (τ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier))
    (hc : T.IsCuspidalConstituent ρ''
      ((Derivative.generalLinearRankCast.{uF, max uF uV} T h).obj τ)) :
    T.IsCuspidalConstituent ρ'' τ := by
  subst h
  exact hc

open LocalFieldPackage.TopologicalData in
/-- An irreducible representation of `GL_(n-k)` receiving a nonzero equivariant map
from the order-`k` derivative of a supercuspidal product, with `0 < k < n`, is a
constituent of a product of a submultiset of the supercuspidal data. -/
theorem derivative_quotient_support
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    {n k : ℕ} (hk : k ≤ n) (hk0 : 0 < k) (hkn : k < n) {r : ℕ}
    (ρ : Fin r → Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.CuspidalDatum.{uV, uF} T) (h : ∑ i, (ρ i).rank = n)
    (A : letI := T.topology
      ∀ i, SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (ρ i).rank))
    (hA : ∀ i, (ρ i).IsRepresentedBy (A i))
    (τ : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (n - k) F.Carrier))
    (hτ : letI := T.topology; τ.IsIrreducible)
    (χ : letI := T.topology
      ((Derivative.generalLinearDerivative.{uF, max uF uV} T ψ n k hk).obj
        (T.cuspidalProductInduced ρ h A)) →ₗ[ℂ] τ)
    (hχ : χ ≠ 0)
    (heq : letI := T.topology
      ∀ g v, χ (((Derivative.generalLinearDerivative.{uF, max uF uV} T ψ n k hk).obj
        (T.cuspidalProductInduced ρ h A)).representation g v) = τ.representation g (χ v)) :
    ∃ (l : ℕ) (ρ'' : Fin l → Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.CuspidalDatum.{uV, uF} T),
      T.IsCuspidalConstituent ρ'' τ ∧
      (List.ofFn ρ'' : Multiset (Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.CuspidalDatum.{uV, uF} T)) ≤ List.ofFn ρ := by
  let := T.topology
  obtain ⟨a, rfl⟩ : ∃ a, n = a + k := ⟨n - k, by omega⟩
  have ha : 0 < a := by omega
  have hc : a + k - k = a := Nat.add_sub_cancel a k
  obtain ⟨hτ', χ', hχ', heq'⟩ := exists_rankCast_map T hc _ τ hτ χ hχ heq
  obtain ⟨E⟩ := Derivative.partialDerivativeJacquetComparison.{uF, max uF uV} F T ψ a k ha hk0
  obtain ⟨χ'', hχ'', heq''⟩ := exists_map_of_equiv
    (SmoothRep.equivOfIso (E.app (T.cuspidalProductInduced ρ h A))) id _ χ' hχ' heq'
  let J := (Derivative.positiveTwoBlockNormalizedJacquet.{uF, max uF uV} T a k ha hk0).obj
    (T.cuspidalProductInduced ρ h A)
  let φ : ((T.normalizedJacquetFunctor (Shahidi.twoBlocks a k ha hk0)).obj
      (T.cuspidalProductInduced ρ h A)) →ₗ[ℂ]
      (Derivative.generalLinearRankCast.{uF, max uF uV} T hc).obj τ :=
    χ''.comp (Derivative.partialDerivativeMk T ψ a k J)
  have hφ : φ ≠ 0 := by
    intro hz
    apply hχ''
    ext x
    obtain ⟨v, rfl⟩ := Derivative.partialDerivativeMk_surjective T ψ a k J x
    exact LinearMap.congr_fun hz v
  have hφeq : ∀ g v, φ (((T.normalizedJacquetFunctor (Shahidi.twoBlocks a k ha hk0)).obj
      (T.cuspidalProductInduced ρ h A)).representation
        ((Shahidi.twoBlockLeviEquiv ha hk0 F.Carrier).symm (g, 1)) v) =
      ((Derivative.generalLinearRankCast.{uF, max uF uV} T hc).obj τ).representation g
        (φ v) := by
    intro g v
    exact (congrArg χ'' (Derivative.partialDerivative_action_mk T ψ a k J g v)).symm.trans
      (heq'' g _)
  obtain ⟨l, ρ'', hcon, hle⟩ := jacquet_quotient_support T ha hk0 ρ h A hA _ hτ' φ hφ hφeq
  exact ⟨l, ρ'', isCuspidalConstituent_of_rankCast T hc ρ'' τ hcon, hle⟩

end Derivative
end Langlands.AllFieldBZ.Classification.CuspidalProductDerivativeQuotientSupport
