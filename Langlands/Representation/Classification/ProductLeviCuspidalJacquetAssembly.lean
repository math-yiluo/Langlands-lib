import Langlands.Representation.Classification.ProductLeviCuspidalJacquetMultiplicityStatement
import Langlands.Representation.Classification.OppositeCuspidalJacquetFiltrationStatement
import Langlands.Representation.Classification.ProductLeviMinimalIndex
import Langlands.Representation.CuspidalSupport.LeviTensorFactorizationProof
import Langlands.Representation.CuspidalSupport.CuspidalTensorProof
import Langlands.Representation.Tensor.FlattenedGLRefinement
import Langlands.Representation.Parabolic.RefinedInductionTensorStatement
import Langlands.Representation.CuspidalSupport.LeviAssociation
import Langlands.Representation.CuspidalSupport.InducedJacquetCount
import Langlands.Representation.Parabolic.RefinedOppositeJacquetTensor
import Langlands.Representation.Tensor.ProductFiltration
import Langlands.Representation.Filtration.ObjectTransport
import Langlands.Representation.Filtration.FiniteFamilyMultiplicityProof

/-! Assembly of the product-Levi opposite cuspidal Jacquet counts from the refined
induction tensor comparison and the general-linear opposite Jacquet filtrations. -/

noncomputable section

namespace Langlands.ProductLeviCuspidalJacquetAssembly

open GeneralLinear Geometric CuspidalSupport

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData) {n : ℕ}
  (B : BlockShape n) (S : BlockRefinement B)

/-- An equivalence of representations of the refined Levi induces an equivalence of their
normalized refined inductions. -/
def normalizedRefinedInducedCongr {V W : Type*} [AddCommGroup V] [Module ℂ V]
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

/-- Transporting the smooth object of a supercuspidal representation along an equality
of ranks gives a supercuspidal representation. -/
theorem supercuspidalProperty_cast {a b : ℕ} (h : a = b)
    (X : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := a)) :
    letI := T.topology
    supercuspidalProperty (F := F.Carrier) (n := b)
      (h ▸ X.obj : SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier)) := by
  subst h
  exact X.property

/-- Every irreducible cuspidal representation of the flattened Levi is equivalent to the
external tensor product, over the coarse blocks, of irreducible cuspidal representations
of the inner Levis, pulled back along `flattenedLeviProductEquiv`. -/
theorem exists_factors (hn : 0 < n) {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ ((B.flatten S).Levi F.Carrier) V) (hσ : σ.IsIrreducible)
    (hc : letI := T.topology; IsLeviCuspidal (B.flatten S) σ) :
    letI := T.topology
    ∃ A : Parabolic.RefinedInductionTensor.Factors.{uF, uV} F T B S,
      (∀ i, (A i).IsIrreducible ∧ IsLeviCuspidal (S i) (A i).representation) ∧
      Nonempty (σ.Equiv ((FiniteTensor.external fun i => (A i).representation).comp
        (flattenedLeviProductEquiv F.Carrier B S).toMonoidHom)) := by
  let := T.topology
  obtain ⟨X, ⟨eX⟩⟩ := padicLeviCuspidalFactorization.{uF, uV, uV} p F T n hn (B.flatten S)
    (SmoothRep.of σ hc.1.1) hσ hc
  let h : ∀ a : (i : Fin B.length) × Fin (S i).length,
      (S a.1).size a.2 = (B.flatten S).size (B.flattenBlockEquiv S a) :=
    fun a => (B.flatten_size_flattenBlockEquiv S a).symm
  let Y : ∀ i (j : Fin (S i).length), SupercuspidalRep.{uF, uV} (F := F.Carrier)
      (n := (S i).size j) := fun i j =>
    ⟨((h ⟨i, j⟩).symm ▸ (X (B.flattenBlockEquiv S ⟨i, j⟩)).obj :
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear ((S i).size j) F.Carrier)),
      supercuspidalProperty_cast T (h ⟨i, j⟩).symm _⟩
  refine ⟨fun i => FiniteTensor.externalSmoothObject (fun j => (Y i j).obj), fun i =>
    glCuspidalTensor.{uV, uF} p F T (B.size i) (B.positive i) (S i) (Y i), ?_⟩
  exact ⟨eX.trans (FiniteTensor.flattenedTensorRegroupEquiv F T B S (fun k => (X k).obj))⟩

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {σ : Representation ℂ ((B.flatten S).Levi F.Carrier) V}
  {A : Parabolic.RefinedInductionTensor.Factors.{uF, uV} F T B S}

/-- The flattened product coordinates of a refined Levi element are its block coordinates. -/
theorem flattenedLeviProductEquiv_flattenedLeviEquiv_symm (m : refinedLevi F.Carrier B S) :
    flattenedLeviProductEquiv F.Carrier B S ((flattenedLeviEquiv F.Carrier B S).symm m) =
      (refinedLeviEquiv F.Carrier B S).symm m := by
  rw [flattenedLeviEquiv, MulEquiv.symm_trans_apply, MulEquiv.apply_symm_apply]

/-- A factorization of `σ` in flattened product coordinates gives the inducing
representation of the refined induction tensor comparison. -/
def inducingEquiv
    (E : letI := T.topology
      σ.Equiv ((FiniteTensor.external fun i => (A i).representation).comp
        (flattenedLeviProductEquiv F.Carrier B S).toMonoidHom)) :
    Representation.Equiv (σ.comp (flattenedLeviEquiv F.Carrier B S).symm.toMonoidHom)
      (Parabolic.RefinedInductionTensor.inducingRepresentation F T B S A) :=
  Representation.Equiv.mk E.toLinearEquiv fun m => by
    let := T.topology
    have := E.isIntertwining' ((flattenedLeviEquiv F.Carrier B S).symm m)
    simpa only [Parabolic.RefinedInductionTensor.inducingRepresentation, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, flattenedLeviProductEquiv_flattenedLeviEquiv_symm] using this

/-- The external tensor product of blockwise transports is the external tensor product
pulled back along the blockwise inverse conjugations. -/
theorem external_transport
    (v : ∀ i, MinimalConjugatingPermutations (F := F.Carrier) (S i) (S i))
    (y : ∀ i, (S i).Levi F.Carrier) :
    letI := T.topology
    FiniteTensor.external (fun i => transport (S i) (S i) (v i).val.val (v i).property
        (A i).representation) y =
      FiniteTensor.external (fun i => (A i).representation)
        (fun i => (leviConjugation (S i) (S i) (v i).val.val (v i).property).symm (y i)) := by
  let := T.topology
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  simp only [LinearMap.compMultilinearMap_apply, FiniteTensor.external_tprod, transport,
    MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]

/-- Blockwise transports of the factors, read on the refined Levi, are the transport of
`σ` by the assembled block-diagonal permutation, read on the refined Levi. -/
def gradedEquiv
    (E : letI := T.topology
      σ.Equiv ((FiniteTensor.external fun i => (A i).representation).comp
        (flattenedLeviProductEquiv F.Carrier B S).toMonoidHom))
    (v : ∀ i, MinimalConjugatingPermutations (F := F.Carrier) (S i) (S i)) :
    letI := T.topology
    Representation.Equiv
      ((FiniteTensor.external fun i => transport (S i) (S i) (v i).val.val (v i).property
        (A i).representation).comp (refinedLeviEquiv F.Carrier B S).symm.toMonoidHom)
      ((transport (B.flatten S) (B.flatten S) (ProductLeviMinimalIndex.assemble B S v).val.val.val
        (ProductLeviMinimalIndex.assemble B S v).val.property σ).comp
          (flattenedLeviEquiv F.Carrier B S).symm.toMonoidHom) :=
  let := T.topology
  Representation.Equiv.mk E.symm.toLinearEquiv fun m => by
    have h := E.symm.isIntertwining'
      ((leviConjugation (B.flatten S) (B.flatten S)
        (ProductLeviMinimalIndex.assemble B S v).val.val.val
        (ProductLeviMinimalIndex.assemble B S v).val.property).symm
          ((flattenedLeviEquiv F.Carrier B S).symm m))
    have hc := ProductLeviMinimalIndex.flattenedLeviProductEquiv_leviConjugation_symm B S
      F.Carrier (fun i => (v i).val.val) (fun i => (v i).property)
      (ProductLeviMinimalIndex.assemble B S v).val.property
      ((flattenedLeviEquiv F.Carrier B S).symm m)
    rw [flattenedLeviProductEquiv_flattenedLeviEquiv_symm] at hc
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at h ⊢
    rw [external_transport, transport, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [← hc]
    exact h

/-- Pulling two representations back along a group isomorphism does not change whether
they are equivalent. -/
theorem nonempty_comp_equiv_iff {G H : Type*} [Monoid G] [Monoid H] {V W : Type*}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G V) (τ : Representation ℂ G W) (φ : H ≃* G) :
    Nonempty (Representation.Equiv (ρ.comp φ.toMonoidHom) (τ.comp φ.toMonoidHom)) ↔
      Nonempty (ρ.Equiv τ) := by
  constructor
  · rintro ⟨E⟩
    exact ⟨((FiniteTensorFiltration.compSymmComp ρ φ).symm.trans
      (FiniteTensorFiltration.compCongr E φ.symm.toMonoidHom)).trans
        (FiniteTensorFiltration.compSymmComp τ φ)⟩
  · rintro ⟨E⟩
    exact ⟨FiniteTensorFiltration.compCongr E φ.toMonoidHom⟩

end Langlands.ProductLeviCuspidalJacquetAssembly

namespace Langlands

open GeneralLinear Geometric CuspidalSupport ProductLeviCuspidalJacquetAssembly

universe uF uV uW

/-- The product-Levi opposite cuspidal Jacquet counts follow from the refined induction
tensor comparison, the associated Jacquet filtrations of the general linear groups, and
their transfer to the opposite radical. -/
theorem productLeviCuspidalJacquetMultiplicity_of_upstream
    (hRIT : Parabolic.RefinedInductionTensorTheorem.{uF, uV})
    (hAJF : ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
      (n : ℕ), 0 < n → AssociatedJacquetFiltrationTheorem.{uF, uV} F T n)
    (hOpp : GLOppositeCuspidalJacquetFiltrationFromUpperStatement.{uF, uV}) :
    ProductLeviCuspidalJacquetMultiplicityStatement.{uF, uV, uW} := by
  intro p _ F T n hn B S C V _ _ σ hσ hc e σr I J
  let := T.topology
  let := T.leviTopologicalGroup B
  obtain ⟨A, hA, ⟨E⟩⟩ := exists_factors T B S hn σ hσ hc
  obtain ⟨⟨E3, -⟩⟩ := hRIT p F T n B S A
  let X : I.ρ.Equiv (Parabolic.RefinedInductionTensor.externalRepresentation F T B S A) :=
    (normalizedRefinedInducedCongr T B S (inducingEquiv T B S E)).trans E3
  let Ai : ∀ i, Rep.{max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier) := fun i =>
    CuspidalJacquetMultiplicity.induced T (S i) (Rep.of (A i).representation)
  let Jo : ∀ i, Rep.{max uF uV} ℂ ((S i).Levi F.Carrier) := fun i =>
    CuspidalJacquetMultiplicity.oppositeJacquet T (S i) (Ai i)
  let φ := (refinedLeviEquiv F.Carrier B S).symm.toMonoidHom
  let K : J.ρ.Equiv ((FiniteTensor.external fun i => (Jo i).ρ).comp φ) :=
    (RefinedOppositeJacquetTensor.normalizedRefinedOppositeJacquetCongr T B S X).trans
      (RefinedOppositeJacquetTensor.oppositeJacquetEquiv T B S Ai)
  have h1 : ∀ i, ∃ (r : ℕ)
      (eI : Fin r ≃ MinimalConjugatingPermutations (F := F.Carrier) (S i) (S i))
      (s : ObjectRepFiltration (Jo i) r), ∀ j, Nonempty ((s.gradedRepresentation j).ρ.Equiv
        (transport (S i) (S i) (eI j).val.val (eI j).property (A i).representation)) :=
    fun i => hOpp p F T (B.size i) (hAJF p F T (B.size i) (B.positive i)) (S i) (S i) (A i)
      (hA i).2.2 (LevisAssociated.refl (S i))
  choose r eI s hs using h1
  obtain ⟨N, f, Eidx, hf⟩ := FiniteTensorFiltration.exists_external B.length Jo r s
  let sJ : ObjectRepFiltration J N := LengthTwo.transport K.symm (f.comp φ)
  let family : ProductLeviMinimalIndex.CoarseMinimalPermutations (F := F.Carrier) B S →
      Rep.{uV} ℂ (refinedLevi F.Carrier B S) := fun w =>
    Rep.of ((transport C C w.val.val.val w.val.property σ).comp e.symm.toMonoidHom)
  have hfam : ∀ w, (family w).ρ.IsIrreducible := fun w =>
    JacquetLength.isIrreducible_comp e.symm.toMonoidHom e.symm.surjective
      (JacquetLength.isIrreducible_transport _ _ hσ)
  let idx : Fin N ≃ ProductLeviMinimalIndex.CoarseMinimalPermutations (F := F.Carrier) B S :=
    Eidx.trans ((Equiv.piCongrRight eI).trans (ProductLeviMinimalIndex.assembleEquiv B S))
  have hgr : ∀ j, Nonempty ((sJ.gradedRepresentation j).ρ.Equiv (family (idx j)).ρ) :=
    fun j => ⟨((((ObjectRepFiltration.equivTransportGradedEquiv (B := J) (f.comp φ)
      K.symm j).symm.trans (ObjectRepFiltration.compGradedEquiv f φ j)).trans
        (FiniteTensorFiltration.compCongr (hf j).some φ)).trans
          (FiniteTensorFiltration.compCongr
            (FiniteTensorFiltration.externalCongr fun i => (hs i (Eidx j i)).some) φ)).trans
              (gradedEquiv T B S E fun i => eI i (Eidx j i))⟩
  have key := finiteFamilyFiltrationMultiplicity.{0, uF, 0, max uF uV, uV, uW} ℂ
    (refinedLevi F.Carrier B S) (ProductLeviMinimalIndex.CoarseMinimalPermutations
      (F := F.Carrier) B S) J family hfam N idx sJ hgr
  refine ⟨key.1, fun W _ _ τ hτ m => ?_⟩
  have hcard : Nat.card {w : ProductLeviMinimalIndex.CoarseMinimalPermutations
      (F := F.Carrier) B S //
        Nonempty ((family w).ρ.Equiv (Rep.of (τ.comp e.symm.toMonoidHom)).ρ)} =
      Nat.card {w : AssociatingPermutations C C σ τ // w.val.val.val ∈ blockWeyl B} :=
    Nat.card_congr
      { toFun := fun w => ⟨⟨w.val.val, (nonempty_comp_equiv_iff _ _ e.symm).mp w.property⟩,
          w.val.property⟩
        invFun := fun w => ⟨⟨w.val.val, w.property⟩,
          (nonempty_comp_equiv_iff _ _ e.symm).mpr w.val.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rw [key.2, hcard]

end Langlands
