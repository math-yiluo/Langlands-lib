import Langlands.Geometry.Building.KPInducedTorusIwahoriStatement
import Langlands.Geometry.Building.KPWeilProductBoundedNorm
import Langlands.GroupScheme.Torus.InducedWeilDecompositionProof

/-! # The Iwahori subgroup of an induced torus over the maximal unramified extension -/

noncomputable section
universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme GaloisPointComparison
open Langlands.LocalGalois.Separable

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
namespace Langlands.Geometry.Building

/-- KP Lemma 2.5.18 over `K`: the Iwahori subgroup of an induced torus is its
character-valuation kernel. -/
theorem inducedTorusIwahori : InducedTorusIwahoriStatement.{u} := by
  intro F _ _ _ _ T _ L _ _ hsplit hind
  obtain ⟨n, E, ⟨e⟩⟩ :=
    inducedTorusWeilDecomposition (UnramifiedClosure F) L T hsplit hind
  let : ∀ i, Algebra (UnramifiedClosure F) (E i) :=
    fun i => (E i).toSubalgebra.algebra
  let : ∀ i, Module (UnramifiedClosure F) (E i) :=
    fun i => @Algebra.toModule _ _ _ _ (E i).toSubalgebra.algebra
  let : ∀ i, SMul (UnramifiedClosure F) (E i) :=
    fun i => (E i).toSubalgebra.algebra.toSMul
  let aE : Algebra (UnramifiedClosure F) (∀ i, E i) := Pi.algebra _ _
  let : Module (UnramifiedClosure F) (∀ i, E i) :=
    @Algebra.toModule _ _ _ _ aE
  let : SMul (UnramifiedClosure F) (∀ i, E i) := aE.toSMul
  have : ∀ i, FiniteDimensional (UnramifiedClosure F) (E i) :=
    fun i => IntermediateField.finiteDimensional_left (E i)
  have : FiniteDimensional (UnramifiedClosure F) (∀ i, E i) := Module.Finite.pi
  have : Module.Projective (UnramifiedClosure F) (∀ i, E i) :=
    Module.Projective.of_basis (Module.Basis.ofVectorSpace (UnramifiedClosure F) (∀ i, E i))
  let J := ULift.{u} (Fin n)
  let q : J ≃ Fin n := Equiv.ulift
  let E' : J → IntermediateField (UnramifiedClosure F) L := fun i => E (q i)
  let : ∀ i, Algebra (UnramifiedClosure F) (E' i) :=
    fun i => (E' i).toSubalgebra.algebra
  let : ∀ i, Module (UnramifiedClosure F) (E' i) :=
    fun i => @Algebra.toModule _ _ _ _ (E' i).toSubalgebra.algebra
  let : ∀ i, SMul (UnramifiedClosure F) (E' i) :=
    fun i => (E' i).toSubalgebra.algebra.toSMul
  let aE' : Algebra (UnramifiedClosure F) (∀ i, E' i) := Pi.algebra _ _
  let : Module (UnramifiedClosure F) (∀ i, E' i) :=
    @Algebra.toModule _ _ _ _ aE'
  let : SMul (UnramifiedClosure F) (∀ i, E' i) := aE'.toSMul
  have : ∀ i, FiniteDimensional (UnramifiedClosure F) (E' i) :=
    fun i => IntermediateField.finiteDimensional_left (E' i)
  have : FiniteDimensional (UnramifiedClosure F) (∀ i, E' i) := Module.Finite.pi
  have : Module.Projective (UnramifiedClosure F) (∀ i, E' i) :=
    Module.Projective.of_basis (Module.Basis.ofVectorSpace (UnramifiedClosure F) (∀ i, E' i))
  let : Algebra (UnramifiedClosure F) (∀ i : J, E (q i)) := aE'
  let eB : (∀ i, E i) ≃ₐ[UnramifiedClosure F] (∀ i, E' i) :=
    (AlgEquiv.piCongrLeft (UnramifiedClosure F) (fun i : Fin n => E i) q).symm
  let W := WeilGm.commGroupScheme (CommRingCat.of (UnramifiedClosure F)) (∀ i, E' i)
  let e' : T ≅ W := e ≪≫ WeilGm.commCongrIso eB
  have : IsAffine W.X.left := by
    change IsAffine (Spec _)
    infer_instance
  apply le_antisymm (torusNormIwahori_le_characterValuationKernel
    (fixedFieldValuation F) (intermediateValuation F L)
    (intermediateValuation_conjugate F L) T)
  intro t ht
  let s := rationalPoints.map (CommGroupScheme.groupHom e'.hom) t
  have hs : s ∈ characterValuationKernel (fixedFieldValuation F) W.toGrp :=
    map_characterValuationKernel_le (fixedFieldValuation F)
      (CommGroupScheme.groupHom e'.hom) ⟨t, ht, rfl⟩
  have hsNorm : s ∈ torusNormIwahori (UnramifiedClosure F) L
      (intermediateValuation F L) W :=
    (weilProduct_torusNormIwahori_eq_characterValuationKernel F L E').ge hs
  have hback := map_torusNormIwahori_le (UnramifiedClosure F) L
    (intermediateValuation F L) e'.inv ⟨s, hsNorm, rfl⟩
  change (t ≫ (CommGroupScheme.groupHom e'.hom).hom.hom) ≫
    (CommGroupScheme.groupHom e'.inv).hom.hom ∈ _ at hback
  rw [← comp_groupHom_comp, e'.hom_inv_id] at hback
  exact hback

end Langlands.Geometry.Building
