import Langlands.Representation.Classification.LinkedSegmentOverlapPiece
import Langlands.Representation.Parabolic.NaturalFirstAdjointness
import Langlands.Representation.Classification.SegmentSocleJacquetReduction

/-!
# A nonzero map out of the product of two overlapping segment socles

Given a natural surjection from the normalized Jacquet module of the product onto
the identity geometric piece, and surjections from the two factors of that piece
onto the blocks of the target, first adjointness gives a nonzero intertwiner from
the product of the source blocks to the product of the target blocks.
-/

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace Langlands.Classification.QuotientHom

open GeneralLinear Geometric CategoryTheory PadicField.TopologicalData
open scoped TensorProduct

universe uF uV uW

section Tensor

variable {G H : Type*} [Monoid G] [Monoid H] {V V' W W' : Type*}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
  [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']

/-- The tensor product of two intertwiners. -/
def tprodMap {ρ : Representation ℂ G V} {ρ' : Representation ℂ G V'}
    {σ : Representation ℂ G W} {σ' : Representation ℂ G W'}
    (f : ρ.IntertwiningMap ρ') (g : σ.IntertwiningMap σ') :
    (Representation.tprod ρ σ).IntertwiningMap (Representation.tprod ρ' σ') where
  toLinearMap := TensorProduct.map f.toLinearMap g.toLinearMap
  isIntertwining' x := by
    apply TensorProduct.ext'
    intro v w
    simp only [LinearMap.comp_apply, Representation.tprod_apply, TensorProduct.map_tmul,
      Representation.IntertwiningMap.toLinearMap_apply,
      Representation.IntertwiningMap.isIntertwining]

theorem tprodMap_surjective {ρ : Representation ℂ G V} {ρ' : Representation ℂ G V'}
    {σ : Representation ℂ G W} {σ' : Representation ℂ G W'}
    (f : ρ.IntertwiningMap ρ') (g : σ.IntertwiningMap σ')
    (hf : Function.Surjective f) (hg : Function.Surjective g) :
    Function.Surjective (tprodMap f g) :=
  TensorProduct.map_surjective (g := f.toLinearMap) (g' := g.toLinearMap) hf hg

theorem compMap_surjective {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (f : ρ.IntertwiningMap σ) (φ : H →* G) (hf : Function.Surjective f) :
    Function.Surjective (SegmentSocleJacquetReduction.compMap φ f) :=
  hf

theorem comp_surjective {U : Type*} [AddCommGroup U] [Module ℂ U]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} {τ : Representation ℂ G U}
    (g : σ.IntertwiningMap τ) (f : ρ.IntertwiningMap σ)
    (hg : Function.Surjective g) (hf : Function.Surjective f) :
    Function.Surjective (g.comp f) :=
  hg.comp hf

theorem equiv_surjective {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (e : ρ.Equiv σ) : Function.Surjective e.toIntertwiningMap :=
  e.toLinearEquiv.surjective

/-- An irreducible representation lives on a nonzero space. -/
theorem nontrivial_of_isIrreducible {σ : Representation ℂ G W}
    (hσ : Representation.IsIrreducible σ) : Nontrivial W := by
  have := (Representation.irreducible_iff_isSimpleModule_asModule σ).mp hσ
  exact IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) σ.asModule

/-- A surjective intertwiner onto a nonzero space is nonzero. -/
theorem ne_zero_of_surjective_of_nontrivial {ρ : Representation ℂ G V}
    {σ : Representation ℂ G W} (hW : Nontrivial W) (f : ρ.IntertwiningMap σ)
    (hf : Function.Surjective f) : f ≠ 0 := by
  intro h
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  obtain ⟨v, rfl⟩ := hf w
  rw [h] at hw
  exact hw rfl

end Tensor

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData} {n : ℕ}

namespace OverlapConfig

variable (O : OverlapConfig.{uF, uV} T n)

set_option maxHeartbeats 1000000 in
/-- Ze80 4.6 step (2), identity-piece form: a natural surjection `η` from the
normalized Jacquet module of the product onto the identity geometric piece, a
surjection from the induced union block onto the first target block, and one from
`π₂` onto the second, give a nonzero intertwiner between the two products. -/
theorem exists_ne_zero_of_identityPiece
    (A : letI := T.topology; ∀ i, SmoothRep.{0, uF, uW} ℂ (GeneralLinear (O.B.size i) F.Carrier))
    (π₁ : letI := T.topology; SmoothRep.{0, uF, uW} ℂ (GeneralLinear O.init.degree F.Carrier))
    (π₂ : letI := T.topology; SmoothRep.{0, uF, uW} ℂ (GeneralLinear O.term.degree F.Carrier))
    (E₁ : letI := T.topology
      (T.normalizedJacquet (O.S ⟨1, Nat.one_lt_two⟩) (A ⟨1, Nat.one_lt_two⟩).obj.ρ).Equiv
      (Representation.tprod
        (π₁.representation.comp (Pi.evalMonoidHom
          (fun j => GeneralLinear ((O.S ⟨1, Nat.one_lt_two⟩).size j) F.Carrier)
            ⟨0, Nat.zero_lt_two⟩))
        (π₂.representation.comp (Pi.evalMonoidHom
          (fun j => GeneralLinear ((O.S ⟨1, Nat.one_lt_two⟩).size j) F.Carrier)
            ⟨1, Nat.one_lt_two⟩))))
    (E : letI := T.topology; ∀ j, SmoothRep.{0, uF, uW} ℂ (GeneralLinear (O.C.size j) F.Carrier))
    (η : letI := T.topology
      jacquetInductionFunctor.{uF, uW} T O.B O.C ⟶
        geometricPieceFunctor T O.B O.C 1 O.S O.R O.hS.2.1 O.hR.2.1)
    (hη : letI := T.topology
      Function.Surjective (η.app (FiniteTensor.externalSmoothObject A)).hom)
    (f₀ : letI := T.topology
      (Parabolic.RefinedInductionTensor.blockRepresentations F T O.C O.R
        (O.targetFactors (A ⟨0, Nat.zero_lt_two⟩) π₁ π₂) (0 : Fin 2)).IntertwiningMap
        (E (0 : Fin 2)).representation)
    (hf₀ : Function.Surjective f₀)
    (f₁ : letI := T.topology
      π₂.representation.IntertwiningMap (E (1 : Fin 2)).representation)
    (hf₁ : Function.Surjective f₁)
    (hE₀ : letI := T.topology; Representation.IsIrreducible (E (0 : Fin 2)).representation)
    (hE₁ : letI := T.topology; Representation.IsIrreducible (E (1 : Fin 2)).representation) :
    letI := T.topology
    ∃ f : ((T.normalizedProductInductionFunctor O.B).obj A).representation.IntertwiningMap
        ((T.normalizedProductInductionFunctor O.C).obj E).representation, f ≠ 0 := by
  let := T.topology
  let := T.generalLinearTopology n
  let := T.generalLinearTopologicalGroup n
  obtain ⟨eG⟩ := O.nonempty_geometricPieceEquiv A π₁ π₂ E₁
  let H := fun j : Fin 2 => GeneralLinear (O.C.size j) F.Carrier
  let g := tprodMap (SegmentSocleJacquetReduction.compMap (Pi.evalMonoidHom H 0) f₀)
    (SegmentSocleJacquetReduction.compMap (Pi.evalMonoidHom H 1) f₁)
  let eE := externalTwoEquiv (H := H) (fun j => (E j).representation)
  let c : (T.normalizedJacquet O.C
      ((T.normalizedProductInductionFunctor O.B).obj A).representation).IntertwiningMap
      (O.C.blockTensor (fun j => (E j).representation)) :=
    eE.symm.toIntertwiningMap.comp (g.comp (eG.toIntertwiningMap.comp
      (η.app (FiniteTensor.externalSmoothObject A)).hom))
  have hc : Function.Surjective c :=
    comp_surjective _ _ (equiv_surjective eE.symm)
      (comp_surjective _ _
        (tprodMap_surjective _ _ (compMap_surjective _ _ hf₀) (compMap_surjective _ _ hf₁))
        (comp_surjective _ _ (equiv_surjective eG) hη))
  have := nontrivial_of_isIrreducible hE₀
  have := nontrivial_of_isIrreducible hE₁
  have hc0 : c ≠ 0 := ne_zero_of_surjective_of_nontrivial eE.toLinearEquiv.toEquiv.nontrivial c hc
  exact ⟨(Parabolic.FirstAdjointness.equiv T O.C
      ((T.normalizedProductInductionFunctor O.B).obj A).isSmooth).symm c,
    (LinearEquiv.map_ne_zero_iff _).mpr hc0⟩

end OverlapConfig

end Langlands.Classification.QuotientHom
