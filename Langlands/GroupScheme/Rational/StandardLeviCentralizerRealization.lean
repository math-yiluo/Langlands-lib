import Langlands.GroupScheme.Rational.CentralizerRootSupport
import Langlands.GroupScheme.Rational.PositiveRootInduction
import Langlands.GroupScheme.Rational.StandardLeviRootTransport

/-! # Realizing standard Levis by cocharacter centralizers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]

/-- A chosen standard cocharacter realizes the choice-free standard Levi, once
its vanishing roots imply those of every other standard cocharacter. -/
theorem standardLevi_eq_dynamicCentralizer_of_root_zero_imp
    (hConn : DynamicConnectedStatement.{u}) (hT : IsSplitTorus T.toGrp)
    (i : T.toGrp ⟶ G) (nu : cocharacterLattice T)
    {J : Set (characterLattice T)} {zeta : cocharacterLattice T}
    (hzeta : IsStandardCocharacter i nu J zeta)
    (hzero : ∀ eta, IsStandardCocharacter i nu J eta →
      ∀ alpha ∈ relativeRoots i,
        latticePairing T alpha zeta = 0 → latticePairing T alpha eta = 0) :
    standardLevi i nu J =
      Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ i) := by
  refine le_antisymm (standardLevi_le_dynamicCentralizer i nu hzeta) ?_
  intro U g hg
  rw [mem_standardLevi]
  intro eta heta
  exact dynamicCentralizer_le_of_root_zero_imp hConn hT i zeta eta
    (hzero eta heta) U hg

/-- Genericity and negation stability extend the same-face vanishing-root
comparison to every actual root. -/
theorem standardLevi_eq_dynamicCentralizer_of_standard
    (hConn : DynamicConnectedStatement.{u}) (hT : IsSplitTorus T.toGrp)
    (i : T.toGrp ⟶ G) (nu : cocharacterLattice T)
    (hnu : IsGenericCocharacter i nu)
    (hneg : ∀ alpha ∈ relativeRoots i, -alpha ∈ relativeRoots i)
    {J : Set (characterLattice T)} {zeta : cocharacterLattice T}
    (hzeta : IsStandardCocharacter i nu J zeta) :
    standardLevi i nu J =
      Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ i) :=
  standardLevi_eq_dynamicCentralizer_of_root_zero_imp hConn hT i nu hzeta
    (fun _ heta _ halpha =>
      (hzeta.same_pairing_signs_of_root i nu hnu hneg heta halpha).2.1.mp)

/-- A cocharacter and its equality realizing a standard Levi as one dynamic
centralizer. Existence, root negation and dynamic connectedness remain explicit. -/
def standardLeviCentralizerModel
    (hConn : DynamicConnectedStatement.{u}) (hT : IsSplitTorus T.toGrp)
    (i : T.toGrp ⟶ G) (nu : cocharacterLattice T)
    (hnu : IsGenericCocharacter i nu)
    (hneg : ∀ alpha ∈ relativeRoots i, -alpha ∈ relativeRoots i)
    (J : Set (characterLattice T))
    (hexists : ∃ zeta, IsStandardCocharacter i nu J zeta) :
    {zeta : cocharacterLattice T //
      IsStandardCocharacter i nu J zeta ∧
        standardLevi i nu J =
          Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ i)} :=
  ⟨hexists.choose, hexists.choose_spec,
    standardLevi_eq_dynamicCentralizer_of_standard hConn hT i nu hnu hneg
      hexists.choose_spec⟩

/-- An exact identity of actual vanishing-root supports yields an identity of
the corresponding simultaneous centralizer on every test scheme. -/
theorem cocharacterCentralizerIntersection_eq_of_root_zero_iff
    (hConn : DynamicConnectedStatement.{u}) (hT : IsSplitTorus T.toGrp)
    (i : T.toGrp ⟶ G) (zeta eta theta : cocharacterLattice T)
    (hzero : ∀ alpha ∈ relativeRoots i,
      (latticePairing T alpha zeta = 0 ∧ latticePairing T alpha eta = 0) ↔
        latticePairing T alpha theta = 0) :
    cocharacterCentralizerIntersection i zeta eta =
      Dynamic.centralizer (CommGroupScheme.groupHom theta ≫ i) := by
  apply le_antisymm
  · exact dynamicCentralizer_inf_le_of_root_zero_imp hConn hT i zeta eta theta
      (fun _ halpha hz he => (hzero _ halpha).mp ⟨hz, he⟩)
  · intro U g hg
    exact ⟨dynamicCentralizer_le_of_root_zero_imp hConn hT i theta zeta
        (fun _ halpha htheta => ((hzero _ halpha).mpr htheta).1) U hg,
      dynamicCentralizer_le_of_root_zero_imp hConn hT i theta eta
        (fun _ halpha htheta => ((hzero _ halpha).mpr htheta).2) U hg⟩

section Normalizer

variable (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]

omit [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
  [Mono i.hom.hom.left] in
/-- The source-side inverse transport of a cocharacter centralizer is the
centralizer of the inversely transported cocharacter, for each actual lift. -/
theorem dynamicCentralizer_comap_innerIso_hom
    (n : normalizerPoints i) (zeta : cocharacterLattice T) :
    (Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ i)).comap
        (G.innerIso (n : rationalPoints G)).hom =
      Dynamic.centralizer (CommGroupScheme.groupHom
        ((cocharacterAut (normalizingAut i n)).symm zeta) ≫ i) := by
  let eta := (cocharacterAut (normalizingAut i n)).symm zeta
  have heq : cocharacterAut (normalizingAut i n) eta = zeta :=
    LinearEquiv.apply_symm_apply _ _
  have h := Dynamic.centralizer_eq_comap_of_iso
    (CommGroupScheme.groupHom eta ≫ i) (G.innerIso (n : rationalPoints G))
  rw [← groupHom_cocharacterAut_comp, heq] at h
  exact h.symm

omit [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left] in
/-- The pairing for inverse cocharacter transport is the pairing against
forward character transport. -/
theorem latticePairing_inverse_cocharacterAut
    (n : normalizerPoints i) (alpha : characterLattice T)
    (zeta : cocharacterLattice T) :
    latticePairing T alpha ((cocharacterAut (normalizingAut i n)).symm zeta) =
      latticePairing T (weylAction i n alpha) zeta := by
  symm
  have h := latticePairing_characterAut_cocharacterAut (normalizingAut i n)
    alpha ((cocharacterAut (normalizingAut i n)).symm zeta)
  simpa only [LinearEquiv.apply_symm_apply, weylAction_apply, characterAut_apply] using h

/-- Standard-Levi twisted intersection reduces to the exact zero-root support
identity with the source-side inverse-comap orientation. -/
theorem standardLevi_twistedIntersection_of_root_zero_iff
    (hConn : DynamicConnectedStatement.{u}) (hT : IsSplitTorus T.toGrp)
    (nu : cocharacterLattice T) (hnu : IsGenericCocharacter i nu)
    (hneg : ∀ alpha ∈ relativeRoots i, -alpha ∈ relativeRoots i)
    {I J K : Set (characterLattice T)}
    {zetaI zetaJ zetaK : cocharacterLattice T}
    (hI : IsStandardCocharacter i nu I zetaI)
    (hJ : IsStandardCocharacter i nu J zetaJ)
    (hK : IsStandardCocharacter i nu K zetaK)
    (n : normalizerPoints i)
    (hzero : ∀ alpha ∈ relativeRoots i,
      (latticePairing T alpha zetaJ = 0 ∧
        latticePairing T (weylAction i n alpha) zetaI = 0) ↔
          latticePairing T alpha zetaK = 0) :
    standardLevi i nu J ⊓
        (standardLevi i nu I).comap (G.innerIso (n : rationalPoints G)).hom =
      standardLevi i nu K := by
  rw [standardLevi_eq_dynamicCentralizer_of_standard hConn hT i nu hnu hneg hI,
    standardLevi_eq_dynamicCentralizer_of_standard hConn hT i nu hnu hneg hJ,
    standardLevi_eq_dynamicCentralizer_of_standard hConn hT i nu hnu hneg hK,
    dynamicCentralizer_comap_innerIso_hom]
  exact cocharacterCentralizerIntersection_eq_of_root_zero_iff hConn hT i _ _ _
    (fun alpha halpha => by
      rw [latticePairing_inverse_cocharacterAut]
      exact hzero alpha halpha)

end Normalizer

end Langlands.GroupScheme
