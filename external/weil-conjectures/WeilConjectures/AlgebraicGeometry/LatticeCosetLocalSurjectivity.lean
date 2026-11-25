/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.LatticeCosetMap
import WeilConjectures.AlgebraicGeometry.LatticePairLocalMatrix
import WeilConjectures.AlgebraicGeometry.LatticeMatrixNeighborhoods

/-!
# Local representatives by constant matrix lattices

Source: Bhatt--Scholze, Proposition 6.8.4(6), pp. 59--60
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Every lattice class is locally a constant matrix lattice in a rational trivialization.
Source: Bhatt--Scholze, Proposition 6.8.4(6), local integral bases and lattice stabilizers
(auxiliary; not a blueprint node).
Proof: represent a section by a pair using surjectivity of the class presentation.
Choose a covering trivializing its integral module. On every nonempty member, the
rationalized basis and the fixed rational trivialization give mutually inverse matrices
of continuous rational coefficients. Evaluation at a point shows that the integral
basis has the prescribed rational rank n. Thus its embedded image is g A^n for a
continuous invertible matrix g, with the same formula after every further restriction.
At any point t, the inverse image under g(t) inverse times g of the open stabilizer
GL_n(A) is an open neighborhood. On it both change matrices have continuous integral
entries and are inverse, so the lattice image agrees with the constant lattice g(t) A^n.
These open neighborhoods give a pro-etale covering. Compose it with the integral-basis
covering. Equality of the images identifies the corresponding restricted class with
the image of the constant coset under latticeCosetMap. Therefore the image sieve covers.
The empty object is handled by the empty covering; rank zero uses the empty matrices. -/
theorem latticeCosetMap_locallySurjective (X : Scheme.{u})
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : SheafOfModules.{u + 1}
      (latticeModuleRing X (WithAbs (Padic.coefficientExtensionAbsoluteValue l E))))
    (F : Sheaf (Scheme.ProEt.topology X) (Type (u + 2)))
    (c : ∀ V : X.ProEt,
      IntegralLatticePair (integralLatticeCoefficientMap X l E) L V → F.obj.obj (op V))
    (hc : IsLatticeClassPresentation (integralLatticeCoefficientMap X l E) L F c)
    (U : X.ProEt) (n : ℕ)
    (e : L.over U ≅ latticeFreeSheaf X
      (WithAbs (Padic.coefficientExtensionAbsoluteValue l E)) U n) :
    Presheaf.IsLocallySurjective ((Scheme.ProEt.topology X).over U)
      (latticeCosetMap X (WithAbs (Padic.coefficientExtensionAbsoluteValue l E))
        (latticeCoefficientIntegers l E) L F c hc U n e) := by
  classical
  let K := WithAbs (Padic.coefficientExtensionAbsoluteValue l E)
  let A := latticeCoefficientIntegers l E
  constructor
  intro T s
  obtain ⟨P, rfl⟩ := hc.1 T.left s
  obtain ⟨S, hS, hmatrix⟩ := integralLatticePair_localMatrix X K A L U n e
    T.left T.hom P
  rw [GrothendieckTopology.mem_over_iff]
  apply (Scheme.ProEt.topology X).transitive hS
  intro W a ha
  obtain ⟨G, hG⟩ := hmatrix W a ha
  let g : W.left → Matrix.GeneralLinearGroup (Fin n) K :=
    fun x ↦ Matrix.GeneralLinearGroup.map (latticeEvaluationRingHom X K W x) G
  have hg (i j : Fin n) : Continuous (fun x ↦ (g x).val i j) :=
    (G.val i j).down.continuous
  have hginv (i j : Fin n) : Continuous (fun x ↦ ((g x)⁻¹).val i j) := by
    change Continuous (fun x ↦ ((Matrix.GeneralLinearGroup.map
      (latticeEvaluationRingHom X K W x) G)⁻¹).val i j)
    simp only [← map_inv]
    exact ((G⁻¹).val i j).down.continuous
  have hnb := fun x ↦ continuousMatrixCoset_neighborhood A
    (isOpen_latticeCoefficientIntegers l E) n g hg hginv x
  let O : W.left → W.left.Opens := fun x ↦ (hnb x).choose
  have hOx (x : W.left) : x ∈ O x := (hnb x).choose_spec.1
  have hO (x y : W.left) (hy : y ∈ O x) :
      (Quotient.mk _ (g x) : integralMatrixCosets A n) = Quotient.mk _ (g y) :=
    (hnb x).choose_spec.2 y hy
  refine Scheme.ProEt.mem_topology_of_openImmersion _ (fun x ↦ (O x).ι) ?_ ?_
  · intro x
    refine ⟨x, ?_⟩
    rw [Scheme.Opens.range_ι]
    exact hOx x
  · intro x
    rw [Sieve.pullback_apply, Sieve.overEquiv_iff]
    let j := Scheme.ProEt.ofOpenImmersionHom W (O x).ι
    change ∃ q, (latticeCosetMap X K A L F c hc U n e).app
      (op (Over.mk ((j ≫ a) ≫ T.hom))) q =
        F.obj.map (j ≫ a).op (c T.left P)
    refine ⟨ULift.up (Quotient.mk _ (g x)), ?_⟩
    apply (latticeCosetMap_eq_restrict_iff X K A L F c hc U n e
      T.left _ T.hom (j ≫ a) P (g x)).mpr
    intro V
    have hv := hG (Over.mk (V.hom ≫ j))
    change Set.image (e.hom.val.app (op (Over.mk ((V.hom ≫ j) ≫ a ≫ T.hom))))
      (P.image (op (Over.mk ((V.hom ≫ j) ≫ a)))) = _ at hv
    simp only [Over.mk_hom] at hv
    have hcomp : (V.hom ≫ j) ≫ a = V.hom ≫ (j ≫ a) := Category.assoc _ _ _
    have hcomp₂ : (V.hom ≫ j) ≫ a ≫ T.hom = V.hom ≫ (j ≫ a) ≫ T.hom :=
      (Category.assoc _ _ _).trans
        (congrArg (V.hom ≫ ·) (Category.assoc j a T.hom).symm)
    rw [hcomp, hcomp₂] at hv
    rw [hv]
    apply sectionMatrixLatticeImage_eq_of_pointwise_coset
    intro y
    exact hO x ((V.hom.left ≫ j.left) y) (V.hom.left y).property

end AlgebraicGeometry.ProEtale
