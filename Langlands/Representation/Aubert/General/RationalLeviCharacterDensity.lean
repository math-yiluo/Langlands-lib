import Langlands.Representation.Aubert.General.RationalLeviNormTopology
import Langlands.Representation.Plancherel.UnramifiedCharacterTransport
import Langlands.Representation.Plancherel.RationalUnramifiedCharacterDensity

/-! # Finite coordinates and principal open density on the literal rational Levi -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry Set
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme Langlands.AlgebraicGeometry.PointTopology Plancherel

variable {F : Type u} [Field F] [TopologicalSpace F]
  [ValuativeRel F] [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T) (I : Finset (SimpleRoot i ν))

local instance instRationalLeviCharacterDensity1 : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance instRationalLeviCharacterDensity2 :
    IsClosedImmersion (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left :=
  Standard.isClosedSubgroup_leviHom i ν (rootSet i ν I)
local instance instRationalLeviCharacterDensity3 : IsAffine (Standard.leviScheme i ν (rootSet i ν I)).X.left :=
  isAffine_of_isAffineHom (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left
local instance instRationalLeviCharacterDensity4 : TopologicalSpace (rationalPoints G) := pointTopology
local instance instRationalLeviCharacterDensity5 :
    TopologicalSpace (rationalPoints (Standard.leviScheme i ν (rootSet i ν I))) :=
  rationalPointTopology F (Standard.leviScheme i ν (rootSet i ν I)).X

/-- Characters of the actual Levi scheme and of the literal subgroup agree
with their compact-open topologies and their full rational norm families. -/
def leviRationalUnramifiedCharacterHomeomorph :
    unramifiedCharacters (fun χ =>
      (rationalNormCharacters (Standard.leviScheme i ν (rootSet i ν I)) χ).toMul) ≃ₜ*
      unramifiedCharacters (leviRationalNormCharacters i ν I) :=
  unramifiedCharactersHomeomorph (leviRationalPointHomeomorph i ν I)
    (fun χ => (rationalNormCharacters (Standard.leviScheme i ν (rootSet i ν I)) χ).toMul)

@[simp]
theorem leviRationalUnramifiedCharacterHomeomorph_apply
    (χ : unramifiedCharacters (fun ψ =>
      (rationalNormCharacters (Standard.leviScheme i ν (rootSet i ν I)) ψ).toMul))
    (m : levi i ν I) :
    (leviRationalUnramifiedCharacterHomeomorph i ν I χ).val m =
      χ.val ((leviRationalPointHomeomorph i ν I).symm m) := rfl

@[simp]
theorem leviRationalUnramifiedCharacterHomeomorph_symm_apply
    (χ : unramifiedCharacters (leviRationalNormCharacters i ν I))
    (m : rationalPoints (Standard.leviScheme i ν (rootSet i ν I))) :
    ((leviRationalUnramifiedCharacterHomeomorph i ν I).symm χ).val m =
      χ.val (leviRationalPointHomeomorph i ν I m) := rfl

/-- The published finite coordinates transferred to the literal Levi subgroup.
Connected reductivity of this exact Levi representative is an explicit input. -/
def leviRationalUnramifiedCharacterCoordinates
    (hL : IsConnectedReductive (Standard.leviScheme i ν (rootSet i ν I))) :
    unramifiedCharacters (leviRationalNormCharacters i ν I) ≃ₜ*
      (Fin (rationalImageRank (Standard.leviScheme i ν (rootSet i ν I))) → ℂˣ) :=
  (leviRationalUnramifiedCharacterHomeomorph i ν I).symm.trans
    (rationalCanonicalUnramifiedCharacterCoordinates
      (Standard.leviScheme i ν (rootSet i ν I)) hL)

/-- Reconstructing a character evaluates the same actual valuation-lattice
Laurent monomial at the inverse image of every literal Levi element. -/
theorem leviRationalUnramifiedCharacterCoordinates_symm_apply
    (hL : IsConnectedReductive (Standard.leviScheme i ν (rootSet i ν I)))
    (z : Fin (rationalImageRank (Standard.leviScheme i ν (rootSet i ν I))) → ℂˣ)
    (m : levi i ν I) :
    ((leviRationalUnramifiedCharacterCoordinates i ν I hL).symm z).val m =
      ∏ j, z j ^ ((rationalReductiveValuationBasis
        (Standard.leviScheme i ν (rootSet i ν I)) hL).repr
          (Additive.ofMul (rationalValuationImageProjection
            (Standard.leviScheme i ν (rootSet i ν I))
              ((leviRationalPointHomeomorph i ν I).symm m))) j) := by
  change ((rationalCanonicalUnramifiedCharacterCoordinates
    (Standard.leviScheme i ν (rootSet i ν I)) hL).symm z).val
      ((leviRationalPointHomeomorph i ν I).symm m) = _
  exact rationalCanonicalUnramifiedCharacterCoordinates_symm_apply _ hL z _

/-- Polynomial nonvanishing in the actual finite coordinates of the literal Levi. -/
def leviUnramifiedPrincipalOpen
    (hL : IsConnectedReductive (Standard.leviScheme i ν (rootSet i ν I)))
    (p : MvPolynomial
      (Fin (rationalImageRank (Standard.leviScheme i ν (rootSet i ν I)))) ℂ) :
    Set (unramifiedCharacters (leviRationalNormCharacters i ν I)) :=
  (leviRationalUnramifiedCharacterCoordinates i ν I hL) ⁻¹' complexTorusPrincipalOpen p

/-- The locus is the pullback of the actual scheme-point character locus. -/
theorem leviUnramifiedPrincipalOpen_eq_preimage
    (hL : IsConnectedReductive (Standard.leviScheme i ν (rootSet i ν I)))
    (p : MvPolynomial
      (Fin (rationalImageRank (Standard.leviScheme i ν (rootSet i ν I)))) ℂ) :
    leviUnramifiedPrincipalOpen i ν I hL p =
      (leviRationalUnramifiedCharacterHomeomorph i ν I).symm ⁻¹'
        rationalUnramifiedPrincipalOpen (Standard.leviScheme i ν (rootSet i ν I)) hL p :=
  rfl

theorem mem_leviUnramifiedPrincipalOpen
    (hL : IsConnectedReductive (Standard.leviScheme i ν (rootSet i ν I)))
    (p : MvPolynomial
      (Fin (rationalImageRank (Standard.leviScheme i ν (rootSet i ν I)))) ℂ)
    (χ : unramifiedCharacters (leviRationalNormCharacters i ν I)) :
    χ ∈ leviUnramifiedPrincipalOpen i ν I hL p ↔
      MvPolynomial.eval
        (fun j => (leviRationalUnramifiedCharacterCoordinates i ν I hL χ j : ℂ)) p ≠ 0 :=
  Iff.rfl

/-- Openness uses the inherited compact-open character topology. -/
theorem isOpen_leviUnramifiedPrincipalOpen
    (hL : IsConnectedReductive (Standard.leviScheme i ν (rootSet i ν I)))
    (p : MvPolynomial
      (Fin (rationalImageRank (Standard.leviScheme i ν (rootSet i ν I)))) ℂ) :
    IsOpen (leviUnramifiedPrincipalOpen i ν I hL p) := by
  rw [leviUnramifiedPrincipalOpen_eq_preimage]
  exact (isOpen_rationalUnramifiedPrincipalOpen _ hL p).preimage
    (leviRationalUnramifiedCharacterHomeomorph i ν I).symm.continuous

/-- Every nonzero polynomial gives a dense family of literal Levi characters. -/
theorem dense_leviUnramifiedPrincipalOpen
    (hL : IsConnectedReductive (Standard.leviScheme i ν (rootSet i ν I)))
    (p : MvPolynomial
      (Fin (rationalImageRank (Standard.leviScheme i ν (rootSet i ν I)))) ℂ)
    (hp : p ≠ 0) :
    Dense (leviUnramifiedPrincipalOpen i ν I hL p) := by
  rw [leviUnramifiedPrincipalOpen_eq_preimage]
  exact (dense_rationalUnramifiedPrincipalOpen _ hL p hp).preimage
    (leviRationalUnramifiedCharacterHomeomorph i ν I).symm.isOpenMap

/-- A product describes the finite intersection of the corresponding loci. -/
theorem leviUnramifiedPrincipalOpen_finsetProd
    (hL : IsConnectedReductive (Standard.leviScheme i ν (rootSet i ν I)))
    {κ : Type v} (s : Finset κ)
    (p : κ → MvPolynomial
      (Fin (rationalImageRank (Standard.leviScheme i ν (rootSet i ν I)))) ℂ) :
    leviUnramifiedPrincipalOpen i ν I hL (∏ j ∈ s, p j) =
      ⋂ j ∈ s, leviUnramifiedPrincipalOpen i ν I hL (p j) := by
  simp only [leviUnramifiedPrincipalOpen, complexTorusPrincipalOpen_finsetProd,
    preimage_iInter]

/-- Finitely many nonzero conditions remain dense, including an empty family. -/
theorem dense_iInter_leviUnramifiedPrincipalOpen
    (hL : IsConnectedReductive (Standard.leviScheme i ν (rootSet i ν I)))
    {κ : Type v} (s : Finset κ)
    (p : κ → MvPolynomial
      (Fin (rationalImageRank (Standard.leviScheme i ν (rootSet i ν I)))) ℂ)
    (hp : ∀ j ∈ s, p j ≠ 0) :
    Dense (⋂ j ∈ s, leviUnramifiedPrincipalOpen i ν I hL (p j)) := by
  rw [← leviUnramifiedPrincipalOpen_finsetProd i ν I hL s p]
  exact dense_leviUnramifiedPrincipalOpen i ν I hL _ (Finset.prod_ne_zero_iff.mpr hp)

/-- A family containing a nonzero coordinate principal open locus is dense. -/
theorem dense_of_leviUnramifiedPrincipalOpen_subset
    (hL : IsConnectedReductive (Standard.leviScheme i ν (rootSet i ν I)))
    (p : MvPolynomial
      (Fin (rationalImageRank (Standard.leviScheme i ν (rootSet i ν I)))) ℂ)
    (hp : p ≠ 0)
    {S : Set (unramifiedCharacters (leviRationalNormCharacters i ν I))}
    (hS : leviUnramifiedPrincipalOpen i ν I hL p ⊆ S) : Dense S :=
  (dense_leviUnramifiedPrincipalOpen i ν I hL p hp).mono hS

end Langlands.Aubert.General.RationalPointFamily
