import Langlands.GroupScheme.Absolute.BorelExistence
import Langlands.AnthropicFLT.Theorems.Thm_Ideal_height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType

/-! # A largest-dimension Borel embedding -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.BorelExistence

private theorem quotient_dimension_le_of_height_le
    (k : Type u) [Field k] {A : Type v} [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A] (P Q : Ideal A) [P.IsPrime] [Q.IsPrime]
    (hheight : P.height ≤ Q.height) :
    ringKrullDim (A ⧸ Q) ≤ ringKrullDim (A ⧸ P) := by
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  have hP : P.height ≠ ⊤ := Ideal.height_ne_top_of_isPrime
  have hQ : Q.height ≠ ⊤ := Ideal.height_ne_top_of_isPrime
  obtain ⟨p, hp⟩ :=
    P2MW.S_Ideal_height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType.P2mDimFormula.exists_ringKrullDim_eq_natCast
      k (A ⧸ P)
  obtain ⟨q, hq⟩ :=
    P2MW.S_Ideal_height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType.P2mDimFormula.exists_ringKrullDim_eq_natCast
      k (A ⧸ Q)
  have hformulaP := Ideal.height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType k P
  have hformulaQ := Ideal.height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType k Q
  rw [hp, ← ENat.natCast_toNat hP] at hformulaP
  rw [hq, ← ENat.natCast_toNat hQ] at hformulaQ
  have hsum : P.height.toNat + p = Q.height.toNat + q := by
    exact_mod_cast hformulaP.trans hformulaQ.symm
  rw [← ENat.natCast_toNat hP, ← ENat.natCast_toNat hQ] at hheight
  have hnat : P.height.toNat ≤ Q.height.toNat := by exact_mod_cast hheight
  rw [hp, hq]
  exact_mod_cast (show q ≤ p by omega)

/-- For an affine scheme, topological dimension is the dimension of its global ring. -/
theorem topologicalKrullDim_eq_globalSections (X : Scheme.{u}) [IsAffine X] :
    topologicalKrullDim X = ringKrullDim Γ(X, ⊤) := by
  calc
    topologicalKrullDim X = topologicalKrullDim (Spec Γ(X, ⊤)) :=
      IsHomeomorph.topologicalKrullDim_eq _ X.isoSpec.hom.homeomorph.isHomeomorph
    _ = ringKrullDim Γ(X, ⊤) :=
      PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _

/-- The coordinate-kernel quotient of an actual closed subgroup is its global ring. -/
theorem ringKrullDim_coordinateQuotient {k : Type u} [Field k]
    {H G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] (i : H ⟶ G) (hi : IsClosedSubgroup i) :
    ringKrullDim (Γ(G.X.left, ⊤) ⧸ coordinateKernel i) =
      ringKrullDim Γ(H.X.left, ⊤) := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : IsClosedImmersion i.hom.hom.left := hi
  exact ringKrullDim_eq_of_ringEquiv
    (RingHom.quotientKerEquivOfSurjective
      (i.hom.hom.left.app_surjective ⊤ (isAffineOpen_top _)))

/-- The global minimum kernel height gives a global maximum subgroup dimension. -/
theorem BorelData.maximalDimension {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [Smooth G.X.hom] [ConnectedSpace G.X.left]
    (d : BorelData G) (H : GroupScheme (Spec (CommRingCat.of k)))
    (i : H ⟶ G) (hi : IsAdmissible i) :
    topologicalKrullDim H.X.left ≤ topologicalKrullDim d.subgroup.X.left := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : IsLocallyNoetherian G.X.left :=
    LocallyOfFiniteType.isLocallyNoetherian G.X.hom
  have : IsIntegral G.X.left := CharacterLatticeProof.isIntegral_of_smooth k G.X.hom
  let θ : k →+* Γ(G.X.left, ⊤) :=
    G.X.hom.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
  have hft : θ.FiniteType := by
    have h₁ : G.X.hom.appTop.hom.FiniteType :=
      (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).mp inferInstance
    have h₀ : (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.FiniteType :=
      RingHom.FiniteType.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).inv).2
    exact h₁.comp h₀
  let : Algebra k Γ(G.X.left, ⊤) := θ.toAlgebra
  have : Algebra.FiniteType k Γ(G.X.left, ⊤) := hft
  have : Smooth d.subgroup.X.hom := d.isBorelSubgroup.smooth
  have : ConnectedSpace d.subgroup.X.left := d.isBorelSubgroup.connectedSpace
  have : Smooth H.X.hom := hi.2.1
  have : ConnectedSpace H.X.left := hi.2.2.1
  have : (coordinateKernel d.inclusion).IsPrime := coordinateKernel_isPrime _
  have : (coordinateKernel i).IsPrime := coordinateKernel_isPrime _
  have : IsClosedImmersion d.inclusion.hom.hom.left := d.isBorelSubgroup.isClosedSubgroup
  have : IsClosedImmersion i.hom.hom.left := hi.1
  have : IsAffine d.subgroup.X.left := isAffine_of_isAffineHom d.inclusion.hom.hom.left
  have : IsAffine H.X.left := isAffine_of_isAffineHom i.hom.hom.left
  rw [topologicalKrullDim_eq_globalSections, topologicalKrullDim_eq_globalSections,
    ← ringKrullDim_coordinateQuotient i hi.1,
    ← ringKrullDim_coordinateQuotient d.inclusion d.isBorelSubgroup.isClosedSubgroup]
  exact quotient_dimension_le_of_height_le k _ _ (d.minimalHeight H i hi)

/-- Actual Borel data equipped with the global largest-dimension property. -/
structure MaximalDimensionBorelData {k : Type u} [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))) extends BorelData G where
  maximalDimension : ∀ (H : GroupScheme (Spec (CommRingCat.of k))) (i : H ⟶ G),
    IsAdmissible i → topologicalKrullDim H.X.left ≤ topologicalKrullDim subgroup.X.left

/-- A chosen actual Borel dominates the dimensions of all admissible subgroups. -/
def maximalDimensionBorelData {k : Type u} [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [Smooth G.X.hom] [ConnectedSpace G.X.left] :
    MaximalDimensionBorelData G where
  toBorelData := borelData G
  maximalDimension := (borelData G).maximalDimension

end Langlands.GroupScheme.BorelExistence
