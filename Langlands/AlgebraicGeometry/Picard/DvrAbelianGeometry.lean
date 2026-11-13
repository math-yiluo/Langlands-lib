import Langlands.AlgebraicGeometry.Picard.DvrAbelianAmpleSpecializationStatement
import Langlands.AlgebraicGeometry.Picard.AffineBaseAmpleLocality
import Langlands.AbelianScheme.SmoothGeometricIntegralityProof
import Langlands.AlgebraicGeometry.Picard.ProperFibreAmpleSpreadingProof

/-! # Geometry of an abelian scheme over a discrete valuation ring -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology TopologicalSpace

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.DvrAbelianGeometry

open Langlands.SchemeModule Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.ProjectiveBundle

set_option backward.isDefEq.respectTransparency.types false in
/-- The structure morphism of an abelian scheme is geometrically integral. -/
theorem geometricallyIntegral {S : Scheme.{u}} (A : Langlands.AbelianScheme S) :
    GeometricallyIntegral A.X.hom := by
  constructor
  intro K _ y Z fst snd h
  have : Smooth snd := MorphismProperty.of_isPullback h inferInstance
  have : GeometricallyConnected snd := MorphismProperty.of_isPullback h inferInstance
  have := Langlands.AbelianScheme.smoothGeometricIntegrality K Z snd inferInstance inferInstance
  exact GeometricallyIntegral.isIntegral_of_subsingleton snd

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- The total space of an abelian scheme over a discrete valuation ring is integral. -/
theorem isIntegral_total (A : Langlands.AbelianScheme (Spec (CommRingCat.of R))) :
    IsIntegral A.X.left := by
  have := geometricallyIntegral A
  exact GeometricallyIntegral.isIntegral_of_isLocallyNoetherian A.X.hom

/-- The spectrum of a discrete valuation ring has exactly the generic and the closed point. -/
theorem eq_bot_or_eq_closedPoint (p : Spec (CommRingCat.of R)) :
    p = (⟨⊥, inferInstance⟩ : PrimeSpectrum R) ∨ p = IsLocalRing.closedPoint R := by
  by_cases hp : p.asIdeal = ⊥
  · exact Or.inl (PrimeSpectrum.ext hp)
  · right
    have : p.asIdeal.IsMaximal := p.isPrime.isMaximal hp
    exact PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal this)

/-- The generic point differs from the closed point. -/
theorem bot_ne_closedPoint :
    ((⟨⊥, inferInstance⟩ : PrimeSpectrum R) : Spec (CommRingCat.of R)) ≠
      IsLocalRing.closedPoint R := by
  intro h
  have h' := congrArg PrimeSpectrum.asIdeal h
  simp only [IsLocalRing.closedPoint] at h'
  exact IsDiscreteValuationRing.not_a_field R h'.symm

/-- A uniformizer, as a global function on the spectrum. -/
def unif (π : R) : Γ(Spec (CommRingCat.of R), ⊤) := (Scheme.ΓSpecIso (CommRingCat.of R)).inv π

/-- The principal open of a uniformizer is exactly the generic point. -/
theorem mem_basicOpen_unif_iff {π : R} (hπ : Irreducible π) (p : Spec (CommRingCat.of R)) :
    p ∈ (Spec (CommRingCat.of R)).basicOpen (unif π) ↔ p ≠ IsLocalRing.closedPoint R := by
  rw [unif, basicOpen_eq_of_affine]
  change π ∉ p.asIdeal ↔ _
  rcases eq_bot_or_eq_closedPoint p with rfl | rfl
  · refine ⟨fun _ ↦ bot_ne_closedPoint, fun _ ↦ ?_⟩
    change π ∉ (⊥ : Ideal R)
    simpa using hπ.ne_zero
  · exact ⟨fun h ↦ absurd ((IsLocalRing.mem_maximalIdeal π).mpr hπ.not_isUnit) h,
      fun h ↦ absurd rfl h⟩

variable (A : Langlands.AbelianScheme (Spec (CommRingCat.of R)))

/-- The pulled-back uniformizer, a global function on the total space. -/
def unifX (π : R) : Γ(A.X.left, ⊤) := A.X.hom.appTop (unif π)

/-- The principal open of the pulled-back uniformizer is the complement of the special
fibre. -/
theorem mem_basicOpen_unifX_iff {π : R} (hπ : Irreducible π) (x : A.X.left) :
    x ∈ A.X.left.basicOpen (unifX A π) ↔ A.X.hom x ≠ IsLocalRing.closedPoint R := by
  rw [unifX, ← Scheme.preimage_basicOpen_top]
  exact mem_basicOpen_unif_iff hπ _

/-- Generic ampleness spreads to the principal open of the uniformizer. -/
theorem isAmple_basicOpen {π : R} (hπ : Irreducible π) (L : LineBundle A.X.left)
    (hη : ((LineBundle.pullback
      (A.X.hom.fiberι (⟨⊥, inferInstance⟩ : PrimeSpectrum R))).obj L).IsAmple) :
    ((LineBundle.pullback (A.X.left.basicOpen (unifX A π)).ι).obj L).IsAmple := by
  obtain ⟨V, hηV, -, hV⟩ := properFibreAmpleSpreading A.X.left _ A.X.hom L _ hη
  have hDV : A.X.left.basicOpen (unifX A π) ≤ A.X.hom ⁻¹ᵁ V := by
    intro x hx
    have hne := (mem_basicOpen_unifX_iff A hπ x).mp hx
    rcases eq_bot_or_eq_closedPoint (A.X.hom x) with h | h
    · change A.X.hom x ∈ V
      rw [h]
      exact hηV
    · exact absurd h hne
  let j := A.X.left.homOfLE hDV
  have hj : IsAffineHom j := by
    have : IsAffineHom (j ≫ (A.X.hom ⁻¹ᵁ V).ι) := by
      rw [A.X.left.homOfLE_ι]
      infer_instance
    exact IsAffineHom.of_comp j (A.X.hom ⁻¹ᵁ V).ι
  exact (hV.pullback_of_isAffineHom j).of_iso (openPullbackIso L.obj hDV)

/-- The special fibre has a generic point specializing to all its points. -/
theorem exists_specialGeneric :
    ∃ ξ : A.X.left, A.X.hom ξ = IsLocalRing.closedPoint R ∧
      ∀ x : A.X.left, A.X.hom x = IsLocalRing.closedPoint R → ξ ⤳ x := by
  have := geometricallyIntegral A
  let s₀ : Spec (CommRingCat.of R) := IsLocalRing.closedPoint R
  let g := genericPoint (A.X.hom.fiber s₀)
  refine ⟨A.X.hom.fiberι s₀ g, (A.X.hom.range_fiberι s₀).le ⟨g, rfl⟩, ?_⟩
  intro x hx
  have hx' : x ∈ Set.range (A.X.hom.fiberι s₀) := by
    rw [A.X.hom.range_fiberι]
    exact hx
  obtain ⟨y, rfl⟩ := hx'
  exact (genericPoint_specializes y).map (A.X.hom.fiberι s₀).continuous

/-- Every point of the special fibre is a specialization of a point of the generic fibre. -/
theorem exists_generic_generization (x : A.X.left)
    (hx : A.X.hom x = IsLocalRing.closedPoint R) :
    ∃ y : A.X.left, y ⤳ x ∧ A.X.hom y ≠ IsLocalRing.closedPoint R := by
  have hspec : ((⟨⊥, inferInstance⟩ : PrimeSpectrum R) : Spec (CommRingCat.of R)) ⤳
      A.X.hom x := by
    rw [hx]
    exact (PrimeSpectrum.le_iff_specializes _ _).mp bot_le
  obtain ⟨y, hyx, hy⟩ := Flat.generalizingMap A.X.hom hspec
  refine ⟨y, hyx, ?_⟩
  rw [hy]
  exact bot_ne_closedPoint

/-- A section of a power over the principal open becomes, after clearing a power of the
function, a global section with the same generation open on the principal open. -/
theorem exists_global_section_of_basicOpen {X : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] (L : LineBundle X) (a : Γ(X, ⊤)) {n : ℕ}
    (s : ((LineBundle.pullback (X.basicOpen a).ι).obj L).powSections n) :
    ∃ t : L.powSections n, (X.basicOpen a).ι ⁻¹ᵁ
        trivializationOpen (tensorPow L.obj n) t =
      ((LineBundle.pullback (X.basicOpen a).ι).obj L).sectionOpen s := by
  let D := X.basicOpen a
  obtain ⟨s₀, hs₀⟩ := L.openPowSection_surjective D n s
  let M : LineBundle X := ⟨tensorPow L.obj n, tensorPow_isLocallyFreeRankOne X L n⟩
  obtain ⟨k, t, ht⟩ := PrincipalSectionExtension.exists_global M a s₀
  refine ⟨t, ?_⟩
  rw [← lineBundlePullbackSectionOpen X D.toScheme D.ι M t,
    ← openSection_restriction M.obj D t]
  rw [ht, openSection_smul, trivializationOpen_smul_unit]
  · rw [← hs₀]
    change trivializationOpen _ (openSection M.obj D s₀) =
      trivializationOpen _
        ((actualPullbackTensorPowIso D.ι L.obj n).hom.app ⊤ (openSection M.obj D s₀))
    exact (trivializationOpen_mapIso _ _).symm
  · exact ((X.toRingedSpace.isUnit_res_basicOpen a).pow k).map D.topIso.inv.hom

end Langlands.AlgebraicGeometry.Picard.DvrAbelianGeometry
