import Langlands.AlgebraicGeometry.Picard.FieldTwoAxisH1InjectivityStatement
import Langlands.AlgebraicGeometry.Modules.CechDegreeOne
import Langlands.AlgebraicGeometry.Picard.FieldTwoAxisH1Injectivity.Core

/-!
# Degree-one restriction to the two axes of a product over a field: proof

Cover `X` and `Y` by finitely many affine opens with affine pairwise intersections and cover
the fibre product `P` by the products of these opens. A class `c ∈ H¹(P, 𝒪_P)` is represented
by a Čech `1`-cocycle on this cover. If `c` is killed by both axis units, the pullbacks of the
cocycle along the axes are coboundaries, so the cocycle is a coboundary by the degree-one
Künneth argument, and `c = 0`.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof
open Langlands.AlgebraicGeometry.Modules

namespace FieldTwoAxisH1Injectivity

/-- A quasi-compact separated scheme over an affine scheme has a finite cover by affine opens
whose pairwise intersections are affine. -/
lemma exists_affineCover {R : CommRingCat.{u}} {X : Scheme.{u}} (p : X ⟶ Spec R)
    [QuasiCompact p] [IsSeparated p] :
    ∃ (I : Type u) (_ : Finite I) (U : I → X.Opens), (∀ i, IsAffineOpen (U i)) ∧
      (∀ i k, IsAffineOpen (U i ⊓ U k)) ∧ ⊤ ≤ iSup U := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  obtain ⟨s, hs, e⟩ := (isCompact_iff_finite_and_eq_biUnion_affineOpens
    (U := (⊤ : X.Opens))).mp (by simpa using isCompact_univ)
  have := hs.to_subtype
  exact ⟨s, inferInstance, fun i ↦ i.1.1, fun i ↦ i.1.2,
    fun i j ↦ (isAffineHom_diagonal_iff (f := p)).mp inferInstance ⊤ (isAffineOpen_top _) _
      (by simp) _ (by simp) i.1.2 j.1.2,
    by rw [iSup_subtype]; exact e.le⟩

/-- The point of the spectrum of a field lies in some member of every open cover. -/
lemma exists_top_le_preimage {R : CommRingCat.{u}} (hR : IsField R) {X : Scheme.{u}}
    (x : Spec R ⟶ X) {I : Type*} {U : I → X.Opens} (hU : ⊤ ≤ iSup U) :
    ∃ i, ⊤ ≤ x ⁻¹ᵁ U i := by
  let _ : Field R := hR.toField
  have : Subsingleton (Spec R) := inferInstanceAs (Subsingleton (PrimeSpectrum R))
  obtain ⟨pt⟩ : Nonempty (Spec R) := inferInstanceAs (Nonempty (PrimeSpectrum R))
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hU (Set.mem_univ (x pt)))
  refine ⟨i, fun q _ ↦ ?_⟩
  obtain rfl : q = pt := Subsingleton.elim _ _
  exact hi

/-- For a smooth proper morphism with geometrically connected fibres to `Spec R`, every global
function comes from `R`. -/
lemma surjective_secHom_top {R : CommRingCat.{u}} {X : Scheme.{u}} (p : X ⟶ Spec R)
    [Smooth p] [IsProper p] [GeometricallyConnected p] :
    Function.Surjective (secHom p ⊤).hom := by
  have : IsIso p.appTop :=
    smoothProperConnectedGlobalFunctions X (Spec R) p inferInstance inferInstance inferInstance ⊤
  have e : secHom p ⊤ = (Scheme.ΓSpecIso R).inv ≫ p.appTop := by
    show _ = _ ≫ p.app ⊤
    rw [Scheme.Hom.app_eq_appLE]
    rfl
  rw [e, CommRingCat.hom_comp, RingHom.coe_comp]
  exact (asIso p.appTop).commRingCatIsoToRingEquiv.surjective.comp
    (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv.surjective

end FieldTwoAxisH1Injectivity

open FieldTwoAxisH1Injectivity in
/-- Over a field, a class in `H¹(X ×_K Y, 𝒪)` killed by the units of both section axes
`i₁ = (id, y₀)` and `i₂ = (x₀, id)` is zero. -/
theorem fieldTwoAxisH1Injectivity : FieldTwoAxisH1InjectivityStatement.{u} := by
  intro K hK X Y _ _ _ _ _ _ x₀ y₀ P p₁ p₂ hP i₁ i₂ O H c hc₁ hc₂
  obtain ⟨I, _, U, hU, hUU, hcovU⟩ := exists_affineCover X.hom
  obtain ⟨J, _, V, hV, hVV, hcovV⟩ := exists_affineCover Y.hom
  let _ : ∀ W : X.left.Opens, Algebra K Γ(X.left, W) := fun W ↦ (secHom X.hom W).hom.toAlgebra
  let _ : ∀ W : Y.left.Opens, Algebra K Γ(Y.left, W) := fun W ↦ (secHom Y.hom W).hom.toAlgebra
  have hx₀ : x₀.left ≫ X.hom = 𝟙 _ := by simp
  have hy₀ : y₀.left ≫ Y.hom = 𝟙 _ := by simp
  obtain ⟨i₀, hi₀⟩ := exists_top_le_preimage hK x₀.left hcovU
  obtain ⟨j₀, hj₀⟩ := exists_top_le_preimage hK y₀.left hcovV
  obtain ⟨z, hz, hzu, hzb⟩ := CechDegreeOne.exists_cocycle (p₁ ≫ X.hom)
    (M := SheafOfModules.unit P.ringCatSheaf)
    (@AffineVanishing.isCechAcyclic_of_isQuasicoherent _ _ (CechDegreeOne.isQuasicoherent_unit P))
    (Z := prodCover p₁ p₂ U V) (fun a ↦ isAffineOpen_prodOpen hP (hU a.1) (hV a.2))
    (top_le_iff.1 (iSup_prodOpen_eq_top hcovU hcovV)) c
  obtain ⟨g₁, hg₁⟩ := hzu _ _ (CechDegreeOne.map_unitToPushforwardUnit_eq_zero _ i₁ 1 c hc₁)
  obtain ⟨g₂, hg₂⟩ := hzu _ _ (CechDegreeOne.map_unitToPushforwardUnit_eq_zero _ i₂ 1 c hc₂)
  exact hzb (exists_coboundary_of_axes (fun _ ↦ rfl) (fun _ ↦ rfl) hK hP U V hU hUU hV hVV
    hcovU hcovV (surjective_secHom_top X.hom) (surjective_secHom_top Y.hom) x₀.left hx₀ i₀ hi₀
    y₀.left hy₀ j₀ hj₀ i₁ (hP.lift_fst _ _ _) (hP.lift_snd _ _ _) i₂ (hP.lift_fst _ _ _)
    (hP.lift_snd _ _ _) z hz ⟨g₁, hg₁⟩ ⟨g₂, hg₂⟩)

end Langlands.AlgebraicGeometry.Picard
