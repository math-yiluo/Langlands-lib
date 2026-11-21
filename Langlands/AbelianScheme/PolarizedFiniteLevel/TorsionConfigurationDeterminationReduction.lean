import Langlands.AbelianScheme.PolarizedFiniteLevel.CubicEmbeddingTorsionEquations
import Langlands.AbelianScheme.PolarizedFiniteLevel.FrameEmbeddingFaithful
import Langlands.AbelianScheme.PolarizedFiniteLevel.TorsionConfigurationDeterminationStatement
import Langlands.AbelianScheme.PolarizedFiniteLevel.TorsionEvaluationSections
import Langlands.AlgebraicGeometry.LinearSystem.BundleComparison

/-! # The remaining inputs for torsion-configuration determination -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.Picard
open Langlands.AlgebraicGeometry.LinearSystem Langlands.AlgebraicGeometry.Modules.DerivedSections
open Langlands.SchemeModule Langlands.Scheme.Modules

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

open GroupScheme.Tate

variable {P : Prerequisites.{u}} {S : Scheme.{u}} {g d n m : ℕ}
  {a b : Datum P S g d n}
  {ψ : a.abelian.X.left ⟶ RelativeProjectiveSpace S m}
  {χ : b.abelian.X.left ⟶ RelativeProjectiveSpace S m}

/-- The scheme isomorphism from equal kernels is pointed and identifies the ordered level
from the labelled points. The common projective twist then identifies the polarization
using the cubic-bundle polarization determination input. -/
theorem Datum.IsCubicEmbedding.nonempty_polarizedIso_of_ker_eq
    [IsLocallyNoetherian S] (HP : CubicBundlePolarizationDeterminationStatement.{u})
    (hψ : a.IsCubicEmbedding ψ) (hχ : b.IsCubicEmbedding χ)
    (hker : ψ.ker = χ.ker) (hpoints : ∀ r, a.torsionPoint r ≫ ψ = b.torsionPoint r ≫ χ) :
    Nonempty (PolarizedIso a b) := by
  have := hψ.isClosedImmersion
  have := hχ.isClosedImmersion
  let φ := IsClosedImmersion.lift χ ψ hker.ge
  have hφ : φ ≫ χ = ψ := IsClosedImmersion.lift_fac _ _ _
  have : IsIso φ := IsClosedImmersion.isIso_lift _ _ hker.symm
  have hφπ : φ ≫ b.abelian.X.hom = a.abelian.X.hom := by
    rw [← hχ.toBase, ← Category.assoc, hφ, hψ.toBase]
  have hpt (r : Fin (2 * g) → ZMod n) : a.torsionPoint r ≫ φ = b.torsionPoint r := by
    apply (cancel_mono χ).mp
    rw [Category.assoc, hφ, hpoints]
  let eO : a.abelian.X ≅ b.abelian.X := Over.isoMk (asIso φ) hφπ
  have hunit : η[a.abelian.X] ≫ eO.hom = η[b.abelian.X] := by
    have h0 := hpt 0
    rw [a.torsionPoint_zero, b.torsionPoint_zero] at h0
    have : IsIso (CartesianMonoidalCategory.toUnit (Over.mk (𝟙 S))).left := by
      have : IsIso (CartesianMonoidalCategory.toUnit (Over.mk (𝟙 S))) :=
        Limits.isIso_of_isTerminal Over.mkIdTerminal CartesianMonoidalCategory.isTerminalTensorUnit _
      infer_instance
    apply Over.OverMorphism.ext
    rw [← cancel_epi (CartesianMonoidalCategory.toUnit (Over.mk (𝟙 S))).left]
    simp only [Over.comp_left] at h0 ⊢
    rw [Category.assoc] at h0
    exact h0
  have hmon : IsMonHom eO.hom :=
    Langlands.AbelianScheme.pointedMorphismRigidity S a.abelian.toGrp b.abelian.toGrp
      ⟨inferInstance, inferInstance, inferInstance⟩ inferInstance inferInstance inferInstance
      eO.hom hunit
  let gIso : a.abelian.toGrp ≅ b.abelian.toGrp :=
    { hom := Grp.homMk eO.hom
      inv := Grp.homMk eO.inv
      hom_inv_id := by apply Grp.hom_ext; exact eO.hom_inv_id
      inv_hom_id := by apply Grp.hom_ext; exact eO.inv_hom_id }
  let e : a.abelian ≅ b.abelian :=
    { hom := Additive.ofMul gIso.hom
      inv := Additive.ofMul gIso.inv
      hom_inv_id := congrArg Additive.ofMul gIso.hom_inv_id
      inv_hom_id := congrArg Additive.ofMul gIso.inv_hom_id }
  let L := (RelativeProjectiveSpace.twistOne S m).obj
  let eL : (Scheme.Modules.pullback (hom e.hom)).obj b.cubicBundle.obj ≅ a.cubicBundle.obj :=
    (Scheme.Modules.pullback φ).mapIso hχ.cubic.some.symm ≪≫
      (Scheme.Modules.pullbackComp φ χ).app L ≪≫
      (Scheme.Modules.pullbackCongr hφ).app L ≪≫ hψ.cubic.some
  let N : LineBundle S := ⟨structureSheaf S, fun x =>
    ⟨⊤, trivial, ⟨Scheme.Modules.restrictUnitIso (⊤ : S.Opens).ι⟩⟩⟩
  have hL : Nonempty ((LineBundle.pullback (hom e.hom)).obj b.cubicBundle ≅
      LineBundle.tensor P.preservation a.cubicBundle ((LineBundle.pullback a.abelian.X.hom).obj N)) :=
    ⟨ObjectProperty.isoMk _ (eL ≪≫ (tensorRightUnitor a.cubicBundle.obj).symm ≪≫
      (tensorFunctor _).mapIso ((Iso.refl _).prod (pullbackUnitIso a.abelian.X.hom).symm))⟩
  refine ⟨{ abelianIso := e, polarization_eq := HP P S g d n a b e N hL, level_eq := fun j => ?_ }⟩
  apply toSection_injective b.abelian.toGrp (Over.mk (𝟙 S)) n
  change Additive.ofMul ((Additive.toMul (a.level.sections j)).val ≫
      (groupHom e.hom).hom.hom) = Additive.ofMul (Additive.toMul (b.level.sections j)).val
  congr 1
  apply Over.OverMorphism.ext
  rw [Over.comp_left, ← a.torsionPoint_single, ← b.torsionPoint_single]
  exact hpt _

section Field

variable {K : Type u} [Field K]
  {A B : Datum P (Spec (CommRingCat.of K)) g d n}

private lemma relativeLinearSystemMap_eq_of_mapIsoSections {X T : Scheme.{u}}
    {L M : LineBundle X} (p : X ⟶ T) (e : L.obj ≅ M.obj)
    (s : Fin (m + 1) → GlobalSections L.obj) (t : Fin (m + 1) → GlobalSections M.obj)
    (hs : ∀ x, ∃ j, x ∈ nonvanishingLocus L.obj (s j))
    (ht : ∀ x, ∃ j, x ∈ nonvanishingLocus M.obj (t j))
    (he : mapIsoSections e s = t) :
    relativeLinearSystemMap p hs = relativeLinearSystemMap p ht := by
  subst t
  exact (relativeLinearSystemMap_mapIso p e hs).symm

private lemma equal_torsionImages_of_pullbackSections
    {s : Fin (m + 1) → GlobalSections A.cubicBundle.obj}
    {t : Fin (m + 1) → GlobalSections B.cubicBundle.obj}
    (hs : ∀ x, ∃ j, x ∈ nonvanishingLocus A.cubicBundle.obj (s j))
    (ht : ∀ x, ∃ j, x ∈ nonvanishingLocus B.cubicBundle.obj (t j))
    (r : Fin (2 * g) → ZMod n)
    (e : (Scheme.Modules.pullback (A.torsionPoint r)).obj A.cubicBundle.obj ≅
      (Scheme.Modules.pullback (B.torsionPoint r)).obj B.cubicBundle.obj)
    (he : ∀ j, e.hom.app ⊤ (pullbackSection (A.torsionPoint r) A.cubicBundle.obj (s j)) =
      pullbackSection (B.torsionPoint r) B.cubicBundle.obj (t j)) :
    A.torsionPoint r ≫ relativeLinearSystemMap A.abelian.X.hom hs =
      B.torsionPoint r ≫ relativeLinearSystemMap B.abelian.X.hom ht := by
  have hA := relativeLinearSystemMap_pullback A.abelian.X.hom (𝟙 _) (A.torsionPoint r) (𝟙 _)
    (by simp) hs
  have hB := relativeLinearSystemMap_pullback B.abelian.X.hom (𝟙 _) (B.torsionPoint r) (𝟙 _)
    (by simp) ht
  rw [RelativeProjectiveSpace.map_id, Category.comp_id] at hA hB
  let L := (LineBundle.pullback (A.torsionPoint r)).obj A.cubicBundle
  let M := (LineBundle.pullback (B.torsionPoint r)).obj B.cubicBundle
  let sa : Fin (m + 1) → GlobalSections L.obj := fun j => pullbackSection (A.torsionPoint r) _ (s j)
  let sb : Fin (m + 1) → GlobalSections M.obj := fun j => pullbackSection (B.torsionPoint r) _ (t j)
  have ha := pullbackSections_generate (A.torsionPoint r) hs
  have hb := pullbackSections_generate (B.torsionPoint r) ht
  have hm : mapIsoSections (L := L) (M := M) e sa = sb := funext he
  have hcomp := relativeLinearSystemMap_eq_of_mapIsoSections (L := L) (M := M) (𝟙 _) e sa sb ha hb hm
  exact hA.symm.trans (hcomp.trans hB)

variable [IsAlgClosed K]

/-- Equivalent evaluations give the same projective images of the labelled torsion points
in complete systems with corresponding bases. -/
theorem Datum.TorsionConfigurationEquivalent.exists_cubicEmbeddings
    (h : A.TorsionConfigurationEquivalent B) (hL : CubicFieldEmbeddingStatement.{u}) (hd : 0 < d) :
    ∃ (ψ : A.abelian.X.left ⟶ RelativeProjectiveSpace (Spec (CommRingCat.of K))
        (cubicProjectiveDimension g d))
      (χ : B.abelian.X.left ⟶ RelativeProjectiveSpace (Spec (CommRingCat.of K))
        (cubicProjectiveDimension g d)),
      A.IsCubicEmbedding ψ ∧ B.IsCubicEmbedding χ ∧
        ∀ r, A.torsionPoint r ≫ ψ = B.torsionPoint r ≫ χ := by
  obtain ⟨φ, hφ⟩ := h
  have : Epi A.cubicEvaluationAdjoint := (hL P K g d n hd A).1
  have : Epi B.cubicEvaluationAdjoint := (hL P K g d n hd B).1
  have hA := Langlands.AlgebraicGeometry.Modules.isFinitePresentation_of_hasFiniteLocalBasis _
    (hasFiniteLocalBasis_of_isLocallyFreeOfRank
      (cubicDirectImage P (Spec (CommRingCat.of K)) g d n hd A).1)
  have hB := Langlands.AlgebraicGeometry.Modules.isFinitePresentation_of_hasFiniteLocalBasis _
    (hasFiniteLocalBasis_of_isLocallyFreeOfRank
      (cubicDirectImage P (Spec (CommRingCat.of K)) g d n hd B).1)
  let V := (relativeGlobalSections A.abelian.X.hom).obj A.cubicBundle.obj
  let W := (relativeGlobalSections B.abelian.X.hom).obj B.cubicBundle.obj
  let m := cubicProjectiveDimension g d
  have hV : Module.finrank K V = m + 1 := A.finrank_cubicSections hd
  have : FiniteDimensional K V := Module.finite_of_finrank_eq_succ hV
  let α : Module.Basis (Fin (m + 1)) K V := Module.finBasisOfFinrankEq K V hV
  let e : V ≃ₗ[K] W := (moduleSpecΓFunctor.mapIso φ).toLinearEquiv
  let β := α.map e
  have hs := A.basis_generates α
  have ht := B.basis_generates β
  let ψ := relativeLinearSystemMap A.abelian.X.hom hs
  let χ := relativeLinearSystemMap B.abelian.X.hom ht
  refine ⟨ψ, χ, ⟨relativeLinearSystemMap_toBase _ _, (hL P K g d n hd A).2 m α hs, ?_⟩,
    ⟨relativeLinearSystemMap_toBase _ _, (hL P K g d n hd B).2 m β ht, ?_⟩, ?_⟩
  · exact ⟨relativeLinearSystemTwistIso (L := A.cubicBundle) (fun j => α j) A.abelian.X.hom hs⟩
  · exact ⟨relativeLinearSystemTwistIso (L := B.cubicBundle) (fun j => β j) B.abelian.X.hom ht⟩
  · intro r
    obtain ⟨eR, heR⟩ := hφ r
    apply equal_torsionImages_of_pullbackSections hs ht r eR
    intro j
    have hj := congrArg (fun k => k.app ⊤ (α j : Γ(A.rigidificationModule, ⊤))) heR
    change (B.torsionEvaluation r).app ⊤ (β j : Γ(B.rigidificationModule, ⊤)) =
      eR.hom.app ⊤ ((A.torsionEvaluation r).app ⊤ (α j)) at hj
    rw [A.torsionEvaluation_app_top, B.torsionEvaluation_app_top] at hj
    exact hj.symm

end Field

set_option linter.defProp false in
/-- The torsion configuration determination statement follows from the field embedding
and polarization recovery statements, with uniform scheme-theoretic kernel determination. -/
def torsionConfigurationDetermination_of_cubicFieldEmbedding
    (hL : CubicFieldEmbeddingStatement.{u})
    (HP : CubicBundlePolarizationDeterminationStatement.{u}) :
    TorsionConfigurationDeterminationStatement.{u} := by
  intro P g d hg hd
  obtain ⟨N, hN⟩ := exists_cubicEmbedding_ker_eq_of_torsion.{u} g d (cubicProjectiveDimension g d) hg hd
  refine ⟨N, fun n hn K _ _ hnK a b h => ?_⟩
  obtain ⟨ψ, χ, hψ, hχ, hp⟩ := h.exists_cubicEmbeddings hL hd
  exact hψ.nonempty_polarizedIso_of_ker_eq HP hχ (hN P K n hn hnK a b ψ χ hψ hχ hp) hp

end Langlands.AbelianScheme.PolarizedFiniteLevel
