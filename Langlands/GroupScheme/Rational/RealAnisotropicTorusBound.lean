import Langlands.GroupScheme.Rational.AnisotropicTorusCompactness
import Langlands.GroupScheme.MatrixRepresentationRationalPoints
import Langlands.GroupScheme.Rational.PointTopology

/-! # Bounded real points of closed tori in anisotropic groups over `ℝ` -/

noncomputable section

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Plancherel.TorusNormKernel

namespace RealAnisotropicTorus

/-- The preimage of a compact set under the inclusion of `ℝ` into a finite extension is
compact. -/
theorem isCompact_preimage_algebraMap (E : Type) [Field E] [Algebra ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace E] [IsModuleTopology ℝ E] {C : Set E}
    (hC : IsCompact C) : IsCompact (algebraMap ℝ E ⁻¹' C) := by
  have : T2Space E := t2Space_of_moduleTopology (F := ℝ)
  have : IsTopologicalAddGroup E := IsModuleTopology.isTopologicalAddGroup ℝ E
  have hker : LinearMap.ker (Algebra.linearMap ℝ E) = ⊥ :=
    LinearMap.ker_eq_bot.mpr (algebraMap ℝ E).injective
  exact (LinearMap.isClosedEmbedding_of_injective hker).isCompact_preimage hC

/-- Every regular function of a closed torus of an anisotropic group over `ℝ` is bounded on
the real points of the torus. -/
theorem exists_abs_rationalPointAlgebraHom_le {G : GroupScheme (Spec (CommRingCat.of ℝ))}
    (hG : IsAnisotropic G) {T : CommGroupScheme (Spec (CommRingCat.of ℝ))}
    [IsAffineHom T.toGrp.X.hom] [LocallyOfFiniteType T.toGrp.X.hom] [IsAffine T.X.left]
    (hT : IsTorus T.toGrp) {i : T.toGrp ⟶ G} (hi : IsClosedSubgroup i)
    (f : AffineCoordinateRing ℝ T.X) :
    ∃ α : ℝ, ∀ s : rationalPoints T.toGrp, |rationalPointAlgebraHom ℝ T.X s f| ≤ α := by
  obtain ⟨E, _, _, _, -, hsplit⟩ := torusFiniteGaloisSplitting ℝ T.toGrp hT
  obtain ⟨I, _, ⟨e⟩⟩ := hsplit
  have := Fintype.ofFinite I
  let _ : TopologicalSpace E := moduleTopology ℝ E
  have : IsModuleTopology ℝ E := ⟨rfl⟩
  have : IsTopologicalRing E := IsModuleTopology.isTopologicalRing ℝ E
  have : IsAffine (GaloisPointComparison.baseChanged ℝ E T.toGrp).X.left := by
    change IsAffine (Limits.pullback T.X.hom (GaloisPointComparison.baseMap ℝ E))
    infer_instance
  obtain ⟨Φ, hΦ, hΦeq⟩ := exists_continuous_of_splitCharacters e
    ((Limits.pullback.fst T.X.hom (GaloisPointComparison.baseMap ℝ E)).appTop.hom f)
  set KU := {u : Eˣ | ‖Algebra.norm ℝ (u : E)‖ = 1}
  have hKU : IsCompact KU := isCompact_units_algebraNorm_eq_one (F := ℝ) (E := E)
  have hC : IsCompact (Φ '' Set.pi Set.univ (fun _ : I => KU)) :=
    (isCompact_univ_pi fun _ => hKU).image hΦ
  obtain ⟨α, hα⟩ := (isCompact_preimage_algebraMap E hC).isBounded.exists_norm_le
  refine ⟨α, fun s => ?_⟩
  rw [← Real.norm_eq_abs]
  refine hα _ ⟨fun j => rationalCharacterEval (splitCharacter e j)
    (GaloisPointComparison.rationalExtend ℝ E T.toGrp s), fun j _ => ?_, ?_⟩
  · change ‖Algebra.norm ℝ ((rationalCharacterEval (splitCharacter e j)
      (GaloisPointComparison.rationalExtend ℝ E T.toGrp s) : Eˣ) : E)‖ = 1
    rw [hG.algebraNorm_characterEval_eq_one_of_closedTorus E hT hi, norm_one]
  · rw [← hΦeq, rationalPointAlgebraHom_rationalExtend]

/-- A matrix entry of the image of a real point of `T` is the value of a regular function of
`T`. -/
theorem rationalMatrix_map_apply_apply {G : GroupScheme (Spec (CommRingCat.of ℝ))}
    {n : Type} [Fintype n] [DecidableEq n] (ρ : MatrixRepresentation G n)
    {T : CommGroupScheme (Spec (CommRingCat.of ℝ))} [IsAffine T.X.left]
    (i : T.toGrp ⟶ G) (s : rationalPoints T.toGrp) (j l : n) :
    (ρ.rationalMatrix (rationalPoints.map i s) : Matrix n n ℝ) j l =
      rationalPointAlgebraHom ℝ T.X s ((i.hom.hom ≫ ρ.hom.hom).left.appTop
        (GeneralLinear.entrySection n (CommRingCat.of ℝ) j l)) := by
  rw [MatrixRepresentation.rationalMatrix_apply_apply, rationalPoints.map_apply]
  have hF := affineSchemePointEquiv_apply_eq_evaluation T.toGrp (rationalPointEquiv ℝ T.X s)
    ((i.hom.hom ≫ ρ.hom.hom).left.appTop
      (GeneralLinear.entrySection n (CommRingCat.of ℝ) j l))
  change _ = affineSchemePointEquiv ℝ T.X ℝ (rationalPointEquiv ℝ T.X s) _
  rw [hF]
  change _ = ((rationalPointEquiv ℝ T.X s).left.appTop ≫ (Scheme.ΓSpecIso _).hom).hom _
  rw [rationalPointEquiv_left, Category.assoc]
  simp only [Over.comp_left, Scheme.Hom.comp_appTop]
  rfl

end RealAnisotropicTorus

open RealAnisotropicTorus

/-- **Bounded tori in anisotropic real groups.** Every closed torus of an anisotropic group
over `ℝ` has bounded matrix entries on its real points, in every matrix representation. -/
theorem IsAnisotropic.exists_abs_rationalMatrix_le_of_closedTorus
    {G : GroupScheme (Spec (CommRingCat.of ℝ))} [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (hG : IsAnisotropic G)
    {n : Type} [Fintype n] [DecidableEq n] (ρ : MatrixRepresentation G n)
    {T : CommGroupScheme (Spec (CommRingCat.of ℝ))} {i : T.toGrp ⟶ G}
    (hT : IsTorus T.toGrp) (hi : IsClosedSubgroup i) :
    ∃ α : ℝ, ∀ (s : rationalPoints T.toGrp) (j l : n),
      |(ρ.rationalMatrix (rationalPoints.map i s) : Matrix n n ℝ) j l| ≤ α := by
  have : IsClosedImmersion i.hom.hom.left := hi
  have : IsAffineHom T.toGrp.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  have : LocallyOfFiniteType T.toGrp.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  have : IsAffine T.X.left := isAffine_of_isAffineHom T.toGrp.X.hom
  choose α hα using fun p : n × n => exists_abs_rationalPointAlgebraHom_le hG hT hi
    ((i.hom.hom ≫ ρ.hom.hom).left.appTop
      (GeneralLinear.entrySection n (CommRingCat.of ℝ) p.1 p.2))
  refine ⟨∑ p, |α p|, fun s j l => ?_⟩
  rw [rationalMatrix_map_apply_apply]
  exact ((hα (j, l) s).trans (le_abs_self _)).trans
    (Finset.single_le_sum (fun p _ => abs_nonneg (α p)) (Finset.mem_univ (j, l)))

end Langlands.GroupScheme
