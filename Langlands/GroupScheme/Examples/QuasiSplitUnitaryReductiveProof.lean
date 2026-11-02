import Langlands.GroupScheme.Examples.QuasiSplitUnitaryReductiveStatement
import Langlands.GroupScheme.Examples.QuasiSplitUnitarySplitting
import Langlands.GroupScheme.Reductive.GeneralLinear
import Langlands.GroupScheme.SmoothProducts
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent

/-! # The quasi-split unitary group `U(1,1)` is connected reductive: proof

Over `E`, `U(1,1)` becomes `GL₂` (`splittingIso`). Smoothness descends along the fpqc map
`Spec E ⟶ Spec F`, connectedness passes along the surjective projection of the base change, and
the geometric unipotent radical is computed after factoring `F → F̄` through `E`.
-/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme.QuasiSplitUnitary

variable {F E : Type u} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]

/-- The scalar map `Spec E ⟶ Spec F` of a field extension is surjective, flat and quasi-compact. -/
theorem scalarMap_fpqc :
    Surjective (Spec.map (CommRingCat.ofHom (algebraMap F E))) ∧
      Flat (Spec.map (CommRingCat.ofHom (algebraMap F E))) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap F E))) := by
  have h : Flat (Spec.map (CommRingCat.ofHom (algebraMap F E))) ∧
      Surjective (Spec.map (CommRingCat.ofHom (algebraMap F E))) := by
    apply (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom (algebraMap F E))).2
    change (algebraMap F E).FaithfullyFlat
    rw [RingHom.faithfullyFlat_algebraMap_iff]
    infer_instance
  exact ⟨h.2, h.1, inferInstance⟩

variable {κ : Type u} [Fintype κ] (b : Module.Basis κ F (Matrix (Fin 2) (Fin 2) E))
  (c : E ≃ₐ[F] E) (hc : c ≠ AlgEquiv.refl)

include hc in
/-- `U(1,1)` is smooth: its base change to `E` is `GL₂`, and smoothness descends. -/
theorem smooth_groupScheme : Smooth (groupScheme b c).X.hom := by
  have hE : Smooth (baseChangeGroupScheme b c).X.hom :=
    GroupScheme.smooth_of_over_iso ((Grp.forget _).mapIso (splittingIso b c hc))
      (GeneralLinear.smoothStatement (Fin 2) (CommRingCat.of E))
  obtain ⟨h1, h2, h3⟩ := scalarMap_fpqc (F := F) (E := E)
  exact MorphismProperty.of_pullback_snd_of_descendsAlong
    (P := @Smooth) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    (f := (groupScheme b c).X.hom) (g := Spec.map (CommRingCat.ofHom (algebraMap F E)))
    ⟨⟨h1, h2⟩, h3⟩ hE

/-- `U(1,1)` is affine over `Spec F`. -/
theorem isAffineHom_groupScheme : IsAffineHom (groupScheme b c).X.hom :=
  isAffineHom_of_isAffine _

include hc in
/-- `U(1,1)` is connected: its base change to `E` is the connected scheme `GL₂`, which maps
onto it. -/
theorem connectedSpace_groupScheme : ConnectedSpace (groupScheme b c).X.left := by
  have hE : ConnectedSpace (baseChangeGroupScheme b c).X.left := by
    have := isIso_left_of_iso (splittingIso b c hc)
    let φ := Scheme.homeoOfIso (asIso (splittingIso b c hc).hom.hom.hom.left)
    exact φ.symm.surjective.connectedSpace φ.symm.continuous
  have : Surjective (Spec.map (CommRingCat.ofHom (algebraMap F E))) :=
    (scalarMap_fpqc (F := F) (E := E)).1
  have hs : Surjective
      (pullback.fst (groupScheme b c).X.hom (Spec.map (CommRingCat.ofHom (algebraMap F E)))) :=
    inferInstance
  have : ConnectedSpace ↥(pullback (groupScheme b c).X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap F E))) : Scheme.{u}) := hE
  exact hs.surj.connectedSpace (pullback.fst (groupScheme b c).X.hom
    (Spec.map (CommRingCat.ofHom (algebraMap F E)))).continuous

include hc in
/-- The geometric unipotent radical of `U(1,1)` is trivial: `F → F̄` factors through `E`, so the
geometric base change is the base change of `GL₂` from `E` to `F̄`. -/
theorem hasTrivialGeometricUnipotentRadical_groupScheme :
    HasTrivialUnipotentRadical
      ((GroupScheme.baseChange (toAlgebraicClosure F)).obj (groupScheme b c)) := by
  have : Module.Finite F E :=
    Module.finite_of_finrank_eq_succ (Algebra.IsQuadraticExtension.finrank_eq_two F E)
  let ι : E →ₐ[F] AlgebraicClosure F := IsAlgClosed.lift
  let ψ : Spec (CommRingCat.of (AlgebraicClosure F)) ⟶ Spec (CommRingCat.of E) :=
    Spec.map (CommRingCat.ofHom ι.toRingHom)
  have hψ : toAlgebraicClosure F = ψ ≫ Spec.map (CommRingCat.ofHom (algebraMap F E)) := by
    rw [toAlgebraicClosure, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun f => Spec.map (CommRingCat.ofHom f))
      (RingHom.ext fun x => (ι.commutes x).symm)
  rw [hψ]
  exact HasTrivialUnipotentRadical.of_iso
    ((Functor.mapGrpNatIso (Over.pullbackComp ψ (Spec.map (CommRingCat.ofHom (algebraMap F E))))).app
        (groupScheme b c) ≪≫ Functor.mapGrpCompIso.app (groupScheme b c) ≪≫
      (GroupScheme.baseChange ψ).mapIso (splittingIso b c hc) ≪≫
      GeneralLinear.baseChangeIso (Fin 2) ψ)
    (hasTrivialUnipotentRadical_generalLinear (AlgebraicClosure F) (Fin 2))

/-- For a nontrivial conjugation `c`, `U(1,1)` is a connected reductive group over `F`. -/
theorem isConnectedReductive : IsConnectedReductiveStatement.{u} := by
  intro F E _ _ _ _ κ _ b c hc
  exact ⟨smooth_groupScheme b c hc, isAffineHom_groupScheme b c,
    connectedSpace_groupScheme b c hc, hasTrivialGeometricUnipotentRadical_groupScheme b c hc⟩

end Langlands.GroupScheme.QuasiSplitUnitary
