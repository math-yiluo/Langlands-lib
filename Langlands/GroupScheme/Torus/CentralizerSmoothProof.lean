import Langlands.GroupScheme.Torus.CentralizerSmoothStatement
import Langlands.GroupScheme.Torus.MaximalBaseChangeForwardReduction
import Langlands.GroupScheme.Torus.Geometry
import Langlands.GroupScheme.Torus.DiagonalizableFixedSmoothProof
import Langlands.GroupScheme.Rational.KernelCentralizerSmooth

/-! # Proof: smoothness of the centralizer of a torus -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Every closed representative of the centralizer of a closed torus in a smooth affine group
over a field is smooth: split the torus over a field extension, apply smoothness of fixed
subgroups of diagonalizable actions there, and descend. -/
theorem torusCentralizerSmooth : TorusCentralizerSmoothStatement.{u} := by
  intro k _ G _ _ T i hT hi C j hj hjC
  let E := hT.splittingExtension
  set b := Spec.map (CommRingCat.ofHom (algebraMap k E.carrier))
  obtain ⟨hsurj, hflat, hqc⟩ := fieldExtension_fpqc k E.carrier
  apply MorphismProperty.of_pullback_snd_of_descendsAlong
    (P := @Smooth) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    (f := C.X.hom) (g := b) ⟨⟨hsurj, hflat⟩, hqc⟩
  have hGK : Smooth ((GroupScheme.baseChange b).obj G).X.hom := by
    change Smooth (pullback.snd G.X.hom b)
    infer_instance
  have hAK : IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom := by
    change IsAffineHom (pullback.snd G.X.hom b)
    infer_instance
  obtain ⟨I, hI, ⟨e⟩⟩ := E.isSplitTorus
  let : Fintype I := Fintype.ofFinite I
  classical
  have : AddGroup.FG (I → ℤ) := Module.Finite.iff_addGroup_fg.1 inferInstance
  have hjK : (AutomorphicAction.conjugation (H := ((CommGroupScheme.baseChange b).obj T).toGrp)
      ((GroupScheme.baseChange b).map i)).fixedSubgroup.IsRepresentedBy
      ((GroupScheme.baseChange b).map j) := by
    have hfix := AutomorphicAction.conjugation_fixedSubgroup_eq_torusCentralizer
      (C := (CommGroupScheme.baseChange b).obj T) ((GroupScheme.baseChange b).map i)
    rw [hfix, torusCentralizer_baseChange]
    exact hj.baseChange b
  exact Diagonalizable.fixedSubgroup_smooth_of_actingIso
    Diagonalizable.FixedSmooth.fixedSubgroupSmooth _
    (e ≪≫ (Diagonalizable.splitIso (CommRingCat.of E.carrier) (AddEquiv.refl (I → ℤ))).symm)
    hGK hAK _ hjK (hjC.baseChange b)

end Langlands.GroupScheme
