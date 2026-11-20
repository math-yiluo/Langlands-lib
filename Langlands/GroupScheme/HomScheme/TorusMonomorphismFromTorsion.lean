import Langlands.AlgebraicGeometry.DiscreteValuationFibreIsomorphism
import Langlands.GroupScheme.CentralIsogeny.FpqcReflection
import Langlands.GroupScheme.KernelTriviality
import Langlands.GroupScheme.Torus.MultiplicativeTypeSubgroups
import Langlands.GroupScheme.Torus.MultiplicativeTypeTorsionDensityProof
import Langlands.GroupScheme.Torus.RelativeFieldComparison
import Langlands.GroupScheme.Torus.RelativeGeometry
import Langlands.GroupScheme.UnitSubgroup

/-! # Monomorphism of a relative torus map from its positive torsion -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme

private theorem isIso_kernel_hom_of_field_torsion_mono {k : Type u} [Field k]
    {H G : GroupScheme (Spec (CommRingCat.of k))} [IsCommMonObj H.X]
    [IsSeparated G.X.hom] (hH : IsMultiplicativeType H) (f : H ⟶ G)
    (ht : ∀ n : ℕ, 0 < n → Mono (torsionι H (n : ℤ) ≫ f).hom.hom.left) :
    IsIso (kernel f).X.hom := by
  let K := kernel f
  have hK : IsMultiplicativeType K := hH.of_isClosedSubgroup (kernelι f)
    (show IsClosedImmersion (kernelι f).hom.hom.left from inferInstance)
  have : IsSeparated H.X.hom := fieldSeparated k H
  have : IsSeparated K.X.hom := by
    rw [← Over.w (kernelι f).hom.hom]
    infer_instance
  have : IsIso (kernelUnit K).hom.hom.left := by
    apply (multiplicativeTypeTorsionDensity k K hK).1 _ _ (kernelUnit_isClosedSubgroup K)
    intro n hn T x hx
    have hx' : (x ≫ (kernelι f).hom.hom) ^ (n : ℤ) = 1 := by
      rw [zpow_natCast]
      let g := ((yonedaGrp.map (kernelι f)).app (.op T)).hom
      change g x ^ n = 1
      rw [← map_pow, hx, map_one]
    obtain ⟨y, hy, _⟩ := (existsUnique_torsion_lift_iff H (n : ℤ) T _).mpr hx'
    have : Mono (torsionι H (n : ℤ) ≫ f).hom.hom.left := ht n hn
    have : Mono (torsionι H (n : ℤ) ≫ f).hom.hom := Over.mono_of_mono_left _
    have hy1 : y = 1 := by
      apply (cancel_mono (torsionι H (n : ℤ) ≫ f).hom.hom).mp
      rw [MonObj.one_comp]
      change y ≫ (torsionι H (n : ℤ)).hom.hom ≫ f.hom.hom = 1
      rw [← Category.assoc, hy]
      exact (kernelPointsEquiv f T x).property
    have hx1 : x = 1 := by
      apply (cancel_mono (kernelι f).hom.hom).mp
      rw [MonObj.one_comp, ← hy, hy1, MonObj.one_comp]
    exact ⟨T.hom, by rw [hx1]; rfl⟩
  exact isIso_of_hom_comp_eq_id _ (kernelUnit K).hom.hom.w

/-- A relative torus homomorphism into a separated group is monomorphic
as soon as every positive torsion restriction is monomorphic. -/
theorem mono_of_torus_torsion_mono {S : Scheme.{u}} {H G : GroupScheme S}
    [IsCommMonObj H.X] [IsSeparated G.X.hom] (hH : RelativeTorus.IsTorus H) (f : H ⟶ G)
    (ht : ∀ n : ℕ, 0 < n → Mono (torsionι H (n : ℤ) ≫ f).hom.hom.left) :
    Mono f.hom.hom := by
  let K := kernel f
  have : LocallyOfFiniteType H.X.hom := by
    have : Smooth H.X.hom := hH.smooth
    infer_instance
  have : LocallyOfFiniteType K.X.hom := by
    rw [← Over.w (kernelι f).hom.hom]
    infer_instance
  let e := (kernelUnit K).hom.hom
  have : Flat (Grp.trivial (Over S)).X.hom := by change Flat (𝟙 S); infer_instance
  have : LocallyOfFinitePresentation (Grp.trivial (Over S)).X.hom := by
    change LocallyOfFinitePresentation (𝟙 S)
    infer_instance
  have he : IsIso e := by
    apply Langlands.AlgebraicGeometry.isIso_of_residueField_fibres
    intro s
    let b := S.fromSpecResidueField s
    let B := baseChange b
    have hs : IsSeparated (B.obj G).X.hom :=
      MorphismProperty.pullback_snd (P := @IsSeparated) _ _ inferInstance
    have hf : IsIso (B.obj K).X.hom := by
      apply (baseChange_kernel_hom_isIso_iff b f).mpr
      apply (mono_iff_kernel_hom_isIso (B.map f)).mpr
      apply isIso_kernel_hom_of_field_torsion_mono (hH.baseChange b).isTorus.isMultiplicativeType
      intro n hn
      have : Mono (torsionι H (n : ℤ) ≫ f).hom.hom.left := ht n hn
      have : Mono (B.map (torsionι H (n : ℤ) ≫ f)).hom.hom.left :=
        (baseChange_map_isPullback b _).flip.mono_snd_of_mono
      have hc : torsionι (B.obj H) (n : ℤ) ≫ B.map f =
          (torsionBaseChangeIso b H (n : ℤ)).inv ≫ B.map (torsionι H (n : ℤ) ≫ f) := by
        rw [B.map_comp, ← Category.assoc, torsionBaseChangeIso_inv_ι]
      rw [hc]
      change Mono ((torsionBaseChangeIso b H (n : ℤ)).inv.hom.hom.left ≫
        (B.map (torsionι H (n : ℤ) ≫ f)).hom.hom.left)
      infer_instance
    let e' := (Over.pullback b).map e
    have htriv : IsIso ((Over.pullback b).obj (Grp.trivial (Over S)).X).hom := by
      change IsIso (pullback.snd (𝟙 S) b)
      infer_instance
    have : IsIso (e'.left ≫ (B.obj K).X.hom) := by
      change IsIso (e'.left ≫ ((Over.pullback b).obj K.X).hom)
      rw [e'.w]
      exact htriv
    have : IsIso ((Over.forget _).map e') :=
      IsIso.of_isIso_comp_right e'.left (B.obj K).X.hom
    exact isIso_of_reflects_iso e' (Over.forget _)
  have : IsIso e.left := (Over.forget S).map_isIso e
  have : IsIso K.X.hom := isIso_of_hom_comp_eq_id e.left e.w
  exact mono_of_kernel_hom_isIso f

/-- The positive torsion restrictions of a relative torus homomorphism
jointly detect monomorphism into a separated target. -/
def TorusMonomorphismFromTorsionStatement : Prop :=
  ∀ (S : Scheme.{u}) (H G : GroupScheme S) [IsCommMonObj H.X] [IsSeparated G.X.hom],
    RelativeTorus.IsTorus H → ∀ f : H ⟶ G,
    (∀ n : ℕ, 0 < n → Mono (torsionι H (n : ℤ) ≫ f).hom.hom.left) → Mono f.hom.hom

theorem torusMonomorphismFromTorsion : TorusMonomorphismFromTorsionStatement.{u} := by
  intro S H G _ _ hH f hf
  exact mono_of_torus_torsion_mono hH f hf

end Langlands.GroupScheme
