import Langlands.GroupScheme.CocycleAffineRefinement
import Langlands.GroupScheme.Rational.CentralMuArchimedeanCorrection
import Langlands.GroupScheme.Rational.SimplyConnectedHasseAlmostSimple
import Langlands.GroupScheme.SimplyConnected.LocalCocycleVanishingProof
import Langlands.Global.AdelicFunctoriality.LocalDegree

/-! # Hasse reduction for central isogenies with roots-of-unity kernel -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain
open scoped Langlands.Global.AdelicFunctoriality.FiniteExtension

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

open Langlands.Global.AdelicFunctoriality

/-- Simply connected cocycles are trivial on the actual pullback cover at a finite place. -/
theorem Cocycle.isTrivial_at_finitePlace {F L : Type u} [Field F] [NumberField F]
    [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    {G : GroupScheme (Spec (CommRingCat.of F))} (hG : IsSimplyConnected G)
    (ξ : Cocycle G (GaloisCocycle.cover F L)) (v : Global.FinitePlace F) :
    (ξ.baseChangePullback (Spec.algebraMap F (Global.FiniteCompletion F v))).IsTrivial := by
  let : NumberField L := NumberField.of_module_finite F L
  obtain ⟨w, hw⟩ := exists_place_above (L := L) v
  let K := v.adicCompletion F
  let M := w.adicCompletion L
  let : FiniteDimensional K M := FiniteExtension.local_finite v w
  let : IsGalois K M := isGalois_adicCompletion v w
  let d := Global.CompletionPadic.topologicalData v
  let : ValuativeRel K := d.valuativeRel
  let : IsNonarchimedeanLocalField K := d.localField
  let Gv := (GroupScheme.baseChange (Spec.algebraMap F K)).obj G
  have hGv : IsSimplyConnected Gv := isSimplyConnectedFieldExtension F K G hG
  let : IsAffineHom Gv.X.hom := hGv.isSemisimple.isConnectedReductive.isAffineHom
  apply GaloisCocycle.isTrivial_baseChange_of_scalarExtension (M := M)
  exact localSimplyConnectedCocycleVanishing K Gv hGv M
    (GaloisCocycle.scalarExtension (K := K) (M := M) ξ)

/-- The simply connected arithmetic kernel over number fields only needs infinite-place tests. -/
theorem Cocycle.LocallyTrivial.of_archimedean {F L : Type u} [Field F] [NumberField F]
    [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    {G : GroupScheme (Spec (CommRingCat.of F))} (hG : IsSimplyConnected G)
    {ξ : Cocycle G (GaloisCocycle.cover F L)} (h : ξ.ArchimedeanTrivial) : ξ.LocallyTrivial := by
  rintro (v | v)
  · exact h v
  · exact ξ.isTrivial_at_finitePlace hG v

/-- The Hasse kernel assertion for a target with a simply connected central cover and
roots-of-unity kernel. -/
def NumberFieldMuKernelHasseStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G H : GroupScheme (Spec (CommRingCat.of F))) (f : G ⟶ H), IsSimplyConnected G →
    IsCentralIsogeny f →
    ∀ n : ℕ, 0 < n → Nonempty (kernel f ≅ (mu (Spec (CommRingCat.of F)) n).toGrp) →
    ∀ (L : Type u) [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
      (ξ : Cocycle H (GaloisCocycle.cover F L)), ξ.LocallyTrivial → ξ.IsTrivial

private theorem isTrivial_of_fieldRefine
    {F L E : Type u} [Field F] [Field L] [Field E] [Algebra F L] [Algebra F E] [Algebra L E]
    [IsScalarTower F L E] {G : GroupScheme (Spec (CommRingCat.of F))}
    {ξ : Cocycle G (GaloisCocycle.cover F L)}
    (h : (ξ.refine (GaloisCocycle.coverMap F L E)).IsTrivial) : ξ.IsTrivial := by
  obtain ⟨hs, hf, hq⟩ := fieldExtension_fpqc F E
  let : Surjective (GaloisCocycle.cover F E).hom := hs
  let : Flat (GaloisCocycle.cover F E).hom := hf
  let : QuasiCompact (GaloisCocycle.cover F E).hom := hq
  exact Cocycle.IsTrivial.of_refine_fpqcCover _ h

/-- The simply connected Hasse kernel implies the kernel for every such central quotient. -/
theorem numberFieldMuKernelHasse_of_simplyConnected
    (hsc : NumberFieldSimplyConnectedGaloisHasseKernelStatement.{u}) :
    NumberFieldMuKernelHasseStatement.{u} := by
  intro F _ _ G H f hG hf n hn hex L _ _ _ _ ξ hξ
  obtain ⟨e⟩ := hex
  let : NumberField L := NumberField.of_module_finite F L
  obtain ⟨E, _, _, _, _, _, _, ζ, hζ⟩ := hf.exists_cocycle_lift_of_mu_kernel n hn.ne' e ξ hξ
  have hζloc : (ζ.map f).LocallyTrivial := hζ.symm ▸ hξ.refine (GaloisCocycle.coverMap F L E)
  obtain ⟨M, _, _, _, _, _, _, α, hα⟩ :=
    hf.exists_corrected_archimedeanTrivial n e hn ζ (fun v => hζloc (.inl v))
  let r := GaloisCocycle.coverMap F E M
  let δ := (ζ.refine r).divCentral α (kernelι f) hf.isCentral_kernelι
  have hδ : δ.IsTrivial := hsc F G hG M δ (Cocycle.LocallyTrivial.of_archimedean hG hα)
  obtain ⟨a, ha⟩ := hδ.map f
  have hzr : ((ζ.map f).refine r).IsTrivial := by
    refine ⟨a, fun x y => ?_⟩
    have he := Cocycle.divCentral_kernel_map_toFun (ζ.refine r) α hf.isCentral_kernelι x y
    exact he.symm.trans (ha x y)
  have hE : (ζ.map f).IsTrivial := isTrivial_of_fieldRefine hzr
  rw [hζ] at hE
  exact isTrivial_of_fieldRefine hE

end Langlands.GroupScheme
