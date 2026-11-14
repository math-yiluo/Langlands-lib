import Langlands.AlgebraicGeometry.Modules.CechResolution.CohomologyIso
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom

/-! # Čech cohomology of presheaves of modules in the FLT port and actual cohomology -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules.CechBridge

variable {R : CommRingCat.{u}} {X : Scheme.{u}} {π : X ⟶ Spec R}

/-- The `ℕ`-indexed alternating Čech cochain complex of a presheaf of modules of the FLT port,
for an ordered affine cover. -/
def cechComplex (F : OModulePresheaf π) (K : X.OrderedAffineCover) :
    CochainComplex (ModuleCat.{u} R) ℕ :=
  CochainComplex.of (fun i => ModuleCat.of R (F.cochain K i)) (fun i => ModuleCat.ofHom (F.d K i))
    (fun i => by
      apply ModuleCat.hom_ext
      exact F.d_comp_d K i)

lemma cechComplex_d (F : OModulePresheaf π) (K : X.OrderedAffineCover) (n : ℕ) :
    (cechComplex F K).d n (n + 1) = ModuleCat.ofHom (F.d K n) :=
  CochainComplex.of_d (V := ModuleCat.{u} R) (fun i => ModuleCat.of R (F.cochain K i))
    (fun i => ModuleCat.ofHom (F.d K i)) n

/-- The FLT Čech group `HSucc n` is the homology of the Čech complex in degree `n + 1`. -/
def homologySuccEquiv (F : OModulePresheaf π) (K : X.OrderedAffineCover) (n : ℕ) :
    (cechComplex F K).homology (n + 1) ≃ₗ[R] F.HSucc K n := by
  let C := cechComplex F K
  let S := ModuleCat.shortComplexOfCompEqZero (F.d K n) (F.d K (n + 1)) (F.d_comp_d K n)
  let e : C.sc' n (n + 1) (n + 1 + 1) ≅ S :=
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp only [Iso.refl_hom]; exact (cechComplex_d F K n).symm)
      (by simp only [Iso.refl_hom]; exact (cechComplex_d F K (n + 1)).symm)
  exact (C.homologyIsoSc' n (n + 1) (n + 1 + 1) (by simp) (by simp) ≪≫
    ShortComplex.homologyMapIso e ≪≫ S.moduleCatHomologyIso).toLinearEquiv ≪≫ₗ
      Submodule.quotEquivOfEq _ _ (LinearMap.range_codRestrict _ _ _)

/-- For the presheaf of sections of a module, the Čech complex is the Library's
`cechCochainComplex`, so its `HSucc n` is the actual cohomology in degree `n + 1`. -/
def hsuccEquivRelativeCohomology [IsSeparated π] (K : X.OrderedAffineCover) (M : X.Modules)
    [M.IsQuasicoherent] (n : ℕ) :
    (OModulePresheaf.ofModules π M).HSucc K n ≃ₗ[R]
      (DerivedSections.relativeCohomology π (n + 1)).obj M :=
  (homologySuccEquiv (OModulePresheaf.ofModules π M) K n).symm ≪≫ₗ
    (CechResolution.cechCohomologyIso π K M (n + 1)).toLinearEquiv

section AffHom

variable [IsSeparated π] (K : X.OrderedAffineCover) {F G : OModulePresheaf π}

/-- A morphism of presheaves bijective on every intersection of the cover gives isomorphic Čech
complexes. -/
def cechComplexIsoOfBijective (φ : OModulePresheaf.AffHom F G)
    (hφ : ∀ (i : ℕ) (s : K.Idx i), Function.Bijective (φ.app (K.affineInter π s))) :
    cechComplex F K ≅ cechComplex G K :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => (LinearEquiv.ofBijective (φ.cochainMap K i)
      ⟨fun x y hxy => funext fun s => (hφ i s).1 (congrFun hxy s),
        fun y => ⟨fun s => (hφ i s).2 (y s) |>.choose,
          funext fun s => (hφ i s).2 (y s) |>.choose_spec⟩⟩).toModuleIso)
    (by
      rintro i j (rfl : i + 1 = j)
      rw [cechComplex_d, cechComplex_d]
      apply ModuleCat.hom_ext
      exact (φ.cochainMap_comp_d K i).symm)

/-- A morphism of presheaves bijective on every intersection of the cover induces isomorphisms
of the Čech groups `HSucc`. -/
def hsuccEquivOfBijective (φ : OModulePresheaf.AffHom F G)
    (hφ : ∀ (i : ℕ) (s : K.Idx i), Function.Bijective (φ.app (K.affineInter π s))) (n : ℕ) :
    F.HSucc K n ≃ₗ[R] G.HSucc K n :=
  (homologySuccEquiv F K n).symm ≪≫ₗ
    (HomologicalComplex.homologyMapIso (cechComplexIsoOfBijective K φ hφ) (n + 1)).toLinearEquiv ≪≫ₗ
    homologySuccEquiv G K n

end AffHom

end Langlands.AlgebraicGeometry.Modules.CechBridge
