import Langlands.AlgebraicGeometry.Modules.LineBundlePrincipalSectionExtension
import Langlands.AlgebraicGeometry.Modules.FibreNeighbourhoodSectionBridge
import Langlands.AlgebraicGeometry.Modules.TensorSectionGenerationLocusProof
import Langlands.AlgebraicGeometry.Picard.AmpleFiniteAffineOpen
import Langlands.AlgebraicGeometry.Picard.ProperFibreAmpleSpreadingProof

/-! # Globalizing ampleness from principal neighbourhoods -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.AlgebraicGeometry.ProjectiveBundle

set_option backward.isDefEq.respectTransparency false

namespace Langlands.SchemeModule

variable {X : Scheme.{u}}

/-- A unit multiple of a section has the same whole generation open. -/
theorem trivializationOpen_smul_unit (M : X.Modules) (r : Γ(X, ⊤))
    (hr : IsUnit r) (s : GlobalSections M) :
    trivializationOpen M (r • s) = trivializationOpen M s := by
  have step (v : (Γ(X, ⊤))ˣ) (t : GlobalSections M) :
      trivializationOpen M t ≤ trivializationOpen M ((v : Γ(X, ⊤)) • t) := by
    apply (maximalTrivialization X M _ _).mp
    apply LineBundleDescent.trivializesOn_of_eq_smul M t _
      (trivializesOn_trivializationOpen M t)
      (X.presheaf.map (homOfLE le_top).op (v : Γ(X, ⊤)))
      (v.isUnit.map (X.presheaf.map (homOfLE le_top).op).hom)
    rw [Scheme.Modules.map_smul]
  obtain ⟨v, rfl⟩ := hr
  apply le_antisymm
  · have h := step v⁻¹ ((v : Γ(X, ⊤)) • s)
    simpa only [smul_smul, Units.inv_mul, one_smul] using h
  · exact step v s

/-- Converting an open section to the actual pullback is bijective. -/
theorem openSection_bijective (M : X.Modules) (U : X.Opens) :
    Function.Bijective (openSection M U) := by
  have hfun : (openSection M U : Γ(M, U) → _ ) =
      sectionPullbackLE U.ι M (show ⊤ ≤ U.ι ⁻¹ᵁ U by simp) := by
    funext s
    exact openSection_eq_sectionPullbackLE M U s
  rw [hfun]
  exact sectionPullbackLE_bijective_of_isOpenImmersion U.ι M (by simp)
    (show ⊤ ≤ U.ι ⁻¹ᵁ U by simp) (by simp)

/-- Restricting a global section and converting it to the actual open pullback
is its usual pulled-back section. -/
theorem openSection_restriction (M : X.Modules) (U : X.Opens)
    (s : GlobalSections M) :
    openSection M U (M.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op s) =
      pullbackSection U.ι M s := by
  rw [openSection_eq_sectionPullbackLE, pullbackSection_eq_sectionPullbackLE]
  exact sectionPullbackLE_restrict U.ι M le_top
    (show ⊤ ≤ U.ι ⁻¹ᵁ U by simp) s

end Langlands.SchemeModule

namespace Langlands.AlgebraicGeometry.Picard

variable {X S : Scheme.{u}}

/-- Every power section of an actual open pullback comes from a section on that open. -/
theorem LineBundle.openPowSection_surjective (L : LineBundle X) (U : X.Opens) (n : ℕ) :
    Function.Surjective (L.openPowSection U (n := n)) := by
  exact (ConcreteCategory.bijective_of_isIso
    ((actualPullbackTensorPowIso U.ι L.obj n).hom.app ⊤)).surjective.comp
      (openSection_bijective (tensorPow L.obj n) U).surjective

/-- Ampleness globalizes from principal open neighbourhoods on a compact
quasi-separated scheme. -/
theorem LineBundle.isAmple_of_principal_neighbourhoods
    [CompactSpace X] [QuasiSeparatedSpace X] (L : LineBundle X)
    (hL : ∀ x : X, ∃ f : Γ(X, ⊤), x ∈ X.basicOpen f ∧
      ((LineBundle.pullback (X.basicOpen f).ι).obj L).IsAmple) :
    L.IsAmple := by
  refine ⟨inferInstance, fun x => ?_⟩
  obtain ⟨f, hxf, hlocal⟩ := hL x
  let D := X.basicOpen f
  let y : D.toScheme := ⟨x, hxf⟩
  obtain ⟨n, hn, s, hys, hs⟩ := hlocal.exists_section y
  obtain ⟨s₀, hs₀⟩ := L.openPowSection_surjective D n s
  let M : LineBundle X := ⟨tensorPow L.obj n, tensorPow_isLocallyFreeRankOne X L n⟩
  obtain ⟨k, t, ht⟩ := PrincipalSectionExtension.exists_global M f s₀
  have hres : D.ι ⁻¹ᵁ trivializationOpen M.obj t =
      ((LineBundle.pullback D.ι).obj L).sectionOpen s := by
    rw [← lineBundlePullbackSectionOpen X D.toScheme D.ι M t,
      ← openSection_restriction M.obj D t]
    rw [ht, openSection_smul, trivializationOpen_smul_unit]
    · rw [← hs₀]
      change trivializationOpen _ (openSection M.obj D s₀) =
        trivializationOpen _
          ((actualPullbackTensorPowIso D.ι L.obj n).hom.app ⊤
            (openSection M.obj D s₀))
      exact (trivializationOpen_mapIso _ _).symm
    · exact ((X.toRingedSpace.isUnit_res_basicOpen f).pow k).map D.topIso.inv.hom
  let z := tensorSection (structureModule X) M.obj f t
  let a := (tensorLeftUnitor M.obj).hom.app ⊤ z
  have ha : L.sectionOpen a = D ⊓ trivializationOpen M.obj t := by
    change trivializationOpen M.obj ((tensorLeftUnitor M.obj).hom.app ⊤ z) = _
    rw [trivializationOpen_mapIso]
    change trivializationOpen (tensorObj (LineBundle.trivial X).obj M.obj)
      (tensorSection (LineBundle.trivial X).obj M.obj f t) = _
    rw [tensorSectionGenerationLocus X (LineBundle.trivial X) M f t]
    change trivializationOpen (structureModule X) f ⊓ trivializationOpen M.obj t = _
    rw [trivializationOpen_structureModule]
  refine ⟨n, hn, a, ?_, ?_⟩
  · rw [ha]
    refine ⟨hxf, ?_⟩
    change y ∈ D.ι ⁻¹ᵁ trivializationOpen M.obj t
    rwa [hres]
  · rw [ha]
    have himage : D.ι ''ᵁ ((LineBundle.pullback D.ι).obj L).sectionOpen s =
        D ⊓ trivializationOpen M.obj t := by
      rw [← hres, Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    rw [← himage]
    exact hs.image_of_isOpenImmersion D.ι

/-- Over an affine base, ampleness on inverse images of neighbourhoods
of every base point implies absolute ampleness. -/
theorem LineBundle.isAmple_of_affine_base_neighbourhoods
    [CompactSpace X] [QuasiSeparatedSpace X] [IsAffine S]
    (f : X ⟶ S) (L : LineBundle X)
    (hL : ∀ s : S, ∃ V : S.Opens, s ∈ V ∧
      ((LineBundle.pullback (f ⁻¹ᵁ V).ι).obj L).IsAmple) :
    L.IsAmple := by
  apply L.isAmple_of_principal_neighbourhoods
  intro x
  obtain ⟨V, hxV, hV⟩ := hL (f x)
  obtain ⟨r, hrV, hxr⟩ := (isAffineOpen_top S).exists_basicOpen_le
    (V := V) ⟨f x, hxV⟩ (by trivial)
  let a : Γ(X, ⊤) := f.appTop r
  have hD : X.basicOpen a = f ⁻¹ᵁ S.basicOpen r :=
    (Scheme.preimage_basicOpen_top f r).symm
  have hDV : X.basicOpen a ≤ f ⁻¹ᵁ V := by
    rw [hD]
    exact f.preimage_mono hrV
  let j := X.homOfLE hDV
  have hj : IsAffineHom j := by
    have : IsAffineHom (j ≫ (f ⁻¹ᵁ V).ι) := by
      rw [X.homOfLE_ι]
      infer_instance
    exact IsAffineHom.of_comp j (f ⁻¹ᵁ V).ι
  let : IsAffineHom j := hj
  refine ⟨a, ?_, ?_⟩
  · rw [hD]
    exact hxr
  · exact (hV.pullback_of_isAffineHom j).of_iso (openPullbackIso L.obj hDV)

/-- A specified line bundle on a proper family over a noetherian affine base
is ample if it is ample on every residue-field fibre. -/
theorem LineBundle.isAmple_of_fibrewise_over_affine
    [IsAffine S] [IsLocallyNoetherian S]
    (f : X ⟶ S) [IsProper f] (L : LineBundle X)
    (hL : ∀ s : S, ((LineBundle.pullback (f.fiberι s)).obj L).IsAmple) :
    L.IsAmple := by
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  apply L.isAmple_of_affine_base_neighbourhoods f
  intro s
  obtain ⟨V, hs, _, hV⟩ := properFibreAmpleSpreading X S f L s (hL s)
  exact ⟨V, hs, hV⟩

end Langlands.AlgebraicGeometry.Picard
